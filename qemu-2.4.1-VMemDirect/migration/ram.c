/*
 * QEMU System Emulator
 *
 * Copyright (c) 2003-2008 Fabrice Bellard
 * Copyright (c) 2011-2015 Red Hat Inc
 *
 * Authors:
 *  Juan Quintela <quintela@redhat.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#include <stdint.h>
#include <zlib.h>
#include "qemu/bitops.h"
#include "qemu/bitmap.h"
#include "qemu/timer.h"
#include "qemu/main-loop.h"
#include "migration/migration.h"
#include "exec/address-spaces.h"
#include "migration/page_cache.h"
#include "qemu/error-report.h"
#include "trace.h"
#include "exec/ram_addr.h"
#include "qemu/rcu_queue.h"


#define MASATO
#define MURAOKA
//#define CHUNK_PAGES 512 /* 2MB(THP ON) */
#define CHUNK_PAGES 256
#define CHUNK_SIZE (CHUNK_PAGES * TARGET_PAGE_SIZE)
#define SKIP_PAGES (32 * 256) /* first 32 MB */
#ifdef MURAOKA
#include <time.h>

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define MTYPE_1_TO_1 0
#define MTYPE_1_TO_2 1
#define MTYPE_2_TO_1 2
#define SWAP_ON
#define HISTORY_TRANSFER

static int flagi = 0;
static int sfileflg = 0;
int flg_page_count = 0;
int ram_load_count = 0;
static ram_addr_t max_sendaddr = 0;
static ram_addr_t addr_tmp = 0;
static ram_addr_t read_addr = 0;
int pages_count = 0;
int resend_flg = 0;
char *swappath = "/nvme/swapspace";
int *swapfd;
int migrate_type;

unsigned long get_main_mem_size(void);
extern unsigned long *mem_dest; //0:memory 1:swap
unsigned long mem_size;
extern uint8_t *swap_buf;
extern uint8_t *swap_sbuf;

extern unsigned char *history;
static unsigned char bit;
unsigned long page_tmp = 0;

#endif/*MURAOKA*/

#ifdef DEBUG_MIGRATION_RAM
#define DPRINTF(fmt, ...) \
    do { fprintf(stdout, "migration_ram: " fmt, ## __VA_ARGS__); } while (0)
#else
#define DPRINTF(fmt, ...) \
    do { } while (0)
#endif

static bool mig_throttle_on;
static int dirty_rate_high_cnt;
static void check_guest_throttling(void);

static uint64_t bitmap_sync_count;

/***********************************************************/
/* ram save/restore */

#define RAM_SAVE_FLAG_FULL     0x01 /* Obsolete, not used anymore */
#define RAM_SAVE_FLAG_COMPRESS 0x02
#define RAM_SAVE_FLAG_MEM_SIZE 0x04
#define RAM_SAVE_FLAG_PAGE     0x08
#define RAM_SAVE_FLAG_EOS      0x10
#define RAM_SAVE_FLAG_CONTINUE 0x20
#define RAM_SAVE_FLAG_XBZRLE   0x40
/* 0x80 is reserved in migration.h start with 0x100 next */
#define RAM_SAVE_FLAG_COMPRESS_PAGE    0x100

#ifdef MURAOKA
#define RAM_SAVE_FLAG_SWAP          0x200
#endif


static const uint8_t ZERO_TARGET_PAGE[TARGET_PAGE_SIZE];

static inline bool is_zero_range(uint8_t *p, uint64_t size)
{
    return buffer_find_nonzero_offset(p, size) == size;
}

/* struct contains XBZRLE cache and a static page
   used by the compression */
static struct {
    /* buffer used for XBZRLE encoding */
    uint8_t *encoded_buf;
    /* buffer for storing page content */
    uint8_t *current_buf;
    /* Cache for XBZRLE, Protected by lock. */
    PageCache *cache;
    QemuMutex lock;
} XBZRLE;

/* buffer used for XBZRLE decoding */
static uint8_t *xbzrle_decoded_buf;

static void XBZRLE_cache_lock(void)
{
    if (migrate_use_xbzrle())
        qemu_mutex_lock(&XBZRLE.lock);
}

static void XBZRLE_cache_unlock(void)
{
    if (migrate_use_xbzrle())
        qemu_mutex_unlock(&XBZRLE.lock);
}

/*
 * called from qmp_migrate_set_cache_size in main thread, possibly while
 * a migration is in progress.
 * A running migration maybe using the cache and might finish during this
 * call, hence changes to the cache are protected by XBZRLE.lock().
 */
int64_t xbzrle_cache_resize(int64_t new_size)
{
    PageCache *new_cache;
    int64_t ret;

    if (new_size < TARGET_PAGE_SIZE) {
        return -1;
    }

    XBZRLE_cache_lock();

    if (XBZRLE.cache != NULL) {
        if (pow2floor(new_size) == migrate_xbzrle_cache_size()) {
            goto out_new_size;
        }
        new_cache = cache_init(new_size / TARGET_PAGE_SIZE,
                                        TARGET_PAGE_SIZE);
        if (!new_cache) {
            error_report("Error creating cache");
            ret = -1;
            goto out;
        }

        cache_fini(XBZRLE.cache);
        XBZRLE.cache = new_cache;
    }

out_new_size:
    ret = pow2floor(new_size);
out:
    XBZRLE_cache_unlock();
    return ret;
}

/* accounting for migration statistics */
typedef struct AccountingInfo {
    uint64_t dup_pages;
    uint64_t skipped_pages;
    uint64_t norm_pages;
    uint64_t iterations;
    uint64_t xbzrle_bytes;
    uint64_t xbzrle_pages;
    uint64_t xbzrle_cache_miss;
    double xbzrle_cache_miss_rate;
    uint64_t xbzrle_overflows;
} AccountingInfo;

static AccountingInfo acct_info;

static void acct_clear(void)
{
    memset(&acct_info, 0, sizeof(acct_info));
}

uint64_t dup_mig_bytes_transferred(void)
{
    return acct_info.dup_pages * TARGET_PAGE_SIZE;
}

uint64_t dup_mig_pages_transferred(void)
{
    return acct_info.dup_pages;
}

uint64_t skipped_mig_bytes_transferred(void)
{
    return acct_info.skipped_pages * TARGET_PAGE_SIZE;
}

uint64_t skipped_mig_pages_transferred(void)
{
    return acct_info.skipped_pages;
}

uint64_t norm_mig_bytes_transferred(void)
{
    return acct_info.norm_pages * TARGET_PAGE_SIZE;
}

uint64_t norm_mig_pages_transferred(void)
{
    return acct_info.norm_pages;
}

uint64_t xbzrle_mig_bytes_transferred(void)
{
    return acct_info.xbzrle_bytes;
}

uint64_t xbzrle_mig_pages_transferred(void)
{
    return acct_info.xbzrle_pages;
}

uint64_t xbzrle_mig_pages_cache_miss(void)
{
    return acct_info.xbzrle_cache_miss;
}

double xbzrle_mig_cache_miss_rate(void)
{
    return acct_info.xbzrle_cache_miss_rate;
}

uint64_t xbzrle_mig_pages_overflow(void)
{
    return acct_info.xbzrle_overflows;
}

/* This is the last block that we have visited serching for dirty pages
 */
static RAMBlock *last_seen_block;
/* This is the last block from where we have sent data */
static RAMBlock *last_sent_block;
static ram_addr_t last_offset;
static unsigned long *migration_bitmap;
static QemuMutex migration_bitmap_mutex;
static uint64_t migration_dirty_pages;
static uint32_t last_version;
static bool ram_bulk_stage;

struct CompressParam {
    bool start;
    bool done;
    QEMUFile *file;
    QemuMutex mutex;
    QemuCond cond;
    RAMBlock *block;
    ram_addr_t offset;
};
typedef struct CompressParam CompressParam;

struct DecompressParam {
    bool start;
    QemuMutex mutex;
    QemuCond cond;
    void *des;
    uint8 *compbuf;
    int len;
};
typedef struct DecompressParam DecompressParam;

static CompressParam *comp_param;
static QemuThread *compress_threads;
/* comp_done_cond is used to wake up the migration thread when
 * one of the compression threads has finished the compression.
 * comp_done_lock is used to co-work with comp_done_cond.
 */
static QemuMutex *comp_done_lock;
static QemuCond *comp_done_cond;
/* The empty QEMUFileOps will be used by file in CompressParam */
static const QEMUFileOps empty_ops = { };

static bool compression_switch;
static bool quit_comp_thread;
static bool quit_decomp_thread;
static DecompressParam *decomp_param;
static QemuThread *decompress_threads;
static uint8_t *compressed_data_buf;

static int do_compress_ram_page(CompressParam *param);

static void *do_data_compress(void *opaque)
{
    CompressParam *param = opaque;

    while (!quit_comp_thread) {
        qemu_mutex_lock(&param->mutex);
        /* Re-check the quit_comp_thread in case of
         * terminate_compression_threads is called just before
         * qemu_mutex_lock(&param->mutex) and after
         * while(!quit_comp_thread), re-check it here can make
         * sure the compression thread terminate as expected.
         */
        while (!param->start && !quit_comp_thread) {
            qemu_cond_wait(&param->cond, &param->mutex);
        }
        if (!quit_comp_thread) {
            do_compress_ram_page(param);
        }
        param->start = false;
        qemu_mutex_unlock(&param->mutex);

        qemu_mutex_lock(comp_done_lock);
        param->done = true;
        qemu_cond_signal(comp_done_cond);
        qemu_mutex_unlock(comp_done_lock);
    }

    return NULL;
}

static inline void terminate_compression_threads(void)
{
    int idx, thread_count;

    thread_count = migrate_compress_threads();
    quit_comp_thread = true;
    for (idx = 0; idx < thread_count; idx++) {
        qemu_mutex_lock(&comp_param[idx].mutex);
        qemu_cond_signal(&comp_param[idx].cond);
        qemu_mutex_unlock(&comp_param[idx].mutex);
    }
}

void migrate_compress_threads_join(void)
{
    int i, thread_count;

    if (!migrate_use_compression()) {
        return;
    }
    terminate_compression_threads();
    thread_count = migrate_compress_threads();
    for (i = 0; i < thread_count; i++) {
        qemu_thread_join(compress_threads + i);
        qemu_fclose(comp_param[i].file);
        qemu_mutex_destroy(&comp_param[i].mutex);
        qemu_cond_destroy(&comp_param[i].cond);
    }
    qemu_mutex_destroy(comp_done_lock);
    qemu_cond_destroy(comp_done_cond);
    g_free(compress_threads);
    g_free(comp_param);
    g_free(comp_done_cond);
    g_free(comp_done_lock);
    compress_threads = NULL;
    comp_param = NULL;
    comp_done_cond = NULL;
    comp_done_lock = NULL;
}

void migrate_compress_threads_create(void)
{
    int i, thread_count;

    if (!migrate_use_compression()) {
        return;
    }
    quit_comp_thread = false;
    compression_switch = true;
    thread_count = migrate_compress_threads();
    compress_threads = g_new0(QemuThread, thread_count);
    comp_param = g_new0(CompressParam, thread_count);
    comp_done_cond = g_new0(QemuCond, 1);
    comp_done_lock = g_new0(QemuMutex, 1);
    qemu_cond_init(comp_done_cond);
    qemu_mutex_init(comp_done_lock);
    for (i = 0; i < thread_count; i++) {
        /* com_param[i].file is just used as a dummy buffer to save data, set
         * it's ops to empty.
         */
        comp_param[i].file = qemu_fopen_ops(NULL, &empty_ops);
        comp_param[i].done = true;
        qemu_mutex_init(&comp_param[i].mutex);
        qemu_cond_init(&comp_param[i].cond);
        qemu_thread_create(compress_threads + i, "compress",
                           do_data_compress, comp_param + i,
                           QEMU_THREAD_JOINABLE);
    }
}

/**
 * save_page_header: Write page header to wire
 *
 * If this is the 1st block, it also writes the block identification
 *
 * Returns: Number of bytes written
 *
 * @f: QEMUFile where to send the data
 * @block: block that contains the page we want to send
 * @offset: offset inside the block for the page
 *          in the lower bits, it contains flags
 */
static size_t save_page_header(QEMUFile *f, RAMBlock *block, ram_addr_t offset)
{
    size_t size, len;

    qemu_put_be64(f, offset);
    size = 8;

    if (!(offset & RAM_SAVE_FLAG_CONTINUE)) {
        len = strlen(block->idstr);
        qemu_put_byte(f, len);
        qemu_put_buffer(f, (uint8_t *)block->idstr, len);
        size += 1 + len;
    }
    return size;
}

/* Update the xbzrle cache to reflect a page that's been sent as all 0.
 * The important thing is that a stale (not-yet-0'd) page be replaced
 * by the new data.
 * As a bonus, if the page wasn't in the cache it gets added so that
 * when a small write is made into the 0'd page it gets XBZRLE sent
 */
static void xbzrle_cache_zero_page(ram_addr_t current_addr)
{
    if (ram_bulk_stage || !migrate_use_xbzrle()) {
        return;
    }

    /* We don't care if this fails to allocate a new cache page
     * as long as it updated an old one */
    cache_insert(XBZRLE.cache, current_addr, ZERO_TARGET_PAGE,
                 bitmap_sync_count);
}

#define ENCODING_FLAG_XBZRLE 0x1

/**
 * save_xbzrle_page: compress and send current page
 *
 * Returns: 1 means that we wrote the page
 *          0 means that page is identical to the one already sent
 *          -1 means that xbzrle would be longer than normal
 *
 * @f: QEMUFile where to send the data
 * @current_data:
 * @current_addr:
 * @block: block that contains the page we want to send
 * @offset: offset inside the block for the page
 * @last_stage: if we are at the completion stage
 * @bytes_transferred: increase it with the number of transferred bytes
 */
static int save_xbzrle_page(QEMUFile *f, uint8_t **current_data,
                            ram_addr_t current_addr, RAMBlock *block,
                            ram_addr_t offset, bool last_stage,
                            uint64_t *bytes_transferred)
{
    int encoded_len = 0, bytes_xbzrle;
    uint8_t *prev_cached_page;

    if (!cache_is_cached(XBZRLE.cache, current_addr, bitmap_sync_count)) {
        acct_info.xbzrle_cache_miss++;
        if (!last_stage) {
            if (cache_insert(XBZRLE.cache, current_addr, *current_data,
                             bitmap_sync_count) == -1) {
                return -1;
            } else {
                /* update *current_data when the page has been
                   inserted into cache */
                *current_data = get_cached_data(XBZRLE.cache, current_addr);
            }
        }
        return -1;
    }

    prev_cached_page = get_cached_data(XBZRLE.cache, current_addr);

    /* save current buffer into memory */
    memcpy(XBZRLE.current_buf, *current_data, TARGET_PAGE_SIZE);

    /* XBZRLE encoding (if there is no overflow) */
    encoded_len = xbzrle_encode_buffer(prev_cached_page, XBZRLE.current_buf,
                                       TARGET_PAGE_SIZE, XBZRLE.encoded_buf,
                                       TARGET_PAGE_SIZE);
    if (encoded_len == 0) {
        DPRINTF("Skipping unmodified page\n");
        return 0;
    } else if (encoded_len == -1) {
        DPRINTF("Overflow\n");
        acct_info.xbzrle_overflows++;
        /* update data in the cache */
        if (!last_stage) {
            memcpy(prev_cached_page, *current_data, TARGET_PAGE_SIZE);
            *current_data = prev_cached_page;
        }
        return -1;
    }

    /* we need to update the data in the cache, in order to get the same data */
    if (!last_stage) {
        memcpy(prev_cached_page, XBZRLE.current_buf, TARGET_PAGE_SIZE);
    }

    /* Send XBZRLE based compressed page */
    bytes_xbzrle = save_page_header(f, block, offset | RAM_SAVE_FLAG_XBZRLE);
    qemu_put_byte(f, ENCODING_FLAG_XBZRLE);
    qemu_put_be16(f, encoded_len);
    qemu_put_buffer(f, XBZRLE.encoded_buf, encoded_len);
    bytes_xbzrle += encoded_len + 1 + 2;
    acct_info.xbzrle_pages++;
    acct_info.xbzrle_bytes += bytes_xbzrle;
    *bytes_transferred += bytes_xbzrle;

    return 1;
}

/* Called with rcu_read_lock() to protect migration_bitmap */
static inline
ram_addr_t migration_bitmap_find_and_reset_dirty(MemoryRegion *mr,
                                                 ram_addr_t start)
{
    unsigned long base = mr->ram_addr >> TARGET_PAGE_BITS;
    unsigned long nr = base + (start >> TARGET_PAGE_BITS);
    uint64_t mr_size = TARGET_PAGE_ALIGN(memory_region_size(mr));
    unsigned long size = base + (mr_size >> TARGET_PAGE_BITS);
    unsigned long *bitmap;

    unsigned long next;

    bitmap = atomic_rcu_read(&migration_bitmap);
    if (ram_bulk_stage && nr > base) {
        next = nr + 1;
    } else {
        next = find_next_bit(bitmap, size, nr);
    }

    if (next < size) {
        clear_bit(next, bitmap);
        migration_dirty_pages--;
    }
    return (next - base) << TARGET_PAGE_BITS;
}

/* Called with rcu_read_lock() to protect migration_bitmap */
static void migration_bitmap_sync_range(ram_addr_t start, ram_addr_t length)
{
    unsigned long *bitmap;
    bitmap = atomic_rcu_read(&migration_bitmap);
    migration_dirty_pages +=
        cpu_physical_memory_sync_dirty_bitmap(bitmap, start, length);
}


/* Fix me: there are too many global variables used in migration process. */
static int64_t start_time;
static int64_t bytes_xfer_prev;
static int64_t num_dirty_pages_period;
static uint64_t xbzrle_cache_miss_prev;
static uint64_t iterations_prev;

static void migration_bitmap_sync_init(void)
{
    start_time = 0;
    bytes_xfer_prev = 0;
    num_dirty_pages_period = 0;
    xbzrle_cache_miss_prev = 0;
    iterations_prev = 0;
}

/* Called with iothread lock held, to protect ram_list.dirty_memory[] */
static void migration_bitmap_sync(void)
{
    RAMBlock *block;
    uint64_t num_dirty_pages_init = migration_dirty_pages;
    MigrationState *s = migrate_get_current();
    int64_t end_time;
    int64_t bytes_xfer_now;

    bitmap_sync_count++;

    if (!bytes_xfer_prev) {
        bytes_xfer_prev = ram_bytes_transferred();
    }

    if (!start_time) {
        start_time = qemu_clock_get_ms(QEMU_CLOCK_REALTIME);
    }

    trace_migration_bitmap_sync_start();
    address_space_sync_dirty_bitmap(&address_space_memory);

    qemu_mutex_lock(&migration_bitmap_mutex);
    rcu_read_lock();
    QLIST_FOREACH_RCU(block, &ram_list.blocks, next) {
        migration_bitmap_sync_range(block->mr->ram_addr, block->used_length);
    }
    rcu_read_unlock();
    qemu_mutex_unlock(&migration_bitmap_mutex);

    trace_migration_bitmap_sync_end(migration_dirty_pages
                                    - num_dirty_pages_init);
    num_dirty_pages_period += migration_dirty_pages - num_dirty_pages_init;
    end_time = qemu_clock_get_ms(QEMU_CLOCK_REALTIME);

    /* more than 1 second = 1000 millisecons */
    if (end_time > start_time + 1000) {
        if (migrate_auto_converge()) {
            /* The following detection logic can be refined later. For now:
               Check to see if the dirtied bytes is 50% more than the approx.
               amount of bytes that just got transferred since the last time we
               were in this routine. If that happens >N times (for now N==4)
               we turn on the throttle down logic */
            bytes_xfer_now = ram_bytes_transferred();
            if (s->dirty_pages_rate &&
               (num_dirty_pages_period * TARGET_PAGE_SIZE >
                   (bytes_xfer_now - bytes_xfer_prev)/2) &&
               (dirty_rate_high_cnt++ > 4)) {
                    trace_migration_throttle();
                    mig_throttle_on = true;
                    dirty_rate_high_cnt = 0;
             }
             bytes_xfer_prev = bytes_xfer_now;
        } else {
             mig_throttle_on = false;
        }
        if (migrate_use_xbzrle()) {
            if (iterations_prev != acct_info.iterations) {
                acct_info.xbzrle_cache_miss_rate =
                   (double)(acct_info.xbzrle_cache_miss -
                            xbzrle_cache_miss_prev) /
                   (acct_info.iterations - iterations_prev);
            }
            iterations_prev = acct_info.iterations;
            xbzrle_cache_miss_prev = acct_info.xbzrle_cache_miss;
        }
        s->dirty_pages_rate = num_dirty_pages_period * 1000
            / (end_time - start_time);
        s->dirty_bytes_rate = s->dirty_pages_rate * TARGET_PAGE_SIZE;
        start_time = end_time;
        num_dirty_pages_period = 0;
    }
    s->dirty_sync_count = bitmap_sync_count;
}

/**
 * save_zero_page: Send the zero page to the stream
 *
 * Returns: Number of pages written.
 *
 * @f: QEMUFile where to send the data
 * @block: block that contains the page we want to send
 * @offset: offset inside the block for the page
 * @p: pointer to the page
 * @bytes_transferred: increase it with the number of transferred bytes
 */
static int save_zero_page(QEMUFile *f, RAMBlock *block, ram_addr_t offset,
                          uint8_t *p, uint64_t *bytes_transferred)
{
    int pages = -1;

    if (is_zero_range(p, TARGET_PAGE_SIZE)) {
        acct_info.dup_pages++;

        *bytes_transferred += save_page_header(f, block,
                                               offset | RAM_SAVE_FLAG_COMPRESS);
        qemu_put_byte(f, 0);
        *bytes_transferred += 1;
        pages = 1;
    }

    return pages;
}



/**
 * ram_save_page: Send the given page to the stream
 *
 * Returns: Number of pages written.
 *
 * @f: QEMUFile where to send the data
 * @block: block that contains the page we want to send
 * @offset: offset inside the block for the page
 * @last_stage: if we are at the completion stage
 * @bytes_transferred: increase it with the number of transferred bytes
 */
#ifdef MURAOKA
static int ram_save_page_1_1(QEMUFile *f, RAMBlock* block, ram_addr_t offset,
                         bool last_stage, uint64_t *bytes_transferred)
#else
static int ram_save_page(QEMUFile *f, RAMBlock* block, ram_addr_t offset, 
                        bool last_stage, uint64_t *bytes_transferred)
#endif
{
    int pages = -1;
    uint64_t bytes_xmit;
    ram_addr_t current_addr;
    MemoryRegion *mr = block->mr;
    uint8_t *p;
    int ret;
    bool send_async = true;

    p = memory_region_get_ram_ptr(mr) + offset;

    /* In doubt sent page as normal */
    bytes_xmit = 0;
    ret = ram_control_save_page(f, block->offset,
                           offset, TARGET_PAGE_SIZE, &bytes_xmit);
    if (bytes_xmit) {
        *bytes_transferred += bytes_xmit;
        pages = 1;
    }

    XBZRLE_cache_lock();

    current_addr = block->offset + offset;

    if (block == last_sent_block) {
        offset |= RAM_SAVE_FLAG_CONTINUE;
    }
    if (ret != RAM_SAVE_CONTROL_NOT_SUPP) {
        if (ret != RAM_SAVE_CONTROL_DELAYED) {
            if (bytes_xmit > 0) {
                acct_info.norm_pages++;
            } else if (bytes_xmit == 0) {
                acct_info.dup_pages++;
            }
        }
    } else {
        pages = save_zero_page(f, block, offset, p, bytes_transferred);
        if (pages > 0) {
            /* Must let xbzrle know, otherwise a previous (now 0'd) cached
             * page would be stale
             */
            xbzrle_cache_zero_page(current_addr);
        } else if (!ram_bulk_stage && migrate_use_xbzrle()) {
            pages = save_xbzrle_page(f, &p, current_addr, block,
                                     offset, last_stage, bytes_transferred);
            if (!last_stage) {
                /* Can't send this cached data async, since the cache page
                 * might get updated before it gets to the wire
                 */
                send_async = false;
            }
        }
    }

    /* XBZRLE overflow or normal page */
    if (pages == -1) {
        *bytes_transferred += save_page_header(f, block,
                                               offset | RAM_SAVE_FLAG_PAGE);
        if (send_async) {
            qemu_put_buffer_async(f, p, TARGET_PAGE_SIZE);
        } else {
            qemu_put_buffer(f, p, TARGET_PAGE_SIZE);
        }
        *bytes_transferred += TARGET_PAGE_SIZE;
        pages = 1;
        acct_info.norm_pages++;
    }

    XBZRLE_cache_unlock();

    return pages;
}

#ifdef MURAOKA
static int ram_save_page_1_2(QEMUFile *f, RAMBlock* block, ram_addr_t offset,
                         bool last_stage, uint64_t *bytes_transferred)
{
    int pages = -1;
    uint64_t bytes_xmit;
    ram_addr_t current_addr;
    MemoryRegion *mr = block->mr;
    uint8_t *p;
    int ret;
    bool send_async = true;
    int rc = 0;
    int mem_bit;

    p = memory_region_get_ram_ptr(mr) + offset;

    /* In doubt sent page as normal */
    bytes_xmit = 0;
    ret = ram_control_save_page(f, block->offset,
                           offset, TARGET_PAGE_SIZE, &bytes_xmit);
    if (bytes_xmit) {
        *bytes_transferred += bytes_xmit;
        pages = 1;
    }

    XBZRLE_cache_lock();

    current_addr = block->offset + offset;

    if (block == last_sent_block) {
        offset |= RAM_SAVE_FLAG_CONTINUE;
    }
    if (ret != RAM_SAVE_CONTROL_NOT_SUPP) {
        if (ret != RAM_SAVE_CONTROL_DELAYED) {
            if (bytes_xmit > 0) {
                acct_info.norm_pages++;
            } else if (bytes_xmit == 0) {
                acct_info.dup_pages++;
            }
        }
    } else {
#if 0 /* for experiment */
        pages = save_zero_page(f, block, offset, p, bytes_transferred);
        if (pages > 0) {
            /* Must let xbzrle know, otherwise a previous (now 0'd) cached
             * page would be stale
             */
            xbzrle_cache_zero_page(current_addr);
        } else if (!ram_bulk_stage && migrate_use_xbzrle()) {
            pages = save_xbzrle_page(f, &p, current_addr, block,
                                     offset, last_stage, bytes_transferred);
            if (!last_stage) {
                /* Can't send this cached data async, since the cache page
                 * might get updated before it gets to the wire
                 */
                send_async = false;
            }
        }
#endif /* 0 */
    }

    /* XBZRLE overflow or normal page */
    if (pages == -1) {

#ifdef MURAOKA
        if(current_addr < mem_size){
            mem_bit = test_bit(current_addr/TARGET_PAGE_SIZE, mem_dest);
        }else{   
            mem_bit = 0;
        }
#ifdef SWAP_ON
  
        if(mem_bit == 1){    //swap page
              *bytes_transferred += save_page_header(f, block,
                                 offset | RAM_SAVE_FLAG_SWAP);
        }else{
            *bytes_transferred += save_page_header(f, block,
                                   offset | RAM_SAVE_FLAG_PAGE);
        }

#else
	    *bytes_transferred += save_page_header(f, block,
                                               offset | RAM_SAVE_FLAG_PAGE);

#endif /*SWAP_ON*/
#endif /*MURAOKA*/
       if (send_async) {
            qemu_put_buffer_async(f, p, TARGET_PAGE_SIZE);
        } else {
            qemu_put_buffer(f, p, TARGET_PAGE_SIZE);
        }
        *bytes_transferred += TARGET_PAGE_SIZE;

#ifdef HISTORY_TRANSFER
        if(current_addr < mem_size){
            bit = history[current_addr / 4096];
            qemu_put_byte(f, bit);
            *bytes_transferred++;
        }
#endif
        pages = 1;
        acct_info.norm_pages++;
    }

    XBZRLE_cache_unlock();

    return pages;
}

static int ram_save_page_2_1(QEMUFile *f, RAMBlock* block, ram_addr_t offset,
                         bool last_stage, uint64_t *bytes_transferred)
{
    int pages = -1;
    uint64_t bytes_xmit;
    ram_addr_t current_addr;
    MemoryRegion *mr = block->mr;
    uint8_t *p;
    int ret;
    bool send_async = true;
    int rc = 0;
    int mem_bit;
    ram_addr_t addr_tmp_start, pa_start;

    p = memory_region_get_ram_ptr(mr) + offset;

    /* In doubt sent page as normal */
    bytes_xmit = 0;
    ret = ram_control_save_page(f, block->offset,
                           offset, TARGET_PAGE_SIZE, &bytes_xmit);
    if (bytes_xmit) {
        *bytes_transferred += bytes_xmit;
        pages = 1;
    }

    XBZRLE_cache_lock();

    current_addr = block->offset + offset;

    if (block == last_sent_block) {
        offset |= RAM_SAVE_FLAG_CONTINUE;
    }
    if (ret != RAM_SAVE_CONTROL_NOT_SUPP) {
        if (ret != RAM_SAVE_CONTROL_DELAYED) {
            if (bytes_xmit > 0) {
                acct_info.norm_pages++;
            } else if (bytes_xmit == 0) {
                acct_info.dup_pages++;
            }
        }
    } else {
#if 0 /* for experiment */
        pages = save_zero_page(f, block, offset, p, bytes_transferred);
        if (pages > 0) {
            /* Must let xbzrle know, otherwise a previous (now 0'd) cached
            * page would be stale
            */
        xbzrle_cache_zero_page(current_addr);
        } else if (!ram_bulk_stage && migrate_use_xbzrle()) {
            pages = save_xbzrle_page(f, &p, current_addr, block,
                                     offset, last_stage, bytes_transferred);
            if (!last_stage) {
                /* Can't send this cached data async, since the cache page
                 * might get updated before it gets to the wire
                 */
                send_async = false;
            }
        }
#endif /* 0 */
    }

    /* XBZRLE overflow or normal page */
    if (pages == -1) {

#ifdef MURAOKA
        if(current_addr < mem_size){
            mem_bit = test_bit(current_addr/TARGET_PAGE_SIZE, mem_dest);
        }else{   
            mem_bit = 0;
        }
#ifdef SWAP_ON


            *bytes_transferred += save_page_header(f, block,
                                   offset | RAM_SAVE_FLAG_PAGE);       
#else
        *bytes_transferred += save_page_header(f, block,
                                    offset | RAM_SAVE_FLAG_PAGE);

#endif /*SWAP_ON*/

        if(addr_tmp > current_addr && resend_flg == 0){
            max_sendaddr = addr_tmp;
            resend_flg = 1;
            printf("memory resend\n");
            printf("current_addr = %lu\n",current_addr);
        }
        if(mem_bit == 0){
            if (send_async) {
                qemu_put_buffer_async(f, p, TARGET_PAGE_SIZE);
            } else {
                qemu_put_buffer(f, p, TARGET_PAGE_SIZE);
            }
        }else{
            if(resend_flg == 1){
                printf("resend swap_dada\n");
                rc = pread(swapfd, swap_sbuf, TARGET_PAGE_SIZE, current_addr);
                if(rc < 0){
                    printf("Error: pread save_page%s\n", strerror(errno));
                }
                qemu_put_buffer(f, swap_sbuf, TARGET_PAGE_SIZE);
            }else{
                addr_tmp_start = addr_tmp & ~(CHUNK_SIZE - 1);
                pa_start = current_addr & ~(CHUNK_SIZE - 1);
/*                //if(pa_start == addr_tmp_start && addr_tmp < current_addr){
                if(current_addr - addr_tmp == TARGET_PAGE_SIZE && pa_start != current_addr){
                    qemu_put_buffer(f, swap_sbuf + current_addr - pa_start, TARGET_PAGE_SIZE);                        
                }else{
                    if(addr_tmp >= current_addr){
                        printf("addr_tmp >= current_addr\n");
                    }
                    rc = pread(swapfd, swap_sbuf, CHUNK_SIZE, current_addr);
                    //printf("pread_chunk\n");
                    if(rc < 0){
                        printf("Error: pread save_page%s\n", strerror(errno));
                    }
                    qemu_put_buffer(f, swap_sbuf, TARGET_PAGE_SIZE);
                }
*/
                if(current_addr == pa_start){
                    rc = pread(swapfd, swap_sbuf, CHUNK_SIZE, current_addr);
                    //printf("pread_chunk\n");
                }
                    qemu_put_buffer(f, swap_sbuf + (current_addr - pa_start), TARGET_PAGE_SIZE);                        
                    if((current_addr - pa_start) == (CHUNK_SIZE - 4096)){
                        //printf("pread_chunk2\n");
                    }


            }

//                qemu_put_buffer(f, swap_sbuf, TARGET_PAGE_SIZE);
        }
        addr_tmp = current_addr;
        *bytes_transferred += TARGET_PAGE_SIZE;

#endif /*MURAOKA*/

#ifdef HISTORY_TRANSFER
        if(current_addr < mem_size){
            bit = history[current_addr / 4096];
            qemu_put_byte(f, bit);
            *bytes_transferred++;
        }
#endif
        pages = 1;
        acct_info.norm_pages++;
    }
    XBZRLE_cache_unlock();

    return pages;
}

static int ram_save_page(QEMUFile *f, RAMBlock* block, ram_addr_t offset,
                            bool last_stage, uint64_t *bytes_transferred)
{
    switch(migrate_type){
        case MTYPE_1_TO_1:
            return ram_save_page_1_1(f, block, offset, last_stage,
                                 bytes_transferred);

        case MTYPE_1_TO_2:
            return ram_save_page_1_2(f, block, offset, last_stage,
                                 bytes_transferred);

        case MTYPE_2_TO_1:
            return ram_save_page_2_1(f, block, offset, last_stage,
                                 bytes_transferred);
    }
    printf("invalid migrate_type\n");
    return -1;
}
#endif /* MURAOKA */

static int do_compress_ram_page(CompressParam *param)
{
    int bytes_sent, blen;
    uint8_t *p;
    RAMBlock *block = param->block;
    ram_addr_t offset = param->offset;

    p = memory_region_get_ram_ptr(block->mr) + (offset & TARGET_PAGE_MASK);

    bytes_sent = save_page_header(param->file, block, offset |
                                  RAM_SAVE_FLAG_COMPRESS_PAGE);
    blen = qemu_put_compression_data(param->file, p, TARGET_PAGE_SIZE,
                                     migrate_compress_level());
    bytes_sent += blen;

    return bytes_sent;
}

static inline void start_compression(CompressParam *param)
{
    param->done = false;
    qemu_mutex_lock(&param->mutex);
    param->start = true;
    qemu_cond_signal(&param->cond);
    qemu_mutex_unlock(&param->mutex);
}

static inline void start_decompression(DecompressParam *param)
{
    qemu_mutex_lock(&param->mutex);
    param->start = true;
    qemu_cond_signal(&param->cond);
    qemu_mutex_unlock(&param->mutex);
}

static uint64_t bytes_transferred;

static void flush_compressed_data(QEMUFile *f)
{
    int idx, len, thread_count;

    if (!migrate_use_compression()) {
        return;
    }
    thread_count = migrate_compress_threads();
    for (idx = 0; idx < thread_count; idx++) {
        if (!comp_param[idx].done) {
            qemu_mutex_lock(comp_done_lock);
            while (!comp_param[idx].done && !quit_comp_thread) {
                qemu_cond_wait(comp_done_cond, comp_done_lock);
            }
            qemu_mutex_unlock(comp_done_lock);
        }
        if (!quit_comp_thread) {
            len = qemu_put_qemu_file(f, comp_param[idx].file);
            bytes_transferred += len;
        }
    }
}

static inline void set_compress_params(CompressParam *param, RAMBlock *block,
                                       ram_addr_t offset)
{
    param->block = block;
    param->offset = offset;
}

static int compress_page_with_multi_thread(QEMUFile *f, RAMBlock *block,
                                           ram_addr_t offset,
                                           uint64_t *bytes_transferred)
{
    int idx, thread_count, bytes_xmit = -1, pages = -1;

    thread_count = migrate_compress_threads();
    qemu_mutex_lock(comp_done_lock);
    while (true) {
        for (idx = 0; idx < thread_count; idx++) {
            if (comp_param[idx].done) {
                bytes_xmit = qemu_put_qemu_file(f, comp_param[idx].file);
                set_compress_params(&comp_param[idx], block, offset);
                start_compression(&comp_param[idx]);
                pages = 1;
                acct_info.norm_pages++;
                *bytes_transferred += bytes_xmit;
                break;
            }
        }
        if (pages > 0) {
            break;
        } else {
            qemu_cond_wait(comp_done_cond, comp_done_lock);
        }
    }
    qemu_mutex_unlock(comp_done_lock);

    return pages;
}

/**
 * ram_save_compressed_page: compress the given page and send it to the stream
 *
 * Returns: Number of pages written.
 *
 * @f: QEMUFile where to send the data
 * @block: block that contains the page we want to send
 * @offset: offset inside the block for the page
 * @last_stage: if we are at the completion stage
 * @bytes_transferred: increase it with the number of transferred bytes
 */
static int ram_save_compressed_page(QEMUFile *f, RAMBlock *block,
                                    ram_addr_t offset, bool last_stage,
                                    uint64_t *bytes_transferred)
{
    int pages = -1;
    uint64_t bytes_xmit;
    MemoryRegion *mr = block->mr;
    uint8_t *p;
    int ret;

    p = memory_region_get_ram_ptr(mr) + offset;

    bytes_xmit = 0;
    ret = ram_control_save_page(f, block->offset,
                                offset, TARGET_PAGE_SIZE, &bytes_xmit);
    if (bytes_xmit) {
        *bytes_transferred += bytes_xmit;
        pages = 1;
    }
    if (block == last_sent_block) {
        offset |= RAM_SAVE_FLAG_CONTINUE;
    }
    if (ret != RAM_SAVE_CONTROL_NOT_SUPP) {
        if (ret != RAM_SAVE_CONTROL_DELAYED) {
            if (bytes_xmit > 0) {
                acct_info.norm_pages++;
            } else if (bytes_xmit == 0) {
                acct_info.dup_pages++;
            }
        }
    } else {
        /* When starting the process of a new block, the first page of
         * the block should be sent out before other pages in the same
         * block, and all the pages in last block should have been sent
         * out, keeping this order is important, because the 'cont' flag
         * is used to avoid resending the block name.
         */
        if (block != last_sent_block) {
            flush_compressed_data(f);
            pages = save_zero_page(f, block, offset, p, bytes_transferred);
            if (pages == -1) {
                set_compress_params(&comp_param[0], block, offset);
                /* Use the qemu thread to compress the data to make sure the
                 * first page is sent out before other pages
                 */
                bytes_xmit = do_compress_ram_page(&comp_param[0]);
                acct_info.norm_pages++;
                qemu_put_qemu_file(f, comp_param[0].file);
                *bytes_transferred += bytes_xmit;
                pages = 1;
            }
        } else {
            pages = save_zero_page(f, block, offset, p, bytes_transferred);
            if (pages == -1) {
                pages = compress_page_with_multi_thread(f, block, offset,
                                                        bytes_transferred);
            }
        }
    }

    return pages;
}

/**
 * ram_find_and_save_block: Finds a dirty page and sends it to f
 *
 * Called within an RCU critical section.
 *
 * Returns:  The number of pages written
 *           0 means no dirty pages
 *
 * @f: QEMUFile where to send the data
 * @last_stage: if we are at the completion stage
 * @bytes_transferred: increase it with the number of transferred bytes
 */

static int ram_find_and_save_block(QEMUFile *f, bool last_stage,
                                   uint64_t *bytes_transferred)
{
    RAMBlock *block = last_seen_block;
    ram_addr_t offset = last_offset;
    bool complete_round = false;
    int pages = 0;
    MemoryRegion *mr;

    if (!block)
        block = QLIST_FIRST_RCU(&ram_list.blocks);

    while (true) {
        mr = block->mr;
        offset = migration_bitmap_find_and_reset_dirty(mr, offset);
        if (complete_round && block == last_seen_block &&
            offset >= last_offset) {
            break;
        }
        if (offset >= block->used_length) {
            offset = 0;
            block = QLIST_NEXT_RCU(block, next);
            if (!block) {
                block = QLIST_FIRST_RCU(&ram_list.blocks);
                complete_round = true;
                ram_bulk_stage = false;
                if (migrate_use_xbzrle()) {
                    /* If xbzrle is on, stop using the data compression at this
                     * point. In theory, xbzrle can do better than compression.
                     */
                    flush_compressed_data(f);
                    compression_switch = false;
                }
            }
        } else {
            if (compression_switch && migrate_use_compression()) {
                pages = ram_save_compressed_page(f, block, offset, last_stage,
                                                 bytes_transferred);
            } else {
                pages = ram_save_page(f, block, offset, last_stage,
                                      bytes_transferred);
            }

            /* if page is unmodified, continue to the next */
            if (pages > 0) {
                last_sent_block = block;
                break;
            }
        }
    }

    last_seen_block = block;
    last_offset = offset;

    return pages;
}

void acct_update_position(QEMUFile *f, size_t size, bool zero)
{
    uint64_t pages = size / TARGET_PAGE_SIZE;
    if (zero) {
        acct_info.dup_pages += pages;
    } else {
        acct_info.norm_pages += pages;
        bytes_transferred += size;
        qemu_update_position(f, size);
    }
}

static ram_addr_t ram_save_remaining(void)
{
    return migration_dirty_pages;
}

uint64_t ram_bytes_remaining(void)
{
    return ram_save_remaining() * TARGET_PAGE_SIZE;
}

uint64_t ram_bytes_transferred(void)
{
    return bytes_transferred;
}

uint64_t ram_bytes_total(void)
{
    RAMBlock *block;
    uint64_t total = 0;

    rcu_read_lock();
    QLIST_FOREACH_RCU(block, &ram_list.blocks, next)
        total += block->used_length;
    rcu_read_unlock();
    return total;
}

void free_xbzrle_decoded_buf(void)
{
    g_free(xbzrle_decoded_buf);
    xbzrle_decoded_buf = NULL;
}

static void migration_end(void)
{
    /* caller have hold iothread lock or is in a bh, so there is
     * no writing race against this migration_bitmap
     */
    unsigned long *bitmap = migration_bitmap;
    atomic_rcu_set(&migration_bitmap, NULL);
    if (bitmap) {
        memory_global_dirty_log_stop();
        synchronize_rcu();
        g_free(bitmap);
    }

    XBZRLE_cache_lock();
    if (XBZRLE.cache) {
        cache_fini(XBZRLE.cache);
        g_free(XBZRLE.encoded_buf);
        g_free(XBZRLE.current_buf);
        XBZRLE.cache = NULL;
        XBZRLE.encoded_buf = NULL;
        XBZRLE.current_buf = NULL;
    }
    XBZRLE_cache_unlock();
}

static void ram_migration_cancel(void *opaque)
{
    migration_end();
}

static void reset_ram_globals(void)
{
    last_seen_block = NULL;
    last_sent_block = NULL;
    last_offset = 0;
    last_version = ram_list.version;
    ram_bulk_stage = true;
}

#define MAX_WAIT 50 /* ms, half buffered_file limit */

void migration_bitmap_extend(ram_addr_t old, ram_addr_t new)
{
    /* called in qemu main thread, so there is
     * no writing race against this migration_bitmap
     */
    if (migration_bitmap) {
        unsigned long *old_bitmap = migration_bitmap, *bitmap;
        bitmap = bitmap_new(new);

        /* prevent migration_bitmap content from being set bit
         * by migration_bitmap_sync_range() at the same time.
         * it is safe to migration if migration_bitmap is cleared bit
         * at the same time.
         */
        qemu_mutex_lock(&migration_bitmap_mutex);
        bitmap_copy(bitmap, old_bitmap, old);
        bitmap_set(bitmap, old, new - old);
        atomic_rcu_set(&migration_bitmap, bitmap);
        qemu_mutex_unlock(&migration_bitmap_mutex);
        migration_dirty_pages += new - old;
        synchronize_rcu();
        g_free(old_bitmap);
    }
}

/* Each of ram_save_setup, ram_save_iterate and ram_save_complete has
 * long-running RCU critical section.  When rcu-reclaims in the code
 * start to become numerous it will be necessary to reduce the
 * granularity of these critical sections.
 */

static int ram_save_setup(QEMUFile *f, void *opaque)
{
    RAMBlock *block;
    int64_t ram_bitmap_pages; /* Size of bitmap in pages, including gaps */

#ifdef MURAOKA
    //migrate_type = MTYPE_1_TO_1;
    //migrate_type = MTYPE_1_TO_2;
    migrate_type = MTYPE_2_TO_1;
    resend_flg = 0;
    addr_tmp = 0;
    //unsigned long mem_size;

       mem_size = get_main_mem_size();
       printf("mem_size = %lx %lu\n",mem_size,mem_size);
       printf("mem_size = %lu GB\n",mem_size/1024/1024/1024);
       unsigned long nr_pages = mem_size / 4096;
       printf("nr_pages = %lu\n", nr_pages);
       unsigned long main_pages = nr_pages /2;

    if(migrate_type != MTYPE_2_TO_1){


       split_chunk_lru8(history, nr_pages, main_pages);
#endif /*MURAOKA*/
    }

    mig_throttle_on = false;
    dirty_rate_high_cnt = 0;
    bitmap_sync_count = 0;
    migration_bitmap_sync_init();
    qemu_mutex_init(&migration_bitmap_mutex);

    if (migrate_use_xbzrle()) {
        XBZRLE_cache_lock();
        XBZRLE.cache = cache_init(migrate_xbzrle_cache_size() /
                                  TARGET_PAGE_SIZE,
                                  TARGET_PAGE_SIZE);
        if (!XBZRLE.cache) {
            XBZRLE_cache_unlock();
            error_report("Error creating cache");
            return -1;
        }
        XBZRLE_cache_unlock();

        /* We prefer not to abort if there is no memory */
        XBZRLE.encoded_buf = g_try_malloc0(TARGET_PAGE_SIZE);
        if (!XBZRLE.encoded_buf) {
            error_report("Error allocating encoded_buf");
            return -1;
        }

        XBZRLE.current_buf = g_try_malloc(TARGET_PAGE_SIZE);
        if (!XBZRLE.current_buf) {
            error_report("Error allocating current_buf");
            g_free(XBZRLE.encoded_buf);
            XBZRLE.encoded_buf = NULL;
            return -1;
        }

        acct_clear();
    }

    /* iothread lock needed for ram_list.dirty_memory[] */
    qemu_mutex_lock_iothread();
    qemu_mutex_lock_ramlist();
    rcu_read_lock();
    bytes_transferred = 0;
    reset_ram_globals();

    ram_bitmap_pages = last_ram_offset() >> TARGET_PAGE_BITS;
    migration_bitmap = bitmap_new(ram_bitmap_pages);
    bitmap_set(migration_bitmap, 0, ram_bitmap_pages);

    /*
     * Count the total number of pages used by ram blocks not including any
     * gaps due to alignment or unplugs.
     */
    migration_dirty_pages = ram_bytes_total() >> TARGET_PAGE_BITS;

    memory_global_dirty_log_start();
    migration_bitmap_sync();
    qemu_mutex_unlock_ramlist();
    qemu_mutex_unlock_iothread();

    qemu_put_be64(f, ram_bytes_total() | RAM_SAVE_FLAG_MEM_SIZE);

    QLIST_FOREACH_RCU(block, &ram_list.blocks, next) {
        qemu_put_byte(f, strlen(block->idstr));
        qemu_put_buffer(f, (uint8_t *)block->idstr, strlen(block->idstr));
        qemu_put_be64(f, block->used_length);
    }

    rcu_read_unlock();

    ram_control_before_iterate(f, RAM_CONTROL_SETUP);
    ram_control_after_iterate(f, RAM_CONTROL_SETUP);

    qemu_put_be64(f, RAM_SAVE_FLAG_EOS);

    return 0;
}

static int ram_save_iterate(QEMUFile *f, void *opaque)
{
    int ret;
    int i;
    int64_t t0;
    int pages_sent = 0;

    rcu_read_lock();
    if (ram_list.version != last_version) {
        reset_ram_globals();
    }

    /* Read version before ram_list.blocks */
    smp_rmb();

    ram_control_before_iterate(f, RAM_CONTROL_ROUND);

    t0 = qemu_clock_get_ns(QEMU_CLOCK_REALTIME);
    i = 0;
    while ((ret = qemu_file_rate_limit(f)) == 0) {
        int pages;

        pages = ram_find_and_save_block(f, false, &bytes_transferred);
        /* no more pages to sent */
        if (pages == 0) {
            break;
        }
        pages_sent += pages;
        acct_info.iterations++;
        check_guest_throttling();
        /* we want to check in the 1st loop, just in case it was the 1st time
           and we had to sync the dirty bitmap.
           qemu_get_clock_ns() is a bit expensive, so we only check each some
           iterations
        */
        if ((i & 63) == 0) {
            uint64_t t1 = (qemu_clock_get_ns(QEMU_CLOCK_REALTIME) - t0) / 1000000;
            if (t1 > MAX_WAIT) {
                DPRINTF("big wait: %" PRIu64 " milliseconds, %d iterations\n",
                        t1, i);
                break;
            }
        }
        i++;
    }
    flush_compressed_data(f);
    rcu_read_unlock();

    /*
     * Must occur before EOS (or any QEMUFile operation)
     * because of RDMA protocol.
     */
    ram_control_after_iterate(f, RAM_CONTROL_ROUND);

    qemu_put_be64(f, RAM_SAVE_FLAG_EOS);
    bytes_transferred += 8;

    ret = qemu_file_get_error(f);
    if (ret < 0) {
        return ret;
    }

    return pages_sent;
}

/* Called with iothread lock */
static int ram_save_complete(QEMUFile *f, void *opaque)
{
    rcu_read_lock();

    migration_bitmap_sync();

    ram_control_before_iterate(f, RAM_CONTROL_FINISH);

    /* try transferring iterative blocks of memory */

    /* flush all remaining blocks regardless of rate limiting */
    while (true) {
        int pages;

        pages = ram_find_and_save_block(f, true, &bytes_transferred);
        /* no more blocks to sent */
        if (pages == 0) {
            break;
        }
    }

    flush_compressed_data(f);
    ram_control_after_iterate(f, RAM_CONTROL_FINISH);

    rcu_read_unlock();

    migration_end();
    qemu_put_be64(f, RAM_SAVE_FLAG_EOS);

    return 0;
}

static uint64_t ram_save_pending(QEMUFile *f, void *opaque, uint64_t max_size)
{
    uint64_t remaining_size;

    remaining_size = ram_save_remaining() * TARGET_PAGE_SIZE;

    if (remaining_size < max_size) {
        qemu_mutex_lock_iothread();
        rcu_read_lock();
        migration_bitmap_sync();
        rcu_read_unlock();
        qemu_mutex_unlock_iothread();
        remaining_size = ram_save_remaining() * TARGET_PAGE_SIZE;
    }
    return remaining_size;
}

static int load_xbzrle(QEMUFile *f, ram_addr_t addr, void *host)
{
    unsigned int xh_len;
    int xh_flags;

    if (!xbzrle_decoded_buf) {
        xbzrle_decoded_buf = g_malloc(TARGET_PAGE_SIZE);
    }

    /* extract RLE header */
    xh_flags = qemu_get_byte(f);
    xh_len = qemu_get_be16(f);

    if (xh_flags != ENCODING_FLAG_XBZRLE) {
        error_report("Failed to load XBZRLE page - wrong compression!");
        return -1;
    }

    if (xh_len > TARGET_PAGE_SIZE) {
        error_report("Failed to load XBZRLE page - len overflow!");
        return -1;
    }
    /* load data and decode */
    qemu_get_buffer(f, xbzrle_decoded_buf, xh_len);

    /* decode RLE */
    if (xbzrle_decode_buffer(xbzrle_decoded_buf, xh_len, host,
                             TARGET_PAGE_SIZE) == -1) {
        error_report("Failed to load XBZRLE page - decode error!");
        return -1;
    }

    return 0;
}

/* Must be called from within a rcu critical section.
 * Returns a pointer from within the RCU-protected ram_list.
 */
#ifdef MASATO
static inline void *host_from_stream_offset(QEMUFile *f,
                                            ram_addr_t offset,
                                            int flags, ram_addr_t *pa)
#else
static inline void *host_from_stream_offset(QEMUFile *f,
                                            ram_addr_t offset,
                                            int flags)
#endif
{
    static RAMBlock *block = NULL;
    char id[256];
    uint8_t len;

    if (flags & RAM_SAVE_FLAG_CONTINUE) {
        if (!block || block->max_length <= offset) {
            error_report("Ack, bad migration stream!");
            return NULL;
        }

#ifdef MASATO
        *pa = block->offset + offset;
#endif

        return memory_region_get_ram_ptr(block->mr) + offset;
    }

    len = qemu_get_byte(f);
    qemu_get_buffer(f, (uint8_t *)id, len);
    id[len] = 0;

    QLIST_FOREACH_RCU(block, &ram_list.blocks, next) {
        if (!strncmp(id, block->idstr, sizeof(id)) &&
            block->max_length > offset) {

#ifdef MASATO
                *pa = block->offset + offset;
#endif
            return memory_region_get_ram_ptr(block->mr) + offset;
        }
    }

    error_report("Can't find block %s!", id);
    return NULL;
}

/*
 * If a page (or a whole RDMA chunk) has been
 * determined to be zero, then zap it.
 */
void ram_handle_compressed(void *host, uint8_t ch, uint64_t size)
{
    if (ch != 0 || !is_zero_range(host, size)) {
        memset(host, ch, size);
    }
}

static void *do_data_decompress(void *opaque)
{
    DecompressParam *param = opaque;
    unsigned long pagesize;

    while (!quit_decomp_thread) {
        qemu_mutex_lock(&param->mutex);
        while (!param->start && !quit_decomp_thread) {
            qemu_cond_wait(&param->cond, &param->mutex);
            pagesize = TARGET_PAGE_SIZE;
            if (!quit_decomp_thread) {
                /* uncompress() will return failed in some case, especially
                 * when the page is dirted when doing the compression, it's
                 * not a problem because the dirty page will be retransferred
                 * and uncompress() won't break the data in other pages.
                 */
                uncompress((Bytef *)param->des, &pagesize,
                           (const Bytef *)param->compbuf, param->len);
            }
            param->start = false;
        }
        qemu_mutex_unlock(&param->mutex);
    }

    return NULL;
}

void migrate_decompress_threads_create(void)
{
    int i, thread_count;

    thread_count = migrate_decompress_threads();
    decompress_threads = g_new0(QemuThread, thread_count);
    decomp_param = g_new0(DecompressParam, thread_count);
    compressed_data_buf = g_malloc0(compressBound(TARGET_PAGE_SIZE));
    quit_decomp_thread = false;
    for (i = 0; i < thread_count; i++) {
        qemu_mutex_init(&decomp_param[i].mutex);
        qemu_cond_init(&decomp_param[i].cond);
        decomp_param[i].compbuf = g_malloc0(compressBound(TARGET_PAGE_SIZE));
        qemu_thread_create(decompress_threads + i, "decompress",
                           do_data_decompress, decomp_param + i,
                           QEMU_THREAD_JOINABLE);
    }
}

void migrate_decompress_threads_join(void)
{
    int i, thread_count;

    quit_decomp_thread = true;
    thread_count = migrate_decompress_threads();
    for (i = 0; i < thread_count; i++) {
        qemu_mutex_lock(&decomp_param[i].mutex);
        qemu_cond_signal(&decomp_param[i].cond);
        qemu_mutex_unlock(&decomp_param[i].mutex);
    }
    for (i = 0; i < thread_count; i++) {
        qemu_thread_join(decompress_threads + i);
        qemu_mutex_destroy(&decomp_param[i].mutex);
        qemu_cond_destroy(&decomp_param[i].cond);
        g_free(decomp_param[i].compbuf);
    }
    g_free(decompress_threads);
    g_free(decomp_param);
    g_free(compressed_data_buf);
    decompress_threads = NULL;
    decomp_param = NULL;
    compressed_data_buf = NULL;
}

static void decompress_data_with_multi_threads(uint8_t *compbuf,
                                               void *host, int len)
{
    int idx, thread_count;

    thread_count = migrate_decompress_threads();
    while (true) {
        for (idx = 0; idx < thread_count; idx++) {
            if (!decomp_param[idx].start) {
                memcpy(decomp_param[idx].compbuf, compbuf, len);
                decomp_param[idx].des = host;
                decomp_param[idx].len = len;
                start_decompression(&decomp_param[idx]);
                break;
            }
        }
        if (idx < thread_count) {
            break;
        }
    }
}

#ifdef MURAOKA
 make_swapfile(void){

   	    int rc = 0;
	    
	    if(sfileflg == 0){
	    	swapfd =open(swappath, O_RDWR|O_CREAT|O_TRUNC|O_DIRECT, 0777);
            if(swapfd<0){
	            printf("Error: open(%d) %s\n",errno, strerror(errno));
			}
	        sfileflg = 1;
		    //rc = truncate(swappath, 2147483648); //2GB
            //rc = truncate(swappath, 12884901888);
            rc = truncate(swappath, get_main_mem_size());
		    if(rc < 0){
    			printf("Error: truncate() %s\n", strerror(errno));
		    }else{
		      printf("made_swapfile\n");
		    }
	    }


}

#endif

static int ram_load(QEMUFile *f, void *opaque, int version_id)
{
    int flags = 0, ret = 0;
    static uint64_t seq_iter;
    int len = 0;

    seq_iter++;

    if (version_id != 4) {
        ret = -EINVAL;
    }
#ifdef MASATO
    ram_addr_t pa;
#endif

#ifdef MURAOKA
    mem_size = get_main_mem_size();
    char vmstat_buf[100];
    int rc = 0;
    //ram_load_count++;
    //printf("ram_load_count=%d\n",ram_load_count);

#endif


    /* This RCU critical section can be very long running.
     * When RCU reclaims in the code start to become numerous,
     * it will be necessary to reduce the granularity of this
     * critical section.
     */
    rcu_read_lock();
    while (!ret && !(flags & RAM_SAVE_FLAG_EOS)) {
        ram_addr_t addr, total_ram_bytes;
        void *host;
        uint8_t ch;

        addr = qemu_get_be64(f);
        flags = addr & ~TARGET_PAGE_MASK;
        addr &= TARGET_PAGE_MASK;

        switch (flags & ~RAM_SAVE_FLAG_CONTINUE) {
        case RAM_SAVE_FLAG_MEM_SIZE:
            /* Synchronize RAM block list */
            total_ram_bytes = addr;
            while (!ret && total_ram_bytes) {
                RAMBlock *block;
                char id[256];
                ram_addr_t length;

                len = qemu_get_byte(f);
                qemu_get_buffer(f, (uint8_t *)id, len);
                id[len] = 0;
                length = qemu_get_be64(f);

                QLIST_FOREACH_RCU(block, &ram_list.blocks, next) {
                    if (!strncmp(id, block->idstr, sizeof(id))) {
                        if (length != block->used_length) {
                            Error *local_err = NULL;

                            ret = qemu_ram_resize(block->offset, length, &local_err);
                            if (local_err) {
                                error_report_err(local_err);
                            }
                        }
                        ram_control_load_hook(f, RAM_CONTROL_BLOCK_REG,
                                              block->idstr);
                        break;
                    }
                }

                if (!block) {
                    error_report("Unknown ramblock \"%s\", cannot "
                                 "accept migration", id);
                    ret = -EINVAL;
                }

                total_ram_bytes -= length;
            }
            break;
        case RAM_SAVE_FLAG_COMPRESS:
#ifdef MASATO
            host = host_from_stream_offset(f, addr, flags, &pa);
#else
            host = host_from_stream_offset(f, addr, flags);
#endif
            if (!host) {
                error_report("Illegal RAM offset " RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }
            ch = qemu_get_byte(f);
            ram_handle_compressed(host, ch, TARGET_PAGE_SIZE);
#ifdef MURAOKA
            clear_bit(pa / TARGET_PAGE_SIZE, mem_dest);
#endif
            break;
        case RAM_SAVE_FLAG_PAGE:
#ifdef MASATO
            host = host_from_stream_offset(f, addr, flags, &pa);
#else
            host = host_from_stream_offset(f, addr, flags);
#endif
            if (!host) {
                error_report("Illegal RAM offset " RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }


#ifdef MURAOKA	    

            if(addr_tmp > pa && resend_flg == 0){
                max_sendaddr =addr_tmp;
                resend_flg = 1;
                printf("memory resend\n");
                printf("pa=%lu\n",pa);
            }

/*
            if(pa -addr_tmp != 4096 && resend_flg == 0){
                pages_count++;
                printf("pages %d\n,addr_tmp = %lu\n, pa = %lu\n",pages_count,addr_tmp,pa); //再送前の不連続ページ数
            }
*/
           addr_tmp = pa;
	
            qemu_flush_chunk();

            qemu_get_buffer(f, host, TARGET_PAGE_SIZE);


#ifdef HISTORY_TRANSFER
            if(pa < mem_size){
            clear_bit(pa / TARGET_PAGE_SIZE, mem_dest);
            bit = qemu_get_byte(f);
            //printf("page = %12lu,bit = %8d\n",pa/TARGET_PAGE_SIZE,bit);
/*            if(page_tmp + 1 < pa/TARGET_PAGE_SIZE && resend_flg == 0){
                while(page_tmp < pa/TARGET_PAGE_SIZE){
                    history[page_tmp] = 255;
                    //printf("set hist page = %lu\n",page_tmp);
                    page_tmp++;
                }
            }
*/        
            history[pa / TARGET_PAGE_SIZE] = bit;
            }
            page_tmp = pa / TARGET_PAGE_SIZE;

#endif
#else
            qemu_get_buffer(f, host, TARGET_PAGE_SIZE); 
#endif
            break;


#ifdef MURAOKA

        case RAM_SAVE_FLAG_SWAP:
#ifdef MASATO
            host = host_from_stream_offset(f, addr, flags, &pa);
#else
            host = host_from_stream_offset(f, pa, flags);
#endif

    	    if(sfileflg == 0)
	          make_swapfile();

            if (!host) {
                error_report("Illegal RAM offset " RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }
	    
	    
	    //  int *str = (int *)host;
//	      printf("pa = %d\n", pa);
//	      printf("host = %x\n",str);
//	      printf("TARGET_PAGE_SIZE = %d\n",TARGET_PAGE_SIZE);
              //int bufd = qemu_get_buffer_swap(f, host, pa, TARGET_PAGE_SIZE);
//	      printf("qemu_get_buffer = %d\n", bufd);

            if(addr_tmp > pa && resend_flg == 0){
                max_sendaddr =addr_tmp;
                resend_flg = 1;
                printf("memory resend\n");
                printf("pa=%lu\n",pa);
            }
/*
            if(pa -addr_tmp != 4096 && resend_flg == 0){
                pages_count++;
                printf("pages %d\n,addr_tmp = %lu\n, pa = %lu\n",pages_count,addr_tmp,pa); //再送前の不連続ページ数
            }
        */
           addr_tmp = pa;

            if(resend_flg == 0){
                qemu_get_buffer_chunk(f, host, pa);
                //qemu_get_buffer_swap(f, host, pa, TARGET_PAGE_SIZE);
            }else{
                //printf("resend pa = %lu\n",pa);
                qemu_flush_chunk();
                qemu_get_buffer_swap(f, host, pa, TARGET_PAGE_SIZE);
            }

            //addr_tmp = pa;
            //qemu_get_buffer_swap(f, host, pa, TARGET_PAGE_SIZE);

#ifdef HISTORY_TRANSFER
            if(pa < mem_size){
                set_bit(pa / TARGET_PAGE_SIZE, mem_dest);
                bit = qemu_get_byte(f);
                //printf("page = %12lu,bit = %8d\n",pa/TARGET_PAGE_SIZE,bit);

/*              if(page_tmp + 1 < pa/TARGET_PAGE_SIZE && resend_flg == 0){
                    while(page_tmp < pa/TARGET_PAGE_SIZE){
                        history[page_tmp] = 255;
                        page_tmp++;
                    }
                }
*/
                history[pa / TARGET_PAGE_SIZE] = bit;
            }
            page_tmp = pa / TARGET_PAGE_SIZE;
#endif
            break;

#endif /*MURAOKA*/


        case RAM_SAVE_FLAG_COMPRESS_PAGE:
#ifdef MASATO
            host = host_from_stream_offset(f, addr, flags, &pa);
#else
            host = host_from_stream_offset(f, addr, flags);
#endif
            if (!host) {
                error_report("Invalid RAM offset " RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }

            len = qemu_get_be32(f);
            if (len < 0 || len > compressBound(TARGET_PAGE_SIZE)) {
                error_report("Invalid compressed data length: %d", len);
                ret = -EINVAL;
                break;
            }
            qemu_get_buffer(f, compressed_data_buf, len);
            decompress_data_with_multi_threads(compressed_data_buf, host, len);
#ifdef MURAOKA
            clear_bit(pa / TARGET_PAGE_SIZE, mem_dest);
#endif
            break;
        case RAM_SAVE_FLAG_XBZRLE:
#ifdef MASATO
            host = host_from_stream_offset(f, addr, flags, &pa);
#else
            host = host_from_stream_offset(f, addr, flags);
#endif
            if (!host) {
                error_report("Illegal RAM offset " RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }
            if (load_xbzrle(f, addr, host) < 0) {
                error_report("Failed to decompress XBZRLE page at "
                             RAM_ADDR_FMT, addr);
                ret = -EINVAL;
                break;
            }
#ifdef MURAOKA
            clear_bit(pa / TARGET_PAGE_SIZE, mem_dest);
#endif
            break;
        case RAM_SAVE_FLAG_EOS:
            /* normal exit */
            break;
        default:
            if (flags & RAM_SAVE_FLAG_HOOK) {
                ram_control_load_hook(f, RAM_CONTROL_HOOK, NULL);
            } else {
                error_report("Unknown combination of migration flags: %#x",
                             flags);
                ret = -EINVAL;
            }
        }
        if (!ret) {
            ret = qemu_file_get_error(f);
        }
    }

    rcu_read_unlock();
    DPRINTF("Completed load of VM with exit code %d seq iteration "
            "%" PRIu64 "\n", ret, seq_iter);
    return ret;

    #ifdef MURAOKA
    //free(swap_buf);
    #endif
}

static SaveVMHandlers savevm_ram_handlers = {
    .save_live_setup = ram_save_setup,
    .save_live_iterate = ram_save_iterate,
    .save_live_complete = ram_save_complete,
    .save_live_pending = ram_save_pending,
    .load_state = ram_load,
    .cancel = ram_migration_cancel,
};

void ram_mig_init(void)
{
    qemu_mutex_init(&XBZRLE.lock);
    register_savevm_live(NULL, "ram", 0, 4, &savevm_ram_handlers, NULL);
}
/* Stub function that's gets run on the vcpu when its brought out of the
   VM to run inside qemu via async_run_on_cpu()*/

static void mig_sleep_cpu(void *opq)
{
    qemu_mutex_unlock_iothread();
    g_usleep(30*1000);
    qemu_mutex_lock_iothread();
}

/* To reduce the dirty rate explicitly disallow the VCPUs from spending
   much time in the VM. The migration thread will try to catchup.
   Workload will experience a performance drop.
*/
static void mig_throttle_guest_down(void)
{
    CPUState *cpu;

    qemu_mutex_lock_iothread();
    CPU_FOREACH(cpu) {
        async_run_on_cpu(cpu, mig_sleep_cpu, NULL);
    }
    qemu_mutex_unlock_iothread();
}

static void check_guest_throttling(void)
{
    static int64_t t0;
    int64_t        t1;

    if (!mig_throttle_on) {
        return;
    }

    if (!t0)  {
        t0 = qemu_clock_get_ns(QEMU_CLOCK_REALTIME);
        return;
    }

    t1 = qemu_clock_get_ns(QEMU_CLOCK_REALTIME);

    /* If it has been more than 40 ms since the last time the guest
     * was throttled then do it again.
     */
    if (40 < (t1-t0)/1000000) {
        mig_throttle_guest_down();
        t0 = t1;
    }
}

#ifdef MURAOKA

/*
 * split pages to memory/swap space
 *
 * history: 8-bit access history per page
 * nr_pages: total number of pages
 * main_pages: number of pages of the physical memory
 */

void split_chunk_lru8(unsigned char *history, unsigned long nr_pages,
                             unsigned long main_pages)
{
    unsigned long histgram[256];
    unsigned short *max_hists;
    unsigned short max_history;
    int i, index;
    unsigned long pfn;
    unsigned long sum = 0;
    long left = 0;
    unsigned long addr;
    max_hists = (unsigned short *)malloc(nr_pages / CHUNK_PAGES *
                                         sizeof(unsigned short));
    for (i = 0; i < 256; i++)
    histgram[i] = 0;

    /* create a histgram of access history (0-255) */
    for (pfn = 0; pfn < nr_pages; pfn += CHUNK_PAGES) {
        max_history = 0;
        for (i = 0; i < CHUNK_PAGES; i++){
            if (max_history < history[pfn + i])
                max_history = history[pfn + i];
        }

        max_hists[pfn / CHUNK_PAGES] = max_history;
        index = max_history;
        histgram[index]++;
    }

    /* find a threshold (index) for sending to the physical memory */
    for (index = 255; index >= 0; index--) {
        sum += histgram[index] * CHUNK_PAGES;
        /* split the pages of the threshold */
        if (sum > main_pages) {
            left = main_pages - (sum - histgram[index] * CHUNK_PAGES);
            break;
        }
    }

    for (pfn = 0; pfn < nr_pages; pfn += CHUNK_PAGES) {
        addr = pfn * 4096;
        max_history = max_hists[pfn / CHUNK_PAGES];

        if (max_history > index) {
	    /* send to the physical memory over the threshold */
	        for (i = 0; i < CHUNK_PAGES; i++)
	            clear_bit(pfn+i,mem_dest);
        }
        else if (max_history < index) {
	    /* send to the swap space under the threshold */
	        for (i = 0; i < CHUNK_PAGES; i++)
	            set_bit(pfn+i, mem_dest);
        }
        else {
            if (left > 0) {
                /* send some pages of the threshold to the physical memory */
                for (i = 0; i < CHUNK_PAGES; i++)
		            clear_bit(pfn+i, mem_dest);
                    left -= CHUNK_PAGES;
            }
            else {
                /* send the others to the swap space */
                for (i = 0; i < CHUNK_PAGES; i++)
		            set_bit(pfn+i,mem_dest);
            }
        }
    }

    free(max_hists);
}

#endif /*MURAOKA*/
