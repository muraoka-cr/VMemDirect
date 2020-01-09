# VMemDirect
VMemDirect achieves efficient migration of large-memory VMs using Private virtual memory.

VMemDirect creates private swap space for each VM on HDDs in a destination host and integrates private virtual memory
with VM migration. 

# Requirement
- OS
  - Linux 4.11

- Virtualization Software
  - QEMU-KVM 2.4.1

# Install
Add files in VMemDirect/qemu-2.4.1-VMemDirect to qemu-2.4.1

`cd qemu-2.4.1`

`./configure --target-list=x86_64-softmmu`

`make`

`make install`

`cp /usr/local/bin/qemu-system-x86_64 /usr/bin/`
