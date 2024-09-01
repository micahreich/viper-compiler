section .text
    global _start

_start:
    mov rax, 0x2000001    ; syscall number for exit in macOS
    xor rdi, rdi          ; exit status 0
    syscall               ; make the syscall
