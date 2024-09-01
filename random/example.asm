section .text
    global _start      ; Entry point for the program
    extern move_one    ; Declare external function (if needed)

_start:
    call move_one      ; Call the function to move 1 into rax
    call exit_program  ; Call the function to exit the program

move_one:
    mov rax, 1         ; Move the value 1 into rax
    mov [rsp-8], rax

exit_program:
    mov rax, 60        ; Syscall number for exit (sys_exit)
    xor rdi, rdi       ; Exit code 0
    syscall            ; Invoke syscall
