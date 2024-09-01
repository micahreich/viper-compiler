
section .text
global our_code_starts_here
our_code_starts_here:
  mov rax, 3
  add rax, 1
  neg rax
  ret
