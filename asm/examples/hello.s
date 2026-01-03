; hello.s

(entry start)

(section data)
(label msg)
    (ascii "Hello World!\n")

(const len (- here msg))

(section text)
(label start)
    (mov %eax 1)                ; SYS_WRITE
    (mov %rdi 1)                ; stdout
    (lea %rsi (mem msg %rip))   ; addr
    (mov %rdx len)              ; length
    (syscall)

    (mov %rax 60)   ; SYS_EXIT
    (xor %rdi %rdi) ; exit code 0
    (syscall)
