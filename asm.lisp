; Assember written in plancklisp
; Copyright (C) 2026 nineties

(import "asm/core.lisp")

(def args (commandline-args))
(when (< (length args) 3) (abort "no input file"))
(def sourcefile (nth 2 args))

(def asm-code (read-sexp-list sourcefile))
(when (= asm-code 'error) (abort "parse error"))

(print asm-code)
