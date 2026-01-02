; Assember written in plancklisp
; Copyright (C) 2026 nineties

(import "asm/core.lisp")

(def args (commandline-args))
(when (< (length args) 3) (abort "no input file"))
(def source (nth 2 args))
(puts source)
