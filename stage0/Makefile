# zero-to-compiler -
# Copyright (C) 2025 nineties

default: planckforth

planckforth: planckforth.xxd
	xxd -r -c 8 $< > planckforth
	chmod +x planckforth

.PHONY: clean test
clean:
	rm -f planckforth

test: planckfoth
