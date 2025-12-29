# zero-to-compiler -
# Copyright (C) 2025 nineties

default:
	$(MAKE) -C stage0

.PHONY: clean test
clean:
	$(MAKE) clean -C stage0

test: default
	$(MAKE) test -C stage0
