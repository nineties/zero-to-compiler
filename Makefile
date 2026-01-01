# zero-to-compiler -
# Copyright (C) 2025 nineties

default:
	$(MAKE) -C stage1

.PHONY: clean test
clean:
	$(MAKE) clean -C stage1

test: default
	$(MAKE) test -C stage1
