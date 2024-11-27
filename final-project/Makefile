UNAME := $(shell uname)

.PRECIOUS: tests/%.s

ifeq ($(UNAME), Linux)
ARCH := elf64
endif
ifeq ($(UNAME), Darwin)
ARCH := macho64
endif

tests/%.s: tests/%.snek src/main.rs
	cargo run -- $< tests/$*.s

tests/%.run: tests/%.s runtime/start.rs
	nasm -f $(ARCH) tests/$*.s -o tests/$*.o
	ar rcs tests/lib$*.a tests/$*.o
	rustc -L tests/ -lour_code:$* -lc -C relocation-model=static -C link-args=-no-pie runtime/start.rs -o tests/$*.run

# --target=x86_64-apple-darwin

.PHONY: test
test:
	cargo build
	cargo test

clean:
	rm -f tests/*.a tests/*.s tests/*.run tests/*.o
