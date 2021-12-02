CKB_DEBUGGER ?= ckb-debugger-rvv


simulator:
	cargo build --features=simulator,use_rvv_vector --bin rvv-tests-simulator --release

rvv-asm:
	cargo build --features=use_rvv_vector --bin rvv-tests-rvv-asm --release

raw:
	cargo build --bin rvv-tests-raw --release

build: simulator rvv-asm raw

run-simulator:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/rvv-tests-simulator

run-rvv-asm:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/rvv-tests-rvv-asm

run-raw:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/rvv-tests-raw

run: run-simulator run-rvv-asm run-raw


expand:
	cargo expand --lib
