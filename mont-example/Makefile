CKB_DEBUGGER ?= ckb-debugger-rvv


simulator:
	cargo build --features=simulator,use_rvv_vector --bin mont-example-simulator --release

rvv-asm:
	cargo build --features=use_rvv_vector --bin mont-example-rvv-asm --release

raw:
	cargo build --bin mont-example-raw --release

build: simulator rvv-asm raw

run-simulator:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/mont-example-simulator

run-rvv-asm:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/mont-example-rvv-asm

run-raw:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/mont-example-raw

run: run-simulator run-rvv-asm run-raw


expand:
	cargo expand --lib
