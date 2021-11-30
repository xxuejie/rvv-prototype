
simulator:
	cargo build --features=simulator --bin mont-example-simulator --release

rvv-asm:
	cargo build --features=use_rvv_vector --bin mont-example-rvv-asm --release

build: simulator rvv-asm

run-simulator:
	RUST_LOG=debug time ckb-debugger --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/mont-example-simulator

run-rvv-asm:
	RUST_LOG=debug time ckb-debugger --max-cycles 1000000000 --bin ./target/riscv64imac-unknown-none-elf/release/mont-example-rvv-asm

run: run-simulator run-rvv-asm


expand:
	cargo expand --lib
