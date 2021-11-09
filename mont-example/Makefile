
all: 
	cargo build

run:
	RUST_LOG=debug ckb-debugger --max-cycles 1000000000 --bin ../target/riscv64imac-unknown-none-elf/debug/rvv-mont-example

expand:
	cargo expand --lib
