
all: 
	cargo build

run:
	RUST_LOG=debug ckb-debugger --max-cycles 20000000000 --bin ../target/riscv64imac-unknown-none-elf/debug/alt_bn128

expand:
	cargo expand --lib
