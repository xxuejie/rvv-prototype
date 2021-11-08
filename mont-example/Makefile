
all: 
	cargo build --features=simulator

run:
	RUST_LOG=debug ckb-debugger --bin ../target/riscv64imac-unknown-none-elf/debug/rvv-mont-example

expand:
	cargo expand --features=simulator
