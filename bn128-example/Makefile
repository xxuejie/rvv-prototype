
all: 
	cargo build --features=simulator --release

run:
	RUST_LOG=debug ckb-debugger --max-cycles 20000000000 --bin target/riscv64imac-unknown-none-elf/release/alt-bn128-example

expand:
	cargo expand --lib
