
simulator:
	cargo build --features=simulator --release

rvv_vector:
	cargo build --features=use_rvv_vector --release

run:
	RUST_LOG=debug ckb-debugger --max-cycles 1000000000 --bin ../target/riscv64imac-unknown-none-elf/release/rvv-mont-example

expand:
	cargo expand --lib
