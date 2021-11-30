
CKB_DEBUGGER ?= ckb-debugger-rvv

simulator:
	cargo build --features=simulator,use_rvv_vector --bin alt-bn128-example-simulator --release

rvv-asm:
	cargo build --features=use_rvv_vector --bin alt-bn128-example-rvv-asm --release

raw:
	cargo build --bin alt-bn128-example-raw --release

build: simulator rvv-asm raw

run-simulator:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-simulator

run-rvv-asm:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm

run-raw:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-raw

run-bench-mont:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm -- bench_mont

run: run-simulator run-rvv-asm run-raw

pprof-rvv:
	ckb-vm-pprof-rvv --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm --arg bench_mont |  inferno-flamegraph > target/rvv.svg

expand:
	cargo expand --lib --features=use_rvv_vector

install-tools:
	cargo install --git https://github.com/mohanson/ckb-vm-pprof.git --branch rvv
