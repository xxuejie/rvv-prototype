
CKB_DEBUGGER ?= ckb-debugger-rvv
TARGET ?= x86_64-apple-darwin
all: build

# Run on ckb-vm, using simulator without V extension.
# It takes a lot of time to run.
# Just for development only. Don't try to bench it.
simulator:
	cargo build --features=simulator,use_rvv_vector --bin alt-bn128-example-simulator --release

# Run on ckb-vm, modified code with RISC-V specialized vectorization
rvv-asm:
	cargo build --features=use_rvv_vector --bin alt-bn128-example-rvv-asm --release

# Run on ckb-vm, original code without RISC-V specialized vectorization.
# Only use RISC-V IMC instructions.
riscv-raw:
	cargo build --bin alt-bn128-example-riscv-raw --release

# Run on x86, original code
x86-raw:
	cargo build --bin alt-bn128-example-x86-raw --release --target=${TARGET}


build: rvv-asm riscv-raw

run-simulator:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-simulator

run-rvv-asm:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm

run-riscv-raw:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-riscv-raw

run-x86-raw:
	time ./target/${TARGET}/release/alt-bn128-example-x86-raw

run-bench-mont:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm -- bench_mont

run: run-riscv-raw run-rvv-asm

pprof-rvv:
	RUST_LOG=debug ${CKB_DEBUGGER} --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm --pprof target/rvv.pprof
	cat target/rvv.pprof | inferno-flamegraph > target/rvv.svg

expand:
	cargo expand --lib --features=use_rvv_vector
