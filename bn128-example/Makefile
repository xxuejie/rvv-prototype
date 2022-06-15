
# can't use actions like `time <command>` without this
SHELL := /bin/bash

CKB_DEBUGGER ?= ckb-debugger-rvv
X86_TARGET ?= x86_64-unknown-linux-gnu
ASM64 ?= asm64
all: build

# Run on ckb-vm, using simulator without V extension.
# It takes a lot of time to run.
# Just for development only. Don't try to bench it.
simulator:
	cargo build --features=simulator,use_rvv_vector --bin alt-bn128-example-simulator --release

# Run on ckb-vm, modified code with RISC-V specialized vectorization
rvv-vector:
	cargo build --features=use_rvv_vector --bin alt-bn128-example-rvv-vector --release

# Same as above, run all test cases, for bench
rvv-vector-bench:
	cargo build --features=use_rvv_vector,run_all_cases --bin alt-bn128-example-rvv-vector-bench --release

# Run on ckb-vm, modified code with RISC-V specialized vectorization, use rvv_asm
rvv-asm:
	cargo build --features=use_rvv_asm --bin alt-bn128-example-rvv-asm --release

# Same as above, run all test cases, for bench
rvv-asm-bench:
	cargo build --features=use_rvv_asm,run_all_cases --bin alt-bn128-example-rvv-asm-bench --release

# Run on ckb-vm, original code without RISC-V specialized vectorization.
# Only use RISC-V IMC instructions.
riscv-raw:
	cargo build --bin alt-bn128-example-riscv-raw --release

# same as above, run all test cases, for bench
riscv-raw-bench:
	cargo build --features=run_all_cases --bin alt-bn128-example-riscv-raw-bench --release

# Run on x86, original code
x86-raw:
	cargo build --bin alt-bn128-example-x86-raw --release --target=${X86_TARGET}


build: rvv-vector riscv-raw

run-simulator:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-simulator | fgrep 'Run result: 0'

run-rvv-vector:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-vector | fgrep 'Run result: 0'

run-riscv-raw:
	RUST_LOG=debug time ${CKB_DEBUGGER} --max-cycles 2000000000 --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-riscv-raw | fgrep 'Run result: 0'

run-x86-raw:
	time ./target/${X86_TARGET}/release/alt-bn128-example-x86-raw

run: run-riscv-raw run-rvv-vector

bench: riscv-raw-bench rvv-asm-bench
	time $(ASM64) ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-asm-bench
	time $(ASM64) ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-riscv-raw-bench

x86-bench:
	export CARGO_BUILD_TARGET=x86_64-unknown-linux-gnu
	cargo flamegraph --bin alt-bn128-example-x86-raw
	
pprof-rvv:
	RUST_LOG=debug ${CKB_DEBUGGER} --bin ./target/riscv64imac-unknown-none-elf/release/alt-bn128-example-rvv-vector --pprof target/rvv.pprof
	cat target/rvv.pprof | inferno-flamegraph > target/rvv.svg

expand:
	cargo expand --lib --features=use_rvv_vector
