
# The RISC-V "V" Vector Extension library for CKB contract development

This is a library to help CKB contract developer to write big uint and integer vector calculation code in a subset of Rust, and it automaticly translate the code to RISC-V "V" Vector Extension (we call it RVV later) assembly code by [asm!][inline-asm] macro.

The translation is implemented through a [proc-macro][?] called `rvv_vector`, and the proc-macro can only be used with bare function type (`fn(usize) -> bool`). Currently `rvv_vector` recognize 3 special uint types by it's name and generate RVV asm code them, the special uint types are:

 - U256 (unsigned 256-bit integer)
 - U512 (unsigned 512-bit integer)
 - U1024 (unsigned 1024-bit integer)
 

## How to Use

Here is a simple example:
```rust
use rvv::rvv_vector;

#[rvv_vector]
fn simple_mixed_ops(mut a: U256, b: U256, c: U256) -> U256 {
    if a > b {
        a = a * c.wrapping_add(b);
    }
    a = (a + b) * c;
    a
}
```

There are 3 special uint variables in above function declaration (`a`, `b`, `c`), they are all `U256` type. All calculation between those variables will be translated to RVV asm:

``` rust
fn simple_mixed_ops(mut a: U256, b: U256, c: U256) -> U256 {
    unsafe {asm!("li t0, 1\n.byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 14u8)}
    unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) a.as_ref().as_ptr(), const 7u8, const 208u8, const 2u8, const 16u8)}
    unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) b.as_ref().as_ptr(), const 135u8, const 208u8, const 2u8, const 16u8)}
    unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) c.as_ref().as_ptr(), const 7u8, const 209u8, const 2u8, const 16u8)}
    if {
        unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 1u8, const 16u8, const 104u8)}
        let tmp_bool_t0: i64;
        unsafe {asm!(".byte {0}, {1}, {2}, {3}\nmv {4}, t0", const 215u8, const 162u8, const 56u8, const 64u8, out (reg) tmp_bool_t0)}
        tmp_bool_t0 == 0
    } {
        a = {
            unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 130u8, const 32u8, const 0u8)}
            unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 34u8, const 2u8, const 148u8)}
            let mut tmp_rvv_vector_buf = [0u8; 32usize];
            unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 167u8, const 210u8, const 2u8, const 16u8)}
            unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
        };
    }
    a = {
        unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 131u8, const 0u8, const 0u8)}
        unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 35u8, const 97u8, const 148u8)}
        let mut tmp_rvv_vector_buf = [0u8; 32usize];
        unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 167u8, const 211u8, const 2u8, const 16u8)}
        unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
    };
    a
}
```

If write above code in pure asm code, will be like following pseudo-code:

```assembly
; Set AVL to 1
li t0, 1
; Config vl and vtype 
vsetvl zero, t0, e256, m1, ta, ma 
; Load a to v0 register
mv t0, {a.as_ref().as_ptr()}
vle256.v v0, (t0) 
; Load b to v1 register
mv t0, {b.as_ref().as_ptr()}
vle256.v v1, (t0) 
; Load c to v2 register
mv t0, {c.as_ref().as_ptr()}
vle256.v v2, (t0) 
if {
    vmsgtu.vv v3, v0, v1
    vfirst.m t0, v3
    mv {tmp_bool_t0}, t0
    tmp_bool_t0 == 0
} {
    a = {
        vadd.vv v4, v2, v1
        vmul.vv v5, v0, v4
        mv t0, {tmp_rvv_vector_buf.as_mut_ptr()}
        vse256.v v5, (t0)
        unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf)
    };
}
a = {
    vadd.vv v6, v0, v1
    vmul.vv v7, v6, v2
    mv t0, {tmp_rvv_vector_buf.as_mut_ptr()}
    vse256.v v7, (t0)
    unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
};
a
```

The main steps are:
* Use `vsetvl` to config the RVV instruction settings
* Use `vse{n}.v` to load every `Uint` variable to vector register in function arguments
* Translate every `Uint op Uint` or `Uint.op(Uint)` and store the data to memory if needed


## Syntax Limitation

Follow syntax are not supported in `rvv_vector`:

- `const`/`async`/`await`/`unsafe`/`extern "C"` keywords
- Any generic type declaration
- Closure declaration
- `while` loop
- `match` expression
- Other limits

All limitations will report as compiler error with an error message and point out the source code location:
```
error: while loop is not supported in rvv_vector
  --> src/cases.rs:21:5
   |
21 | /     while true {
22 | |         a += c;
23 | |     }
   | |_____^
error[E0425]: cannot find function `simple_mixed_ops` in this scope
```

## Translate Rules

### Binary operation output same type ([`T = T op T`](https://doc.rust-lang.org/core/ops/index.html#traits)) 

Those ops are directly translated to corresponding RVV instructions.

**NOTE**: Please be aware that the RVV instruction behavior may different from Rust. Follow the link below for more details.

* `+` (`core::ops::Add`)

   Translated to [`vadd.vv vd, vs2, vs1`][vadd-vv]

* `-` (`core::ops::Sub`)

   Translated to [`vsub.vv vd, vs2, vs1`][vsub-vv]

* `*` (`core::ops::Mul`)

   Translated to [`vmul.vv vd, vs2, vs1`][vmul-vv]

* `/` (`core::ops::Div`)

   Translated to [`vdivu.vv vd, vs2, vs1`][vdivu-vv] (different behavior from Rust)

* `%` (`core::ops::Rem`)

   Translated to [`vremu.vv vd, vs2, vs1`][vremu-vv] (different behavior from Rust)

* `^` (`core::ops::BitXor`)

   Translated to [`vxor.vv vd, vs2, vs1`][vxor-vv]

* `&` (`core::ops::BitAnd`)

   Translated to [`vand.vv vd, vs2, vs1`][vand-vv]

* `|` (`core::ops::BitOr`)

   Translated to [`vor.vv vd, vs2, vs1`][vor-vv]

* `<<` (`core::ops::Shl`)

   Translated to [`vsll.vv vd, vs2, vs1`][vsll-vv]

* `>>` (`core::ops::Shr`)

   Translated to [`vsrl.vv vd, vs2, vs1`][vsrl-vv]


### Binary assgin operation ([`T op= T`](https://doc.rust-lang.org/core/ops/index.html#traits))

Same translation as `T = T op T`, the difference is use `vs1` as `vd` (`{inst} vs1, vs2, vs1`).

* `+=` (`core::ops::AddAssign`)
* `-=` (`core::ops::SubAssign`)
* `*=` (`core::ops::MulAssign`)
* `/=` (`core::ops::DivAssign`)
* `%=` (`core::ops::RemAssign`)
* `^=` (`core::ops::BitXorAssign`)
* `&=` (`core::ops::BitAndAssign`)
* `|=` (`core::ops::BitOrAssign`)
* `<<=` (`core::ops::ShlAssign`)
* `>>=` (`core::ops::ShrAssign`)

### Binary operation output bool type ([`bool = T op T`](https://doc.rust-lang.org/core/cmp/index.html#traits))
* `==` (`core::cmp::Eq`)

   Translated to [`vmseq.vv vd, vs2, vs1`][vmseq-vv]

* `!=` (`core::cmp::Eq`)

   Translated to [`vmsne.vv vd, vs2, vs1`][vmsne-vv]

* `<` (`core::cmp::Ord`)

   Translated to [`vmsltu.vv vd, vs2, vs1`][vmsltu-vv]

* `>` (`core::cmp::Ord`)

   Translated to [`vmsltu.vv vd, vs1, vs2`][vmsltu-vv]

* `<=` (`core::cmp::Ord`)

   Translated to [`vmsleu.vv vd, vs2, vs1`][vmsleu-vv]

* `>=` (`core::cmp::Ord`)

   Translated to [`vmsleu.vv vd, vs1, vs2`][vmsleu-vv]


### Call special uint methods (`wrapping_{op}`)
* `wrapping_add` (same translation as `+`)
* `wrapping_sub` (same translation as `-`)
* `wrapping_mul` (same translation as `*`)
* `wrapping_div` (same translation as `/`)
* `wrapping_rem` (same translation as `%`)

### Call special uint methods (`overflowing_{op}`)
* `overflowing_add`

Translated to:
```
vadd.vv v1, v2, v3
vmsltu.vv v4, v1, v2
vfirst.m t0, v4
if t0 == 0 {
    (v1, true)
} else {
    (v1, false)
}
```

* `overflowing_sub`

Translated to:
```
vsub.vv v1, v2, v3
vmsltu.vv v4, v2, v3
vfirst.m t0, v4
if t0 == 0 {
    (v1, true)
} else {
    (v1, false)
}
```

* `overflowing_mul`

Translated to:
```
vmul.vv v1, v2, v3
vmsne.vi v4 v1, 0
vfirst.m t0, v4
if t0 == 0 {
    vdivu.vv v4, v1, v2
    vmsne.vv v4, v4, v3
    vfirst.m t1, v4
    (v1, t1 == 0)
} else {
    (v1, false)
}
```

### Call special uint methods (`checked_{op}`)
* `checked_add`

Translated to:
```
let (value, overflow) = self.overflowing_add(other);
if overflow {
    None
} else {
    Some(value)
}
```

* `checked_sub`

Translated to:
```
vmsltu.vv v4, v2, v3
vfirst.m t0, v4
if t0 == 0 {
    None
} else {
    vsub.vv v1, v2, v3
    Some(v1)
}
```

* `checked_mul`

Translated to:
```
let (value, overflow) = self.overflowing_mul(other);
if overflow {
    None
} else {
    Some(value)
}
```

* `checked_div`

Translated to:
```
vmseq.vi v4, v2, 0  # (v2 == vs1)
vfirst.m t0, v4
if t0 == 0 {
    None
} else {
    vdivu.vv v1, v2, v3
    Some(v1)
}
```

* `checked_rem`

Translated to:
```
// Same as checked_div()
```

### Call special uint methods (`saturating_{op}`)
* `saturating_add`

Translated to:
```
vsaddu.vv vd, vs2, vs1, vm
```

* `saturating_sub`

Translated to:
```
vssubu.vv vd, vs2, vs1, vm
```

* `saturating_mul`

Translated to:
```
vmul.vv v1, v2, v3
vmsne.vi v4 v1, 0
vfirst.m t0, v4
if t0 == 0 {
    vdivu.vv v4, v1, v2
    vmsne.vv v4, v4, v3
    vfirst.m t1, v4
    if t1 == 0 {
        Uxx::max_value()
    } else {
        v1
    }
} else {
    v1
}
```

## Debugging

For some advanced purposes you may want to see the actual code to be compiled, you can use [`cargo-expand`][cargo-expand] to see the generated code.

For example, if you want see the generated code of `fn op_add()` in `rvv-tests/src/cases.rs`:

```shell
cd rvv-tests
cargo expand --lib cases::op_add
```

It will output following code:
```rust
fn op_add(a: U256, b: U256) -> U256 {
    let _ = "li t0, 1";
    let _ = "243462231 - vsetvl zero, t0, e256, m1, ta, ma";
    unsafe {asm!("li t0, 1\n.byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 14u8)}
    let _ = "268619783 - vle256.v v0, (t0)";
    unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) a.as_ref().as_ptr(), const 7u8, const 208u8, const 2u8, const 16u8)}
    let _ = "268619911 - vle256.v v1, (t0)";
    unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) b.as_ref().as_ptr(), const 135u8, const 208u8, const 2u8, const 16u8)}
    {
        let _ = "vadd.vv v2, v0, v1 - 33111";
        unsafe {asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 129u8, const 0u8, const 0u8)}
        let _ = "vse256.v v2, (t0) - 268620071";
        let mut tmp_rvv_vector_buf = [0u8; 32usize];
        unsafe {asm!("mv t0, {0}\n.byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 209u8, const 2u8, const 16u8)}
        unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
    }
}
```

[inline-asm]: https://rust-lang.github.io/rfcs/2873-inline-asm.html
[cargo-expand]: https://github.com/dtolnay/cargo-expand
[vadd-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vadd_vv.h
[vsub-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vsub_vv.h
[vmul-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vmul_vv.h
[vdivu-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vdivu_vv.h
[vremu-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vremu_vv.h
[vxor-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vxor_vv.h
[vand-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vand_vv.h
[vor-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vor_vv.h
[vsll-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vsll_vv.h
[vsrl-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vsrl_vv.h
[vmseq-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vmseq_vv.h
[vmsne-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vmsne_vv.h
[vmsltu-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vmsltu_vv.h
[vmsleu-vv]: https://github.com/riscv-software-src/riscv-isa-sim/tree/master/riscv/insns/vmsleu_vv.h
