This is a modified version of [Uint](https://github.com/paritytech/parity-common/tree/master/uint). 

Modification:
* Use `const generic` instead of macros

Warning: don't use `from_little_endian`, `from_big_endian` series functions in performance critical scenario.
Construct Uint by:
```Rust
let buf: &[u64; 4] = <...>;
Uint::<4>(buf.clone())
```

