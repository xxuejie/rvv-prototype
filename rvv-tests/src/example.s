    .text
    .balign 4
    .global bn256_add
    # bn256_add(xxx)
bn256_add:
    li t0, 1             # AVL = 1
    vsetvli  x0, t0, e256, m1, ta, ma  # Max length vectors of bytes
    vle256.v v1, (a0)
    vle256.v v2, (a1)
    vadd.vv v0, v1, v2
    vse256.v v0, (a3)
    ret
