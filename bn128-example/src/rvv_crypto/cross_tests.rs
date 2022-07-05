// extern crate alloc;
// use alloc::format;
// use ckb_std::syscalls::debug;

use super::gfp;
use core::mem::size_of;

pub fn entry() {
    test_memory_alignments();
    test_multi_batch_gfp_mul();
    test_gfp_mul_with_carry();
    test_gfp_add();
    test_gfp_sub();
    test_gfp_neg();
    test_gfp_invert();
    test_gfp_sqrt();
}

pub fn test_memory_alignments() {
    assert_eq!(size_of::<gfp::Gfp>(), 32);
    assert_eq!(size_of::<[gfp::Gfp; 64]>(), 32 * 64);
}

pub fn test_multi_batch_gfp_mul() {
    let a = gfp::Gfp([
        11250488846250692438,
        4656389213572280514,
        123,
        8950588588633063607,
    ]);
    let b = gfp::Gfp([
        1755467536201717349,
        17175472035685840286,
        12281294985516866593,
        10355184993929758713,
    ]);

    let aa: [gfp::Gfp; 53] = [
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
    ];

    let bb: [gfp::Gfp; 53] = [
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
        b.clone(),
    ];

    let mut cc: [gfp::Gfp; 53] = [
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
        gfp::Gfp::default(),
    ];

    gfp::mul(&aa, &bb, &mut cc);

    let c = gfp::Gfp([
        15559124068522268778,
        4388294418392014253,
        13026942575419976433,
        9224681250169400588,
    ]);

    for i in 0..53 {
        assert_eq!(cc[i], c);
    }
}

pub fn test_gfp_mul_with_carry() {
    let a = gfp::Gfp([
        0x9c21c3ff7e444f56,
        0x409ed151b2efb0c2,
        0x7c36e0e62c2380b7,
        0xFFFFFFFFFFFFFFFE,
    ]);
    let b = gfp::Gfp([
        0x185cac6c5e089665,
        0xee5b88d120b5b59e,
        0xaa6fecb86184dc21,
        0xFFFFFFFFFFFFFFFE,
    ]);

    let c = a * b;

    assert_eq!(
        c,
        gfp::Gfp([
            8285319100095743200,
            10296293173922742217,
            6548902816963158894,
            10996926879179715675,
        ])
    );
}

pub fn test_gfp_add() {
    let a = gfp::Gfp([
        11250488846250692438,
        4656389213572280514,
        123,
        8950588588633063607,
    ]);
    let b = gfp::Gfp([
        1755467536201717349,
        17175472035685840286,
        213721987,
        10355184993929758713,
    ]);

    let c = a + b;

    assert_eq!(
        c,
        gfp::Gfp([
            11250488846250692436,
            4656389213572280514,
            6165449088406407133,
            8950588588633063606,
        ])
    );
}

pub fn test_gfp_sub() {
    let a = gfp::Gfp([
        11250488846250692438,
        4656389213572280514,
        8950588588633063607,
        123,
    ]);
    let b = gfp::Gfp([
        1755467536201717349,
        17175472035685840286,
        213721987,
        10355184993929758713,
    ]);

    let c = a - b;

    assert_eq!(
        c,
        gfp::Gfp([
            11250488846250692440,
            4656389213572280514,
            2785139500226656597,
            124
        ])
    );
}

pub fn test_gfp_neg() {
    let a = gfp::Gfp([
        11250488846250692438,
        4656389213572280514,
        8950588588633063607,
        123,
    ]);
    let b = gfp::Gfp([
        1755467536201717349,
        17175472035685840286,
        213721987,
        10355184993929758713,
    ]);

    assert_eq!(
        (-a),
        gfp::Gfp([
            8951722763660576529,
            12519082822113559771,
            3330706396883802986,
            10355184993929758590
        ])
    );

    assert_eq!((-b), gfp::Gfp([2, 0, 12281294985303144606, 0]));
}

pub fn test_gfp_invert() {
    let mut a = gfp::Gfp([
        11250488846250692438,
        4656389213572280514,
        8950588588633063607,
        123,
    ]);
    a.invert();

    assert_eq!(
        a,
        gfp::Gfp([
            5773649162373703676,
            376681799751688925,
            2825795984682414485,
            9194822151192441938
        ])
    );
}

pub fn test_gfp_sqrt() {
    let mut b = gfp::Gfp([
        1755467536201717349,
        17175472035685840286,
        213721987,
        10355184993929758713,
    ]);
    b.sqrt();

    assert_eq!(
        b,
        gfp::Gfp([
            16445677904934073556,
            4460622770300838374,
            15941605659616619718,
            2666621848948930475
        ])
    );
}
