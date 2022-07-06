// extern crate alloc;
// use alloc::format;
// use ckb_std::syscalls::debug;

use super::{gfp, gfp12, gfp2, gfp6};
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
    test_gfp_mont_encode_decode();
    test_gfp2_conjugate();
    test_gfp2_mul();
    test_gfp2_mul_scalar();
    test_gfp2_mul_xi();
    test_gfp2_square();
    test_gfp2_invert();
}

pub fn test_memory_alignments() {
    assert_eq!(size_of::<gfp::Gfp>(), 32);
    assert_eq!(size_of::<gfp2::Gfp2>(), 64);
    assert_eq!(size_of::<gfp6::Gfp6>(), 192);
    assert_eq!(size_of::<gfp12::Gfp12>(), 384);
    assert_eq!(size_of::<[gfp::Gfp; 64]>(), 32 * 64);
    assert_eq!(size_of::<[gfp2::Gfp2; 8]>(), 64 * 8);
    assert_eq!(size_of::<[gfp6::Gfp6; 15]>(), 192 * 15);
    assert_eq!(size_of::<[gfp12::Gfp12; 3]>(), 384 * 3);
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

pub fn test_gfp_mont_encode_decode() {
    let mut c = [gfp::Gfp([
        16445677904934073556,
        4460622770300838374,
        15941605659616619718,
        2666621848948930475,
    ])];
    let mut c2 = c.clone();

    gfp::mont_encode(&mut c);
    assert_eq!(
        c[0],
        gfp::Gfp([
            9624780884217287538,
            5996517144107171957,
            5822160666522832865,
            5212132491394613704
        ])
    );

    gfp::mont_decode(&mut c2);
    assert_eq!(
        c2[0],
        gfp::Gfp([
            10658238715199466746,
            1200261570185971627,
            16649185520430610962,
            10253963333291830384
        ])
    );
}

pub fn test_gfp2_conjugate() {
    let mut b = gfp2::Gfp2([
        gfp::Gfp([
            11250488846250692438,
            4656389213572280514,
            8950588588633063607,
            123,
        ]),
        gfp::Gfp([
            1755467536201717349,
            17175472035685840286,
            213721987,
            10355184993929758713,
        ]),
    ]);
    b.conjugate();
    assert_eq!(
        b,
        gfp2::Gfp2([
            gfp::Gfp([
                8951722763660576529,
                12519082822113559771,
                3330706396883802986,
                10355184993929758590
            ]),
            gfp::Gfp([
                1755467536201717349,
                17175472035685840286,
                213721987,
                10355184993929758713
            ]),
        ])
    )
}

pub fn test_gfp2_mul() {
    let mut a = gfp2::Gfp2([
        gfp::Gfp([123123123, 432432523, 12343432423, 5234543534]),
        gfp::Gfp([
            16045690984833335023,
            188899839028173,
            72057594037927935,
            320263130583841,
        ]),
    ]);
    let b = gfp2::Gfp2([
        gfp::Gfp([
            11250488846250692438,
            4656389213572280514,
            8950588588633063607,
            123,
        ]),
        gfp::Gfp([
            1755467536201717349,
            17175472035685840286,
            213721987,
            10355184993929758713,
        ]),
    ]);
    a.mul_ref(&b);
    assert_eq!(
        a,
        gfp2::Gfp2([
            gfp::Gfp([
                2489387057500270750,
                1327558915820720488,
                14258554181724279548,
                7728970882490758084
            ]),
            gfp::Gfp([
                16350727825498422601,
                9698509411976742198,
                13143318885643114834,
                8969178055545188830
            ]),
        ])
    )
}

pub fn test_gfp2_mul_scalar() {
    let mut a = gfp2::Gfp2([
        gfp::Gfp([123123123, 432432523, 12343432423, 5234543534]),
        gfp::Gfp([
            16045690984833335023,
            188899839028173,
            72057594037927935,
            320263130583841,
        ]),
    ]);
    let b = gfp2::Gfp2([
        gfp::Gfp([
            11250488846250692438,
            4656389213572280514,
            8950588588633063607,
            123,
        ]),
        gfp::Gfp([
            1755467536201717349,
            17175472035685840286,
            213721987,
            10355184993929758713,
        ]),
    ]);
    a.mul_scalar(b.x());
    assert_eq!(
        a,
        gfp2::Gfp2([
            gfp::Gfp([
                14721675226523201950,
                18190855699907848119,
                10139236777107793065,
                8752730092639463160
            ]),
            gfp::Gfp([
                10210682578032766731,
                591857751552811498,
                14628815490910629706,
                6936890750848109067
            ]),
        ])
    )
}

pub fn test_gfp2_mul_xi() {
    let mut a = gfp2::Gfp2([
        gfp::Gfp([123123123, 432432523, 12343432423, 5234543534]),
        gfp::Gfp([
            16045690984833335023,
            188899839028173,
            72057594037927935,
            320263130583841,
        ]),
    ]);
    a.mul_xi();
    assert_eq!(
        a,
        gfp2::Gfp2([
            gfp::Gfp([
                16045690985202704392,
                188901136325742,
                72057631068225204,
                320278834214443
            ]),
            gfp::Gfp([
                11243584806957778714,
                566699084651998,
                216172769770351382,
                960784157207989
            ]),
        ])
    )
}

pub fn test_gfp2_square() {
    let mut a = gfp2::Gfp2([
        gfp::Gfp([123123123, 432432523, 12343432423, 5234543534]),
        gfp::Gfp([
            16045690984833335023,
            188899839028173,
            72057594037927935,
            320263130583841,
        ]),
    ]);
    a.square();
    assert_eq!(
        a,
        gfp2::Gfp2([
            gfp::Gfp([
                11531738038236630210,
                13126667805834787204,
                18112355732282690172,
                2273042299983030315
            ]),
            gfp::Gfp([
                7110594916861888900,
                4154062045572080677,
                10875259129568976175,
                5353020417179791541
            ]),
        ])
    )
}

pub fn test_gfp2_invert() {
    let mut a = gfp2::Gfp2([
        gfp::Gfp([123123123, 432432523, 12343432423, 5234543534]),
        gfp::Gfp([
            16045690984833335023,
            188899839028173,
            72057594037927935,
            320263130583841,
        ]),
    ]);
    a.invert();
    assert_eq!(
        a,
        gfp2::Gfp2([
            gfp::Gfp([
                3911113778245031709,
                16268145991669920417,
                16013053519776358408,
                66489236252843360
            ]),
            gfp::Gfp([
                8539473088330600381,
                15068154429679669105,
                5918236881039899774,
                6959643544030151944
            ]),
        ])
    );
}
