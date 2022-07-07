// See https://github.com/cloudflare/bn256/blob/9bd9f73a0273ed2f42707ed13b3e36d38baa2a49/constants.go
// for the meaning of all constants.
pub const NP: [u64; 4] = [
    0x2387f9007f17daa9,
    0x734b3343ab8513c8,
    0x2524282f48054c12,
    0x38997ae661c3ef3c,
];
pub const P2: [u64; 4] = [
    0x185cac6c5e089667,
    0xee5b88d120b5b59e,
    0xaa6fecb86184dc21,
    0x8fb501e34aa387f9,
];
pub const RN1: [u64; 4] = [
    0xcbb781e36236117d,
    0xcc65f3bcec8c91b,
    0x2eab68888ea1f515,
    0x1fc5c0956f92f825,
];
pub const P_MINUS2: [u64; 4] = [
    0x185cac6c5e089665,
    0xee5b88d120b5b59e,
    0xaa6fecb86184dc21,
    0x8fb501e34aa387f9,
];
pub const P_PLUS1_OVER4: [u64; 4] = [
    0x86172b1b1782259a,
    0x7b96e234482d6d67,
    0x6a9bfb2e18613708,
    0x23ed4078d2a8e1fe,
];
pub const R3: [u64; 4] = [
    0x2af2dfb9324a5bb8,
    0x388f899054f538a4,
    0xdf2ff66396b107a7,
    0x24ebbbb3a2529292,
];
pub const R2: [u64; 4] = [
    0x9c21c3ff7e444f56,
    0x409ed151b2efb0c2,
    0xc6dc37b80fb1651,
    0x7c36e0e62c2380b7,
];
pub const XI_TO_2P_MINUS2_OVER3: [[u64; 4]; 2] = [
    [
        0x51678e7469b3c52a,
        0x4fb98f8b13319fc9,
        0x29b2254db3f1df75,
        0x1c044935a3d22fb2,
    ],
    [
        0x4d2ea218872f3d2c,
        0x2fcb27fc4abe7b69,
        0xd31d972f0e88ced9,
        0x53adc04a00a73b15,
    ],
];
pub const XI_TO_P_MINUS1_OVER3: [[u64; 4]; 2] = [
    [
        0x4f59e37c01832e57,
        0xae6be39ac2bbbfe4,
        0xe04ea1bb697512f8,
        0x3097caa8fc40e10e,
    ],
    [
        0xf8606916d3816f2c,
        0x1e5c0d7926de927e,
        0xbc45f3946d81185e,
        0x80752a25aa738091,
    ],
];
pub const XI_TO_2P_SQUARED_MINUS2_OVER3: [u64; 4] = [
    0x3642364f386c1db8,
    0xe825f92d2acd661f,
    0xf2aba7e846c19d14,
    0x5a0bcea3dc52b7a0,
];
pub const XI_TO_P_SQUARED_MINUS1_OVER3: [u64; 4] = [
    0x12d3cef5e1ada57d,
    0xe2eca1463753babb,
    0xca41e40ddccf750,
    0x551337060397e04c,
];
