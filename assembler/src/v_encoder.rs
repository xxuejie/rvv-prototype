// 7 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Vtypei(u8);
// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Uimm(u8);
// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Imm(u8);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum Vlmul {
    // LMUL=1/8
    Mf8 = 0b101,
    // LMUL=1/4
    Mf4 = 0b110,
    // LMUL=1/2
    Mf2 = 0b111,
    // LMUL=1
    M1 = 0b000,
    // LMUL=2
    M2 = 0b001,
    // LMUL=4
    M4 = 0b010,
    // LMUL=8
    M8 = 0b011,
}

impl Vtypei {
    pub fn new(sew: u16, lmul: Vlmul, ta: bool, ma: bool) -> Vtypei {
        let vsew: u8 = match sew {
            8 => 0,
            16 => 1,
            32 => 2,
            64 => 3,
            128 => 4,
            256 => 5,
            512 => 6,
            1024 => 7,
            _ => panic!("Invalid sew value for vtypei: {}", sew),
        };
        let mut value = lmul as u8;
        value |= vsew << 3;
        if ta {
            value |= 1 << 6;
        }
        if ma {
            value |= 1 << 7;
        }
        Vtypei(value)
    }
}

/*
Register| ABI      | Use by convention                   | Preserved?
:-------| :--------| :---------------                    | ------
x0      | zero     | hardwired to 0, ignores writes      | n/a
x1      | ra       | return address for jumps            | no
x2      | sp       | stack pointer                       | yes
x3      | gp       | global pointer                      | n/a
x4      | tp       | thread pointer                      | n/a
x5      | t0       | temporary register 0                | no
x6      | t1       | temporary register 1                | no
x7      | t2       | temporary register 2                | no
x8      | s0 or fp | saved register 0 or frame pointer   | yes
x9      | s1       | saved register 1                    | yes
x10     | a0       | return value or function argument 0 | no
x11     | a1       | return value or function argument 1 | no
x12     | a2       | function argument 2                 | no
x13     | a3       | function argument 3                 | no
x14     | a4       | function argument 4                 | no
x15     | a5       | function argument 5                 | no
x16     | a6       | function argument 6                 | no
x17     | a7       | function argument 7                 | no
x18     | s2       | saved register 2                    | yes
x19     | s3       | saved register 3                    | yes
x20     | s4       | saved register 4                    | yes
x21     | s5       | saved register 5                    | yes
x22     | s6       | saved register 6                    | yes
x23     | s7       | saved register 7                    | yes
x24     | s8       | saved register 8                    | yes
x25     | s9       | saved register 9                    | yes
x26     | s10      | saved register 10                   | yes
x27     | s11      | saved register 11                   | yes
x28     | t3       | temporary register 3                | no
x29     | t4       | temporary register 4                | no
x30     | t5       | temporary register 5                | no
x31     | t6       | temporary register 6                | no
pc      | (none)   | program counter                     | n/a */

// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum XReg {
    Zero = 0,
    Ra,
    Sp,
    Gp,
    Tp,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum VReg {
    V0 = 0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    V10,
    V11,
    V12,
    V13,
    V14,
    V15,
    V16,
    V17,
    V18,
    V19,
    V20,
    V21,
    V22,
    V23,
    V24,
    V25,
    V26,
    V27,
    V28,
    V29,
    V30,
    V31,
}

impl VReg {
    pub fn from_u8(value: u8) -> VReg {
        match value {
            0 => VReg::V0,
            1 => VReg::V1,
            2 => VReg::V2,
            3 => VReg::V3,
            4 => VReg::V4,
            5 => VReg::V5,
            6 => VReg::V6,
            7 => VReg::V7,
            8 => VReg::V8,
            9 => VReg::V9,
            10 => VReg::V10,
            11 => VReg::V11,
            12 => VReg::V12,
            13 => VReg::V13,
            14 => VReg::V14,
            15 => VReg::V15,
            16 => VReg::V16,
            17 => VReg::V17,
            18 => VReg::V18,
            19 => VReg::V19,
            20 => VReg::V20,
            21 => VReg::V21,
            22 => VReg::V22,
            23 => VReg::V23,
            24 => VReg::V24,
            25 => VReg::V25,
            26 => VReg::V26,
            27 => VReg::V27,
            28 => VReg::V28,
            29 => VReg::V29,
            30 => VReg::V30,
            31 => VReg::V31,
            _ => panic!("Invalid vreg value: {}", value),
        }
    }
}

/// Vector Integer Arithmetic Instructions data structures
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Ivv {
    pub vd: VReg,
    pub vs2: VReg,
    pub vs1: VReg,
    pub vm: bool,
}
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Ivx {
    pub vd: VReg,
    pub vs2: VReg,
    pub rs1: XReg,
    pub vm: bool,
}
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Ivi {
    pub vd: VReg,
    pub vs2: VReg,
    pub imm: Imm,
    pub vm: bool,
}

// Vector Arithmetic Instruction
fn encode_vai(dst: u8, funct3: u8, src1: u8, src2: u8, vm: bool, funct6: u8) -> u32 {
    let mut value = OP_V;
    value = set_bits(value, OFFSET_DST, dst as u32);
    value = set_bits(value, OFFSET_FUNCT3, funct3 as u32);
    value = set_bits(value, OFFSET_SRC1, src1 as u32);
    value = set_bits(value, OFFSET_SRC2, src2 as u32);
    if vm {
        value = set_bits(value, OFFSET_VM, 1);
    }
    value = set_bits(value, OFFSET_FUNCT6, funct6 as u32);
    value
}

impl Ivv {
    fn encode_u32(&self, funct6: u8) -> u32 {
        encode_vai(
            self.vd as u8,
            FUNCT3_OPIVV,
            self.vs1 as u8,
            self.vs2 as u8,
            self.vm,
            funct6,
        )
    }
}
impl Ivx {
    fn encode_u32(&self, funct6: u8) -> u32 {
        encode_vai(
            self.vd as u8,
            FUNCT3_OPIVX,
            self.rs1 as u8,
            self.vs2 as u8,
            self.vm,
            funct6,
        )
    }
}
impl Ivi {
    fn encode_u32(&self, funct6: u8) -> u32 {
        encode_vai(
            self.vd as u8,
            FUNCT3_OPIVI,
            self.imm.0,
            self.vs2 as u8,
            self.vm,
            funct6,
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum VConfig {
    /// vsetvli  rd, rs1, vtypei  # rd = new vl, rs1 = AVL, vtypei = new vtype setting
    Vsetvli { rd: XReg, rs1: XReg, vtypei: Vtypei },
    /// vsetivli rd, uimm, vtypei # rd = new vl, uimm = AVL, vtypei = new vtype setting
    Vsetivli {
        rd: XReg,
        uimm: Uimm,
        vtypei: Vtypei,
    },
    /// vsetvl   rd, rs1, rs2     # rd = new vl, rs1 = AVL, rs2 = new vtype value
    Vsetvl { rd: XReg, rs1: XReg, rs2: XReg },
}

// 32 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum VInst {
    VConfig(VConfig),

    // ==== Vector Integer Arithmetic Instructions ====

    // # Integer adds
    /// vadd.vv vd, vs2, vs1, vm   # Vector-vector
    VaddVv(Ivv),
    /// vadd.vx vd, vs2, rs1, vm   # vector-scalar
    VaddVx(Ivx),
    /// vadd.vi vd, vs2, imm, vm   # vector-immediate
    VaddVi(Ivi),

    // # Integer subtract
    /// vsub.vv vd, vs2, vs1, vm # Vector-vector
    VsubVv(Ivv),
    /// vsub.vx vd, vs2, rs1, vm # vector-scalar
    VsubVx(Ivx),

    // # Integer reverse subtract
    /// vrsub.vx vd, vs2, rs1, vm   # vd[i] = x[rs1] - vs2[i]
    VrsubVx(Ivx),
    /// vrsub.vi vd, vs2, imm, vm   # vd[i] = imm - vs2[i]
    VrsubVi(Ivi),

    // # Signed multiply, returning low bits of product
    /// vmul.vv vd, vs2, vs1, vm # Vector-vector
    VmulVv(Ivv),
    /// vmul.vx vd, vs2, rs1, vm # vector-scalar
    VmulVx(Ivx),

    // # Signed multiply, returning high bits of product
    /// TODO: vmulh.vv vd, vs2, vs1, vm   # Vector-vector
    /// TODO: vmulh.vx vd, vs2, rs1, vm   # vector-scalar

    // # Unsigned multiply, returning high bits of product
    /// TODO: vmulhu.vv vd, vs2, vs1, vm   # Vector-vector
    /// TODO: vmulhu.vx vd, vs2, rs1, vm   # vector-scalar

    // # Signed(vs2)-Unsigned multiply, returning high bits of product
    /// TODO: vmulhsu.vv vd, vs2, vs1, vm   # Vector-vector
    /// TODO: vmulhsu.vx vd, vs2, rs1, vm   # vector-scalar

    // # Unsigned remainder
    /// vremu.vv vd, vs2, vs1, vm   # Vector-vector
    VremuVv(Ivv),
    /// vremu.vx vd, vs2, rs1, vm   # vector-scalar
    VremuVx(Ivx),
    // # Signed remainder
    /// TODO: vrem.vv vd, vs2, vs1, vm   # Vector-vector
    /// TODO: vrem.vx vd, vs2, rs1, vm   # vector-scalar

    /// Vector unit-stride loads
    /// vle{64, 256, 1024}.v vd, (rs1), vm
    VleV {
        width: u16,
        vd: VReg,
        rs1: XReg,
        vm: bool,
    },
    /// Vector unit-stride stores
    /// vse{64, 256, 1024}.v vd, (rs1), vm
    VseV {
        width: u16,
        vs3: VReg,
        rs1: XReg,
        vm: bool,
    },
}

const FUNCT3_OPIVV: u8 = 0b000;
const FUNCT3_OPFVV: u8 = 0b001;
const FUNCT3_OPMVV: u8 = 0b010;
const FUNCT3_OPIVI: u8 = 0b011;
const FUNCT3_OPIVX: u8 = 0b100;
const FUNCT3_OPFVF: u8 = 0b101;
const FUNCT3_OPMVX: u8 = 0b110;
const FUNCT3_OPCFG: u8 = 0b111;
const MOP_UNIT_STRIDE: u8 = 0b00;
const OFFSET_DST: usize = 7;
const OFFSET_FUNCT3: usize = OFFSET_DST + 5;
const OFFSET_SRC1: usize = OFFSET_FUNCT3 + 3;
const OFFSET_SRC2: usize = OFFSET_SRC1 + 5;
const OFFSET_REST: usize = OFFSET_SRC2;
const OFFSET_VM: usize = OFFSET_SRC2 + 5;
const OFFSET_FUNCT6: usize = OFFSET_VM + 1;

const OP_V: u32 = 0b1010111;
const OP_LOAD_FP: u32 = 0b0000111;
const OP_STORE_FP: u32 = 0b0100111;

const FUNCT6_VADD: u8 = 0b0;
const FUNCT6_VSUB: u8 = 0b000010;
const FUNCT6_VRSUB: u8 = 0b000011;
const FUNCT6_VMUL: u8 = 0b100101;
const FUNCT6_VREMU: u8 = 0b100010;
const FUNCT6_VREM: u8 = 0b100011;

impl VInst {
    pub fn encode_u32(self) -> u32 {
        let (base, rest, src1, funct3, dst) = match self {
            VInst::VaddVv(ivv) => {
                return ivv.encode_u32(FUNCT6_VADD);
            }
            VInst::VaddVx(ivx) => {
                return ivx.encode_u32(FUNCT6_VADD);
            }
            VInst::VaddVi(ivi) => {
                return ivi.encode_u32(FUNCT6_VADD);
            }
            VInst::VsubVv(ivv) => {
                return ivv.encode_u32(FUNCT6_VSUB);
            }
            VInst::VsubVx(ivx) => {
                return ivx.encode_u32(FUNCT6_VSUB);
            }
            VInst::VrsubVx(ivx) => {
                return ivx.encode_u32(FUNCT6_VRSUB);
            }
            VInst::VrsubVi(ivi) => {
                return ivi.encode_u32(FUNCT6_VRSUB);
            }
            VInst::VmulVv(ivv) => {
                return ivv.encode_u32(FUNCT6_VMUL);
            }
            VInst::VmulVx(ivx) => {
                return ivx.encode_u32(FUNCT6_VMUL);
            }
            VInst::VremuVv(ivv) => {
                return ivv.encode_u32(FUNCT6_VREMU);
            }
            VInst::VremuVx(ivx) => {
                return ivx.encode_u32(FUNCT6_VREMU);
            }
            VInst::VConfig(cfg) => match cfg {
                VConfig::Vsetvli { rd, rs1, vtypei } => {
                    let funct3: u8 = FUNCT3_OPCFG;
                    let rest: u32 = vtypei.0 as u32;
                    (OP_V, rest, rs1 as u8, funct3, rd as u8)
                }
                VConfig::Vsetivli { rd, uimm, vtypei } => {
                    let funct3: u8 = FUNCT3_OPCFG;
                    let mut rest: u32 = vtypei.0 as u32;
                    rest = set_bits(rest, 10, 0b11);
                    (OP_V, rest, uimm.0, funct3, rd as u8)
                }
                VConfig::Vsetvl { rd, rs1, rs2 } => {
                    let funct3: u8 = FUNCT3_OPCFG;
                    let rest: u32 = set_bits(rs2 as u8 as u32, 5 + 6, 1);
                    (OP_V, rest, rs1 as u8, funct3, rd as u8)
                }
            },
            VInst::VleV { width, vd, rs1, vm } => {
                let (funct3, mew) = width_bits(width);
                let lumop: u8 = 0b00000;
                let vm = if vm { 1 } else { 0 };
                let mop: u8 = MOP_UNIT_STRIDE;
                let mut rest: u32 = lumop as u32;
                rest = set_bits(rest, 5, vm);
                rest = set_bits(rest, 5 + 1, mop as u32);
                if mew {
                    rest = set_bits(rest, 5 + 1 + 2, 1);
                }
                (OP_LOAD_FP, rest, rs1 as u8, funct3, vd as u8)
            }
            VInst::VseV {
                width,
                vs3,
                rs1,
                vm,
            } => {
                let (funct3, mew) = width_bits(width);
                let sumop: u8 = 0b00000;
                let vm = if vm { 1 } else { 0 };
                let mop: u8 = MOP_UNIT_STRIDE;
                let mut rest: u32 = sumop as u32;
                rest = set_bits(rest, 5, vm);
                rest = set_bits(rest, 5 + 1, mop as u32);
                if mew {
                    rest = set_bits(rest, 5 + 1 + 2, 1);
                }
                (OP_STORE_FP, rest, rs1 as u8, funct3, vs3 as u8)
            }
        };
        let mut value = base;
        value = set_bits(value, OFFSET_DST, dst as u32);
        value = set_bits(value, OFFSET_FUNCT3, funct3 as u32);
        value = set_bits(value, OFFSET_SRC1, src1 as u32);
        value = set_bits(value, OFFSET_REST, rest);
        value
    }

    pub fn encode_bytes(self) -> [u8; 4] {
        self.encode_u32().to_le_bytes()
    }
}

fn set_bits(src: u32, offset: usize, value: u32) -> u32 {
    src | (value << offset)
}

fn width_bits(width: u16) -> (u8, bool) {
    match width {
        8 => (0, false),
        16 => (0b101, false),
        32 => (0b110, false),
        64 => (0b111, false),
        // NOTE: must consist with decoder
        128 => (0b000, true),
        256 => (0b001, true),
        512 => (0b010, true),
        1024 => (0b011, true),
        _ => panic!("Invalid width: {}", width),
    }
}
