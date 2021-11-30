use std::fmt;

// 7 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Vtypei(u8);
// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Uimm(pub u8);
// 5 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Imm(pub u8);

impl fmt::Display for Uimm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl fmt::Display for Imm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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

impl Vlmul {
    pub fn from_u8(value: u8) -> Vlmul {
        match value {
            0b101 => Vlmul::Mf8,
            0b110 => Vlmul::Mf4,
            0b111 => Vlmul::Mf2,
            0b000 => Vlmul::M1,
            0b001 => Vlmul::M2,
            0b010 => Vlmul::M4,
            0b011 => Vlmul::M8,
            _ => panic!("invalid vlmul value: {}", value),
        }
    }
}

impl fmt::Display for Vlmul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vlmul_str = match self {
            Vlmul::Mf8 => "mf8",
            Vlmul::Mf4 => "mf4",
            Vlmul::Mf2 => "mf2",
            Vlmul::M1 => "m1",
            Vlmul::M2 => "m2",
            Vlmul::M4 => "m4",
            Vlmul::M8 => "m8",
        };
        write!(f, "{}", vlmul_str)
    }
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

    pub fn sew(&self) -> u16 {
        let vsew = (self.0 & 0b111000) >> 3;
        match vsew {
            0 => 8,
            1 => 16,
            2 => 32,
            3 => 64,
            4 => 128,
            5 => 256,
            6 => 512,
            7 => 1024,
            _ => panic!("Invalid vsew value for vtypei: {}", vsew),
        }
    }
    pub fn lmul(&self) -> Vlmul {
        Vlmul::from_u8(self.0 & 0b111)
    }
    pub fn ta(&self) -> bool {
        (self.0 & (1 << 6)) != 0
    }
    pub fn ma(&self) -> bool {
        (self.0 & (1 << 7)) != 0
    }
}

impl fmt::Display for Vtypei {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = format!("e{}, {}", self.sew(), self.lmul());
        if self.ta() {
            output = format!("{}, ta", output);
        }
        if self.ma() {
            output = format!("{}, ma", output);
        }
        write!(f, "{}", output)
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

impl fmt::Display for XReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let xreg_str = match self {
            XReg::Zero => "zero",
            XReg::Ra => "ra",
            XReg::Sp => "sp",
            XReg::Gp => "gp",
            XReg::Tp => "tp",
            XReg::T0 => "t0",
            XReg::T1 => "t1",
            XReg::T2 => "t2",
            XReg::S0 => "s0",
            XReg::S1 => "s1",
            XReg::A0 => "a0",
            XReg::A1 => "a1",
            XReg::A2 => "a2",
            XReg::A3 => "a3",
            XReg::A4 => "a4",
            XReg::A5 => "a5",
            XReg::A6 => "a6",
            XReg::A7 => "a7",
            XReg::S2 => "s2",
            XReg::S3 => "s3",
            XReg::S4 => "s4",
            XReg::S5 => "s5",
            XReg::S6 => "s6",
            XReg::S7 => "s7",
            XReg::S8 => "s8",
            XReg::S9 => "s9",
            XReg::S10 => "s10",
            XReg::S11 => "s11",
            XReg::T3 => "t3",
            XReg::T4 => "t4",
            XReg::T5 => "t5",
            XReg::T6 => "t6",
        };
        write!(f, "{}", xreg_str)
    }
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

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vreg_str = match self {
            VReg::V0 => "v0",
            VReg::V1 => "v1",
            VReg::V2 => "v2",
            VReg::V3 => "v3",
            VReg::V4 => "v4",
            VReg::V5 => "v5",
            VReg::V6 => "v6",
            VReg::V7 => "v7",
            VReg::V8 => "v8",
            VReg::V9 => "v9",
            VReg::V10 => "v10",
            VReg::V11 => "v11",
            VReg::V12 => "v12",
            VReg::V13 => "v13",
            VReg::V14 => "v14",
            VReg::V15 => "v15",
            VReg::V16 => "v16",
            VReg::V17 => "v17",
            VReg::V18 => "v18",
            VReg::V19 => "v19",
            VReg::V20 => "v20",
            VReg::V21 => "v21",
            VReg::V22 => "v22",
            VReg::V23 => "v23",
            VReg::V24 => "v24",
            VReg::V25 => "v25",
            VReg::V26 => "v26",
            VReg::V27 => "v27",
            VReg::V28 => "v28",
            VReg::V29 => "v29",
            VReg::V30 => "v30",
            VReg::V31 => "v31",
        };
        write!(f, "{}", vreg_str)
    }
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

impl fmt::Display for Ivv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = format!("{}, {}, {}", self.vd, self.vs2, self.vs1);
        if self.vm {
            output = format!("{}, vm", output);
        }
        write!(f, "{}", output)
    }
}
impl fmt::Display for Ivx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = format!("{}, {}, {}", self.vd, self.vs2, self.rs1);
        if self.vm {
            output = format!("{}, vm", output);
        }
        write!(f, "{}", output)
    }
}
impl fmt::Display for Ivi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = format!("{}, {}, {}", self.vd, self.vs2, self.imm);
        if self.vm {
            output = format!("{}, vm", output);
        }
        write!(f, "{}", output)
    }
}

// vector Arithmetic Instruction
fn encode_vai(dst: u8, funct3: u8, src1: u8, src2: u8, vm: bool, funct6: u8) -> u32 {
    let mut value = op::V;
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
    fn encode_u32(&self, funct6: u8, funct3: u8) -> u32 {
        encode_vai(
            self.vd as u8,
            funct3,
            self.vs1 as u8,
            self.vs2 as u8,
            self.vm,
            funct6,
        )
    }
}
impl Ivx {
    fn encode_u32(&self, funct6: u8, funct3: u8) -> u32 {
        encode_vai(
            self.vd as u8,
            funct3,
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
            funct3::OPIVI,
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

impl fmt::Display for VConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VConfig::Vsetvli { rd, rs1, vtypei } => {
                write!(f, "vsetvl {}, {}, {}", rd, rs1, vtypei)
            }
            VConfig::Vsetivli { rd, uimm, vtypei } => {
                write!(f, "vsetivli {}, {}, {}", rd, uimm, vtypei)
            }
            VConfig::Vsetvl { rd, rs1, rs2 } => {
                write!(f, "vsetvl {}, {}, {}", rd, rs1, rs2)
            }
        }
    }
}

// 32 bit
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum VInst {
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

    // # Unsigned divide.
    /// vdivu.vv vd, vs2, vs1, vm   # Vector-vector
    VdivuVv(Ivv),
    /// vdivu.vx vd, vs2, rs1, vm   # vector-scalar
    VdivuVx(Ivx),

    // # Unsigned remainder
    /// vremu.vv vd, vs2, vs1, vm   # Vector-vector
    VremuVv(Ivv),
    /// vremu.vx vd, vs2, rs1, vm   # vector-scalar
    VremuVx(Ivx),
    // # Signed remainder
    /// TODO: vrem.vv vd, vs2, vs1, vm   # Vector-vector
    /// TODO: vrem.vx vd, vs2, rs1, vm   # vector-scalar

    // # Saturating adds of unsigned integers.
    /// vsaddu.vv vd, vs2, vs1, vm   # Vector-vector
    VsadduVv(Ivv),
    /// vsaddu.vx vd, vs2, rs1, vm   # vector-scalar
    VsadduVx(Ivx),
    /// vsaddu.vi vd, vs2, imm, vm   # vector-immediate
    VsadduVi(Ivi),

    // # Saturating subtract of unsigned integers.
    /// vssubu.vv vd, vs2, vs1, vm   # Vector-vector
    VssubuVv(Ivv),
    /// vssubu.vx vd, vs2, rs1, vm   # vector-scalar
    VssubuVx(Ivx),

    // ==== Vector Single-Width Bit Shift Instructions ====
    // # Bit shift operations
    /// vsll.vv vd, vs2, vs1, vm   # Vector-vector
    VsllVv(Ivv),
    /// vsll.vx vd, vs2, rs1, vm   # vector-scalar
    VsllVx(Ivx),
    /// vsll.vi vd, vs2, uimm, vm   # vector-immediate
    VsllVi(Ivi),

    /// vsrl.vv vd, vs2, vs1, vm   # Vector-vector
    VsrlVv(Ivv),
    /// vsrl.vx vd, vs2, rs1, vm   # vector-scalar
    VsrlVx(Ivx),
    /// vsrl.vi vd, vs2, uimm, vm   # vector-immediate
    VsrlVi(Ivi),

    // ==== Vector Bitwise Logical Instructions ====
    /// vand.vv vd, vs2, vs1, vm   # Vector-vector
    VandVv(Ivv),
    /// vand.vx vd, vs2, rs1, vm   # vector-scalar
    VandVx(Ivx),
    /// vand.vi vd, vs2, imm, vm   # vector-immediate
    VandVi(Ivi),

    /// vor.vv vd, vs2, vs1, vm    # Vector-vector
    VorVv(Ivv),
    /// vor.vx vd, vs2, rs1, vm    # vector-scalar
    VorVx(Ivx),
    /// vor.vi vd, vs2, imm, vm    # vector-immediate
    VorVi(Ivi),

    /// vxor.vv vd, vs2, vs1, vm    # Vector-vector
    VxorVv(Ivv),
    /// vxor.vx vd, vs2, rs1, vm    # vector-scalar
    VxorVx(Ivx),
    /// vxor.vi vd, vs2, imm, vm    # vector-immediate
    VxorVi(Ivi),

    // ==== Vector Integer Comparison Instructions ====
    // `==` # Set if equal
    /// vmseq.vv vd, vs2, vs1, vm  # Vector-vector
    VmseqVv(Ivv),
    /// vmseq.vx vd, vs2, rs1, vm  # vector-scalar
    VmseqVx(Ivx),
    /// vmseq.vi vd, vs2, imm, vm  # vector-immediate
    VmseqVi(Ivi),

    // `!=` # Set if not equal
    /// vmsne.vv vd, vs2, vs1, vm  # Vector-vector
    VmsneVv(Ivv),
    /// vmsne.vx vd, vs2, rs1, vm  # vector-scalar
    VmsneVx(Ivx),
    /// vmsne.vi vd, vs2, imm, vm  # vector-immediate
    VmsneVi(Ivi),

    // `<` # Set if less than, unsigned
    /// vmsltu.vv vd, vs2, vs1, vm  # Vector-vector
    VmsltuVv(Ivv),
    /// vmsltu.vx vd, vs2, rs1, vm  # Vector-scalar
    VmsltuVx(Ivx),

    // `<=` # Set if less than or equal, unsigned
    /// vmsleu.vv vd, vs2, vs1, vm   # Vector-vector
    VmsleuVv(Ivv),
    /// vmsleu.vx vd, vs2, rs1, vm   # vector-scalar
    VmsleuVx(Ivx),
    /// vmsleu.vi vd, vs2, imm, vm   # Vector-immediate
    VmsleuVi(Ivi),

    // `>` # Set if greater than, unsigned
    /// vmsgtu.vv vd, vs2, vs1, vm   # Vector-vector
    VmsgtuVv(Ivv),
    /// vmsgtu.vx vd, vs2, rs1, vm   # Vector-scalar
    VmsgtuVx(Ivx),
    /// vmsgtu.vi vd, vs2, imm, vm   # Vector-immediate
    VmsgtuVi(Ivi),

    // # Following two instructions are not provided directly
    // # Set if greater than or equal, unsigned
    // # vmsgeu.vx vd, vs2, rs1, vm    # Vector-scalar
    // va >= vb        vmsle{u}.vv vd, vb, va, vm    vmsge{u}.vv vd, va, vb, vm
    VmsgeuVv(Ivv),

    /// vfirst.m rd, vs2, vm
    VfirstM {
        rd: XReg,
        vs2: VReg,
        vm: bool,
    },

    /// vsetvli rd, rs1, vtypei   # rd = new vl, rs1 = AVL, vtypei = new vtype setting
    /// vsetivli rd, uimm, vtypei # rd = new vl, uimm = AVL, vtypei = new vtype setting
    /// vsetvl  rd, rs1, rs2      # rd = new vl, rs1 = AVL, rs2 = new vtype value
    VConfig(VConfig),

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

const MOP_UNIT_STRIDE: u8 = 0b00;
const OFFSET_DST: usize = 7;
const OFFSET_FUNCT3: usize = OFFSET_DST + 5;
const OFFSET_SRC1: usize = OFFSET_FUNCT3 + 3;
const OFFSET_SRC2: usize = OFFSET_SRC1 + 5;
const OFFSET_REST: usize = OFFSET_SRC2;
const OFFSET_VM: usize = OFFSET_SRC2 + 5;
const OFFSET_FUNCT6: usize = OFFSET_VM + 1;

mod op {
    pub(crate) const V: u32 = 0b1010111;
    pub(crate) const LOAD_FP: u32 = 0b0000111;
    pub(crate) const STORE_FP: u32 = 0b0100111;
}

mod funct3 {
    // See: https://github.com/riscv/riscv-v-spec/blob/master/v-spec.adoc#sec-arithmetic-encoding
    pub(crate) const OPIVV: u8 = 0b000;
    pub(crate) const OPFVV: u8 = 0b001;
    pub(crate) const OPMVV: u8 = 0b010;
    pub(crate) const OPIVI: u8 = 0b011;
    pub(crate) const OPIVX: u8 = 0b100;
    pub(crate) const OPFVF: u8 = 0b101;
    pub(crate) const OPMVX: u8 = 0b110;
    pub(crate) const OPCFG: u8 = 0b111;
}

mod funct6 {
    // See: https://github.com/riscv/riscv-v-spec/blob/master/inst-table.adoc
    pub(crate) const VADD: u8 = 0b000000;
    pub(crate) const VSUB: u8 = 0b000010;
    pub(crate) const VRSUB: u8 = 0b000011;
    pub(crate) const VMUL: u8 = 0b100101;
    pub(crate) const VDIVU: u8 = 0b100000;
    pub(crate) const VDIV: u8 = 0b100001;
    pub(crate) const VREMU: u8 = 0b100010;
    pub(crate) const VREM: u8 = 0b100011;
    pub(crate) const VSADDU: u8 = 0b100000;
    pub(crate) const VSSUBU: u8 = 0b100010;
    pub(crate) const VSLL: u8 = 0b100101;
    pub(crate) const VSRL: u8 = 0b101000;
    pub(crate) const VAND: u8 = 0b001001;
    pub(crate) const VOR: u8 = 0b001010;
    pub(crate) const VXOR: u8 = 0b001011;
    pub(crate) const VMSEQ: u8 = 0b011000;
    pub(crate) const VMSNE: u8 = 0b011001;
    pub(crate) const VMSLTU: u8 = 0b011010;
    pub(crate) const VMSLEU: u8 = 0b011100;
    pub(crate) const VMSGTU: u8 = 0b011110;
}

impl VInst {
    pub fn encode_u32(self) -> u32 {
        let (base, rest, src1, funct3, dst) = match self {
            // ==== Vector Integer Arithmetic Instructions ====
            VInst::VaddVv(ivv) => {
                return ivv.encode_u32(funct6::VADD, funct3::OPIVV);
            }
            VInst::VaddVx(ivx) => {
                return ivx.encode_u32(funct6::VADD, funct3::OPIVX);
            }
            VInst::VaddVi(ivi) => {
                return ivi.encode_u32(funct6::VADD);
            }
            VInst::VsubVv(ivv) => {
                return ivv.encode_u32(funct6::VSUB, funct3::OPIVV);
            }
            VInst::VsubVx(ivx) => {
                return ivx.encode_u32(funct6::VSUB, funct3::OPIVX);
            }
            VInst::VrsubVx(ivx) => {
                return ivx.encode_u32(funct6::VRSUB, funct3::OPIVX);
            }
            VInst::VrsubVi(ivi) => {
                return ivi.encode_u32(funct6::VRSUB);
            }
            VInst::VmulVv(ivv) => {
                return ivv.encode_u32(funct6::VMUL, funct3::OPMVV);
            }
            VInst::VmulVx(ivx) => {
                return ivx.encode_u32(funct6::VMUL, funct3::OPMVX);
            }
            VInst::VdivuVv(ivv) => {
                return ivv.encode_u32(funct6::VDIVU, funct3::OPMVV);
            }
            VInst::VdivuVx(ivx) => {
                return ivx.encode_u32(funct6::VDIVU, funct3::OPMVX);
            }
            VInst::VremuVv(ivv) => {
                return ivv.encode_u32(funct6::VREMU, funct3::OPMVV);
            }
            VInst::VremuVx(ivx) => {
                return ivx.encode_u32(funct6::VREMU, funct3::OPMVX);
            }
            VInst::VsadduVv(ivv) => {
                return ivv.encode_u32(funct6::VSADDU, funct3::OPIVV);
            }
            VInst::VsadduVx(ivx) => {
                return ivx.encode_u32(funct6::VSADDU, funct3::OPIVX);
            }
            VInst::VsadduVi(ivi) => {
                return ivi.encode_u32(funct6::VSADDU);
            }
            VInst::VssubuVv(ivv) => {
                return ivv.encode_u32(funct6::VSSUBU, funct3::OPIVV);
            }
            VInst::VssubuVx(ivx) => {
                return ivx.encode_u32(funct6::VSSUBU, funct3::OPIVX);
            }

            // ==== Vector Single-Width Bit Shift Instructions ====
            VInst::VsllVv(ivv) => {
                return ivv.encode_u32(funct6::VSLL, funct3::OPIVV);
            }
            VInst::VsllVx(ivx) => {
                return ivx.encode_u32(funct6::VSLL, funct3::OPIVX);
            }
            VInst::VsllVi(ivi) => {
                return ivi.encode_u32(funct6::VSLL);
            }
            VInst::VsrlVv(ivv) => {
                return ivv.encode_u32(funct6::VSRL, funct3::OPIVV);
            }
            VInst::VsrlVx(ivx) => {
                return ivx.encode_u32(funct6::VSRL, funct3::OPIVX);
            }
            VInst::VsrlVi(ivi) => {
                return ivi.encode_u32(funct6::VSRL);
            }

            // ==== Vector Bitwise Logical Instructions ====
            VInst::VandVv(ivv) => {
                return ivv.encode_u32(funct6::VAND, funct3::OPIVV);
            }
            VInst::VandVx(ivx) => {
                return ivx.encode_u32(funct6::VAND, funct3::OPIVX);
            }
            VInst::VandVi(ivi) => {
                return ivi.encode_u32(funct6::VAND);
            }
            VInst::VorVv(ivv) => {
                return ivv.encode_u32(funct6::VOR, funct3::OPIVV);
            }
            VInst::VorVx(ivx) => {
                return ivx.encode_u32(funct6::VOR, funct3::OPIVX);
            }
            VInst::VorVi(ivi) => {
                return ivi.encode_u32(funct6::VOR);
            }
            VInst::VxorVv(ivv) => {
                return ivv.encode_u32(funct6::VXOR, funct3::OPIVV);
            }
            VInst::VxorVx(ivx) => {
                return ivx.encode_u32(funct6::VXOR, funct3::OPIVX);
            }
            VInst::VxorVi(ivi) => {
                return ivi.encode_u32(funct6::VXOR);
            }

            // ==== Vector Integer Comparison Instructions ====
            VInst::VmseqVv(ivv) => {
                return ivv.encode_u32(funct6::VMSEQ, funct3::OPIVV);
            }
            VInst::VmseqVx(ivx) => {
                return ivx.encode_u32(funct6::VMSEQ, funct3::OPIVX);
            }
            VInst::VmseqVi(ivi) => {
                return ivi.encode_u32(funct6::VMSEQ);
            }
            VInst::VmsneVv(ivv) => {
                return ivv.encode_u32(funct6::VMSNE, funct3::OPIVV);
            }
            VInst::VmsneVx(ivx) => {
                return ivx.encode_u32(funct6::VMSNE, funct3::OPIVX);
            }
            VInst::VmsneVi(ivi) => {
                return ivi.encode_u32(funct6::VMSNE);
            }
            VInst::VmsltuVv(ivv) => {
                return ivv.encode_u32(funct6::VMSLTU, funct3::OPIVV);
            }
            VInst::VmsltuVx(ivx) => {
                return ivx.encode_u32(funct6::VMSLTU, funct3::OPIVX);
            }
            VInst::VmsleuVv(ivv) => {
                return ivv.encode_u32(funct6::VMSLEU, funct3::OPIVV);
            }
            VInst::VmsleuVx(ivx) => {
                return ivx.encode_u32(funct6::VMSLEU, funct3::OPIVX);
            }
            VInst::VmsleuVi(ivi) => {
                return ivi.encode_u32(funct6::VMSLEU);
            }
            VInst::VmsgtuVv(Ivv { vd, vs2, vs1, vm }) => {
                return VInst::VmsltuVv(Ivv {
                    vd,
                    vm,
                    vs2: vs1,
                    vs1: vs2,
                })
                .encode_u32();
            }
            VInst::VmsgtuVx(ivx) => {
                return ivx.encode_u32(funct6::VMSGTU, funct3::OPIVX);
            }
            VInst::VmsgtuVi(ivi) => {
                return ivi.encode_u32(funct6::VMSGTU);
            }
            VInst::VmsgeuVv(Ivv { vd, vs2, vs1, vm }) => {
                return VInst::VmsleuVv(Ivv {
                    vd,
                    vm,
                    vs2: vs1,
                    vs1: vs2,
                })
                .encode_u32();
            }

            // ==== other instructions ====
            VInst::VfirstM { rd, vs2, vm } => {
                let mut value = 0b010000_0_00000_10001_010_00000_1010111;
                value = set_bits(value, OFFSET_DST, rd as u8 as u32);
                value = set_bits(value, OFFSET_SRC2, vs2 as u8 as u32);
                if vm {
                    value = set_bits(value, OFFSET_VM, 1);
                }
                return value;
            }

            VInst::VConfig(cfg) => match cfg {
                VConfig::Vsetvli { rd, rs1, vtypei } => {
                    let funct3: u8 = funct3::OPCFG;
                    let rest: u32 = vtypei.0 as u32;
                    (op::V, rest, rs1 as u8, funct3, rd as u8)
                }
                VConfig::Vsetivli { rd, uimm, vtypei } => {
                    let funct3: u8 = funct3::OPCFG;
                    let mut rest: u32 = vtypei.0 as u32;
                    rest = set_bits(rest, 10, 0b11);
                    (op::V, rest, uimm.0, funct3, rd as u8)
                }
                VConfig::Vsetvl { rd, rs1, rs2 } => {
                    let funct3: u8 = funct3::OPCFG;
                    let rest: u32 = set_bits(rs2 as u8 as u32, 5 + 6, 1);
                    (op::V, rest, rs1 as u8, funct3, rd as u8)
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
                (op::LOAD_FP, rest, rs1 as u8, funct3, vd as u8)
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
                (op::STORE_FP, rest, rs1 as u8, funct3, vs3 as u8)
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

impl fmt::Display for VInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // ==== Vector Integer Arithmetic Instructions ====
            VInst::VaddVv(ivv) => {
                write!(f, "vadd.vv {}", ivv)
            }
            VInst::VaddVx(ivx) => {
                write!(f, "vadd.vx {}", ivx)
            }
            VInst::VaddVi(ivi) => {
                write!(f, "vadd.vi {}", ivi)
            }
            VInst::VsubVv(ivv) => {
                write!(f, "vsub.vv {}", ivv)
            }
            VInst::VsubVx(ivx) => {
                write!(f, "vsub.vx {}", ivx)
            }
            VInst::VrsubVx(ivx) => {
                write!(f, "vrsub.vx {}", ivx)
            }
            VInst::VrsubVi(ivi) => {
                write!(f, "vrsub.vi {}", ivi)
            }
            VInst::VmulVv(ivv) => {
                write!(f, "vmul.vv {}", ivv)
            }
            VInst::VmulVx(ivx) => {
                write!(f, "vmul.vx {}", ivx)
            }
            VInst::VdivuVv(ivv) => {
                write!(f, "vdivu.vv {}", ivv)
            }
            VInst::VdivuVx(ivx) => {
                write!(f, "vdivu.vx {}", ivx)
            }
            VInst::VremuVv(ivv) => {
                write!(f, "vremu.vv {}", ivv)
            }
            VInst::VremuVx(ivx) => {
                write!(f, "vremu.vx {}", ivx)
            }
            VInst::VsadduVv(ivv) => {
                write!(f, "vsaddu.vv {}", ivv)
            }
            VInst::VsadduVx(ivx) => {
                write!(f, "vsaddu.vx {}", ivx)
            }
            VInst::VsadduVi(ivi) => {
                write!(f, "vsaddu.vi {}", ivi)
            }
            VInst::VssubuVv(ivv) => {
                write!(f, "vssubu.vv {}", ivv)
            }
            VInst::VssubuVx(ivx) => {
                write!(f, "vssubu.vx {}", ivx)
            }

            // ==== Vector Single-Width Bit Shift Instructions ====
            VInst::VsllVv(ivv) => {
                write!(f, "vsll.vv {}", ivv)
            }
            VInst::VsllVx(ivx) => {
                write!(f, "vsll.vx {}", ivx)
            }
            VInst::VsllVi(ivi) => {
                write!(f, "vsll.vi {}", ivi)
            }
            VInst::VsrlVv(ivv) => {
                write!(f, "vsrl.vv {}", ivv)
            }
            VInst::VsrlVx(ivx) => {
                write!(f, "vsrl.vx {}", ivx)
            }
            VInst::VsrlVi(ivi) => {
                write!(f, "vsrl.vi {}", ivi)
            }

            // ==== Vector Bitwise Logical Instructions ====
            VInst::VandVv(ivv) => {
                write!(f, "vand.vv {}", ivv)
            }
            VInst::VandVx(ivx) => {
                write!(f, "vand.vx {}", ivx)
            }
            VInst::VandVi(ivi) => {
                write!(f, "vand.vi {}", ivi)
            }
            VInst::VorVv(ivv) => {
                write!(f, "vor.vv {}", ivv)
            }
            VInst::VorVx(ivx) => {
                write!(f, "vor.vx {}", ivx)
            }
            VInst::VorVi(ivi) => {
                write!(f, "vor.vi {}", ivi)
            }
            VInst::VxorVv(ivv) => {
                write!(f, "vxor.vv {}", ivv)
            }
            VInst::VxorVx(ivx) => {
                write!(f, "vxor.vx {}", ivx)
            }
            VInst::VxorVi(ivi) => {
                write!(f, "vxor.vi {}", ivi)
            }

            // ==== Vector Integer Comparison Instructions ====
            VInst::VmseqVv(ivv) => {
                write!(f, "vmseq.vv {}", ivv)
            }
            VInst::VmseqVx(ivx) => {
                write!(f, "vmseq.vx {}", ivx)
            }
            VInst::VmseqVi(ivi) => {
                write!(f, "vmseq.vi {}", ivi)
            }
            VInst::VmsneVv(ivv) => {
                write!(f, "vmsne.vv {}", ivv)
            }
            VInst::VmsneVx(ivx) => {
                write!(f, "vmsne.vx {}", ivx)
            }
            VInst::VmsneVi(ivi) => {
                write!(f, "vmsne.vi {}", ivi)
            }
            VInst::VmsltuVv(ivv) => {
                write!(f, "vmsltu.vv {}", ivv)
            }
            VInst::VmsltuVx(ivx) => {
                write!(f, "vmsltu.vx {}", ivx)
            }
            VInst::VmsleuVv(ivv) => {
                write!(f, "vmsleu.vv {}", ivv)
            }
            VInst::VmsleuVx(ivx) => {
                write!(f, "vmsleu.vx {}", ivx)
            }
            VInst::VmsleuVi(ivi) => {
                write!(f, "vmsleu.vi {}", ivi)
            }
            VInst::VmsgtuVv(ivv) => {
                write!(f, "vmsgtu.vv {}", ivv)
            }
            VInst::VmsgtuVx(ivx) => {
                write!(f, "vmsgtu.vx {}", ivx)
            }
            VInst::VmsgtuVi(ivi) => {
                write!(f, "vmsgtu.vi {}", ivi)
            }
            VInst::VmsgeuVv(ivv) => {
                write!(f, "vmsgeu.vv {}", ivv)
            }
            VInst::VfirstM { rd, vs2, vm } => {
                let mut output = format!("{}, {}", rd, vs2);
                if *vm {
                    output = format!("{}, vm", output);
                }
                write!(f, "vfirst.m {}", output)
            }
            VInst::VConfig(cfg) => {
                write!(f, "{}", cfg)
            }
            VInst::VleV { width, vd, rs1, vm } => {
                let mut output = format!("{}, ({})", vd, rs1);
                if *vm {
                    output = format!("{}, vm", output);
                }
                write!(f, "vle{}.v {}", width, output)
            }
            VInst::VseV {
                width,
                vs3,
                rs1,
                vm,
            } => {
                let mut output = format!("{}, ({})", vs3, rs1);
                if *vm {
                    output = format!("{}, vm", output);
                }
                write!(f, "vse{}.v {}", width, output)
            }
        }
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
        // See: https://five-embeddev.com/riscv-v-spec/draft/v-spec.html#_vector_load_store_instruction_encoding
        128 => (0b000, true),
        256 => (0b101, true),
        512 => (0b110, true),
        1024 => (0b111, true),
        _ => panic!("Invalid width: {}", width),
    }
}
