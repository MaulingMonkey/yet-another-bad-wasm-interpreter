//! [Instructions](https://webassembly.github.io/spec/core/binary/instructions.html)

use crate::*;

use std::fmt::{self, Debug, Display, Formatter};

const MAX_2 : usize = !0/2;



#[derive(Clone, Default, PartialEq, PartialOrd)]
pub struct Expr(pub Vec<Instr>);

impl From<i32> for Expr {
    fn from(value: i32) -> Expr {
        Expr(vec![
            Instr::I32_Const(value),
            Instr::End,
        ])
    }
}

impl Debug for Expr {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        let mut indent = 0usize;
        let n = self.0.len();
        writeln!(fmt, "Expr([")?;
        for (i, op) in self.0.iter().enumerate() {
            match op {
                Instr::Else | Instr::End => indent = indent.saturating_sub(1),
                _other => {},
            }
            if i < MAX_2 || (n-i-1) < MAX_2 {
                writeln!(fmt, "    {0: >1$}{2}", "", 4*indent, op)?;
            } else if n > 2*MAX_2 && i == MAX_2 {
                writeln!(fmt, "    {0: >1$}{2}", "", 4*indent, "...")?;
            }
            match op {
                Instr::If(_) | Instr::Block(_) | Instr::Loop(_) | Instr::Else => indent += 1,
                _other => {},
            }
        }
        write!(fmt, "])")
    }
}



#[allow(non_camel_case_types)]
#[derive(Clone, PartialEq, PartialOrd)]
pub enum Instr {
    // https://webassembly.github.io/spec/core/binary/instructions.html#control-instructions
    Unreachable,
    Nop,
    Block           (BlockType),
    Loop            (BlockType),
    If              (BlockType),
    Else,
    Br              (LabelIdx),
    BrIf            (LabelIdx),
    BrTable         (Vec<LabelIdx>),
    Return,
    Call            (FuncIdx),
    CallIndirect    (TableIdx, TypeIdx),

    // https://webassembly.github.io/spec/core/binary/instructions.html#reference-instructions
    RefNull         (RefType),
    RefIsNull,
    RefFunc         (FuncIdx),

    // https://webassembly.github.io/spec/core/binary/instructions.html#parametric-instructions
    Drop,
    Select          (Vec<ValType>),

    // https://webassembly.github.io/spec/core/binary/instructions.html#variable-instructions
    LocalGet        (LocalIdx),
    LocalSet        (LocalIdx),
    LocalTee        (LocalIdx),
    GlobalGet       (GlobalIdx),
    GlobalSet       (GlobalIdx),

    // https://webassembly.github.io/spec/core/binary/instructions.html#table-instructions
    TableGet        (TableIdx),
    TableSet        (TableIdx),
    TableInit       (TableIdx, ElemIdx),
    ElemDrop        (ElemIdx),
    TableCopy       (TableIdx, TableIdx),
    TableGrow       (TableIdx),
    TableSize       (TableIdx),
    TableFill       (TableIdx),

    // https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions
    I32_Load        (MemArg),
    I64_Load        (MemArg),
    F32_Load        (MemArg),
    F64_Load        (MemArg),

    I32_Load8_s     (MemArg),
    I32_Load8_u     (MemArg),
    I32_Load16_s    (MemArg),
    I32_Load16_u    (MemArg),

    I64_Load8_s     (MemArg),
    I64_Load8_u     (MemArg),
    I64_Load16_s    (MemArg),
    I64_Load16_u    (MemArg),
    I64_Load32_s    (MemArg),
    I64_Load32_u    (MemArg),

    I32_Store       (MemArg),
    I64_Store       (MemArg),
    F32_Store       (MemArg),
    F64_Store       (MemArg),
    I32_Store8      (MemArg),
    I32_Store16     (MemArg),
    I64_Store8      (MemArg),
    I64_Store16     (MemArg),
    I64_Store32     (MemArg),

    MemorySize,
    MemoryGrow,
    MemoryInit      (DataIdx),
    DataDrop        (DataIdx),
    MemoryCopy,
    MemoryFill,

    // https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions
    I32_Const       (i32),
    I64_Const       (i64),
    F32_Const       (f32),
    F64_Const       (f64),

    I32_Eqz,
    I32_Eq,
    I32_Ne,
    I32_Lt_s,
    I32_Lt_u,
    I32_Gt_s,
    I32_Gt_u,
    I32_Le_s,
    I32_Le_u,
    I32_Ge_s,
    I32_Ge_u,

    I64_Eqz,
    I64_Eq,
    I64_Ne,
    I64_Lt_s,
    I64_Lt_u,
    I64_Gt_s,
    I64_Gt_u,
    I64_Le_s,
    I64_Le_u,
    I64_Ge_s,
    I64_Ge_u,

    F32_Eq,
    F32_Ne,
    F32_Lt,
    F32_Gt,
    F32_Le,
    F32_Ge,

    F64_Eq,
    F64_Ne,
    F64_Lt,
    F64_Gt,
    F64_Le,
    F64_Ge,

    I32_Clz,
    I32_Ctz,
    I32_PopCnt,
    I32_Add,
    I32_Sub,
    I32_Mul,
    I32_Div_s,
    I32_Div_u,
    I32_Rem_s,
    I32_Rem_u,
    I32_And,
    I32_Or,
    I32_Xor,
    I32_Shl,
    I32_Shr_s,
    I32_Shr_u,
    I32_Rotl,
    I32_Rotr,

    I64_Clz,
    I64_Ctz,
    I64_PopCnt,
    I64_Add,
    I64_Sub,
    I64_Mul,
    I64_Div_s,
    I64_Div_u,
    I64_Rem_s,
    I64_Rem_u,
    I64_And,
    I64_Or,
    I64_Xor,
    I64_Shl,
    I64_Shr_s,
    I64_Shr_u,
    I64_Rotl,
    I64_Rotr,

    F32_Abs,
    F32_Neg,
    F32_Ceil,
    F32_Floor,
    F32_Trunc,
    F32_Nearest,
    F32_Sqrt,
    F32_Add,
    F32_Sub,
    F32_Mul,
    F32_Div,
    F32_Min,
    F32_Max,
    F32_Copysign,

    F64_Abs,
    F64_Neg,
    F64_Ceil,
    F64_Floor,
    F64_Trunc,
    F64_Nearest,
    F64_Sqrt,
    F64_Add,
    F64_Sub,
    F64_Mul,
    F64_Div,
    F64_Min,
    F64_Max,
    F64_Copysign,

    I32_Wrap_I64,
    I32_Trunc_F32_s,
    I32_Trunc_F32_u,
    I32_Trunc_F64_s,
    I32_Trunc_F64_u,
    I64_Extend_I32_s,
    I64_Extend_I32_u,
    I64_Trunc_F32_s,
    I64_Trunc_F32_u,
    I64_Trunc_F64_s,
    I64_Trunc_F64_u,
    F32_Convert_I32_s,
    F32_Convert_I32_u,
    F32_Convert_I64_s,
    F32_Convert_I64_u,
    F32_Demote_F64,
    F64_Convert_I32_s,
    F64_Convert_I32_u,
    F64_Convert_I64_s,
    F64_Convert_I64_u,
    F64_Promote_F32,
    I32_Reinterpret_F32,
    I64_Reinterpret_F64,
    F32_Reinterpret_I32,
    F64_Reinterpret_I64,

    I32_Extend8_s,
    I32_Extend16_s,
    I64_Extend8_s,
    I64_Extend16_s,
    I64_Extend32_s,

    I32_TruncSat_F32_s,
    I32_TruncSat_F32_u,
    I32_TruncSat_F64_s,
    I32_TruncSat_F64_u,
    I64_TruncSat_F32_s,
    I64_TruncSat_F32_u,
    I64_TruncSat_F64_s,
    I64_TruncSat_F64_u,

    End,
}

impl Debug for Instr {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, fmt)
    }
}

impl Display for Instr {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match self {
            // https://webassembly.github.io/spec/core/binary/instructions.html#control-instructions
            Unreachable         => write!(fmt, "unreachable"),
            Nop                 => write!(fmt, "nop"),
            Block(ty)           => write!(fmt, "block {}", ty),
            Loop(ty)            => write!(fmt, "loop {}", ty),
            If(ty)              => write!(fmt, "if {}", ty),
            Else                => write!(fmt, "else"),
            Br(label_idx)       => write!(fmt, "br {}", label_idx),
            BrIf(label_idx)     => write!(fmt, "br_if {}", label_idx),
            BrTable(labels)     => {
                write!(fmt, "br_table")?;
                for label in labels.iter() { write!(fmt, " {}", label)?; }
                Ok(())
            },
            Return              => write!(fmt, "return"),
            Call(x)             => write!(fmt, "call {}", x),
            CallIndirect(x, y)  => write!(fmt, "call_indirect {} {}", x, y),

            // https://webassembly.github.io/spec/core/binary/instructions.html#reference-instructions
            RefNull(t)          => write!(fmt, "ref.null {}", t),
            RefIsNull           => write!(fmt, "ref.is_null"),
            RefFunc(x)          => write!(fmt, "ref.func {}", x),

            // https://webassembly.github.io/spec/core/binary/instructions.html#parametric-instructions
            Drop                => write!(fmt, "drop"),
            Select(types)       => {
                write!(fmt, "select")?;
                for ty in types.iter() { write!(fmt, " {}", ty)?; }
                Ok(())
            },

            // https://webassembly.github.io/spec/core/binary/instructions.html#variable-instructions
            LocalGet(x)         => write!(fmt, "local.get {}", x),
            LocalSet(x)         => write!(fmt, "local.set {}", x),
            LocalTee(x)         => write!(fmt, "local.tee {}", x),
            GlobalGet(x)        => write!(fmt, "global.get {}", x),
            GlobalSet(x)        => write!(fmt, "global.set {}", x),

            // https://webassembly.github.io/spec/core/binary/instructions.html#table-instructions
            TableGet(x)         => write!(fmt, "table.get {}", x),
            TableSet(x)         => write!(fmt, "table.set {}", x),
            TableInit(x, y)     => write!(fmt, "table.init {} {}", x, y),
            ElemDrop(x)         => write!(fmt, "elem.drop {}", x),
            TableCopy(x, y)     => write!(fmt, "table.copy {} {}", x, y),
            TableGrow(x)        => write!(fmt, "table.grow {}", x),
            TableSize(x)        => write!(fmt, "table.size {}", x),
            TableFill(x)        => write!(fmt, "table.fill {}", x),

            // https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions
            I32_Load(m)         => write!(fmt, "i32.load {}", m),
            I64_Load(m)         => write!(fmt, "i64.load {}", m),
            F32_Load(m)         => write!(fmt, "f32.load {}", m),
            F64_Load(m)         => write!(fmt, "f64.load {}", m),

            I32_Load8_s(m)      => write!(fmt, "i32.load8_s {}", m),
            I32_Load8_u(m)      => write!(fmt, "i32.load8_u {}", m),
            I32_Load16_s(m)     => write!(fmt, "i32.load16_s {}", m),
            I32_Load16_u(m)     => write!(fmt, "i32.load16_u {}", m),

            I64_Load8_s(m)      => write!(fmt, "i64.load8_s {}", m),
            I64_Load8_u(m)      => write!(fmt, "i64.load8_u {}", m),
            I64_Load16_s(m)     => write!(fmt, "i64.load16_s {}", m),
            I64_Load16_u(m)     => write!(fmt, "i64.load16_u {}", m),
            I64_Load32_s(m)     => write!(fmt, "i64.load32_s {}", m),
            I64_Load32_u(m)     => write!(fmt, "i64.load32_u {}", m),

            I32_Store(m)        => write!(fmt, "i32.store {}", m),
            I64_Store(m)        => write!(fmt, "i64.store {}", m),
            F32_Store(m)        => write!(fmt, "f32.store {}", m),
            F64_Store(m)        => write!(fmt, "f64.store {}", m),
            I32_Store8(m)       => write!(fmt, "i32.store8 {}", m),
            I32_Store16(m)      => write!(fmt, "i32.store16 {}", m),
            I64_Store8(m)       => write!(fmt, "i64.store8 {}", m),
            I64_Store16(m)      => write!(fmt, "i64.store16 {}", m),
            I64_Store32(m)      => write!(fmt, "i64.store32 {}", m),

            MemorySize          => write!(fmt, "memory.size"),
            MemoryGrow          => write!(fmt, "memory.grow"),
            MemoryInit(x)       => write!(fmt, "memory.init {}", x),
            DataDrop(x)         => write!(fmt, "data.drop {}", x),
            MemoryCopy          => write!(fmt, "memory.copy"),
            MemoryFill          => write!(fmt, "memory.fill"),

            // https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions
            I32_Const(n)        => write!(fmt, "i32.const {}", n),
            I64_Const(n)        => write!(fmt, "i64.const {}", n),
            F32_Const(z)        => write!(fmt, "f32.const {}", z),
            F64_Const(z)        => write!(fmt, "f64.const {}", z),

            I32_Eqz             => write!(fmt, "i32.eqz"),
            I32_Eq              => write!(fmt, "i32.eq"),
            I32_Ne              => write!(fmt, "i32.ne"),
            I32_Lt_s            => write!(fmt, "i32.lt_s"),
            I32_Lt_u            => write!(fmt, "i32.lt_u"),
            I32_Gt_s            => write!(fmt, "i32.gt_s"),
            I32_Gt_u            => write!(fmt, "i32.gt_u"),
            I32_Le_s            => write!(fmt, "i32.le_s"),
            I32_Le_u            => write!(fmt, "i32.le_u"),
            I32_Ge_s            => write!(fmt, "i32.ge_s"),
            I32_Ge_u            => write!(fmt, "i32.ge_u"),

            I64_Eqz             => write!(fmt, "i64.eqz"),
            I64_Eq              => write!(fmt, "i64.eq"),
            I64_Ne              => write!(fmt, "i64.ne"),
            I64_Lt_s            => write!(fmt, "i64.lt_s"),
            I64_Lt_u            => write!(fmt, "i64.lt_u"),
            I64_Gt_s            => write!(fmt, "i64.gt_s"),
            I64_Gt_u            => write!(fmt, "i64.gt_u"),
            I64_Le_s            => write!(fmt, "i64.le_s"),
            I64_Le_u            => write!(fmt, "i64.le_u"),
            I64_Ge_s            => write!(fmt, "i64.ge_s"),
            I64_Ge_u            => write!(fmt, "i64.ge_u"),

            F32_Eq              => write!(fmt, "f32.eq"),
            F32_Ne              => write!(fmt, "f32.ne"),
            F32_Lt              => write!(fmt, "f32.lt"),
            F32_Gt              => write!(fmt, "f32.gt"),
            F32_Le              => write!(fmt, "f32.le"),
            F32_Ge              => write!(fmt, "f32.ge"),

            F64_Eq              => write!(fmt, "f64.eq"),
            F64_Ne              => write!(fmt, "f64.ne"),
            F64_Lt              => write!(fmt, "f64.lt"),
            F64_Gt              => write!(fmt, "f64.gt"),
            F64_Le              => write!(fmt, "f64.le"),
            F64_Ge              => write!(fmt, "f64.ge"),

            I32_Clz             => write!(fmt, "i32.clz"),
            I32_Ctz             => write!(fmt, "i32.ctz"),
            I32_PopCnt          => write!(fmt, "i32.popcnt"),
            I32_Add             => write!(fmt, "i32.add"),
            I32_Sub             => write!(fmt, "i32.sub"),
            I32_Mul             => write!(fmt, "i32.mul"),
            I32_Div_s           => write!(fmt, "i32.div_s"),
            I32_Div_u           => write!(fmt, "i32.div_u"),
            I32_Rem_s           => write!(fmt, "i32.rem_s"),
            I32_Rem_u           => write!(fmt, "i32.rem_u"),
            I32_And             => write!(fmt, "i32.and"),
            I32_Or              => write!(fmt, "i32.or"),
            I32_Xor             => write!(fmt, "i32.xor"),
            I32_Shl             => write!(fmt, "i32.shl"),
            I32_Shr_s           => write!(fmt, "i32.shr_s"),
            I32_Shr_u           => write!(fmt, "i32.shr_u"),
            I32_Rotl            => write!(fmt, "i32.rotl"),
            I32_Rotr            => write!(fmt, "i32.rotr"),

            I64_Clz             => write!(fmt, "i64.clz"),
            I64_Ctz             => write!(fmt, "i64.ctz"),
            I64_PopCnt          => write!(fmt, "i64.popcnt"),
            I64_Add             => write!(fmt, "i64.add"),
            I64_Sub             => write!(fmt, "i64.sub"),
            I64_Mul             => write!(fmt, "i64.mul"),
            I64_Div_s           => write!(fmt, "i64.div_s"),
            I64_Div_u           => write!(fmt, "i64.div_u"),
            I64_Rem_s           => write!(fmt, "i64.rem_s"),
            I64_Rem_u           => write!(fmt, "i64.rem_u"),
            I64_And             => write!(fmt, "i64.and"),
            I64_Or              => write!(fmt, "i64.or"),
            I64_Xor             => write!(fmt, "i64.xor"),
            I64_Shl             => write!(fmt, "i64.shl"),
            I64_Shr_s           => write!(fmt, "i64.shr_s"),
            I64_Shr_u           => write!(fmt, "i64.shr_u"),
            I64_Rotl            => write!(fmt, "i64.rotl"),
            I64_Rotr            => write!(fmt, "i64.rotr"),

            F32_Abs             => write!(fmt, "f32.abs"),
            F32_Neg             => write!(fmt, "f32.neg"),
            F32_Ceil            => write!(fmt, "f32.ceil"),
            F32_Floor           => write!(fmt, "f32.floor"),
            F32_Trunc           => write!(fmt, "f32.trunc"),
            F32_Nearest         => write!(fmt, "f32.nearest"),
            F32_Sqrt            => write!(fmt, "f32.sqrt"),
            F32_Add             => write!(fmt, "f32.add"),
            F32_Sub             => write!(fmt, "f32.sub"),
            F32_Mul             => write!(fmt, "f32.mul"),
            F32_Div             => write!(fmt, "f32.div"),
            F32_Min             => write!(fmt, "f32.min"),
            F32_Max             => write!(fmt, "f32.max"),
            F32_Copysign        => write!(fmt, "f32.copysign"),

            F64_Abs             => write!(fmt, "f64.abs"),
            F64_Neg             => write!(fmt, "f64.neg"),
            F64_Ceil            => write!(fmt, "f64.ceil"),
            F64_Floor           => write!(fmt, "f64.floor"),
            F64_Trunc           => write!(fmt, "f64.trunc"),
            F64_Nearest         => write!(fmt, "f64.nearest"),
            F64_Sqrt            => write!(fmt, "f64.sqrt"),
            F64_Add             => write!(fmt, "f64.add"),
            F64_Sub             => write!(fmt, "f64.sub"),
            F64_Mul             => write!(fmt, "f64.mul"),
            F64_Div             => write!(fmt, "f64.div"),
            F64_Min             => write!(fmt, "f64.min"),
            F64_Max             => write!(fmt, "f64.max"),
            F64_Copysign        => write!(fmt, "f64.copysign"),

            I32_Wrap_I64        => write!(fmt, "i32.wrap_i64"),
            I32_Trunc_F32_s     => write!(fmt, "i32.trunc_f32_s"),
            I32_Trunc_F32_u     => write!(fmt, "i32.trunc_f32_u"),
            I32_Trunc_F64_s     => write!(fmt, "i32.trunc_f64_s"),
            I32_Trunc_F64_u     => write!(fmt, "i32.trunc_f64_u"),
            I64_Extend_I32_s    => write!(fmt, "i64.extend.i32_s"),
            I64_Extend_I32_u    => write!(fmt, "i64.extend.i32_u"),
            I64_Trunc_F32_s     => write!(fmt, "i64.trunc.f32_s"),
            I64_Trunc_F32_u     => write!(fmt, "i64.trunc.f32_u"),
            I64_Trunc_F64_s     => write!(fmt, "i64.trunc.f64_s"),
            I64_Trunc_F64_u     => write!(fmt, "i64.trunc.f64_u"),
            F32_Convert_I32_s   => write!(fmt, "f32.convert_i32_s"),
            F32_Convert_I32_u   => write!(fmt, "f32.convert_i32_u"),
            F32_Convert_I64_s   => write!(fmt, "f32.convert_i64_s"),
            F32_Convert_I64_u   => write!(fmt, "f32.convert_i64_u"),
            F32_Demote_F64      => write!(fmt, "f32.demote_f64"),
            F64_Convert_I32_s   => write!(fmt, "f64.convert_i32_s"),
            F64_Convert_I32_u   => write!(fmt, "f64.convert_i32_u"),
            F64_Convert_I64_s   => write!(fmt, "f64.convert_i64_s"),
            F64_Convert_I64_u   => write!(fmt, "f64.convert_i64_u"),
            F64_Promote_F32     => write!(fmt, "f64.promote_f32"),
            I32_Reinterpret_F32 => write!(fmt, "i32.reinterpret_f32"),
            I64_Reinterpret_F64 => write!(fmt, "i64.reinterpret_f64"),
            F32_Reinterpret_I32 => write!(fmt, "f32.reinterpret_i32"),
            F64_Reinterpret_I64 => write!(fmt, "f64.reinterpret_i64"),

            I32_Extend8_s       => write!(fmt, "i32.extend8_s"),
            I32_Extend16_s      => write!(fmt, "i32.extend16_s"),
            I64_Extend8_s       => write!(fmt, "i64.extend8_s"),
            I64_Extend16_s      => write!(fmt, "i64.extend16_s"),
            I64_Extend32_s      => write!(fmt, "i64.extend32_s"),

            I32_TruncSat_F32_s  => write!(fmt, "i32.truncsat_f32_s"),
            I32_TruncSat_F32_u  => write!(fmt, "i32.truncsat_f32_u"),
            I32_TruncSat_F64_s  => write!(fmt, "i32.truncsat_f64_s"),
            I32_TruncSat_F64_u  => write!(fmt, "i32.truncsat_f64_u"),
            I64_TruncSat_F32_s  => write!(fmt, "i64.truncsat_f32_s"),
            I64_TruncSat_F32_u  => write!(fmt, "i64.truncsat_f32_u"),
            I64_TruncSat_F64_s  => write!(fmt, "i64.truncsat_f64_s"),
            I64_TruncSat_F64_u  => write!(fmt, "i64.truncsat_f64_u"),

            End                 => write!(fmt, "end"),
        }
    }
}



/// [blocktype](https://webassembly.github.io/spec/core/binary/instructions.html#binary-blocktype)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BlockType {
    Empty,
    ValType(ValType),
    TypeIndex(u32), // XXX: Actually encoded as "s33"
}

impl Display for BlockType {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BlockType::Empty        => write!(fmt, "(empty)"),
            BlockType::ValType(t)   => write!(fmt, "{}", t),
            BlockType::TypeIndex(t) => write!(fmt, "typeidx {}", t),
        }
    }
}

/// [memarg](https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemArg { pub offset: u32, pub align: u32 }

impl Debug for MemArg {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "+{} (align {})", self.offset, (1 << self.align))
    }
}

impl Display for MemArg {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "+{} (align {})", self.offset, (1 << self.align))
    }
}


impl Decoder<'_> {
    /// [Instructions](https://webassembly.github.io/spec/core/binary/instructions.html)
    pub fn instr(&mut self) -> Instr {
        match self.byte() {
            // https://webassembly.github.io/spec/core/binary/instructions.html#control-instructions

            0x00 => Instr::Unreachable,
            0x01 => Instr::Nop,
            0x02 => Instr::Block(self.blocktype()),
            0x03 => Instr::Loop(self.blocktype()),
            0x04 => Instr::If(self.blocktype()),
            0x05 => Instr::Else,
            0x0B => Instr::End,
            0x0C => Instr::Br(self.u32()),
            0x0D => Instr::BrIf(self.u32()),
            0x0E => {
                let mut labels = self.vec(|d| d.u32());
                labels.push(self.u32());
                Instr::BrTable(labels)
            },
            0x0F => Instr::Return,
            0x10 => Instr::Call(self.u32()),
            0x11 => {
                // NOTE: opposite of reading order
                let y = self.u32();
                let x = self.u32();
                Instr::CallIndirect(x, y)
            },

            // https://webassembly.github.io/spec/core/binary/instructions.html#reference-instructions

            0xD0 => Instr::RefNull(self.reftype()),
            0xD1 => Instr::RefIsNull,
            0xD2 => Instr::RefFunc(self.u32()),

            // https://webassembly.github.io/spec/core/binary/instructions.html#parametric-instructions

            0x1A => Instr::Drop,
            0x1B => Instr::Select(Vec::new()),
            0x1C => Instr::Select(self.vec(|d| d.valtype())),

            // https://webassembly.github.io/spec/core/binary/instructions.html#variable-instructions

            0x20 => Instr::LocalGet(self.u32()),
            0x21 => Instr::LocalSet(self.u32()),
            0x22 => Instr::LocalTee(self.u32()),
            0x23 => Instr::GlobalGet(self.u32()),
            0x24 => Instr::GlobalSet(self.u32()),

            // https://webassembly.github.io/spec/core/binary/instructions.html#table-instructions

            0x25 => Instr::TableGet(self.u32()),
            0x26 => Instr::TableSet(self.u32()),
            0xFC => {
                match self.byte() {
                    // https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions
                    0 => Instr::I32_TruncSat_F32_s,
                    1 => Instr::I32_TruncSat_F32_u,
                    2 => Instr::I32_TruncSat_F64_s,
                    3 => Instr::I32_TruncSat_F64_u,
                    4 => Instr::I64_TruncSat_F32_s,
                    5 => Instr::I64_TruncSat_F32_u,
                    6 => Instr::I64_TruncSat_F64_s,
                    7 => Instr::I64_TruncSat_F64_u,

                    // https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions
                    8 => match (self.u32(), self.byte()) {
                        (x, 0x00) => Instr::MemoryInit(x),
                        (_x, other) => { self.error(format!("invalid instruction bytecode 0xFC 0x08 [x:u32] 0x{:02x}", other)); Instr::Nop }
                    },
                    9 => Instr::DataDrop(self.u32()),
                    10 => match (self.byte(), self.byte()) {
                        (0x00, 0x00) => Instr::MemoryCopy,
                        (a, _) => { self.error(format!("invalid instruction bytecode 0xFC 0x0A 0x{:02x} ...", a)); Instr::Nop },
                    },
                    11 => match self.byte() {
                        0x00 => Instr::MemoryFill,
                        a => { self.error(format!("invalid instruction bytecode 0xFc 0x0B 0x{:02x} ...", a)); Instr::Nop },
                    },

                    // https://webassembly.github.io/spec/core/binary/instructions.html#table-instructions
                    12 => {
                        // NOTE: opposite of reading order
                        let y = self.u32();
                        let x = self.u32();
                        Instr::TableInit(x, y)
                    },
                    13 => Instr::ElemDrop(self.u32()),
                    14 => {
                        // NOTE: DIFFERENT ORDER VS TABLEINIT (reading order!)
                        let x = self.u32();
                        let y = self.u32();
                        Instr::TableCopy(x, y)
                    },
                    15 => Instr::TableGrow(self.u32()),
                    16 => Instr::TableSize(self.u32()),
                    17 => Instr::TableFill(self.u32()),

                    other => {
                        self.error(format!("invalid instruction bytecode 0xFC 0x{:02x}", other));
                        Instr::Nop
                    },
                }
            },

            // https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions

            0x28 => Instr::I32_Load(self.memarg()),
            0x29 => Instr::I64_Load(self.memarg()),
            0x2A => Instr::F32_Load(self.memarg()),
            0x2B => Instr::F64_Load(self.memarg()),
            0x2C => Instr::I32_Load8_s(self.memarg()),
            0x2D => Instr::I32_Load8_u(self.memarg()),
            0x2E => Instr::I32_Load16_s(self.memarg()),
            0x2F => Instr::I32_Load16_u(self.memarg()),
            0x30 => Instr::I64_Load8_s(self.memarg()),
            0x31 => Instr::I64_Load8_u(self.memarg()),
            0x32 => Instr::I64_Load16_s(self.memarg()),
            0x33 => Instr::I64_Load16_u(self.memarg()),
            0x34 => Instr::I64_Load32_s(self.memarg()),
            0x35 => Instr::I64_Load32_u(self.memarg()),
            0x36 => Instr::I32_Store(self.memarg()),
            0x37 => Instr::I64_Store(self.memarg()),
            0x38 => Instr::F32_Store(self.memarg()),
            0x39 => Instr::F64_Store(self.memarg()),
            0x3A => Instr::I32_Store8(self.memarg()),
            0x3B => Instr::I32_Store16(self.memarg()),
            0x3C => Instr::I64_Store8(self.memarg()),
            0x3D => Instr::I64_Store16(self.memarg()),
            0x3E => Instr::I64_Store32(self.memarg()),
            0x3F => match self.byte() { 0x00 => Instr::MemorySize, other => { self.error(format!("invalid instruction bytecode 0x3F 0x{:02x}", other)); Instr::Nop } },
            0x40 => match self.byte() { 0x00 => Instr::MemoryGrow, other => { self.error(format!("invalid instruction bytecode 0x40 0x{:02x}", other)); Instr::Nop } },

            // https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions

            0x41 => Instr::I32_Const(self.s32()),
            0x42 => Instr::I64_Const(self.s64()),
            0x43 => Instr::F32_Const(self.f32()),
            0x44 => Instr::F64_Const(self.f64()),

            0x45 => Instr::I32_Eqz,
            0x46 => Instr::I32_Eq,
            0x47 => Instr::I32_Ne,
            0x48 => Instr::I32_Lt_s,
            0x49 => Instr::I32_Lt_u,
            0x4A => Instr::I32_Gt_s,
            0x4B => Instr::I32_Gt_u,
            0x4C => Instr::I32_Le_s,
            0x4D => Instr::I32_Le_u,
            0x4E => Instr::I32_Ge_s,
            0x4F => Instr::I32_Ge_u,

            0x50 => Instr::I64_Eqz,
            0x51 => Instr::I64_Eq,
            0x52 => Instr::I64_Ne,
            0x53 => Instr::I64_Lt_s,
            0x54 => Instr::I64_Lt_u,
            0x55 => Instr::I64_Gt_s,
            0x56 => Instr::I64_Gt_u,
            0x57 => Instr::I64_Le_s,
            0x58 => Instr::I64_Le_u,
            0x59 => Instr::I64_Ge_s,
            0x5A => Instr::I64_Ge_u,

            0x5B => Instr::F32_Eq,
            0x5C => Instr::F32_Ne,
            0x5D => Instr::F32_Lt,
            0x5E => Instr::F32_Gt,
            0x5F => Instr::F32_Le,
            0x60 => Instr::F32_Ge,

            0x61 => Instr::F64_Eq,
            0x62 => Instr::F64_Ne,
            0x63 => Instr::F64_Lt,
            0x64 => Instr::F64_Gt,
            0x65 => Instr::F64_Le,
            0x66 => Instr::F64_Ge,

            0x67 => Instr::I32_Clz,
            0x68 => Instr::I32_Ctz,
            0x69 => Instr::I32_PopCnt,
            0x6A => Instr::I32_Add,
            0x6B => Instr::I32_Sub,
            0x6C => Instr::I32_Mul,
            0x6D => Instr::I32_Div_s,
            0x6E => Instr::I32_Div_u,
            0x6F => Instr::I32_Rem_s,
            0x70 => Instr::I32_Rem_u,
            0x71 => Instr::I32_And,
            0x72 => Instr::I32_Or,
            0x73 => Instr::I32_Xor,
            0x74 => Instr::I32_Shl,
            0x75 => Instr::I32_Shr_s,
            0x76 => Instr::I32_Shr_u,
            0x77 => Instr::I32_Rotl,
            0x78 => Instr::I32_Rotr,

            0x79 => Instr::I64_Clz,
            0x7A => Instr::I64_Ctz,
            0x7B => Instr::I64_PopCnt,
            0x7C => Instr::I64_Add,
            0x7D => Instr::I64_Sub,
            0x7E => Instr::I64_Mul,
            0x7F => Instr::I64_Div_s,
            0x80 => Instr::I64_Div_u,
            0x81 => Instr::I64_Rem_s,
            0x82 => Instr::I64_Rem_u,
            0x83 => Instr::I64_And,
            0x84 => Instr::I64_Or,
            0x85 => Instr::I64_Xor,
            0x86 => Instr::I64_Shl,
            0x87 => Instr::I64_Shr_s,
            0x88 => Instr::I64_Shr_u,
            0x89 => Instr::I64_Rotl,
            0x8A => Instr::I64_Rotr,

            0x8B => Instr::F32_Abs,
            0x8C => Instr::F32_Neg,
            0x8D => Instr::F32_Ceil,
            0x8E => Instr::F32_Floor,
            0x8F => Instr::F32_Trunc,
            0x90 => Instr::F32_Nearest,
            0x91 => Instr::F32_Sqrt,
            0x92 => Instr::F32_Add,
            0x93 => Instr::F32_Sub,
            0x94 => Instr::F32_Mul,
            0x95 => Instr::F32_Div,
            0x96 => Instr::F32_Min,
            0x97 => Instr::F32_Max,
            0x98 => Instr::F32_Copysign,

            0x99 => Instr::F64_Abs,
            0x9A => Instr::F64_Neg,
            0x9B => Instr::F64_Ceil,
            0x9C => Instr::F64_Floor,
            0x9D => Instr::F64_Trunc,
            0x9E => Instr::F64_Nearest,
            0x9F => Instr::F64_Sqrt,
            0xA0 => Instr::F64_Add,
            0xA1 => Instr::F64_Sub,
            0xA2 => Instr::F64_Mul,
            0xA3 => Instr::F64_Div,
            0xA4 => Instr::F64_Min,
            0xA5 => Instr::F64_Max,
            0xA6 => Instr::F64_Copysign,

            0xA7 => Instr::I32_Wrap_I64,
            0xA8 => Instr::I32_Trunc_F32_s,
            0xA9 => Instr::I32_Trunc_F32_u,
            0xAA => Instr::I32_Trunc_F64_s,
            0xAB => Instr::I32_Trunc_F64_u,
            0xAC => Instr::I64_Extend_I32_s,
            0xAD => Instr::I64_Extend_I32_u,
            0xAE => Instr::I64_Trunc_F32_s,
            0xAF => Instr::I64_Trunc_F32_u,
            0xB0 => Instr::I64_Trunc_F64_s,
            0xB1 => Instr::I64_Trunc_F64_u,
            0xB2 => Instr::F32_Convert_I32_s,
            0xB3 => Instr::F32_Convert_I32_u,
            0xB4 => Instr::F32_Convert_I64_s,
            0xB5 => Instr::F32_Convert_I64_u,
            0xB6 => Instr::F32_Demote_F64,
            0xB7 => Instr::F64_Convert_I32_s,
            0xB8 => Instr::F64_Convert_I32_u,
            0xB9 => Instr::F64_Convert_I64_s,
            0xBA => Instr::F64_Convert_I64_u,
            0xBB => Instr::F64_Promote_F32,
            0xBC => Instr::I32_Reinterpret_F32,
            0xBD => Instr::I64_Reinterpret_F64,
            0xBE => Instr::F32_Reinterpret_I32,
            0xBF => Instr::F64_Reinterpret_I64,

            0xC0 => Instr::I32_Extend8_s,
            0xC1 => Instr::I32_Extend16_s,
            0xC2 => Instr::I64_Extend8_s,
            0xC3 => Instr::I64_Extend16_s,
            0xC4 => Instr::I64_Extend32_s,

            other => {
                self.error(format!("invalid instruction bytecode 0x{:02x}", other));
                Instr::Nop
            },
        }
    }

    /// [blocktype](https://webassembly.github.io/spec/core/binary/instructions.html#binary-blocktype)
    pub fn blocktype(&mut self) -> BlockType {
        if self.remaining.starts_with(&[0x40]) {
            self.skip(1); // 0x40
            BlockType::Empty
        } else if let Some(vt) = self.try_valtype() {
            BlockType::ValType(vt)
        } else {
            BlockType::TypeIndex(self.s33_positive())
        }
    }

    /// [memarg](https://webassembly.github.io/spec/core/binary/instructions.html#memory-instructions)
    pub fn memarg(&mut self) -> MemArg {
        MemArg {
            align: self.u32(),
            offset: self.u32(),
        }
    }
}
