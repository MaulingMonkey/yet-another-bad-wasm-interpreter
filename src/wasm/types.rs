//! [Types](https://webassembly.github.io/spec/core/binary/types.html)

use crate::*;

use std::fmt::{self, Debug, Display, Formatter};



/// [Number types](https://webassembly.github.io/spec/core/binary/types.html#number-types)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum NumType {
    I32 = 0x7F,
    I64 = 0x7E,
    F32 = 0x7D,
    F64 = 0x7C,
}

/// [Reference types](https://webassembly.github.io/spec/core/binary/types.html#reference-types)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum RefType {
    FuncRef     = 0x70,
    ExternRef   = 0x6F,
}

/// [Value types](https://webassembly.github.io/spec/core/binary/types.html#value-types)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ValType {
    Num(NumType),
    Ref(RefType),
}

impl From<NumType> for ValType { fn from(value: NumType) -> Self { ValType::Num(value) } }
impl From<RefType> for ValType { fn from(value: RefType) -> Self { ValType::Ref(value) } }

/// [Result types](https://webassembly.github.io/spec/core/binary/types.html#result-types)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResultType(pub Vec<ValType>);

/// [Function types](https://webassembly.github.io/spec/core/binary/types.html#function-types)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncType(pub ResultType, pub ResultType);

/// [Limits](https://webassembly.github.io/spec/core/binary/types.html#limits)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Limits { pub min: u32, pub max: Option<u32> }

/// [Memory types](https://webassembly.github.io/spec/core/binary/types.html#memory-types)
#[derive(Clone, Debug)]
pub struct MemType { pub lim: Limits }

/// [Table types](https://webassembly.github.io/spec/core/binary/types.html#table-types)
#[derive(Clone, Debug)]
pub struct TableType { pub et: RefType, pub lim: Limits }

/// [Global types](https://webassembly.github.io/spec/core/binary/types.html#global-types)
#[derive(Clone, Debug)]
pub struct GlobalType { pub t: ValType, pub mutable: bool }




impl NumType {
    fn as_str(&self) -> &'static str {
        match *self {
            NumType::I32 => "i32",
            NumType::I64 => "i64",
            NumType::F32 => "f32",
            NumType::F64 => "f64",
        }
    }
}

impl RefType {
    fn as_str(&self) -> &'static str {
        match *self {
            RefType::FuncRef    => "funcref",
            RefType::ExternRef  => "externref",
        }
    }
}

impl ValType {
    fn as_str(&self) -> &'static str {
        match *self {
            ValType::Num(n) => n.as_str(),
            ValType::Ref(r) => r.as_str(),
        }
    }
}

impl Display for NumType  { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { write!(fmt, "{}", self.as_str()) } }
impl Display for RefType  { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { write!(fmt, "{}", self.as_str()) } }
impl Display for ValType  { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { write!(fmt, "{}", self.as_str()) } }
impl Display for FuncType { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { write!(fmt, "{:?} -> {:?}", self.0, self.1) } }

impl Display for ResultType { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
    write!(fmt, "(")?;
    for (i, v) in self.0.iter().enumerate() {
        write!(fmt, "{}{:?}", if i == 0 { "" } else { ", " }, v)?;
    }
    write!(fmt, ")")
}}

impl Debug for NumType      { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { Display::fmt(self, fmt) } }
impl Debug for RefType      { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { Display::fmt(self, fmt) } }
impl Debug for ValType      { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { Display::fmt(self, fmt) } }
impl Debug for FuncType     { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { Display::fmt(self, fmt) } }
impl Debug for ResultType   { fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result { Display::fmt(self, fmt) } }



impl Decoder<'_> {
    /// [Number types](https://webassembly.github.io/spec/core/binary/types.html#number-types)
    pub fn numtype(&mut self) -> NumType {
        match self.byte() {
            0x7F => NumType::I32,
            0x7E => NumType::I64,
            0x7D => NumType::F32,
            0x7C => NumType::F64,
            _other => {
                self.error("invalid numtype");
                NumType::I32
            },
        }
    }

    /// [Reference types](https://webassembly.github.io/spec/core/binary/types.html#reference-types)
    pub fn reftype(&mut self) -> RefType {
        match self.byte() {
            0x70 => RefType::FuncRef,
            0x6F => RefType::ExternRef,
            _other => {
                self.error("invalid reftype");
                RefType::FuncRef
            },
        }
    }

    /// [Value types](https://webassembly.github.io/spec/core/binary/types.html#value-types)
    pub fn valtype(&mut self) -> ValType {
        self.try_valtype().unwrap_or_else(||{
            self.error("invalid valtype");
            ValType::Num(NumType::I32)
        })
    }

    pub fn try_valtype(&mut self) -> Option<ValType> {
        let r = match self.remaining.get(0)? {
            0x7F    => ValType::Num(NumType::I32),
            0x7E    => ValType::Num(NumType::I64),
            0x7D    => ValType::Num(NumType::F32),
            0x7C    => ValType::Num(NumType::F64),
            0x70    => ValType::Ref(RefType::FuncRef),
            0x6F    => ValType::Ref(RefType::ExternRef),
            _other  => return None,
        };
        self.skip(1);
        Some(r)
    }

    /// [Result types](https://webassembly.github.io/spec/core/binary/types.html#result-types)
    pub fn resulttype(&mut self) -> ResultType { ResultType(self.vec(|d| d.valtype())) }

    /// [Function types](https://webassembly.github.io/spec/core/binary/types.html#function-types)
    pub fn functype(&mut self) -> FuncType {
        match self.byte() {
            0x60 => {
                let input  = self.resulttype();
                let output = self.resulttype();
                FuncType(input, output)
            },
            _other => {
                self.error("invalid functype");
                FuncType(ResultType(Vec::new()), ResultType(Vec::new()))
            },
        }
    }

    /// [Limits](https://webassembly.github.io/spec/core/binary/types.html#limits)
    pub fn limits(&mut self) -> Limits {
        match self.byte() {
            0x00 => Limits { min: self.u32(), max: None },
            0x01 => Limits { min: self.u32(), max: Some(self.u32()) },
            _other => {
                self.error("invalid limits");
                Limits { min: 0, max: None }
            },
        }
    }

    /// [Memory types](https://webassembly.github.io/spec/core/binary/types.html#memory-types)
    pub fn memtype(&mut self) -> MemType { MemType { lim: self.limits() } }

    /// [Table types](https://webassembly.github.io/spec/core/binary/types.html#table-types)
    pub fn tabletype(&mut self) -> TableType { TableType { et: self.reftype(), lim: self.limits() } }

    /// [Global types](https://webassembly.github.io/spec/core/binary/types.html#global-types)
    pub fn globaltype(&mut self) -> GlobalType { GlobalType { t: self.valtype(), mutable: match self.byte() {
        0x00 => false,
        0x01 => true,
        _other => {
            self.error("invalid mut for globaltype (expected 0x00 or 0x01)");
            true
        },
    }}}
}
