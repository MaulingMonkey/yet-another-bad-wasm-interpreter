//! [Modules](https://webassembly.github.io/spec/core/binary/modules.html)

use crate::*;

use std::fmt::{self, Debug, Formatter};



pub type Unknown = ();



// https://webassembly.github.io/spec/core/binary/modules.html#indices

pub type TypeIdx    = u32;
pub type FuncIdx    = u32;
pub type TableIdx   = u32;
pub type MemIdx     = u32;
pub type GlobalIdx  = u32;
pub type ElemIdx    = u32;
pub type DataIdx    = u32;
pub type LocalIdx   = u32;
pub type LabelIdx   = u32;



// https://webassembly.github.io/spec/core/binary/modules.html#sections



/// [Custom sections](https://webassembly.github.io/spec/core/binary/modules.html#custom-section)
#[derive(Clone, Default)]
pub struct CustomSec {
    pub name: String,
    pub data: Vec<u8>,
}

impl Debug for CustomSec {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "CustomSec {{ name: {:?}, data: {} byte(s) }}", self.name, self.data.len())
    }
}



/// [Type section](https://webassembly.github.io/spec/core/binary/modules.html#type-section)
#[derive(Clone, Debug, Default)]
pub struct TypeSec(pub Vec<FuncType>);



/// [Import section](https://webassembly.github.io/spec/core/binary/modules.html#import-section)
#[derive(Clone, Debug, Default)]
pub struct ImportSec(pub Vec<Import>);
#[derive(Clone)]
pub struct Import { pub module: String, pub name: String, pub desc: ImportDesc }
#[derive(Clone)]
pub enum ImportDesc {
    Func(TypeIdx),
    Table(TableType),
    Mem(MemType),
    Global(GlobalType),
}

impl Debug for Import {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Import {{ module: {:?}, name: {:?}, desc: {:?} }}", self.module, self.name, self.desc)
    }
}

impl Debug for ImportDesc {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ImportDesc::Func    (_i) => write!(fmt, "func ..."),
            ImportDesc::Table   (ty) => write!(fmt, "table {:?}", ty),
            ImportDesc::Mem     (ty) => write!(fmt, "mem {:?}", ty),
            ImportDesc::Global  (ty) => write!(fmt, "global {:?}", ty),
        }
    }
}



/// [Function section](https://webassembly.github.io/spec/core/binary/modules.html#function-section)
#[derive(Clone, Default)]
pub struct FuncSec(pub Vec<TypeIdx>);

impl Debug for FuncSec {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "FuncSec({:?})", self.0)
    }
}



/// [Table section](https://webassembly.github.io/spec/core/binary/modules.html#table-section)
#[derive(Clone, Debug, Default)]
pub struct TableSec(pub Vec<Table>);
#[derive(Clone)]
pub struct Table { pub ty: TableType }

impl Debug for Table {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Table {{ ty: {:?} }}", self.ty)
    }
}



/// [Memory section](https://webassembly.github.io/spec/core/binary/modules.html#memory-section)
#[derive(Clone, Debug, Default)]
pub struct MemSec(pub Vec<Mem>);
#[derive(Clone)]
pub struct Mem { pub ty: MemType }

impl Debug for Mem {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Mem {{ ty: {:?} }}", self.ty)
    }
}



/// [Global section](https://webassembly.github.io/spec/core/binary/modules.html#global-section)
#[derive(Clone, Debug, Default)]
pub struct GlobalSec(pub Vec<Global>);
#[derive(Clone)]
pub struct Global { pub ty: GlobalType, pub init: Expr }

impl Debug for Global {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Global {{ ty: {:?}, init: {:?} }}", self.ty, self.init)
    }
}



/// [Export section](https://webassembly.github.io/spec/core/binary/modules.html#export-section)
#[derive(Clone, Debug, Default)]
pub struct ExportSec(pub Vec<Export>);
#[derive(Clone)]
pub struct Export { pub name: String, pub desc: ExportDesc }
#[derive(Clone)]
pub enum ExportDesc {
    Func(FuncIdx),
    Table(TableIdx),
    Mem(MemIdx),
    Global(GlobalIdx),
}

impl Debug for Export {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Export {{ name: {:?}, desc: {:?} }}", self.name, self.desc)
    }
}

impl Debug for ExportDesc {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ExportDesc::Func    (idx) => write!(fmt, "func #{}", idx),
            ExportDesc::Table   (idx) => write!(fmt, "table #{}", idx),
            ExportDesc::Mem     (idx) => write!(fmt, "mem #{}", idx),
            ExportDesc::Global  (idx) => write!(fmt, "global #{}", idx),
        }
    }
}



/// [Start section](https://webassembly.github.io/spec/core/binary/modules.html#start-section)
#[derive(Clone, Debug)]
pub struct StartSec(pub Start);
#[derive(Clone, Debug)]
pub struct Start { pub func: FuncIdx }



/// [Element section](https://webassembly.github.io/spec/core/binary/modules.html#element-section)
#[derive(Clone, Debug, Default)]
pub struct ElemSec(pub Vec<Elem>);
#[derive(Clone)]
pub struct Elem {
    pub ty:     RefType,
    pub init:   ElemInit,
    pub mode:   ElemMode,
}
#[derive(Clone, Debug)]
pub enum ElemInit {
    Funcs(Vec<FuncIdx>),
    Exprs(Vec<Expr>),
}
#[derive(Clone, Debug)]
pub enum ElemMode {
    Active { table: TableIdx, offset: Expr },
    Passive,
    Declarative,
}

impl Debug for Elem {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Elem {{ ... }}")
    }
}



/// [Code section](https://webassembly.github.io/spec/core/binary/modules.html#code-section)
#[derive(Clone, Debug, Default)]
pub struct CodeSec(pub Vec<Code>);
#[derive(Clone, Debug)]
pub struct Code { pub locals: Vec<Local>, pub body: Expr }
#[derive(Clone)]
pub struct Local { pub n: u32, pub t: ValType }

impl Debug for Local {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "Local {{ n: {}, t: {} }}", self.n, self.t)
    }
}

#[derive(Clone, Debug)]
pub struct Func { pub ty: TypeIdx, pub locals: Vec<Local>, pub body: Expr }



/// [Data section](https://webassembly.github.io/spec/core/binary/modules.html#data-section)
#[derive(Clone, Debug, Default)]
pub struct DataSec(pub Vec<Data>);
#[derive(Clone)]
pub struct Data { // XXX
    pub init: Vec<u8>,
    pub mode_passive: bool,
    pub active_memory: TableIdx,
    pub active_offset: Option<Expr>,
}

impl Debug for Data {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "Data {{ init: {} bytes, ... }}", self.init.len())
    }
}


/// [Data count section](https://webassembly.github.io/spec/core/binary/modules.html#data-count-section)
#[derive(Clone, Debug, Default)]
pub struct DataCountSec(pub u32);



/// [Modules](https://webassembly.github.io/spec/core/binary/modules.html#binary-module)
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub types:      TypeSec,
    pub tables:     TableSec,
    pub mems:       MemSec,
    pub globals:    GlobalSec,
    pub elems:      ElemSec,
    pub datas:      DataSec,
    pub start:      Option<StartSec>,
    pub imports:    ImportSec,
    pub exports:    ExportSec,
    pub customs:    Vec<CustomSec>,

    pub funcs:      Vec<Func>,
}



impl Decoder<'_> {
    /// [Modules](https://webassembly.github.io/spec/core/binary/modules.html#binary-module)
    pub fn module(&mut self) -> Module {
        if self.remaining.get(0..4) != Some(b"\0asm") { self.error("expected WASM module magic b\"\\0asm\", is this not a WASM file?"); }
        if self.remaining.get(4..8) != Some(b"\x01\0\0\0") { self.error("expected WASM module version 01 00 00 00, is this a newer format?"); }
        self.skip(8); // magic, version

        let mut m = Module::default();

        self.customsecs(|custom| m.customs.push(custom));
        m.types = self.typesec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.imports = self.importsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        let funcsec = self.funcsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.tables = self.tablesec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.mems = self.memsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.globals = self.globalsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.exports = self.exportsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.start = self.startsec();
        self.customsecs(|custom| m.customs.push(custom));
        m.elems = self.elemsec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        let datacountsec = self.datacountsec();
        self.customsecs(|custom| m.customs.push(custom));
        let codesec = self.codesec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));
        m.datas = self.datasec().unwrap_or_default();
        self.customsecs(|custom| m.customs.push(custom));

        let _ = datacountsec;

        if !funcsec.0.is_empty() && !codesec.0.is_empty() {
            if funcsec.0.len() != codesec.0.len() {
                self.error(format!("different number of entries in funcsec ({}) vs codesec ({})", funcsec.0.len(), codesec.0.len()));
            }
            m.funcs = codesec.0.into_iter().zip(funcsec.0.into_iter()).map(|(code, func)| Func {
                ty:     func,
                locals: code.locals,
                body:   code.body,
            }).collect();
        } else {
            self.error("missing codesec or funcsec");
        }

        if !self.remaining.is_empty() { self.error("unexpected data after WASM module"); }

        dbg!(m)
    }

    fn try_section<R>(&mut self, id: u8, desc: &str, full: bool, op: impl FnOnce(&mut Self) -> R) -> Option<R> {
        if !self.remaining.starts_with(&[id]) { return None; }
        self.skip(1); // consume `id`
        let size = self.u32().into32();

        let mut section_decoder = self.clone();
        section_decoder.truncate_remaining(size);
        let result = op(&mut section_decoder);
        if full && !section_decoder.remaining.is_empty() {
            section_decoder.error(format!("unexpected data after WASM module section {:?} ({} bytes)", desc, section_decoder.remaining.len()));
        }

        self.skip(size);
        Some(result)
    }

    /// [Custom sections](https://webassembly.github.io/spec/core/binary/modules.html#custom-section)
    pub fn customsecs(&mut self, mut on_sec: impl FnMut(CustomSec)) {
        while let Some(s) = self.try_section(0, "custom", true, |d| CustomSec {
            name:   d.name(),
            data:   std::mem::replace(&mut d.remaining, &[]).to_owned(),
        }) {
            on_sec(s)
        }
    }

    /// [Type section](https://webassembly.github.io/spec/core/binary/modules.html#type-section)
    pub fn typesec(&mut self) -> Option<TypeSec> {
        self.try_section(1, "typesec", true, |d| TypeSec(d.vec(|d| d.functype())))
    }

    /// [Import section](https://webassembly.github.io/spec/core/binary/modules.html#import-section)
    pub fn importsec(&mut self) -> Option<ImportSec> {
        self.try_section(2, "importsec", true, |d| ImportSec(d.vec(|d| {
            let module = d.name();
            let name   = d.name();
            let desc   = match d.byte() {
                0x00 => ImportDesc::Func    (d.u32()),
                0x01 => ImportDesc::Table   (d.tabletype()),
                0x02 => ImportDesc::Mem     (d.memtype()),
                0x03 => ImportDesc::Global  (d.globaltype()),
                _other => {
                    d.error("invalid `importdesc` type");
                    ImportDesc::Func(!0)
                },
            };
            Import { module, name, desc }
        })))
    }

    /// [Function section](https://webassembly.github.io/spec/core/binary/modules.html#function-section)
    pub fn funcsec(&mut self) -> Option<FuncSec> {
        self.try_section(3, "funcsec", true, |d| FuncSec(d.vec(|d| d.u32())))
    }

    /// [Table section](https://webassembly.github.io/spec/core/binary/modules.html#table-section)
    pub fn tablesec(&mut self) -> Option<TableSec> {
        self.try_section(4, "tablesec", true, |d| TableSec(d.vec(|d| Table { ty: d.tabletype() })))
    }

    /// [Memory section](https://webassembly.github.io/spec/core/binary/modules.html#memory-section)
    pub fn memsec(&mut self) -> Option<MemSec> {
        self.try_section(5, "memsec", true, |d| MemSec(d.vec(|d| Mem { ty: d.memtype() })))
    }

    /// [Global section](https://webassembly.github.io/spec/core/binary/modules.html#global-section)
    pub fn globalsec(&mut self) -> Option<GlobalSec> {
        self.try_section(6, "globalsec", true, |d| GlobalSec(d.vec(|d| Global { ty: d.globaltype(), init: d.expr() })))
    }

    /// [Export section](https://webassembly.github.io/spec/core/binary/modules.html#export-section)
    pub fn exportsec(&mut self) -> Option<ExportSec> {
        self.try_section(7, "exportsec", true, |d| ExportSec(d.vec(|d| {
            let name   = d.name();
            let desc   = match d.byte() {
                0x00 => ExportDesc::Func    (d.u32()),
                0x01 => ExportDesc::Table   (d.u32()),
                0x02 => ExportDesc::Mem     (d.u32()),
                0x03 => ExportDesc::Global  (d.u32()),
                _other => {
                    d.error("invalid `exportdesc` type");
                    ExportDesc::Func(!0)
                },
            };
            Export { name, desc }
        })))
    }

    /// [Start section](https://webassembly.github.io/spec/core/binary/modules.html#start-section)
    pub fn startsec(&mut self) -> Option<StartSec> {
        self.try_section(8, "startsec", true, |d| StartSec(Start { func: d.u32() }))
    }

    /// [Element section](https://webassembly.github.io/spec/core/binary/modules.html#element-section)
    pub fn elemsec(&mut self) -> Option<ElemSec> {
        self.try_section(9, "elemsec", true, |d| ElemSec(d.vec(|d| {
            match d.byte() {
                0x00 => {
                    let e = d.expr();
                    let y = d.vec(|d| d.u32());
                    Elem { ty: RefType::FuncRef, init: ElemInit::Funcs(y), mode: ElemMode::Active { table: 0, offset: e } }
                },
                0x01 => {
                    let et = d.elemkind();
                    let y  = d.vec(|d| d.u32());
                    Elem { ty: et, init: ElemInit::Funcs(y), mode: ElemMode::Passive }
                },
                0x02 => {
                    let x  = d.u32();
                    let e  = d.expr();
                    let et = d.elemkind();
                    let y  = d.vec(|d| d.u32());
                    Elem { ty: et, init: ElemInit::Funcs(y), mode: ElemMode::Active { table: x, offset: e } }
                },
                0x03 => {
                    let et = d.elemkind();
                    let y  = d.vec(|d| d.u32());
                    Elem { ty: et, init: ElemInit::Funcs(y), mode: ElemMode::Declarative }
                },
                0x04 => {
                    let e  = d.expr();
                    let el = d.vec(|d| d.expr());
                    Elem { ty: RefType::FuncRef, init: ElemInit::Exprs(el), mode: ElemMode::Active { table: 0, offset: e } }
                },
                0x05 => {
                    let et = d.reftype();
                    let el = d.vec(|d| d.expr());
                    Elem { ty: et, init: ElemInit::Exprs(el), mode: ElemMode::Passive }
                },
                0x06 => {
                    let x  = d.u32();
                    let e  = d.expr();
                    let et = d.reftype();
                    let el = d.vec(|d| d.expr());
                    Elem { ty: et, init: ElemInit::Exprs(el), mode: ElemMode::Active { table: x, offset: e } }
                },
                0x07 => {
                    let et = d.reftype();
                    let el = d.vec(|d| d.expr());
                    Elem { ty: et, init: ElemInit::Exprs(el), mode: ElemMode::Declarative }
                },
                _other => {
                    d.error("invalid `elem` type");
                    Elem { ty: RefType::FuncRef, init: ElemInit::Exprs(Vec::new()), mode: ElemMode::Declarative }
                },
            }
        })))
    }

    fn elemkind(&mut self) -> RefType {
        match self.byte() {
            0x00 => RefType::FuncRef,
            _other => {
                self.error("invalid `elemkind`");
                RefType::FuncRef
            },
        }
    }

    /// [Code section](https://webassembly.github.io/spec/core/binary/modules.html#code-section)
    pub fn codesec(&mut self) -> Option<CodeSec> {
        self.try_section(10, "codesec", true, |d| CodeSec(d.vec(|d| {
            let _code_size = d.u32(); // not super necessary
            let locals = d.vec(|d| Local { n: d.u32(), t: d.valtype() });
            let body = d.expr();
            Code { locals, body }
        })))
    }

    /// [Data section](https://webassembly.github.io/spec/core/binary/modules.html#data-section)
    pub fn datasec(&mut self) -> Option<DataSec> {
        self.try_section(11, "datasec", true, |d| DataSec(d.vec(|d| {
            match d.byte() {
                0x00 => {
                    let e = d.expr();
                    let b = d.blob();
                    Data { init: b, mode_passive: false, active_memory: 0, active_offset: Some(e) }
                },
                0x01 => {
                    let b = d.blob();
                    Data { init: b, mode_passive: true, active_memory: 0, active_offset: None }
                },
                0x02 => {
                    let x = d.u32();
                    let e = d.expr();
                    let b = d.blob();
                    Data { init: b, mode_passive: false, active_memory: x, active_offset: Some(e) }
                },
                _other => {
                    d.error("invalid `data` type");
                    Data { init: Vec::new(), mode_passive: true, active_memory: 0, active_offset: None }
                },
            }
        })))
    }

    /// [Data count section](https://webassembly.github.io/spec/core/binary/modules.html#data-count-section)
    pub fn datacountsec(&mut self) -> Option<DataCountSec> {
        self.try_section(12, "datacountsec", true, |d| DataCountSec(d.u32()))
    }


    fn expr(&mut self) -> Expr {
        let mut indent = 0;
        let mut expr = Expr::default();
        loop {
            let instr = self.instr();
            match &instr {
                Instr::Block(_) | Instr::Loop(_) | Instr::If(_) => indent += 1,
                Instr::Else => indent += 0, // -1, +1
                Instr::End if indent == 0 => {
                    expr.0.push(instr);
                    break;
                },
                Instr::End => indent -= 1,
                _other => {},
            }
            expr.0.push(instr);
        }
        expr
    }
}
