//! [Values](https://webassembly.github.io/spec/core/binary/values.html)

use crate::*;

use std::borrow::Cow;
use std::convert::*;
use std::ops::{BitOr, Neg, Shl};



/// [Names](https://webassembly.github.io/spec/core/binary/values.html#names)
pub type Name = String;



impl<'b> Decoder<'b> {
    /// [Bytes](https://webassembly.github.io/spec/core/binary/values.html#bytes)
    pub fn byte(&mut self) -> u8 {
        if let &[b, ref rest @ ..] = self.remaining {
            self.remaining = rest;
            b
        } else {
            self.error("ran out of bytes decoding `byte`");
            0
        }
    }

    // [Integers](https://webassembly.github.io/spec/core/binary/values.html#integers)
    // TODO:
    // - [ ] Signed LEB128
    // - [ ] Byte count limits

    pub fn u32(&mut self) -> u32 { self.uleb128() }
    pub fn u64(&mut self) -> u64 { self.uleb128() }
    pub fn s32(&mut self) -> i32 { self.sleb128() }
    pub fn s64(&mut self) -> i64 { self.sleb128() }

    pub fn s33_positive(&mut self) -> u32 { // XXX: badhackywrong as heck
        let n : i64 = self.sleb128();
        u32::try_from(n).unwrap_or_else(|_|{
            self.error("LEB exceeded bounds of s33");
            0
        })
    }

    fn uleb128<T: Default + Shl<u8, Output = T> + BitOr<Output = T> + From<u8>>(&mut self) -> T {
        let mut u = T::default();
        let mut shift = 0u8;
        while let &[b, ref rest @ ..] = self.remaining {
            if usize::from(shift) >= 8 * std::mem::size_of::<T>() {
                self.error("`uleb128` had too many continuation bytes");
                return T::default();
            }
            self.remaining = rest;
            let masked = b & 0x7F;
            u = u | T::from(masked) << shift;
            shift += 7;
            if b == masked { return u; }
        }
        self.error("ran out of bytes decoding `uleb128`");
        T::default()
    }

    fn sleb128<T: Default + Neg<Output = T> + Shl<u8, Output = T> + BitOr<Output = T> + From<u8>>(&mut self) -> T {
        let valbits = 8 * std::mem::size_of::<T>();

        let mut s = T::default();
        let mut shift = 0u8;
        while let &[b, ref rest @ ..] = self.remaining {
            if usize::from(shift) >= valbits {
                self.error("`sleb128` had too many continuation bytes");
                return T::default();
            }
            self.remaining = rest;
            let masked = b & 0x7F;
            if b == masked {
                let neg     = (b & 0x40) != 0;
                let masked  = b & 0x3F;
                s = s | T::from(masked) << shift;
                shift += 7;
                if neg && (usize::from(shift) < valbits) {
                    let neg1 = -T::from(1);
                    return s | (neg1 << shift);
                } else {
                    return s;
                }
            } else {
                s = s | T::from(masked) << shift;
                shift += 7;
            }
        }
        self.error("ran out of bytes decoding `sleb128`");
        T::default()
    }

    /// [Floating-point](https://webassembly.github.io/spec/core/binary/values.html#floating-point)
    pub fn f32(&mut self) -> f32 {
        if let &[a, b, c, d, ref rest @ ..] = self.remaining {
            self.remaining = rest;
            f32::from_le_bytes([a, b, c, d])
        } else {
            self.error("ran out of bytes decoding `f32`");
            0.0
        }
    }

    /// [Floating-point](https://webassembly.github.io/spec/core/binary/values.html#floating-point)
    pub fn f64(&mut self) -> f64 {
        if let &[a, b, c, d, e, f, g, h, ref rest @ ..] = self.remaining {
            self.remaining = rest;
            f64::from_le_bytes([a, b, c, d, e, f, g, h])
        } else {
            self.error("ran out of bytes decoding `f64`");
            0.0
        }
    }

    /// [Names](https://webassembly.github.io/spec/core/binary/values.html#names)
    pub fn name(&mut self) -> Name {
        let n = self.u32().into32();
        match self.remaining.get(0..n) {
            Some(bytes) => {
                self.skip(n);
                let name = String::from_utf8_lossy(bytes);
                if matches!(&name, Cow::Owned(_)) { self.error(format!("`name` {:?} contains invalid UTF8", name)); }
                name.into_owned()
            },
            None => {
                self.error("ran out of bytes decoding `name`");
                self.remaining = &[];
                String::new()
            },
        }
    }

    pub(crate) fn blob(&mut self) -> Vec<u8> {
        let n = self.u32().into32();
        match self.remaining.get(0..n) {
            Some(bytes) => {
                self.skip(n);
                bytes.to_owned()
            },
            None => {
                self.error("ran out of bytes decoding `name`");
                self.remaining = &[];
                Vec::new()
            },
        }
    }
}