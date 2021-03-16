use std::cell::RefCell;
use std::rc::Rc;



#[derive(Clone)]
pub struct Decoder<'b> {
    pub(crate) original_len:    usize,
    pub(crate) remaining:       &'b [u8],
    pub(crate) errors:          Rc<RefCell<Vec<String>>>,
}

impl<'b> Decoder<'b> {
    pub fn new(bytes: &'b [u8]) -> Self {
        Self {
            original_len:   bytes.len(),
            remaining:      bytes,
            errors:         Default::default(),
        }
    }

    pub fn truncate_remaining(&mut self, len: usize) {
        if let Some(trunc) = self.remaining.get(..len) {
            self.original_len -= self.remaining.len() - len;
            self.remaining = trunc;
        }
    }

    pub fn vec<T>(&mut self, mut op: impl FnMut(&mut Self) -> T) -> Vec<T> {
        let n = self.u32();
        let mut v = Vec::new();
        for _ in 0 .. n { v.push(op(self)); }
        v
    }

    pub(crate) fn error(&mut self, reason: impl AsRef<str>) {
        let offset = self.original_len - self.remaining.len();
        self.errors.borrow_mut().push(format!("offset 0x{:x}: {}", offset, reason.as_ref()));
    }

    pub(crate) fn skip(&mut self, n: usize) {
        self.remaining = self.remaining.get(n..).unwrap_or(&[]);
    }
}
