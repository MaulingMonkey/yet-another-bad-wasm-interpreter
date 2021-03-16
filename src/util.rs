pub trait Into32<T> { fn into32(self) -> T; }

impl Into32<usize> for u32 { fn into32(self) -> usize { self as usize } }
