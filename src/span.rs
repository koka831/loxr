pub type BytePos = usize;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Span {
    pub base: BytePos,
    pub len: usize,
}

impl Span {
    // Span with [lo, hi)
    pub fn new(lo: BytePos, hi: BytePos) -> Self {
        assert!(lo <= hi);
        Span {
            base: lo,
            len: hi - lo,
        }
    }

    pub fn from_len(base: BytePos, len: usize) -> Self {
        Span { base, len }
    }

    pub fn with_lo(&self, lo: BytePos) -> Self {
        Span::new(lo, self.hi())
    }

    pub fn with_hi(&self, hi: BytePos) -> Self {
        Span::new(self.lo(), hi)
    }

    pub fn lo(&self) -> BytePos {
        self.base
    }

    pub fn hi(&self) -> BytePos {
        self.base + self.len
    }
}
