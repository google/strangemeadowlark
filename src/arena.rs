use bumpalo::Bump;

#[derive(Default)]
pub struct Arena {
    bump: Bump,
}

impl Arena {
    pub fn new() -> Self {
        Self { bump: Bump::new() }
    }

    pub fn alloc<T>(&self, val: T) -> &mut T {
        self.bump.alloc(val)
    }

    pub fn alloc_slice_copy<T: Copy>(&self, val: &[T]) -> &mut [T] {
        self.bump.alloc_slice_copy(val)
    }

    pub fn alloc_str(&self, src: &str) -> &mut str {
        self.bump.alloc_str(src)
    }
}
