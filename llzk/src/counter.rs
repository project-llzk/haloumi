use std::cell::RefCell;

#[derive(Debug)]
pub struct Counter {
    inner: RefCell<usize>,
}

impl Default for Counter {
    fn default() -> Self {
        Self {
            inner: RefCell::new(0),
        }
    }
}

impl Counter {
    pub fn peek(&self) -> usize {
        *self.inner.borrow()
    }

    pub fn step(&self) {
        *self.inner.borrow_mut() += 1;
    }
}
