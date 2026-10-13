pub struct Foo<'a, T, const N: usize> {
    a: &'a T,
}

pub struct Bar;

pub struct Tuple(pub usize);

pub union Union {
    pub value: usize,
}
