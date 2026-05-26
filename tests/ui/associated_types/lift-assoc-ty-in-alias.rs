//@ known-failure
pub trait HasAssoc {
    type Assoc;
}

pub type Alias<B> = <B as HasAssoc>::Assoc;
