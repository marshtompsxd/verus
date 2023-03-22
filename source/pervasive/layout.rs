#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use crate::prelude::*;

verus!{

// TODO Use the Rust trait 'Sized' instead
// TODO add some means for Verus to calculate the size & alignment of types

/// Trait for reasoning about size and alignment of types.
/// *Currently in an experimental state, and not ready for general use*

pub trait SizeOf : Sized {
    /// this is a temporary hack in order to add the SizeOf support in 
    /// experimental state without breaking soundness of the overall library.
    /// To implement the SizeOf trait, the user has to prove 'sizeof_is_correct()'.
    /// which requires 'external_body' or an 'assume' or some such.
    proof fn proof_sizeof_is_correct()
        ensures sizeof_is_correct::<Self>();

    spec fn size_of() -> nat;
    spec fn align_of() -> nat;
}

pub spec fn sizeof_is_correct<T>() -> bool;

pub open spec fn is_power_2(n: int) -> bool
  decreases n
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_power_2(n / 2)
    }
}

/// Matches the conditions here: https://doc.rust-lang.org/stable/std/alloc/struct.Layout.html
pub open spec fn valid_layout(size: usize, align: usize) -> bool {
    is_power_2(align as int)
      && size <= isize::MAX as int - (isize::MAX as int % align as int)
}

#[verifier(inline)]
pub open spec fn size_of<V: SizeOf>() -> nat {
    V::size_of()
}

#[verifier(inline)]
pub open spec fn align_of<V: SizeOf>() -> nat {
    V::align_of()
}

#[verifier(external_body)]
#[inline(always)]
pub fn get_size_of<V: SizeOf>() -> (u: usize)
    ensures u as nat == size_of::<V>()
{
    core::mem::size_of::<V>()
}

#[verifier(external_body)]
#[inline(always)]
pub fn get_align_of<V: SizeOf>() -> (u: usize)
    ensures u as nat == align_of::<V>()
{
    core::mem::align_of::<V>()
}

// TODO check that this is sound
#[verifier(external_body)]
pub proof fn layout_for_type_is_valid<V: SizeOf>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
{ unimplemented!() }

}
