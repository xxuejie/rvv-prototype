#![no_std]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::branches_sharing_code)]

// Re-export libcore using an alias so that the macros can work without
// requiring `extern crate core` downstream.
#[doc(hidden)]
pub use core as core_;

#[doc(hidden)]
pub use byteorder;

#[doc(hidden)]
pub use hex;

#[doc(hidden)]
pub use static_assertions;

mod uint;
pub use crate::uint::*;
