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

#[macro_use]
#[rustfmt::skip]
mod uint;
pub use crate::uint::*;
