extern crate alloc;

use alloc::vec::Vec;
use core::fmt;

use crate::byteorder::{BigEndian, ByteOrder, LittleEndian};

/// A list of error categories encountered when parsing numbers.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[non_exhaustive]
pub enum FromStrRadixErrKind {
    /// A character in the input string is not valid for the given radix.
    InvalidCharacter,

    /// The input length is not valid for the given radix.
    InvalidLength,

    /// The given radix is not supported.
    UnsupportedRadix,
}

#[derive(Debug)]
enum FromStrRadixErrSrc {
    Hex(FromHexError),
    Dec(FromDecStrErr),
}

impl fmt::Display for FromStrRadixErrSrc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FromStrRadixErrSrc::Dec(d) => write!(f, "{}", d),
            FromStrRadixErrSrc::Hex(h) => write!(f, "{}", h),
        }
    }
}

/// The error type for parsing numbers from strings.
#[derive(Debug)]
pub struct FromStrRadixErr {
    kind: FromStrRadixErrKind,
    source: Option<FromStrRadixErrSrc>,
}

impl FromStrRadixErr {
    #[doc(hidden)]
    pub fn unsupported() -> Self {
        Self {
            kind: FromStrRadixErrKind::UnsupportedRadix,
            source: None,
        }
    }

    /// Returns the corresponding `FromStrRadixErrKind` for this error.
    pub fn kind(&self) -> FromStrRadixErrKind {
        self.kind
    }
}

impl fmt::Display for FromStrRadixErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref src) = self.source {
            return write!(f, "{}", src);
        }

        match self.kind {
            FromStrRadixErrKind::UnsupportedRadix => write!(f, "the given radix is not supported"),
            FromStrRadixErrKind::InvalidCharacter => {
                write!(f, "input contains an invalid character")
            }
            FromStrRadixErrKind::InvalidLength => {
                write!(f, "length not supported for radix or type")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromStrRadixErr {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self.source {
            Some(FromStrRadixErrSrc::Dec(ref d)) => Some(d),
            Some(FromStrRadixErrSrc::Hex(ref h)) => Some(h),
            None => None,
        }
    }
}

impl From<FromDecStrErr> for FromStrRadixErr {
    fn from(e: FromDecStrErr) -> Self {
        let kind = match e {
            FromDecStrErr::InvalidCharacter => FromStrRadixErrKind::InvalidCharacter,
            FromDecStrErr::InvalidLength => FromStrRadixErrKind::InvalidLength,
        };

        Self {
            kind,
            source: Some(FromStrRadixErrSrc::Dec(e)),
        }
    }
}

impl From<FromHexError> for FromStrRadixErr {
    fn from(e: FromHexError) -> Self {
        let kind = match e.inner {
            hex::FromHexError::InvalidHexCharacter { .. } => FromStrRadixErrKind::InvalidCharacter,
            hex::FromHexError::InvalidStringLength => FromStrRadixErrKind::InvalidLength,
            hex::FromHexError::OddLength => FromStrRadixErrKind::InvalidLength,
        };

        Self {
            kind,
            source: Some(FromStrRadixErrSrc::Hex(e)),
        }
    }
}

/// Conversion from decimal string error
#[derive(Debug, PartialEq)]
pub enum FromDecStrErr {
    /// Char not from range 0-9
    InvalidCharacter,
    /// Value does not fit into type
    InvalidLength,
}

impl fmt::Display for FromDecStrErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                FromDecStrErr::InvalidCharacter => "a character is not in the range 0-9",
                FromDecStrErr::InvalidLength => "the number is too large for the type",
            }
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromDecStrErr {}

#[derive(Debug)]
pub struct FromHexError {
    inner: hex::FromHexError,
}

impl fmt::Display for FromHexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromHexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.inner)
    }
}

#[doc(hidden)]
impl From<hex::FromHexError> for FromHexError {
    fn from(inner: hex::FromHexError) -> Self {
        Self { inner }
    }
}

#[repr(C)]
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Uint<const N: usize>(pub [u64; N]);

impl<const N: usize> crate::core_::convert::From<u128> for Uint<N> {
    fn from(value: u128) -> Self {
        let mut ret = [0; N];
        ret[0] = value as u64;
        ret[1] = (value >> 64) as u64;
        Self(ret)
    }
}

impl<const N: usize> crate::core_::convert::From<i128> for Uint<N> {
    fn from(value: i128) -> Self {
        match value >= 0 {
            true => From::from(value as u128),
            false => {
                panic!("Unsigned integer can't be created from negative value");
            }
        }
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! overflowing {
    ($op: expr, $overflow: expr) => {{
        let (overflow_x, overflow_overflow) = $op;
        $overflow |= overflow_overflow;
        overflow_x
    }};
    ($op: expr) => {{
        let (overflow_x, _overflow_overflow) = $op;
        overflow_x
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! panic_on_overflow {
    ($name: expr) => {
        if $name {
            panic!("arithmetic operation overflow")
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_map_from {
    ($thing:ident, $from:ty, $to:ty) => {
        impl<const N: usize> From<$from> for $thing<N> {
            fn from(value: $from) -> $thing<N> {
                From::from(value as $to)
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_mul_for_primitive {
    ($name: ty, $other: ident) => {
        impl<const N: usize> $crate::core_::ops::Mul<$other> for $name {
            type Output = $name;

            fn mul(self, other: $other) -> Self::Output {
                let (result, carry) = self.overflowing_mul_u64(other as u64);
                panic_on_overflow!(carry > 0);
                result
            }
        }

        impl<'a, const N: usize> $crate::core_::ops::Mul<&'a $other> for $name {
            type Output = $name;

            fn mul(self, other: &'a $other) -> Self::Output {
                let (result, carry) = self.overflowing_mul_u64(*other as u64);
                panic_on_overflow!(carry > 0);
                result
            }
        }

        impl<'a, const N: usize> $crate::core_::ops::Mul<&'a $other> for &'a $name {
            type Output = $name;

            fn mul(self, other: &'a $other) -> Self::Output {
                let (result, carry) = self.overflowing_mul_u64(*other as u64);
                panic_on_overflow!(carry > 0);
                result
            }
        }

        impl<'a, const N: usize> $crate::core_::ops::Mul<$other> for &'a $name {
            type Output = $name;

            fn mul(self, other: $other) -> Self::Output {
                let (result, carry) = self.overflowing_mul_u64(other as u64);
                panic_on_overflow!(carry > 0);
                result
            }
        }

        impl<const N: usize> $crate::core_::ops::MulAssign<$other> for $name {
            fn mul_assign(&mut self, other: $other) {
                let result = *self * (other as u64);
                *self = result
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_try_from_for_primitive {
    ($from:ty, $to:ty) => {
        impl<const N: usize> $crate::core_::convert::TryFrom<$from> for $to {
            type Error = &'static str;

            #[inline]
            fn try_from(u: $from) -> $crate::core_::result::Result<$to, &'static str> {
                let arr = &u.0;
                if !u.fits_word() || arr[0] > <$to>::max_value() as u64 {
                    Err(concat!(
                        "integer overflow when casting to ",
                        stringify!($to)
                    ))
                } else {
                    Ok(arr[0] as $to)
                }
            }
        }
    };
}

impl<const N: usize> Uint<N> {
    /// Low 2 words (u128)
    #[inline]
    pub const fn low_u128(&self) -> u128 {
        let &Self(ref arr) = self;
        ((arr[1] as u128) << 64) + arr[0] as u128
    }

    /// Conversion to u128 with overflow checking
    ///
    /// # Panics
    ///
    /// Panics if the number is larger than 2^128.
    #[inline]
    pub fn as_u128(&self) -> u128 {
        let &Self(ref arr) = self;
        for i in 2..N {
            if arr[i] != 0 {
                panic!("Integer overflow when casting to u128")
            }
        }
        self.low_u128()
    }
}

impl<const N: usize> crate::core_::convert::TryFrom<Uint<N>> for u128 {
    type Error = &'static str;

    #[inline]
    fn try_from(u: Uint<N>) -> crate::core_::result::Result<u128, &'static str> {
        let Uint::<N>(arr) = u;
        for i in 2..N {
            if arr[i] != 0 {
                return Err("integer overflow when casting to u128");
            }
        }
        Ok(((arr[1] as u128) << 64) + arr[0] as u128)
    }
}

impl<const N: usize> crate::core_::convert::TryFrom<Uint<N>> for i128 {
    type Error = &'static str;

    #[inline]
    fn try_from(u: Uint<N>) -> crate::core_::result::Result<i128, &'static str> {
        let err_str = "integer overflow when casting to i128";
        let i = u128::try_from(u).map_err(|_| err_str)?;
        if i > i128::MAX as u128 {
            Err(err_str)
        } else {
            Ok(i as i128)
        }
    }
}

/// Get a reference to the underlying little-endian words.
impl<const N: usize> AsRef<[u64]> for Uint<N> {
    #[inline]
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}

impl<'a, const N: usize> From<&'a Uint<N>> for Uint<N> {
    fn from(x: &'a Self) -> Self {
        *x
    }
}

impl<const N: usize> Uint<N> {
    const WORD_BITS: usize = 64;
    /// Maximum value.
    pub const MAX: Self = Uint::<N>([u64::MAX; N]);
    pub const NN: usize = N;

    pub fn get_n(self) -> usize {
        Self::NN
    }

    /// Converts a string slice in a given base to an integer. Only supports radixes of 10
    /// and 16.
    pub fn from_str_radix(txt: &str, radix: u32) -> Result<Self, crate::FromStrRadixErr> {
        let parsed = match radix {
            10 => Self::from_dec_str(txt)?,
            16 => core::str::FromStr::from_str(txt)?,
            _ => return Err(crate::FromStrRadixErr::unsupported()),
        };
        Ok(parsed)
    }

    /// Convert from a decimal string.
    pub fn from_dec_str(value: &str) -> crate::core_::result::Result<Self, crate::FromDecStrErr> {
        let mut res = Self::default();
        for b in value.bytes().map(|b| b.wrapping_sub(b'0')) {
            if b > 9 {
                return Err(crate::FromDecStrErr::InvalidCharacter);
            }
            let (r, overflow) = res.overflowing_mul_u64(10);
            if overflow > 0 {
                return Err(crate::FromDecStrErr::InvalidLength);
            }
            let (r, overflow) = r.overflowing_add(b.into());
            if overflow {
                return Err(crate::FromDecStrErr::InvalidLength);
            }
            res = r;
        }
        Ok(res)
    }

    /// Conversion to u32
    #[inline]
    pub const fn low_u32(&self) -> u32 {
        let &Self(ref arr) = self;
        arr[0] as u32
    }

    /// Low word (u64)
    #[inline]
    pub const fn low_u64(&self) -> u64 {
        let &Self(ref arr) = self;
        arr[0]
    }

    /// Conversion to u32 with overflow checking
    ///
    /// # Panics
    ///
    /// Panics if the number is larger than 2^32.
    #[inline]
    pub fn as_u32(&self) -> u32 {
        let &Self(ref arr) = self;
        if !self.fits_word() || arr[0] > u32::MAX as u64 {
            panic!("Integer overflow when casting to u32")
        }
        self.as_u64() as u32
    }

    /// Conversion to u64 with overflow checking
    ///
    /// # Panics
    ///
    /// Panics if the number is larger than u64::max_value().
    #[inline]
    pub fn as_u64(&self) -> u64 {
        let &Self(ref arr) = self;
        if !self.fits_word() {
            panic!("Integer overflow when casting to u64")
        }
        arr[0]
    }

    /// Conversion to usize with overflow checking
    ///
    /// # Panics
    ///
    /// Panics if the number is larger than usize::max_value().
    #[inline]
    pub fn as_usize(&self) -> usize {
        let &Self(ref arr) = self;
        if !self.fits_word() || arr[0] > usize::MAX as u64 {
            panic!("Integer overflow when casting to usize")
        }
        arr[0] as usize
    }

    /// Whether this is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        let &Self(ref arr) = self;
        for i in 0..N {
            if arr[i] != 0 {
                return false;
            }
        }
        true
    }

    // Whether this fits u64.
    #[inline]
    fn fits_word(&self) -> bool {
        let &Self(ref arr) = self;
        for i in 1..N {
            if arr[i] != 0 {
                return false;
            }
        }
        true
    }
    /// Return the least number of bits needed to represent the number
    #[inline]
    pub fn bits(&self) -> usize {
        let &Self(ref arr) = self;
        for i in 1..N {
            if arr[N - i] > 0 {
                return (0x40 * (N - i + 1)) - arr[N - i].leading_zeros() as usize;
            }
        }
        0x40 - arr[0].leading_zeros() as usize
    }

    /// Return if specific bit is set.
    ///
    /// # Panics
    ///
    /// Panics if `index` exceeds the bit width of the number.
    #[inline]
    pub const fn bit(&self, index: usize) -> bool {
        let &Self(ref arr) = self;
        arr[index / 64] & (1 << (index % 64)) != 0
    }

    /// Returns the number of leading zeros in the binary representation of self.
    pub fn leading_zeros(&self) -> u32 {
        let mut r = 0;
        for i in 0..N {
            let w = self.0[N - i - 1];
            if w == 0 {
                r += 64;
            } else {
                r += w.leading_zeros();
                break;
            }
        }
        r
    }

    /// Returns the number of trailing zeros in the binary representation of self.
    pub fn trailing_zeros(&self) -> u32 {
        let mut r = 0;
        for i in 0..N {
            let w = self.0[i];
            if w == 0 {
                r += 64;
            } else {
                r += w.trailing_zeros();
                break;
            }
        }
        r
    }

    /// Return specific byte.
    ///
    /// # Panics
    ///
    /// Panics if `index` exceeds the byte width of the number.
    #[inline]
    pub const fn byte(&self, index: usize) -> u8 {
        let &Self(ref arr) = self;
        (arr[index / 8] >> ((index % 8) * 8)) as u8
    }

    /// Write to the slice in big-endian format.
    #[inline]
    pub fn to_big_endian(&self, bytes: &mut [u8]) {
        debug_assert!(N * 8 == bytes.len());
        for i in 0..N {
            BigEndian::write_u64(&mut bytes[8 * i..], self.0[N - i - 1]);
        }
    }

    /// Write to the slice in little-endian format.
    #[inline]
    pub fn to_little_endian(&self, bytes: &mut [u8]) {
        debug_assert!(N * 8 == bytes.len());
        for i in 0..N {
            LittleEndian::write_u64(&mut bytes[8 * i..], self.0[i]);
        }
    }

    /// Create `10**n` as this type.
    ///
    /// # Panics
    ///
    /// Panics if the result overflows the type.
    #[inline]
    pub fn exp10(n: usize) -> Self {
        match n {
            0 => Self::from(1u64),
            _ => Self::exp10(n - 1) * 10u32,
        }
    }

    /// Zero (additive identity) of this type.
    #[inline]
    pub const fn zero() -> Self {
        Self([0; N])
    }

    /// One (multiplicative identity) of this type.
    #[inline]
    pub fn one() -> Self {
        From::from(1u64)
    }

    /// The maximum value which can be inhabited by this type.
    #[inline]
    pub fn max_value() -> Self {
        let mut result = [0; N];
        for i in 0..N {
            result[i] = u64::MAX;
        }
        Self(result)
    }

    fn full_shl(self, shift: u32) -> (Self, u64) {
        debug_assert!(shift < Self::WORD_BITS as u32);
        let mut u = [0u64; N];
        let u_lo = self.0[0] << shift;
        let u_hi = self >> (Self::WORD_BITS as u32 - shift);
        u[0] = u_lo;
        u[1..N].copy_from_slice(&u_hi.0[..N - 1]);

        (Self(u), u_hi.0[N - 1])
    }

    fn full_shr(u: Vec<u64>, shift: u32) -> Self {
        debug_assert!(shift < Self::WORD_BITS as u32);
        let mut res = Self::zero();
        for i in 0..N {
            res.0[i] = u[i] >> shift;
        }
        // carry
        if shift > 0 {
            for i in 1..=N {
                res.0[i - 1] |= u[i] << (Self::WORD_BITS as u32 - shift);
            }
        }
        res
    }

    fn full_mul_u64(self, by: u64) -> Vec<u64> {
        let (prod, carry) = self.overflowing_mul_u64(by);
        let mut res = Vec::<u64>::new();
        res.resize(N + 1, 0);

        res[..N].copy_from_slice(&prod.0[..]);
        res[N] = carry;
        res
    }

    fn div_mod_small(mut self, other: u64) -> (Self, Self) {
        let mut rem = 0u64;
        self.0.iter_mut().rev().for_each(|d| {
            let (q, r) = Self::div_mod_word(rem, *d, other);
            *d = q;
            rem = r;
        });
        (self, rem.into())
    }
    // See Knuth, TAOCP, Volume 2, section 4.3.1, Algorithm D.
    fn div_mod_knuth(self, mut v: Self, n: usize, m: usize) -> (Self, Self) {
        debug_assert!(self.bits() >= v.bits() && !v.fits_word());
        debug_assert!(n + m <= N);
        // D1.
        // Make sure 64th bit in v's highest word is set.
        // If we shift both self and v, it won't affect the quotient
        // and the remainder will only need to be shifted back.
        let shift = v.0[n - 1].leading_zeros();
        v <<= shift;
        // u will store the remainder (shifted)
        let (u0, u_high) = self.full_shl(shift);
        let mut u = Vec::<u64>::new();
        u.resize(N + 1, 0);

        u[0..N].copy_from_slice(&u0.0[0..N]);
        u[N] = u_high;

        // quotient
        let mut q = Self::zero();
        let v_n_1 = v.0[n - 1];
        let v_n_2 = v.0[n - 2];

        // D2. D7.
        // iterate from m downto 0
        for j in (0..=m).rev() {
            let u_jn = u[j + n];

            // D3.
            // q_hat is our guess for the j-th quotient digit
            // q_hat = min(b - 1, (u_{j+n} * b + u_{j+n-1}) / v_{n-1})
            // b = 1 << WORD_BITS
            // Theorem B: q_hat >= q_j >= q_hat - 2
            let mut q_hat = if u_jn < v_n_1 {
                let (mut q_hat, mut r_hat) = Self::div_mod_word(u_jn, u[j + n - 1], v_n_1);
                // this loop takes at most 2 iterations
                loop {
                    // check if q_hat * v_{n-2} > b * r_hat + u_{j+n-2}
                    let (hi, lo) = Self::split_u128(u128::from(q_hat) * u128::from(v_n_2));
                    if (hi, lo) <= (r_hat, u[j + n - 2]) {
                        break;
                    }
                    // then iterate till it doesn't hold
                    q_hat -= 1;
                    let (new_r_hat, overflow) = r_hat.overflowing_add(v_n_1);
                    r_hat = new_r_hat;
                    // if r_hat overflowed, we're done
                    if overflow {
                        break;
                    }
                }
                q_hat
            } else {
                // here q_hat >= q_j >= q_hat - 1
                u64::MAX
            };

            // ex. 20:
            // since q_hat * v_{n-2} <= b * r_hat + u_{j+n-2},
            // either q_hat == q_j, or q_hat == q_j + 1

            // D4.
            // let's assume optimistically q_hat == q_j
            // subtract (q_hat * v) from u[j..]
            let q_hat_v = v.full_mul_u64(q_hat);
            // u[j..] -= q_hat_v;
            let c = Self::sub_slice(&mut u[j..], &q_hat_v[..n + 1]);

            // D6.
            // actually, q_hat == q_j + 1 and u[j..] has overflowed
            // highly unlikely ~ (1 / 2^63)
            if c {
                q_hat -= 1;
                // add v to u[j..]
                let c = Self::add_slice(&mut u[j..], &v.0[..n]);
                u[j + n] = u[j + n].wrapping_add(u64::from(c));
            }

            // D5.
            q.0[j] = q_hat;
        }

        // D8.
        let remainder = Self::full_shr(u, shift);

        (q, remainder)
    }
    // Returns the least number of words needed to represent the nonzero number
    fn words(bits: usize) -> usize {
        debug_assert!(bits > 0);
        1 + (bits - 1) / Self::WORD_BITS
    }

    /// Returns a pair `(self / other, self % other)`.
    ///
    /// # Panics
    ///
    /// Panics if `other` is zero.
    pub fn div_mod(self, other: Self) -> (Self, Self) {
        let my_bits = self.bits();
        let your_bits = other.bits();

        assert!(your_bits != 0, "division by zero");

        // Early return in case we are dividing by a larger number than us
        if my_bits < your_bits {
            return (Self::zero(), self);
        }

        if your_bits <= Self::WORD_BITS {
            return self.div_mod_small(other.low_u64());
        }

        let (n, m) = {
            let my_words = Self::words(my_bits);
            let your_words = Self::words(your_bits);
            (your_words, my_words - your_words)
        };

        self.div_mod_knuth(other, n, m)
    }

    /// Compute the highest `n` such that `n * n <= self`.
    pub fn integer_sqrt(&self) -> Self {
        let one = Self::one();
        if self <= &one {
            return *self;
        }

        // the implementation is based on:
        // https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division

        // Set the initial guess to something higher than √self.
        let shift: u32 = (self.bits() as u32 + 1) / 2;
        let mut x_prev = one << shift;
        loop {
            let x = (x_prev + self / x_prev) >> 1;
            if x >= x_prev {
                return x_prev;
            }
            x_prev = x;
        }
    }

    /// Fast exponentiation by squaring
    /// https://en.wikipedia.org/wiki/Exponentiation_by_squaring
    ///
    /// # Panics
    ///
    /// Panics if the result overflows the type.
    pub fn pow(self, expon: Self) -> Self {
        if expon.is_zero() {
            return Self::one();
        }
        let is_even = |x: &Self| x.low_u64() & 1 == 0;

        let u_one = Self::one();
        let mut y = u_one;
        let mut n = expon;
        let mut x = self;
        while n > u_one {
            if is_even(&n) {
                x = x * x;
            } else {
                y = x * y;
                x = x * x;
                // to reduce odd number by 1 we should just clear the last bit
                n.0[N - 1] &= (!0u64) >> 1;
            }
            n >>= 1usize;
        }
        x * y
    }

    /// Fast exponentiation by squaring. Returns result and overflow flag.
    pub fn overflowing_pow(self, expon: Self) -> (Self, bool) {
        if expon.is_zero() {
            return (Self::one(), false);
        }

        let is_even = |x: &Self| x.low_u64() & 1 == 0;

        let u_one = Self::one();
        let mut y = u_one;
        let mut n = expon;
        let mut x = self;
        let mut overflow = false;

        while n > u_one {
            if is_even(&n) {
                x = overflowing!(x.overflowing_mul(x), overflow);
                n >>= 1usize;
            } else {
                y = overflowing!(x.overflowing_mul(y), overflow);
                x = overflowing!(x.overflowing_mul(x), overflow);
                n = (n - u_one) >> 1usize;
            }
        }
        let res = overflowing!(x.overflowing_mul(y), overflow);
        (res, overflow)
    }

    /// Checked exponentiation. Returns `None` if overflow occurred.
    pub fn checked_pow(self, expon: Self) -> Option<Self> {
        match self.overflowing_pow(expon) {
            (_, true) => None,
            (val, _) => Some(val),
        }
    }

    /// Add with overflow.
    #[inline(always)]
    pub fn overflowing_add(self, other: Self) -> (Self, bool) {
        let Self(ref me) = self;
        let Self(ref you) = other;

        let mut ret = [0u64; N];
        let ret_ptr = &mut ret as *mut [u64; N] as *mut u64;
        let mut carry = 0u64;
        // crate::static_assertions::const_assert!(
        // 	core::isize::MAX as usize / core::mem::size_of::<u64>() > N
        // );
        for i in 0..N {
            if carry != 0 {
                let (res1, overflow1) = u64::overflowing_add(me[i], you[i]);
                let (res2, overflow2) = u64::overflowing_add(res1, carry);

                unsafe {
                    // SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
                    *ret_ptr.add(i) = res2
                }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = u64::overflowing_add(me[i], you[i]);

                unsafe {
                    // SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
                    *ret_ptr.add(i) = res
                }

                carry = overflow as u64;
            }
        }
        (Self(ret), carry > 0)
    }

    /// Addition which saturates at the maximum value (Self::max_value()).
    pub fn saturating_add(self, other: Self) -> Self {
        match self.overflowing_add(other) {
            (_, true) => Self::max_value(),
            (val, false) => val,
        }
    }

    /// Checked addition. Returns `None` if overflow occurred.
    pub fn checked_add(self, other: Self) -> Option<Self> {
        match self.overflowing_add(other) {
            (_, true) => None,
            (val, _) => Some(val),
        }
    }

    /// Subtraction which underflows and returns a flag if it does.
    #[inline(always)]
    pub fn overflowing_sub(self, other: Self) -> (Self, bool) {
        let Self(ref me) = self;
        let Self(ref you) = other;

        let mut ret = [0u64; N];
        let ret_ptr = &mut ret as *mut [u64; N] as *mut u64;
        let mut carry = 0u64;
        // crate::static_assertions::const_assert!(
        // 	core::isize::MAX as usize / core::mem::size_of::<u64>() > N
        // );

        for i in 0..N {
            if carry != 0 {
                let (res1, overflow1) = u64::overflowing_sub(me[i], you[i]);
                let (res2, overflow2) = u64::overflowing_sub(res1, carry);

                unsafe {
                    // SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
                    *ret_ptr.add(i) = res2
                }
                carry = (overflow1 as u8 + overflow2 as u8) as u64;
            } else {
                let (res, overflow) = u64::overflowing_sub(me[i], you[i]);

                unsafe {
                    // SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
                    *ret_ptr.add(i) = res
                }

                carry = overflow as u64;
            }
        }
        (Self(ret), carry > 0)
    }

    /// Subtraction which saturates at zero.
    pub fn saturating_sub(self, other: Self) -> Self {
        match self.overflowing_sub(other) {
            (_, true) => Self::zero(),
            (val, false) => val,
        }
    }

    /// Checked subtraction. Returns `None` if overflow occurred.
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        match self.overflowing_sub(other) {
            (_, true) => None,
            (val, _) => Some(val),
        }
    }

    pub fn uint_full_mul_reg(self, other: Self) -> Vec<u64> {
        let Self(ref me) = self;
        let Self(ref you) = other;
        let mut ret = Vec::<u64>::new();
        ret.resize(N * 2, 0);

        for i in 0..N {
            let mut carry = 0u64;
            let b = you[i];
            for j in 0..N {
                // if $check(me[j], carry) {
                if true {
                    let a = me[j];

                    let (hi, low) = Self::split_u128(a as u128 * b as u128);

                    let overflow = {
                        let existing_low = &mut ret[i + j];
                        let (low, o) = low.overflowing_add(*existing_low);
                        *existing_low = low;
                        o
                    };

                    carry = {
                        let existing_hi = &mut ret[i + j + 1];
                        let hi = hi + overflow as u64;
                        let (hi, o0) = hi.overflowing_add(carry);
                        let (hi, o1) = hi.overflowing_add(*existing_hi);
                        *existing_hi = hi;

                        (o0 | o1) as u64
                    }
                }
            }
        }
        ret
    }
    /// Multiply with overflow, returning a flag if it does.
    #[inline(always)]
    pub fn overflowing_mul(self, other: Self) -> (Self, bool) {
        let ret = self.uint_full_mul_reg(other);

        // The safety of this is enforced by the compiler
        // let ret: [[u64; N]; 2] = unsafe { crate::core_::mem::transmute(ret.as_ptr()) };
        let mut ret0 = [0u64; N];
        let mut ret1 = [0u64; N];
        ret0.copy_from_slice(&ret[0..N]);
        ret1.copy_from_slice(&ret[N..2 * N]);

        let ret0 = Self(ret0);
        let ret1 = Self(ret1);

        // The compiler WILL NOT inline this if you remove this annotation.
        #[inline(always)]
        fn any_nonzero<const N: usize>(arr: &[u64; N]) -> bool {
            for i in 0..N {
                if arr[i] != 0 {
                    return true;
                }
            }
            false
        }
        (ret0, any_nonzero::<N>(&ret1.0))
    }

    /// Multiplication which saturates at the maximum value..
    pub fn saturating_mul(self, other: Self) -> Self {
        match self.overflowing_mul(other) {
            (_, true) => Self::max_value(),
            (val, false) => val,
        }
    }

    /// Checked multiplication. Returns `None` if overflow occurred.
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        match self.overflowing_mul(other) {
            (_, true) => None,
            (val, _) => Some(val),
        }
    }

    /// Checked division. Returns `None` if `other == 0`.
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(self / other)
        }
    }

    /// Checked modulus. Returns `None` if `other == 0`.
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            Some(self % other)
        }
    }

    /// Negation with overflow.
    pub fn overflowing_neg(self) -> (Self, bool) {
        if self.is_zero() {
            (self, false)
        } else {
            (!self, true)
        }
    }

    /// Checked negation. Returns `None` unless `self == 0`.
    pub fn checked_neg(self) -> Option<Self> {
        match self.overflowing_neg() {
            (_, true) => None,
            (zero, false) => Some(zero),
        }
    }

    #[inline(always)]
    fn div_mod_word(hi: u64, lo: u64, y: u64) -> (u64, u64) {
        debug_assert!(hi < y);
        // NOTE: this is slow (__udivti3)
        // let x = (u128::from(hi) << 64) + u128::from(lo);
        // let d = u128::from(d);
        // ((x / d) as u64, (x % d) as u64)
        // TODO: look at https://gmplib.org/~tege/division-paper.pdf
        const TWO32: u64 = 1 << 32;
        let s = y.leading_zeros();
        let y = y << s;
        let (yn1, yn0) = Self::split(y);
        let un32 = (hi << s) | lo.checked_shr(64 - s).unwrap_or(0);
        let un10 = lo << s;
        let (un1, un0) = Self::split(un10);
        let mut q1 = un32 / yn1;
        let mut rhat = un32 - q1 * yn1;

        while q1 >= TWO32 || q1 * yn0 > TWO32 * rhat + un1 {
            q1 -= 1;
            rhat += yn1;
            if rhat >= TWO32 {
                break;
            }
        }

        let un21 = un32
            .wrapping_mul(TWO32)
            .wrapping_add(un1)
            .wrapping_sub(q1.wrapping_mul(y));
        let mut q0 = un21 / yn1;
        rhat = un21.wrapping_sub(q0.wrapping_mul(yn1));

        while q0 >= TWO32 || q0 * yn0 > TWO32 * rhat + un0 {
            q0 -= 1;
            rhat += yn1;
            if rhat >= TWO32 {
                break;
            }
        }

        let rem = un21
            .wrapping_mul(TWO32)
            .wrapping_add(un0)
            .wrapping_sub(y.wrapping_mul(q0));
        (q1 * TWO32 + q0, rem >> s)
    }

    #[inline(always)]
    fn add_slice(a: &mut [u64], b: &[u64]) -> bool {
        Self::binop_slice(a, b, u64::overflowing_add)
    }

    #[inline(always)]
    fn sub_slice(a: &mut [u64], b: &[u64]) -> bool {
        Self::binop_slice(a, b, u64::overflowing_sub)
    }

    #[inline(always)]
    fn binop_slice(
        a: &mut [u64],
        b: &[u64],
        binop: impl Fn(u64, u64) -> (u64, bool) + Copy,
    ) -> bool {
        let mut c = false;
        a.iter_mut().zip(b.iter()).for_each(|(x, y)| {
            let (res, carry) = Self::binop_carry(*x, *y, c, binop);
            *x = res;
            c = carry;
        });
        c
    }

    #[inline(always)]
    fn binop_carry(
        a: u64,
        b: u64,
        c: bool,
        binop: impl Fn(u64, u64) -> (u64, bool),
    ) -> (u64, bool) {
        let (res1, overflow1) = b.overflowing_add(u64::from(c));
        let (res2, overflow2) = binop(a, res1);
        (res2, overflow1 || overflow2)
    }

    #[inline(always)]
    const fn mul_u64(a: u64, b: u64, carry: u64) -> (u64, u64) {
        let (hi, lo) = Self::split_u128(a as u128 * b as u128 + carry as u128);
        (lo, hi)
    }

    #[inline(always)]
    const fn split(a: u64) -> (u64, u64) {
        (a >> 32, a & 0xFFFF_FFFF)
    }

    #[inline(always)]
    const fn split_u128(a: u128) -> (u64, u64) {
        ((a >> 64) as _, (a & 0xFFFFFFFFFFFFFFFF) as _)
    }

    /// Overflowing multiplication by u64.
    /// Returns the result and carry.
    fn overflowing_mul_u64(mut self, other: u64) -> (Self, u64) {
        let mut carry = 0u64;

        for d in self.0.iter_mut() {
            let (res, c) = Self::mul_u64(*d, other, carry);
            *d = res;
            carry = c;
        }

        (self, carry)
    }

    /// Converts from big endian representation bytes in memory.
    pub fn from_big_endian(slice: &[u8]) -> Self {
        // assert!(N * 8 >= slice.len());
        let slice = if slice.len() > (N * 8) {
            &slice[slice.len() - N * 8..slice.len()]
        } else {
            slice
        };

        let mut padded = Vec::<u8>::new();
        padded.resize(N * 8, 0);

        padded[N * 8 - slice.len()..N * 8].copy_from_slice(slice);

        let mut ret = [0; N];
        for i in 0..N {
            ret[N - i - 1] = BigEndian::read_u64(&padded[8 * i..]);
        }
        Self(ret)
    }

    /// Converts from little endian representation bytes in memory.
    pub fn from_little_endian(slice: &[u8]) -> Self {
        assert!(N * 8 >= slice.len());

        let mut padded = Vec::<u8>::new();
        padded.resize(N * 8, 0);

        padded[0..slice.len()].copy_from_slice(slice);

        let mut ret = [0; N];
        for i in 0..N {
            ret[i] = LittleEndian::read_u64(&padded[8 * i..]);
        }
        Self(ret)
    }
}

impl<const N: usize, const M: usize> crate::core_::convert::From<Uint<M>> for [u8; N] {
    fn from(number: Uint<M>) -> Self {
        let mut arr = [0u8; N];
        number.to_big_endian(&mut arr);
        arr
    }
}

impl<const N: usize, const M: usize> crate::core_::convert::From<[u8; M]> for Uint<N> {
    fn from(bytes: [u8; M]) -> Self {
        Self::from(&bytes)
    }
}

impl<'a, const N: usize, const M: usize> crate::core_::convert::From<&'a [u8; M]> for Uint<N>
where
    [u64; M]: Sized,
{
    fn from(bytes: &[u8; M]) -> Self {
        Self::from(&bytes[..])
    }
}

impl<const N: usize> crate::core_::default::Default for Uint<N> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const N: usize> crate::core_::convert::From<u64> for Uint<N> {
    fn from(value: u64) -> Self {
        let mut ret = [0; N];
        ret[0] = value;
        Self(ret)
    }
}

impl_map_from!(Uint, u8, u64);
impl_map_from!(Uint, u16, u64);
impl_map_from!(Uint, u32, u64);
impl_map_from!(Uint, usize, u64);

impl<const N: usize> crate::core_::convert::From<i64> for Uint<N> {
    fn from(value: i64) -> Self {
        match value >= 0 {
            true => From::from(value as u64),
            false => {
                panic!("Unsigned integer can't be created from negative value");
            }
        }
    }
}

impl_map_from!(Uint, i8, i64);
impl_map_from!(Uint, i16, i64);
impl_map_from!(Uint, i32, i64);
impl_map_from!(Uint, isize, i64);

// Converts from big endian representation.
impl<'a, const N: usize> crate::core_::convert::From<&'a [u8]> for Uint<N> {
    fn from(bytes: &[u8]) -> Self {
        Self::from_big_endian(bytes)
    }
}

impl_try_from_for_primitive!(Uint<N>, u8);
impl_try_from_for_primitive!(Uint<N>, u16);
impl_try_from_for_primitive!(Uint<N>, u32);
impl_try_from_for_primitive!(Uint<N>, usize);
impl_try_from_for_primitive!(Uint<N>, u64);
impl_try_from_for_primitive!(Uint<N>, i8);
impl_try_from_for_primitive!(Uint<N>, i16);
impl_try_from_for_primitive!(Uint<N>, i32);
impl_try_from_for_primitive!(Uint<N>, isize);
impl_try_from_for_primitive!(Uint<N>, i64);

impl<T, const N: usize> crate::core_::ops::Add<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn add(self, other: T) -> Uint<N> {
        let (result, overflow) = self.overflowing_add(other.into());
        panic_on_overflow!(overflow);
        result
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Add<T> for &'a Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn add(self, other: T) -> Self::Output {
        *self + other
    }
}

impl<const N: usize> crate::core_::ops::AddAssign<Uint<N>> for Uint<N> {
    fn add_assign(&mut self, other: Self) {
        let (result, overflow) = self.overflowing_add(other);
        panic_on_overflow!(overflow);
        *self = result
    }
}

impl<T, const N: usize> crate::core_::ops::Sub<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    #[inline]
    fn sub(self, other: T) -> Uint<N> {
        let (result, overflow) = self.overflowing_sub(other.into());
        panic_on_overflow!(overflow);
        result
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Sub<T> for &'a Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn sub(self, other: T) -> Uint<N> {
        *self - other
    }
}

impl<const N: usize> crate::core_::ops::SubAssign<Uint<N>> for Uint<N> {
    fn sub_assign(&mut self, other: Uint<N>) {
        let (result, overflow) = self.overflowing_sub(other);
        panic_on_overflow!(overflow);
        *self = result
    }
}

impl<const N: usize> crate::core_::str::FromStr for Uint<N> {
    type Err = crate::FromHexError;
    fn from_str(value: &str) -> crate::core_::result::Result<Uint<N>, Self::Err> {
        let value = value.strip_prefix("0x").unwrap_or(value);
        // can't use `N+1`: use maximum value instead
        // const BYTES_LEN: usize = $n_words * 8;
        const BYTES_LEN: usize = 64 * 8;
        const MAX_ENCODED_LEN: usize = BYTES_LEN * 2;

        let mut bytes = [0_u8; BYTES_LEN];

        let encoded = value.as_bytes();

        if encoded.len() % 2 == 0 {
            let out = &mut bytes[BYTES_LEN - encoded.len() / 2..];

            crate::hex::decode_to_slice(encoded, out).map_err(Self::Err::from)?;
        } else {
            // Prepend '0' by overlaying our value on a scratch buffer filled with '0' characters.
            let mut s = [b'0'; MAX_ENCODED_LEN];
            s[MAX_ENCODED_LEN - encoded.len()..].copy_from_slice(encoded);
            let encoded = &s[MAX_ENCODED_LEN - encoded.len() - 1..];

            let out = &mut bytes[BYTES_LEN - encoded.len() / 2..];

            crate::hex::decode_to_slice(encoded, out).map_err(Self::Err::from)?;
        }

        let bytes_ref: &[u8] = &bytes;
        let res: Uint<N> = From::from(bytes_ref);

        let n = res.get_n();
        let bytes_len: usize = n * 8;
        let max_encoded_len: usize = bytes_len * 2;
        if encoded.len() > max_encoded_len {
            return Err(crate::hex::FromHexError::InvalidStringLength.into());
        }

        Ok(res)
    }
}

impl<const N: usize> crate::core_::convert::From<&'static str> for Uint<N> {
    fn from(s: &'static str) -> Self {
        s.parse().unwrap()
    }
}

impl<const N: usize> crate::core_::ops::Mul<Uint<N>> for Uint<N> {
    type Output = Uint<N>;

    fn mul(self, other: Self) -> Self::Output {
        let (result, overflow) = self.overflowing_mul(other);
        panic_on_overflow!(overflow);
        result
    }
}

impl<'a, const N: usize> crate::core_::ops::Mul<&'a Uint<N>> for Uint<N> {
    type Output = Uint<N>;

    fn mul(self, other: &'a Self) -> Self::Output {
        let (result, overflow) = self.overflowing_mul(*other);
        panic_on_overflow!(overflow);
        result
    }
}

impl<'a, const N: usize> crate::core_::ops::Mul<&'a Uint<N>> for &'a Uint<N> {
    type Output = Uint<N>;

    fn mul(self, other: &'a Uint<N>) -> Self::Output {
        let (result, overflow) = self.overflowing_mul(*other);
        panic_on_overflow!(overflow);
        result
    }
}

impl<'a, const N: usize> crate::core_::ops::Mul<Uint<N>> for &'a Uint<N> {
    type Output = Uint<N>;

    fn mul(self, other: Uint<N>) -> Self::Output {
        let (result, overflow) = self.overflowing_mul(other);
        panic_on_overflow!(overflow);
        result
    }
}

impl<const N: usize> crate::core_::ops::MulAssign<Uint<N>> for Uint<N> {
    fn mul_assign(&mut self, other: Uint<N>) {
        let result = *self * other;
        *self = result
    }
}

impl_mul_for_primitive!(Uint<N>, u8);
impl_mul_for_primitive!(Uint<N>, u16);
impl_mul_for_primitive!(Uint<N>, u32);
impl_mul_for_primitive!(Uint<N>, u64);
impl_mul_for_primitive!(Uint<N>, usize);
impl_mul_for_primitive!(Uint<N>, i8);
impl_mul_for_primitive!(Uint<N>, i16);
impl_mul_for_primitive!(Uint<N>, i32);
impl_mul_for_primitive!(Uint<N>, i64);
impl_mul_for_primitive!(Uint<N>, isize);

impl<T, const N: usize> crate::core_::ops::Div<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn div(self, other: T) -> Self::Output {
        let other: Self = other.into();
        self.div_mod(other).0
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Div<T> for &'a Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn div(self, other: T) -> Self::Output {
        *self / other
    }
}

impl<T, const N: usize> crate::core_::ops::DivAssign<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    fn div_assign(&mut self, other: T) {
        *self = *self / other.into();
    }
}

impl<T, const N: usize> crate::core_::ops::Rem<T> for Uint<N>
where
    T: Into<Uint<N>> + Copy,
{
    type Output = Uint<N>;

    fn rem(self, other: T) -> Self::Output {
        let mut sub_copy = self;
        sub_copy %= other;
        sub_copy
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Rem<T> for &'a Uint<N>
where
    T: Into<Uint<N>> + Copy,
{
    type Output = Uint<N>;

    fn rem(self, other: T) -> Self::Output {
        *self % other
    }
}

impl<T, const N: usize> crate::core_::ops::RemAssign<T> for Uint<N>
where
    T: Into<Uint<N>> + Copy,
{
    fn rem_assign(&mut self, other: T) {
        let other: Self = other.into();
        let rem = self.div_mod(other).1;
        *self = rem;
    }
}

impl<const N: usize> crate::core_::ops::BitAnd<Uint<N>> for Uint<N> {
    type Output = Uint<N>;

    #[inline]
    fn bitand(self, other: Self) -> Self {
        let Self(ref arr1) = self;
        let Self(ref arr2) = other;
        let mut ret = [0u64; N];
        for i in 0..N {
            ret[i] = arr1[i] & arr2[i];
        }
        Self(ret)
    }
}

impl<const N: usize> crate::core_::ops::BitXor<Uint<N>> for Uint<N> {
    type Output = Uint<N>;

    #[inline]
    fn bitxor(self, other: Self) -> Self {
        let Self(ref arr1) = self;
        let Self(ref arr2) = other;
        let mut ret = [0u64; N];
        for i in 0..N {
            ret[i] = arr1[i] ^ arr2[i];
        }
        Self(ret)
    }
}

impl<const N: usize> crate::core_::ops::BitOr<Uint<N>> for Uint<N> {
    type Output = Self;

    #[inline]
    fn bitor(self, other: Self) -> Self {
        let Self(ref arr1) = self;
        let Self(ref arr2) = other;
        let mut ret = [0u64; N];
        for i in 0..N {
            ret[i] = arr1[i] | arr2[i];
        }
        Self(ret)
    }
}

impl<const N: usize> crate::core_::ops::Not for Uint<N> {
    type Output = Self;

    #[inline]
    fn not(self) -> Self {
        let Self(ref arr) = self;
        let mut ret = [0u64; N];
        for i in 0..N {
            ret[i] = !arr[i];
        }
        Self(ret)
    }
}

impl<T, const N: usize> crate::core_::ops::Shl<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Self;

    fn shl(self, shift: T) -> Self {
        let shift = shift.into().as_usize();
        let Self(ref original) = self;
        let mut ret = [0u64; N];
        let word_shift = shift / 64;
        let bit_shift = shift % 64;

        // shift
        for i in word_shift..N {
            ret[i] = original[i - word_shift] << bit_shift;
        }
        // carry
        if bit_shift > 0 {
            for i in word_shift + 1..N {
                ret[i] += original[i - 1 - word_shift] >> (64 - bit_shift);
            }
        }
        Self(ret)
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Shl<T> for &'a Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;
    fn shl(self, shift: T) -> Uint<N> {
        *self << shift
    }
}

impl<T, const N: usize> crate::core_::ops::ShlAssign<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    fn shl_assign(&mut self, shift: T) {
        *self = *self << shift;
    }
}

impl<T, const N: usize> crate::core_::ops::Shr<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;

    fn shr(self, shift: T) -> Self::Output {
        let shift = shift.into().as_usize();
        let Self(ref original) = self;
        let mut ret = [0u64; N];
        let word_shift = shift / 64;
        let bit_shift = shift % 64;

        // shift
        for i in word_shift..N {
            ret[i - word_shift] = original[i] >> bit_shift;
        }

        // Carry
        if bit_shift > 0 {
            for i in word_shift + 1..N {
                ret[i - word_shift - 1] += original[i] << (64 - bit_shift);
            }
        }

        Self(ret)
    }
}

impl<'a, T, const N: usize> crate::core_::ops::Shr<T> for &'a Uint<N>
where
    T: Into<Uint<N>>,
{
    type Output = Uint<N>;
    fn shr(self, shift: T) -> Self::Output {
        *self >> shift
    }
}

impl<T, const N: usize> crate::core_::ops::ShrAssign<T> for Uint<N>
where
    T: Into<Uint<N>>,
{
    fn shr_assign(&mut self, shift: T) {
        *self = *self >> shift;
    }
}

impl<const N: usize> crate::core_::cmp::Ord for Uint<N> {
    fn cmp(&self, other: &Self) -> crate::core_::cmp::Ordering {
        self.as_ref().iter().rev().cmp(other.as_ref().iter().rev())
    }
}

impl<const N: usize> crate::core_::cmp::PartialOrd for Uint<N> {
    fn partial_cmp(&self, other: &Self) -> Option<crate::core_::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> crate::core_::fmt::Debug for Uint<N> {
    fn fmt(&self, f: &mut crate::core_::fmt::Formatter) -> crate::core_::fmt::Result {
        crate::core_::fmt::Display::fmt(self, f)
    }
}

impl<const N: usize> crate::core_::fmt::Display for Uint<N> {
    fn fmt(&self, f: &mut crate::core_::fmt::Formatter) -> crate::core_::fmt::Result {
        if self.is_zero() {
            return crate::core_::write!(f, "0");
        }

        // let mut buf = [0_u8; N * 20];
        let mut buf = Vec::<u8>::new();
        buf.resize(N * 20, 0);

        let mut i = buf.len() - 1;
        let mut current = *self;
        let ten = Self::from(10);

        loop {
            let digit = (current % ten).low_u64() as u8;
            buf[i] = digit + b'0';
            current /= ten;
            if current.is_zero() {
                break;
            }
            i -= 1;
        }

        // sequence of `'0'..'9'` chars is guaranteed to be a valid UTF8 string
        let s = unsafe { crate::core_::str::from_utf8_unchecked(&buf[i..]) };
        f.write_str(s)
    }
}

impl<const N: usize> crate::core_::fmt::LowerHex for Uint<N> {
    fn fmt(&self, f: &mut crate::core_::fmt::Formatter) -> crate::core_::fmt::Result {
        let &Self(ref data) = self;
        if f.alternate() {
            crate::core_::write!(f, "0x")?;
        }
        // special case.
        if self.is_zero() {
            return crate::core_::write!(f, "0");
        }

        let mut latch = false;
        for ch in data.iter().rev() {
            for x in 0..16 {
                let nibble = (ch & (15u64 << ((15 - x) * 4) as u64)) >> (((15 - x) * 4) as u64);
                if !latch {
                    latch = nibble != 0;
                }

                if latch {
                    crate::core_::write!(f, "{:x}", nibble)?;
                }
            }
        }
        Ok(())
    }
}

// The following APIs are not in original uint version
macro_rules! convert {
    ($small:tt, $big:tt) => {
        impl crate::core_::convert::From<Uint<$small>> for Uint<$big> {
            fn from(num: Uint<$small>) -> Self {
                let Uint::<$small>(ref arr) = num;
                let mut arr2 = [0; $big];
                for i in 0..$small {
                    arr2[i] = arr[i];
                }
                Uint::<$big>(arr2)
            }
        }

        impl crate::core_::convert::From<Uint<$big>> for Uint<$small> {
            fn from(num: Uint<$big>) -> Self {
                let Uint::<$big>(ref arr) = num;
                let mut arr2 = [0; $small];
                for i in 0..$small {
                    arr2[i] = arr[i];
                }
                Uint::<$small>(arr2)
            }
        }
    };
}

// U256 <-> U512
convert!(4, 8);
// U512 <-> U1024
convert!(8, 16);
// U1024 <-> U2048
convert!(16, 32);
