use core::cmp::{Ord, Ordering};
use core::ops::{Add, Div, Mul, Rem, Sub};

#[derive(Copy, Clone, Eq, Debug)]
pub struct SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    pub signed: bool,
    pub num: T,
}

impl<T> SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    pub fn new(signed: bool, num: T) -> Self {
        SignedInteger { signed, num }
    }
}

impl<T> From<T> for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    fn from(n: T) -> Self {
        Self::new(true, n)
    }
}

impl<T> Add for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        match (self.signed, rhs.signed) {
            (true, true) => Self::new(true, self.num + rhs.num),
            (true, false) => {
                if self.num > rhs.num {
                    Self::new(true, self.num - rhs.num)
                } else {
                    Self::new(false, rhs.num - self.num)
                }
            }
            (false, true) => {
                if self.num > rhs.num {
                    Self::new(false, self.num - rhs.num)
                } else {
                    Self::new(true, rhs.num - self.num)
                }
            }
            (false, false) => Self::new(false, self.num + rhs.num),
        }
    }
}

impl<T> Sub for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        match (self.signed, rhs.signed) {
            (true, true) => {
                if self.num > rhs.num {
                    Self::new(true, self.num - rhs.num)
                } else {
                    Self::new(false, rhs.num - self.num)
                }
            }
            (true, false) => Self::new(true, self.num + rhs.num),
            (false, true) => Self::new(false, self.num + rhs.num),
            (false, false) => {
                if self.num > rhs.num {
                    Self::new(true, self.num - rhs.num)
                } else {
                    Self::new(false, rhs.num - self.num)
                }
            }
        }
    }
}

impl<T> Mul for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let signed = match (self.signed, rhs.signed) {
            (true, true) => true,
            (true, false) => false,
            (false, true) => false,
            (false, false) => false,
        };
        Self {
            signed,
            num: self.num * rhs.num,
        }
    }
}

impl<T> Div for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let signed = match (self.signed, rhs.signed) {
            (true, true) => true,
            (true, false) => false,
            (false, true) => false,
            (false, false) => false,
        };
        Self {
            signed,
            num: self.num / rhs.num,
        }
    }
}

impl<T> Rem for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq
        + Copy,
{
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        // assert!(rhs.num > 0.into());
        assert!(rhs.signed);
        if self.signed {
            Self::new(true, self.num % rhs.num)
        } else {
            let res = Self::new(false, self.num % rhs.num);
            res + Self::new(true, rhs.num)
        }
    }
}

impl<T> Ord for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Eq
        + Ord,
{
    fn cmp(&self, rhs: &Self) -> Ordering {
        match (self.signed, rhs.signed) {
            (true, true) => self.num.cmp(&rhs.num),
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => self.num.cmp(&rhs.num).reverse(),
        }
    }
}

impl<T> PartialOrd for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Eq
        + Ord,
{
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl<T> PartialEq for SignedInteger<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Mul<Output = T>
        + Rem<Output = T>
        + Ord
        + Eq,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.signed == rhs.signed && self.num == rhs.num
    }
}
