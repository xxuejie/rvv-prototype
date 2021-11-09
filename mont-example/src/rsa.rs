#![allow(dead_code)]

use super::uint_version::Mont;
use super::uint_version::U256;
use super::U;

// https://www.cs.utexas.edu/~mitra/honors/soln.html

// Choose p = 3 and q = 11
// Compute n = p * q = 3 * 11 = 33
// Compute φ(n) = (p - 1) * (q - 1) = 2 * 10 = 20
// Choose e such that 1 < e < φ(n) and e and φ (n) are co-prime. Let e = 7
// Compute a value for d such that (d * e) % φ(n) = 1. One solution is d = 3 [(3 * 7) % 20 = 1]
// Public key is (e, n) => (7, 33)
// Private key is (d, n) => (3, 33)

// The encryption of m = 2 is c = 2**7 % 33 = 29 (m ** e mod n)
// The decryption of c = 29 is m = 29**3 % 33 = 2 ( c ** d mod n)

pub struct Rsa {
    pub p: U256,
    pub q: U256,
    pub n: U256,
    pub e: U256,
    pub d: U256,
}

impl Rsa {
    pub fn new() -> Self {
        Rsa {
            p: U!(3),
            q: U!(11),
            n: U!(33),
            e: U!(7),
            d: U!(3),
        }
    }

    pub fn encrypt(&self, plain_text: U256) -> U256 {
        assert!(plain_text < self.n);
        let mut mont = Mont::new(self.n);
        mont.precompute();
        let plain_text2 = mont.to_mont(plain_text);
        let cipher_text2 = mont.pow(plain_text2, self.e);
        let cipher_text = mont.reduce(cipher_text2.into());
        cipher_text
    }
    pub fn decrypt(&self, cipher_text: U256) -> U256 {
        assert!(cipher_text < self.n);
        let mut mont = Mont::new(self.n);
        mont.precompute();
        let cipher_text2 = mont.to_mont(cipher_text);
        let plain_text2 = mont.pow(cipher_text2, self.d);
        let plain_text = mont.reduce(plain_text2.into());
        plain_text
    }
}
