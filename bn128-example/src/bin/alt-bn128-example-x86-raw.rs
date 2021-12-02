extern crate std;
use alt_bn128_example;
fn main() {
    println!("start test_alt_bn128_pairing...");
    alt_bn128_example::ethereum::ut::test_alt_bn128_pairing();
    println!("test_alt_bn128_pairing done");
}
