fn main() {
    alt_bn128::ethereum::ut::test_alt_bn128_add();
    println!("test_alt_bn128_add     pass");
    alt_bn128::ethereum::ut::test_alt_bn128_mul();
    println!("test_alt_bn128_mul     pass");
    alt_bn128::ethereum::ut::test_alt_bn128_pairing();
    println!("test_alt_bn128_pairing pass");
}
