// Signed notional of a list of fills: sum of price * quantity, in integer ticks and lots.
fn notional(px: &[i64], qty: &[i64]) -> i64 {
    let mut acc: i64 = 0;
    for i in 0..px.len() {
        acc = acc + px[i] * qty[i];
    }
    acc
}
fn main() {
    // 12 fills of 1,000,000,000 lots at 1,000,000,000 ticks: each product is 10^18, the sum 1.2 * 10^19.
    let px = vec![1_000_000_000i64; 12];
    let qty = vec![1_000_000_000i64; 12];
    println!("{}", notional(std::hint::black_box(&px), std::hint::black_box(&qty)));
}
