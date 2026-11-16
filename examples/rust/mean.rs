fn mean(x: &[i64]) -> i64 {
    let mut s: i64 = 0;
    for v in x { s += *v; }
    s / x.len() as i64
}
fn main() {
    let x: Vec<i64> = Vec::new();
    println!("{}", mean(std::hint::black_box(&x)));
}
