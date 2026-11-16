// Rolling window sum, with the classic slip: the element that leaves is read before the window is full.
fn rolling_sum(x: &[i64], w: usize, out: &mut [i64]) {
    let mut acc: i64 = 0;
    for i in 0..x.len() {
        acc = acc + x[i] - x[i - w];
        out[i] = acc;
    }
}
fn main() {
    let x: Vec<i64> = (1..=10).collect();
    let mut out = vec![0i64; 10];
    rolling_sum(&x, std::hint::black_box(3), &mut out);
    println!("{:?}", out);
}
