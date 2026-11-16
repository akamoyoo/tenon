// A parallel float sum: each thread sums a chunk, partial sums are added in the order they arrive.
// Prints the bits of the result for 1, 2, 4, 8, 16 threads, then counts distinct results over 2000 runs.
use std::sync::mpsc;
use std::thread;
fn par_sum(data: &std::sync::Arc<Vec<f64>>, k: usize) -> f64 {
    let n = data.len();
    let (tx, rx) = mpsc::channel();
    for t in 0..k {
        let (tx, data) = (tx.clone(), data.clone());
        thread::spawn(move || {
            let (lo, hi) = (t * n / k, (t + 1) * n / k);
            let s: f64 = data[lo..hi].iter().sum();
            tx.send(s).unwrap();
        });
    }
    drop(tx);
    rx.iter().sum()                       // partial sums added in the order they arrive
}
fn main() {
    let n = 1_000_000;
    let data: Vec<f64> = (0..n).map(|i| ((i as f64) * 0.7).sin() * 1e8 + 1e-3 * (i % 7) as f64).collect();
    let data = std::sync::Arc::new(data);
    for k in [1, 2, 4, 8, 16] {
        println!("threads {:2}: {:016x}", k, par_sum(&data, k).to_bits());
    }
    let mut seen = std::collections::BTreeMap::new();
    for _ in 0..2000 { *seen.entry(par_sum(&data, 16).to_bits()).or_insert(0) += 1; }
    println!("16 threads, 2000 runs: {} distinct results {:x?}", seen.len(), seen);
}
