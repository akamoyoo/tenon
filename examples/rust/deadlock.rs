// Two accounts, two threads, locks taken in opposite order.
use std::sync::{Arc, Mutex};
use std::thread;
fn main() {
    let a = Arc::new(Mutex::new(100i64));
    let b = Arc::new(Mutex::new(100i64));
    let (a1, b1) = (a.clone(), b.clone());
    let t1 = thread::spawn(move || for _ in 0..100000 { let mut x = a1.lock().unwrap(); let mut y = b1.lock().unwrap(); *x -= 1; *y += 1; });
    let (a2, b2) = (a.clone(), b.clone());
    let t2 = thread::spawn(move || for _ in 0..100000 { let mut y = b2.lock().unwrap(); let mut x = a2.lock().unwrap(); *y -= 1; *x += 1; });
    t1.join().unwrap(); t2.join().unwrap();
    println!("done: {} {}", a.lock().unwrap(), b.lock().unwrap());
}
