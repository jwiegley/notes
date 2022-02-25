pub fn bug() {
    let mut p1: (u64, u64) = (10, 20);
    let p2 = &mut p1;
    println!("{:?}", p2);
    p1.1 = 0;
    p2.1 = 0;
}
