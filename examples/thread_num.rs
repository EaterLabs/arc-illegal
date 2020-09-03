use eater_arc_illegal::arc;

fn main() {
    let mut shared_num = arc(4);
    let mut cloned = shared_num.dup();
    *shared_num += 2;

    std::thread::spawn(move || {
        *cloned += 2;
    });

    std::thread::sleep(std::time::Duration::from_secs(1));

    assert_eq!(8, *shared_num);
}
