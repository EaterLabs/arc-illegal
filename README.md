# eater's Arc Illegal

It's made of crimes. and gay.

Do you ever feel like you need an Arc, but don't need a Mutex or RwLock because you know better?

`ArcIllegal` is for you! 

`ArcIllegal` works like an `Arc` but instead lets you use the held value as mutable! and all via safe* code!

Complete with a few convenience methods!

```rust
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
```


\* Code inside this library is not safe.