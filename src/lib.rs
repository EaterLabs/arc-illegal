use std::fmt::{Debug, Display};
use std::ops::{Deref, DerefMut};
use std::ptr::{drop_in_place, null_mut, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering};

/// ArcIllegal is an Arc that's illegal
///
/// ArcIllegal can always use it's contents as mutable, it sounds unsafe and
/// is unsafe too, but now without unsafe code blocks (they're just hidden in this lib), because that's what we're
/// Measuring these days
///
/// ```rust
/// use eater_arc_illegal::ArcIllegal;
/// use std::time::Duration;
/// use std::thread::{spawn, sleep};
///
/// let mut x = ArcIllegal::new("hewwo".to_string());
/// let mut y = x.clone();
/// let mut z = y.dup();
/// let a = &mut *x;
/// let b = &mut *y.dup();
/// let c = &mut *z.dup();
/// c.push_str(" wo");
/// b.push_str("rl");
/// a.push_str("d!");
/// y.push_str(" :)");
///
/// let mut zz = z.dup();
///
/// spawn(move || {
///     z.push_str(" :OOO");
/// });
///
/// spawn(move || {
///     zz.push_str("race!!!");
/// });
///
/// println!("{}", a);
/// sleep(Duration::from_millis(50));
/// println!("{}", a);
/// ```
pub struct ArcIllegal<T> {
    inner: NonNull<ArcIllegalInner<T>>,
}

unsafe impl<T> Send for ArcIllegal<T> {}
unsafe impl<T> Sync for ArcIllegal<T> {}

impl<T: Debug> Debug for ArcIllegal<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        T::fmt(&*self, f)
    }
}

impl<T: Display> Display for ArcIllegal<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        T::fmt(&*self, f)
    }
}

struct ArcIllegalInner<T: ?Sized> {
    refs: AtomicUsize,
    weak_refs: AtomicUsize,
    value: *mut T,
}

/// Creates a new [ArcIllegal], inlines [ArcIllegal::new]
#[inline]
pub fn arc<T>(inner: T) -> ArcIllegal<T> {
    ArcIllegal::new(inner)
}

impl<T> ArcIllegal<T> {
    /// Creates a new [ArcIllegal] for given object
    #[inline]
    pub fn new(inner: T) -> ArcIllegal<T> {
        let inner_arc = Box::new(ArcIllegalInner {
            refs: AtomicUsize::new(1),
            weak_refs: AtomicUsize::new(0),
            value: Box::leak(Box::new(inner)),
        });

        unsafe {
            ArcIllegal {
                inner: NonNull::new_unchecked(Box::leak(inner_arc)),
            }
        }
    }

    /// Returns the raw pointer of the value
    pub fn as_ptr(&self) -> *mut T {
        unsafe { (*self.inner.as_ptr()).value }
    }

    /// Return the amount of references that hold this object
    pub fn ref_count(&self) -> usize {
        self.strong_ref_count() + self.weak_ref_count()
    }

    /// Return the amount of weak references that hold this object
    pub fn weak_ref_count(&self) -> usize {
        unsafe {
            let inner = &*self.inner.as_ptr();
            inner.weak_refs.load(Ordering::SeqCst)
        }
    }

    /// Return the amount of "strong" references that hold this object
    pub fn strong_ref_count(&self) -> usize {
        unsafe {
            let inner = &*self.inner.as_ptr();
            inner.refs.load(Ordering::SeqCst)
        }
    }

    /// Clones the ArcIllegal,
    /// convenience function for when the held type can be cloned
    pub fn dup(&self) -> Self {
        ArcIllegal::clone(&self)
    }

    /// Get a Weak reference to the value inside the IllegalArc
    pub fn weak(&self) -> WeakIllegal<T> {
        unsafe {
            (&mut *self.inner.as_ptr())
                .weak_refs
                .fetch_add(1, Ordering::SeqCst);

            WeakIllegal {
                inner: NonNull::new_unchecked(self.inner.as_ptr()),
            }
        }
    }

    /// If we're the only reference, destroy it and give the object back as owned
    pub fn dismantle(self) -> Result<T, Self> {
        unsafe {
            if 1 != self.ref_count() {
                return Err(self);
            }
            (&mut *self.inner.as_ptr())
                .refs
                .fetch_sub(1, Ordering::SeqCst);

            let inner = self.inner.as_ptr();
            let obj = (*inner).value.read();
            drop_in_place(inner);

            Ok(obj)
        }
    }

    pub fn dismantle_with_weak(self) -> Result<T, Self> {
        unsafe {
            if 1 != self.strong_ref_count() {
                return Err(self);
            }

            (&mut *self.inner.as_ptr())
                .refs
                .fetch_sub(1, Ordering::SeqCst);

            let obj = (*self.inner.as_ptr()).value.read();
            (*self.inner.as_ptr()).value = null_mut();
            Ok(obj)
        }
    }
}

impl<T> Drop for ArcIllegal<T> {
    fn drop(&mut self) {
        unsafe {
            let prev = (&mut *self.inner.as_ptr())
                .refs
                .fetch_sub(1, Ordering::SeqCst);
            if 1 != prev {
                return;
            }

            if (&mut *self.inner.as_ptr()).refs.load(Ordering::SeqCst) == 0 {
                drop_in_place((*self.inner.as_ptr()).value);
                (*self.inner.as_ptr()).value = null_mut();
            }

            if (&mut *self.inner.as_ptr()).weak_refs.load(Ordering::SeqCst) == 0 {
                drop_in_place(self.inner.as_ptr());
            }
        }
    }
}

impl<T> Clone for ArcIllegal<T> {
    fn clone(&self) -> Self {
        unsafe {
            (&mut *self.inner.as_ptr())
                .refs
                .fetch_add(1, Ordering::SeqCst);

            ArcIllegal {
                inner: NonNull::new_unchecked(self.inner.as_ptr()),
            }
        }
    }
}

impl<T> Deref for ArcIllegal<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*(*self.inner.as_ptr()).value }
    }
}

impl<T> DerefMut for ArcIllegal<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *(*self.inner.as_ptr()).value }
    }
}

/// A weak reference to T
pub struct WeakIllegal<T> {
    inner: NonNull<ArcIllegalInner<T>>,
}

unsafe impl<T> Sync for WeakIllegal<T> {}
unsafe impl<T> Send for WeakIllegal<T> {}

impl<T> WeakIllegal<T> {
    /// Get a reference to T if T still exists
    pub fn get(&self) -> Option<&T> {
        if unsafe { self.inner.as_ref() }.refs.load(Ordering::SeqCst) == 0 {
            None
        } else {
            Some(unsafe { &*self.inner.as_ref().value })
        }
    }

    /// Get a mutable reference to T if T still exists
    pub fn get_mut(&self) -> Option<&mut T> {
        if unsafe { self.inner.as_ref() }.refs.load(Ordering::SeqCst) == 0 {
            None
        } else {
            Some(unsafe { &mut *self.inner.as_ref().value })
        }
    }

    /// Upgrade this weak reference to a STRONG reference
    pub fn strong(&self) -> Option<ArcIllegal<T>> {
        if unsafe { self.inner.as_ref() }.refs.load(Ordering::SeqCst) == 0 {
            None
        } else {
            unsafe { self.inner.as_ref() }
                .refs
                .fetch_add(1, Ordering::SeqCst);

            Some(ArcIllegal {
                inner: unsafe { NonNull::new_unchecked(self.inner.as_ptr()) },
            })
        }
    }

    /// Upgrade this weak reference to a [ArcIllegal]
    pub fn upgrade(&self) -> Option<ArcIllegal<T>> {
        self.strong()
    }

    /// Return the amount of references that hold this object
    pub fn ref_count(&self) -> usize {
        self.strong_ref_count() + self.weak_ref_count()
    }

    /// Return the amount of weak references that hold this object
    pub fn weak_ref_count(&self) -> usize {
        unsafe {
            let inner = &*self.inner.as_ptr();
            inner.weak_refs.load(Ordering::SeqCst)
        }
    }

    /// Return the amount of "strong" references that hold this object
    pub fn strong_ref_count(&self) -> usize {
        unsafe {
            let inner = &*self.inner.as_ptr();
            inner.refs.load(Ordering::SeqCst)
        }
    }
}

impl<T> Clone for WeakIllegal<T> {
    fn clone(&self) -> Self {
        unsafe {
            (&mut *self.inner.as_ptr())
                .weak_refs
                .fetch_add(1, Ordering::SeqCst);

            WeakIllegal {
                inner: NonNull::new_unchecked(self.inner.as_ptr()),
            }
        }
    }
}

impl<T> Drop for WeakIllegal<T> {
    fn drop(&mut self) {
        unsafe {
            let prev = (&mut *self.inner.as_ptr())
                .weak_refs
                .fetch_sub(1, Ordering::SeqCst);
            if 1 != prev {
                return;
            }

            if (&mut *self.inner.as_ptr()).refs.load(Ordering::SeqCst) != 0 {
                return;
            }

            if (&mut *self.inner.as_ptr()).weak_refs.load(Ordering::SeqCst) == 0 {
                drop_in_place(self.inner.as_ptr());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::arc;

    #[test]
    pub fn weak_works() {
        let aa = &[0u8; 4];
        let x = arc(&aa[..]);
        let y = x.weak();
        let z = y.strong().unwrap();
        assert_eq!(&[0, 0, 0, 0][..], *x);
        assert_eq!(Some(&[0, 0, 0, 0][..]), y.get().copied());
        drop(x);
        assert_eq!(Some(&[0, 0, 0, 0][..]), y.get().copied());
        drop(z);
        assert_eq!(None, y.get().copied());
        assert_eq!(None, y.strong().map(|_| true));
    }

    #[test]
    pub fn dismantle_works() {
        let input = {
            let input = arc(vec![1u8; 5]);
            let clone = input.dup();
            let _ = match clone.dismantle() {
                Err(clone) => clone,
                Ok(_) => panic!("Shouldn't be able to dismantle ArcIllegal with 2 references"),
            };

            input
        };

        assert_eq!(1, input.ref_count());
        assert_eq!(Some(vec![1u8; 5]), input.dismantle().ok());
    }

    #[test]
    pub fn dismantle_weak_works() {
        let (input, weak) = {
            let input = arc(vec![1u8; 5]);
            let clone = input.dup();
            let weak = input.weak();
            let _ = match clone.dismantle_with_weak() {
                Err(clone) => clone,
                Ok(_) => panic!("Shouldn't be able to dismantle ArcIllegal with 2 references"),
            };

            (input, weak)
        };

        assert_eq!(2, input.ref_count());
        let res = input.dismantle_with_weak().ok();
        assert_eq!(Some(vec![1u8; 5]), res);
        std::mem::drop(res.unwrap());
        unsafe {
            assert!((*weak.inner.as_ptr()).value.is_null());
        }
        assert_eq!(None, weak.get());
    }
}
