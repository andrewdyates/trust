use std::marker::PhantomData;
use std::sync::atomic::{AtomicPtr, Ordering};

/// This is essentially an `AtomicPtr` but is guaranteed to always be valid
pub struct AtomicRef<T: 'static>(AtomicPtr<T>, PhantomData<&'static T>);

impl<T: 'static> AtomicRef<T> {
    pub const fn new(initial: &'static T) -> AtomicRef<T> {
        AtomicRef(AtomicPtr::new(initial as *const T as *mut T), PhantomData)
    }

    pub fn swap(&self, new: &'static T) -> &'static T {
        // SAFETY: We never allow storing anything but a `'static` reference so the
        // pointer is always valid to dereference for the `'static` lifetime.
        unsafe { &*self.0.swap(new as *const T as *mut T, Ordering::SeqCst) }
    }
}

impl<T: 'static> std::ops::Deref for AtomicRef<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        // SAFETY: We never allow storing anything but a `'static` reference so the
        // pointer is always valid to dereference for any lifetime.
        unsafe { &*self.0.load(Ordering::SeqCst) }
    }
}
