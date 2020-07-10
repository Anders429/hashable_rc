#![deny(missing_docs)]

//! Hashable wrappers for reference countings.
//!
//! Provides hashable wrappers for [`Rc<T>`] and [`Weak<T>`] references
//! with the types [`HashableRc<T>`] and [`HashableWeak<T>`],
//! respectively. This allows use of both strong and weak reference
//! countings in hash-based data structures, such as [`HashMap`] or
//! [`HashSet`].
//!
//! # Quick Start
//!
//! The most common use cases are wrapping [`Rc<T>`] or [`Weak<T>`] in
//! [`HashableRc<T>`] or [`HashableWeak<T>`] respectively to be 
//! contained in a hash-based container. An example of using both types
//! as keys in a [`HashMap`] follows.
//!
//! ```
//! use std::collections::HashMap;
//! use std::rc::{Rc, Weak};
//!
//! use hashable_rc::{HashableRc, HashableWeak};
//!
//! // Create a strong reference counting for an object.
//! let rc: Rc<u32> = Rc::new(42);
//!
//! // Use the strong reference as a key for a HashMap.
//! let mut strong_map = HashMap::new();
//! strong_map.insert(HashableRc::new(rc.clone()), "foo");
//! assert_eq!(strong_map[&HashableRc::new(rc.clone())], "foo");
//!
//! // Create a weak reference counting for the same object as above.
//! let weak: Weak<u32> = Rc::downgrade(&rc);
//!
//! // Use the weak reference as a key for a HashMap.
//! let mut weak_map = HashMap::new();
//! weak_map.insert(HashableWeak::new(weak.clone()), "bar");
//! assert_eq!(weak_map[&HashableWeak::new(weak.clone())], "bar");
//! ```
//!
//! Insertion into other hash-based containers (such as a [`HashSet`])
//! follows similarly.
//!
//! [`HashableRc<T>`]: struct.HashableRc.html
//! [`HashableWeak<T>`]: struct.HashableWeak.html
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
//! [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
//! [`Rc<T>`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
//! [`Weak<T>`]: https://doc.rust-lang.org/std/rc/struct.Weak.html

use std::hash::{Hash, Hasher};
use std::rc::{Rc, Weak};

fn hash_rc<T, H: Hasher>(rc: Rc<T>, state: &mut H) {
    let raw_ptr = Rc::into_raw(rc);
    raw_ptr.hash(state);
    // Convert back to Rc to prevent memory leak.
    let _ = unsafe {Rc::from_raw(raw_ptr)};
}

/// A hashable wrapper around the [`Rc<T>`] type.
///
/// A hash of a [`HashableRc<T>`] is taken from the underlying pointer.
/// Therefore, two separate objects that may be considered equal will, 
/// when contained in a [`HashableRc<T>`], almost always have different
/// hashed values. For example, the following holds:
///
/// ```
/// use std::collections::hash_map::DefaultHasher;
/// use std::hash::{Hash, Hasher};
/// use std::rc::Rc;
///
/// use hashable_rc::HashableRc;
///
/// fn hash<H: Hash>(value: &H) -> u64 {
///     let mut state = DefaultHasher::new();
///     value.hash(&mut state);
///     state.finish()
/// }
///
/// // While the underlying values are considered equal, the hash values
/// // will be different, due to being separate allocated objects with 
/// // different underlying pointers.
/// let rc1 = Rc::new(42);
/// let rc2 = Rc::new(42);
/// 
/// // The hashes of the two reference countings are different.
/// assert_ne!(hash(&HashableRc::new(rc1.clone())), 
///            hash(&HashableRc::new(rc2.clone())));
///
/// // Contrastingly, the hashes of clone reference countings pointing to 
/// // the same object are the equal.
/// assert_eq!(hash(&HashableRc::new(rc1.clone())), 
///            hash(&HashableRc::new(rc1.clone())));
/// ```
///
/// Similarly, equality of [`HashableRc<T>`] objects is done by
/// evaluating pointer equality (using 
/// [`ptr_eq()`](https://doc.rust-lang.org/std/rc/struct.Rc.html#method.ptr_eq)).
/// The equality is not from the value itself, but from the pointer.
///
/// ```
/// use std::rc::Rc;
///
/// use hashable_rc::HashableRc;
///
/// // Again, the values contained are equal, but the underlying pointers
/// // are different.
/// let rc1 = Rc::new(42);
/// let rc2 = Rc::new(42);
///
/// // Therefore, two HashableRc wrappers containing these reference 
/// // counters are not equal.
/// assert_ne!(HashableRc::new(rc1.clone()),
///            HashableRc::new(rc2.clone()));
///
/// // But HashableRc holding the same underlying object are equal.
/// assert_eq!(HashableRc::new(rc1.clone()),
///            HashableRc::new(rc1.clone()));
/// ```
#[derive(Debug, Eq)]
pub struct HashableRc<T> {
    value: Rc<T>,
}

impl <T> HashableRc<T> {
    /// Constructs a new [`HashableRc<T>`] wrapping an [`Rc<T>`].
    pub fn new(value: Rc<T>) -> Self {
        HashableRc {value}
    }
}

impl <T> Hash for HashableRc<T> {
    /// Generate a hash value for the [`HashableRc<T>`].
    ///
    /// This hash value is based on the underlying pointer. Two unique 
    /// objects will most likely have different hashes, even if their 
    /// values are the same.
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        hash_rc(self.value.clone(), state);
    }
}

impl <T> PartialEq for HashableRc<T> {
    /// Equality for two [`HashableRc<T>`] objects.
    ///
    /// Equality is determined by pointer equality, rather than value 
    /// equality. Objects are only considered equal if they point to 
    /// the same object.
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.value, &other.value)
    }
}

/// A hashable wrapper around the [`Weak<T>`] type.
///
/// A hash of a [`HashableWeak<T>`] is taken from the underlying pointer.
/// Therefore, two separate objects that may be considered equal will, 
/// when contained in a [`HashableWeak<T>`], almost always have different
/// hashed values. For example, the following holds:
///
/// ```
/// use std::collections::hash_map::DefaultHasher;
/// use std::hash::{Hash, Hasher};
/// use std::rc::Rc;
///
/// use hashable_rc::HashableWeak;
///
/// fn hash<H: Hash>(value: &H) -> u64 {
///     let mut state = DefaultHasher::new();
///     value.hash(&mut state);
///     state.finish()
/// }
///
/// // While the underlying values are considered equal, the hash values
/// // will be different, due to being separate allocated objects with 
/// // different underlying pointers.
/// let rc1 = Rc::new(42);
/// let rc2 = Rc::new(42);
/// 
/// // The hashes of the two reference countings are different.
/// assert_ne!(hash(&HashableWeak::new(Rc::downgrade(&rc1))), 
///            hash(&HashableWeak::new(Rc::downgrade(&rc2))));
///
/// // Contrastingly, the hashes of clone reference countings pointing to 
/// // the same object are the equal.
/// assert_eq!(hash(&HashableWeak::new(Rc::downgrade(&rc1))), 
///            hash(&HashableWeak::new(Rc::downgrade(&rc1))));
/// ```
///
/// Similarly, equality of [`HashableWeak<T>`] objects is done by
/// evaluating pointer equality (using 
/// [`ptr_eq()`](https://doc.rust-lang.org/std/rc/struct.Weak.html#method.ptr_eq)).
/// The equality is not from the value itself, but from the pointer.
///
/// ```
/// use std::rc::Rc;
///
/// use hashable_rc::HashableWeak;
///
/// // Again, the values contained are equal, but the underlying pointers
/// // are different.
/// let rc1 = Rc::new(42);
/// let rc2 = Rc::new(42);
///
/// // Therefore, two HashableWeak wrappers containing these reference
/// // counters are not equal.
/// assert_ne!(HashableWeak::new(Rc::downgrade(&rc1)),
///            HashableWeak::new(Rc::downgrade(&rc2)));
///
/// // But HashableWeak holding the same underlying object are equal.
/// assert_eq!(HashableWeak::new(Rc::downgrade(&rc1)),
///            HashableWeak::new(Rc::downgrade(&rc1)));
/// ```
///
/// Since [`Weak<T>`] is a weak reference, the underlying value is not
/// guaranteed to exist. A [`Weak<T>`] that is empty can still be wrapped
/// in a [`HashableWeak<T>`].
///
/// ```
/// use std::collections::hash_map::DefaultHasher;
/// use std::hash::{Hash, Hasher};
/// use std::rc::{Rc, Weak};
///
/// use hashable_rc::HashableWeak;
///
/// fn hash<H: Hash>(value: &H) -> u64 {
///     let mut state = DefaultHasher::new();
///     value.hash(&mut state);
///     state.finish()
/// }
/// 
/// let weak: Weak<i32> = Weak::new();
/// let rc = Rc::new(0);
///
/// // Hashing still works for a HashableWeak pointing to no value. It will
/// // hash differently than HashableWeak objects containing values, and
/// // will hash the same as other empty HashableWeak objects.
/// assert_ne!(hash(&HashableWeak::new(weak.clone())), 
///            hash(&HashableWeak::new(Rc::downgrade(&rc))));
/// assert_eq!(hash(&HashableWeak::new(weak.clone())), 
///            hash(&HashableWeak::new(weak.clone())));
///
/// // Empty HashableWeak objects are also not equal to assigned 
/// // HashableWeak objects, while being equal to other empty HashableWeak
/// // objects.
/// assert_ne!(HashableWeak::new(weak.clone()), 
///            HashableWeak::new(Rc::downgrade(&rc)));
/// assert_eq!(HashableWeak::new(weak.clone()), 
///            HashableWeak::new(weak.clone()));
/// ```
#[derive(Debug)]
pub struct HashableWeak<T> {
    value: Weak<T>,
}

impl <T> HashableWeak<T> {
    /// Constructs a new [`HashableWeak<T>`] wrapping a [`Weak<T>`].
    pub fn new(value: Weak<T>) -> Self {
        HashableWeak {value}
    }
}

impl <T> Hash for HashableWeak<T> {
    /// Generate a hash value for the [`HashableWeak<T>`].
    ///
    /// This hash value is based on the underlying pointer. Two unique 
    /// objects will most likely have different hashes, even if their 
    /// values are the same.
    ///
    /// If no value is pointed to, the Hasher state remains unaltered.
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        let upgraded_weak: Option<Rc<T>> = self.value.clone().upgrade();
        match upgraded_weak {
            None => {}
            Some(rc) => {
                hash_rc(rc, state);
            }
        }
    }
}

impl <T> PartialEq for HashableWeak<T> {
    /// Equality for two [`HashableWeak<T>`] objects.
    ///
    /// Equality is determined by pointer equality, rather than value 
    /// equality. Objects are only considered equal if they point to 
    /// the same object (or if both point to no object).
    fn eq(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.value, &other.value)
    }
}

impl <T> Eq for HashableWeak<T> {}

#[cfg(test)]
mod tests {
    use crate::{HashableRc, HashableWeak};
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use std::rc::{Rc, Weak};
    
    fn hash<H: Hash>(value: &H) -> u64 {
        let mut state = DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }
    
    #[test]
    fn test_hashable_rc_hash() {
        let rc1 = Rc::new(42);
        let rc2 = Rc::new(42);
        
        assert_ne!(hash(&HashableRc::new(rc1.clone())), hash(&HashableRc::new(rc2.clone())));
        assert_eq!(hash(&HashableRc::new(rc1.clone())), hash(&HashableRc::new(rc1.clone())));
    }
    
    #[test]
    fn test_hashable_rc_eq() {
        let rc1 = Rc::new(42);
        let rc2 = Rc::new(42);
        
        assert_ne!(HashableRc::new(rc1.clone()), HashableRc::new(rc2.clone()));
        assert_eq!(HashableRc::new(rc1.clone()), HashableRc::new(rc1.clone()));
    }
    
    #[test]
    fn test_hashable_rc_hash_does_not_memory_leak() {
        let rc = Rc::new(42);
        
        hash(&HashableRc::new(rc.clone()));
        
        assert_eq!(Rc::strong_count(&rc), 1);
        assert_eq!(Rc::weak_count(&rc), 0);
    }
    
    #[test]
    fn test_hashable_weak_hash() {
        let rc1 = Rc::new(42);
        let rc2 = Rc::new(42);
        
        assert_ne!(hash(&HashableWeak::new(Rc::downgrade(&rc1))), hash(&HashableWeak::new(Rc::downgrade(&rc2))));
        assert_eq!(hash(&HashableWeak::new(Rc::downgrade(&rc1))), hash(&HashableWeak::new(Rc::downgrade(&rc1))));
    }
    
    #[test]
    fn test_hashable_weak_eq() {
        let rc1 = Rc::new(42);
        let rc2 = Rc::new(42);
        
        assert_ne!(HashableWeak::new(Rc::downgrade(&rc1)), HashableWeak::new(Rc::downgrade(&rc2)));
        assert_eq!(HashableWeak::new(Rc::downgrade(&rc1)), HashableWeak::new(Rc::downgrade(&rc1)));
    }
    
    #[test]
    fn test_hashable_weak_hash_does_not_memory_leak() {
        let rc = Rc::new(42);
        let weak = Rc::downgrade(&rc);
        
        hash(&HashableWeak::new(weak.clone()));
        
        assert_eq!(Rc::strong_count(&rc), 1);
        assert_eq!(Rc::weak_count(&rc), 1);
    }
    
    #[test]
    fn test_hashable_weak_hash_no_value() {
        // Weak is an empty weak reference.
        let weak: Weak<i32> = Weak::new();
        let rc = Rc::new(0);
        
        assert_ne!(hash(&HashableWeak::new(weak.clone())), hash(&HashableWeak::new(Rc::downgrade(&rc))));
        assert_eq!(hash(&HashableWeak::new(weak.clone())), hash(&HashableWeak::new(weak.clone())));
    }
    
    #[test]
    fn test_hashable_weak_eq_no_value() {
        // Weak is an empty weak reference.
        let weak: Weak<i32> = Weak::new();
        let rc = Rc::new(0);
        
        assert_ne!(HashableWeak::new(weak.clone()), HashableWeak::new(Rc::downgrade(&rc)));
        assert_eq!(HashableWeak::new(weak.clone()), HashableWeak::new(weak.clone()));
    }
}
