Hashable wrappers for reference countings.

Provides hashable wrappers for `Rc<T>` and `Weak<T>` references
with the types `HashableRc<T>` and `HashableWeak<T>`,
respectively. This allows use of both strong and weak reference
countings in hash-based data structures, such as `HashMap` or
`HashSet`.

# Quick Start

The most common use cases are wrapping `Rc<T>` or `Weak<T>` in
`HashableRc<T>` or `HashableWeak<T>` respectively to be 
contained in a hash-based container. An example of using both types
as keys in a `HashMap` follows.

```rust
use std::collections::HashMap;
use std::rc::{Rc, Weak};

use hashable_rc::{HashableRc, HashableWeak};

// Create a strong reference counting for an object.
let rc: Rc<u32> = Rc::new(42);

// Use the strong reference as a key for a HashMap.
let mut strong_map = HashMap::new();
strong_map.insert(HashableRc::new(rc.clone()), "foo");
assert_eq!(strong_map[&HashableRc::new(rc.clone())], "foo");

// Create a weak reference counting for the same object as above.
let weak: Weak<u32> = Rc::downgrade(&rc);

// Use the weak reference as a key for a HashMap.
let mut weak_map = HashMap::new();
weak_map.insert(HashableWeak::new(weak.clone()), "bar");
assert_eq!(weak_map[&HashableWeak::new(weak.clone())], "bar");
```

Insertion into other hash-based containers (such as a `HashSet`)
follows similarly.