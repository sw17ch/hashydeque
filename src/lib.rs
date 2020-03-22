use std::collections::hash_map::RandomState;
use std::convert::TryInto;
use std::fmt;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::usize;

mod inner;

/// A hash map that preserves insertion order so that it can be used
/// like a deque.
pub struct HashyDeque<K, V, S = RandomState>
where
    K: Hash + PartialEq,
{
    // Backing memory of the HashyDeque.
    backing: inner::Backing<(K, V)>,
    // The hash builder out of which we build hashers.
    hash_builder: S,
}

impl<K, V, S> fmt::Debug for HashyDeque<K, V, S>
where
    K: fmt::Debug + Hash + PartialEq,
    V: fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V> Default for HashyDeque<K, V, RandomState>
where
    K: Hash + PartialEq,
{
    fn default() -> Self {
        HashyDeque {
            backing: inner::Backing::new(0),
            hash_builder: RandomState::new(),
        }
    }
}

impl<K, V> HashyDeque<K, V, RandomState>
where
    K: Hash + PartialEq,
{
    /// Create a new `HashyDeque`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Create a new `HashyDeque` with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        HashyDeque {
            backing: inner::Backing::new(capacity),
            hash_builder: RandomState::new(),
        }
    }
}

impl<K, V, S> HashyDeque<K, V, S>
where
    K: Hash + PartialEq,
    S: BuildHasher,
{
    /// Create a new `HashyDeque` with the specified initial capacity
    /// and hash builder.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        HashyDeque {
            backing: inner::Backing::new(capacity),
            hash_builder,
        }
    }

    /// Insert a `(key,value)` pair into the `HashyDeque`. Any
    /// existing element with the same key is removed and returned.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        use inner::BackingEntry::{Occupied, Removed, Vacant};

        // First, remove any existing entry that matches the key.
        let removed = self.remove(&key);

        // Run the logic to check if we need to resize to accomodate new entries.
        self.resize_for(self.backing.len() + 1);

        // Compute an ideal index for insertion, and insert the (key,value) pair.
        let ix = ideal_index_for_key(&self.hash_builder, &self.backing, &key).unwrap();
        let push_removed = self
            .backing
            .push_back_with(ix, (key, value), |check, data| {
                let (key, _) = data;
                match check {
                    Vacant => inner::PushWithResult::Push,
                    Removed => inner::PushWithResult::Push,
                    Occupied(o) => {
                        debug_assert!(o.data.0 != *key, "this should be impossible");
                        inner::PushWithResult::Skip
                    }
                }
            });

        // When doing a push_back_with, we should not be replacing any
        // entries as they should have been removed by the remove step
        // at the top of this method. We also should not fail to push
        // because we resize the backing before pushing.
        match push_removed {
            Ok(None) => {}
            Ok(Some(_)) => unreachable!(),
            Err(_) => unreachable!(),
        }

        // Return any item we may have removed at the top of this
        // method.
        removed
    }

    /// Get a value corresponding to `key`. If the `key` is not
    /// present, `None` is returned.
    pub fn get(&self, key: &K) -> Option<&V> {
        use inner::BackingEntry::{Occupied, Removed, Vacant};

        // Compute an ideal index for getting.
        let ix = ideal_index_for_key(&self.hash_builder, &self.backing, &key).unwrap();
        let entry = self.backing.get_entry_with(ix, |check| match check {
            Vacant => inner::GetWithResult::Done,
            Removed => inner::GetWithResult::Skip,
            Occupied(o) => {
                if o.data.0 == *key {
                    inner::GetWithResult::Get
                } else {
                    inner::GetWithResult::Skip
                }
            }
        });

        entry.map(|e| &e.as_occupied().data.1)
    }

    /// Remove a value corresponding to `kdy`. If the `key` is not
    /// present, `None` is returned.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        use inner::BackingEntry::{Occupied, Removed, Vacant};

        // Compute an ideal index for removal, and then remove any
        // existing entry that matches the key.
        if let Some(ix) = ideal_index_for_key(&self.hash_builder, &self.backing, &key) {
            self.backing
                .remove_with(ix, |check| match check {
                    Vacant => inner::RemoveWithResult::Done,
                    Removed => inner::RemoveWithResult::Skip,
                    Occupied(o) => {
                        if o.data.0 == *key {
                            inner::RemoveWithResult::Remove
                        } else {
                            inner::RemoveWithResult::Skip
                        }
                    }
                })
                .map(|o| o.data.1)
        } else {
            None
        }
    }

    /// Create an iterator that will visit all elements in the
    /// `HashyDeque` in the order in which they were inserted.
    pub fn iter(&self) -> InsertionOrderIter<'_, K, V> {
        InsertionOrderIter {
            inner: self.backing.iter(),
        }
    }

    fn resize_for(&mut self, size: usize) {
        let current_cap = self.backing.capacity();
        if current_cap < size {
            // Determine the new size.
            let new_cap = if current_cap == 0 { 1 } else { current_cap * 2 };

            // Allocate and initialize the new backing, and swap it
            // for our existing backing.
            let mut backing = inner::Backing::new(new_cap);
            std::mem::swap(&mut self.backing, &mut backing);

            // Drain the existing backing into the new backing.
            for (k, v) in backing.drain() {
                let replaced = self.insert(k, v);
                debug_assert!(replaced.is_none());
            }
        }

        assert!(self.backing.capacity() >= size);
    }
}

/// An iterator over the `HashyDeque` that visits elements in the
/// order they were inserted.
pub struct InsertionOrderIter<'t, K, V>
where
    K: Hash + PartialEq,
{
    inner: inner::IterBacking<'t, (K, V)>,
}

impl<'t, K, V> Iterator for InsertionOrderIter<'t, K, V>
where
    K: Hash + PartialEq,
{
    type Item = &'t (K, V);

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        self.inner.next()
    }
}

fn ideal_index_for_key<S, K, V>(
    hash_builder: &S,
    backing: &inner::Backing<(K, V)>,
    key: &K,
) -> Option<usize>
where
    S: BuildHasher,
    K: PartialEq + Hash,
{
    let len: u64 = backing.capacity().try_into().unwrap();
    if len == 0 {
        None
    } else {
        let hash = hash_key(hash_builder, key);
        Some((hash % len).try_into().unwrap())
    }
}

fn hash_key<S, K>(hash_builder: &S, key: &K) -> u64
where
    S: BuildHasher,
    K: Hash,
{
    let mut hasher = hash_builder.build_hasher();
    key.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn insert_get_works() {
        let mut m: HashyDeque<u8, char> = HashyDeque::new();

        assert_eq!(None, m.insert(0, 'a'));
        assert_eq!(None, m.insert(1, 'b'));
        assert_eq!(None, m.insert(2, 'c'));

        assert_eq!(Some(&'a'), m.get(&0));
        assert_eq!(Some(&'b'), m.get(&1));
        assert_eq!(Some(&'c'), m.get(&2));

        assert_eq!(Some('a'), m.remove(&0));
        assert_eq!(Some('b'), m.remove(&1));
        assert_eq!(Some('c'), m.remove(&2));

        assert_eq!(None, m.remove(&0));
        assert_eq!(None, m.remove(&1));
        assert_eq!(None, m.remove(&2));

        assert_eq!(None, m.insert(3, 'd'));
        assert_eq!(None, m.insert(4, 'e'));
        assert_eq!(None, m.insert(5, 'f'));

        assert_eq!(Some('d'), m.remove(&3));
        assert_eq!(Some('e'), m.remove(&4));
        assert_eq!(Some('f'), m.remove(&5));
    }

    #[test]
    fn insert_remove_get_insert() {
        let mut m: HashyDeque<u8, char> = HashyDeque::new();

        assert_eq!(None, m.insert(0, 'a'));
        assert_eq!(None, m.insert(1, 'b'));
        assert_eq!(None, m.insert(2, 'c'));
        assert_eq!(None, m.insert(3, 'd'));
        assert_eq!(None, m.insert(4, 'e'));
        assert_eq!(Some('a'), m.insert(0, 'f'));
        assert_eq!(Some('f'), m.remove(&0));
        assert_eq!(None, m.insert(0, 'g'));
    }

    #[test]
    fn iter_gives_insertion_order() {
        let mut m: HashyDeque<u8, char> = HashyDeque::new();

        assert_eq!(None, m.insert(0, 'a'));
        assert_eq!(None, m.insert(1, 'b'));
        assert_eq!(None, m.insert(2, 'c'));
        assert_eq!(None, m.insert(3, 'd'));
        assert_eq!(None, m.insert(4, 'e'));

        assert_eq!(
            vec![&(0, 'a'), &(1, 'b'), &(2, 'c'), &(3, 'd'), &(4, 'e')],
            m.iter().collect::<Vec<&(u8, char)>>()
        );

        assert_eq!(Some('c'), m.remove(&2));

        assert_eq!(
            vec![&(0, 'a'), &(1, 'b'), &(3, 'd'), &(4, 'e')],
            m.iter().collect::<Vec<&(u8, char)>>()
        );

        assert_eq!(None, m.insert(2, 'c'));

        assert_eq!(
            vec![&(0, 'a'), &(1, 'b'), &(3, 'd'), &(4, 'e'), &(2, 'c')],
            m.iter().collect::<Vec<&(u8, char)>>()
        );
    }
}
