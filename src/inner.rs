use std::usize;

pub(crate) enum PushWithResult {
    Skip,
    Push,
}

pub(crate) enum RemoveWithResult {
    Skip,
    Remove,
    Done,
}

pub(crate) enum GetWithResult {
    Skip,
    Get,
    Done,
}

#[derive(Debug)]
pub(crate) struct Backing<T> {
    data: Box<[BackingEntry<T>]>,
    len: usize,
    front: usize,
    back: usize,
}

impl<T> Backing<T> {
    pub(crate) fn new(capacity: usize) -> Self {
        let mut data = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            data.push(BackingEntry::Vacant);
        }
        Self {
            data: data.into_boxed_slice(),
            len: 0,
            front: usize::MAX,
            back: usize::MAX,
        }
    }

    fn push_back_at(&mut self, at: usize, data: T) -> Option<T> {
        let old = self.remove(at);

        self.data[at] = BackingEntry::Occupied(Occupied {
            data,
            prev: self.back,
            next: usize::MAX,
        });

        if self.back != usize::MAX {
            if let BackingEntry::Occupied(o) = &mut self.data[self.back] {
                o.next = at;
            }
        }

        self.back = at;

        if self.front == usize::MAX {
            self.front = at;
        }

        self.len = self.len.checked_add(1).unwrap();

        old.map(|o| o.data)
    }

    pub(crate) fn push_back_with<F>(
        &mut self,
        start_at: usize,
        data: T,
        with: F,
    ) -> Result<Option<T>, T>
    where
        F: Fn(&BackingEntry<T>, &T) -> PushWithResult,
    {
        use PushWithResult::{Push, Skip};

        let len = self.data.len();

        for i in 0..len {
            let ix = (start_at + i) % len;
            match with(self.get_entry(ix), &data) {
                // The predicate decided this index cannot be used to
                // store the value.
                Skip => {}
                // the predicate decided that this index can be used
                // to store the value.
                Push => {
                    return Ok(self.push_back_at(ix, data));
                }
            }
        }

        // We skipped all the the slots without pushing. Return the
        // input data back as an error.
        return Err(data);
    }

    pub(crate) fn remove(&mut self, at: usize) -> Option<Occupied<T>> {
        if self.data[at].is_occupied() {
            let mut e = BackingEntry::Removed;
            std::mem::swap(&mut e, &mut self.data[at]);
            match e {
                BackingEntry::Occupied(o) => {
                    if at == self.front {
                        self.front = o.next;
                    }
                    if at == self.back {
                        self.back = o.prev;
                    }
                    if o.prev != usize::MAX {
                        self.data[o.prev].set_next(o.next);
                    }
                    if o.next != usize::MAX {
                        self.data[o.next].set_prev(o.prev);
                    }

                    self.len = self.len.checked_sub(1).unwrap();

                    Some(o)
                }
                _ => unreachable!(),
            }
        } else {
            None
        }
    }

    pub(crate) fn remove_with<F>(&mut self, start_at: usize, with: F) -> Option<Occupied<T>>
    where
        F: Fn(&BackingEntry<T>) -> RemoveWithResult,
    {
        use RemoveWithResult::{Done, Remove, Skip};

        let len = self.data.len();
        for i in 0..len {
            let ix = (start_at + i) % len;
            match with(self.get_entry(ix)) {
                Skip => {}
                Remove => return self.remove(ix),
                Done => break,
            }
        }

        None
    }

    fn get_entry(&self, at: usize) -> &BackingEntry<T> {
        &self.data[at]
    }

    pub(crate) fn get_entry_with<F>(&self, start_at: usize, with: F) -> Option<&BackingEntry<T>>
    where
        F: Fn(&BackingEntry<T>) -> GetWithResult,
    {
        use GetWithResult::{Done, Get, Skip};

        let len = self.data.len();
        for i in 0..len {
            let ix = (start_at + i) % len;
            match with(self.get_entry(ix)) {
                Skip => {}
                Get => return Some(self.get_entry(ix)),
                Done => break,
            }
        }

        None
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn capacity(&self) -> usize {
        self.data.len()
    }

    pub(crate) fn iter(&self) -> IterBacking<'_, T> {
        IterBacking {
            focus: self.front,
            target: self,
        }
    }

    pub(crate) fn drain(&mut self) -> DrainBacking<'_, T> {
        DrainBacking {
            focus: self.front,
            target: self,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Occupied<T> {
    prev: usize,
    next: usize,
    pub(crate) data: T,
}

#[derive(Debug)]
pub(crate) enum BackingEntry<T> {
    Vacant,
    Removed,
    Occupied(Occupied<T>),
}

impl<T> BackingEntry<T> {
    fn set_prev(&mut self, new_prev: usize) {
        if let BackingEntry::Occupied(o) = self {
            o.prev = new_prev;
        } else {
            panic!("can only set prev on occupied entry");
        }
    }

    fn set_next(&mut self, new_next: usize) {
        if let BackingEntry::Occupied(o) = self {
            o.next = new_next;
        } else {
            panic!("can only set next on occupied entry");
        }
    }

    fn is_occupied(&self) -> bool {
        if let BackingEntry::Occupied { .. } = self {
            true
        } else {
            false
        }
    }

    pub(crate) fn as_occupied(&self) -> &Occupied<T> {
        if let BackingEntry::Occupied(o) = self {
            o
        } else {
            panic!("can only represent data from occupied entry");
        }
    }
}

pub(crate) struct IterBacking<'t, T> {
    focus: usize,
    target: &'t Backing<T>,
}

impl<'t, T> Iterator for IterBacking<'t, T> {
    type Item = &'t T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.focus == usize::MAX {
            None
        } else {
            if let BackingEntry::Occupied(o) = self.target.get_entry(self.focus) {
                self.focus = o.next;
                Some(&o.data)
            } else {
                panic!("self.focus should be a valid occupied index.");
            }
        }
    }
}

pub(crate) struct DrainBacking<'t, T> {
    focus: usize,
    target: &'t mut Backing<T>,
}

impl<'t, T> Iterator for DrainBacking<'t, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.focus == usize::MAX {
            None
        } else if let Some(e) = self.target.remove(self.focus) {
            self.focus = e.next;
            Some(e.data)
        } else {
            panic!("self.focus should be a valid occupied index.");
        }
    }
}
