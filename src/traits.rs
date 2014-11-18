use core::cmp::{Eq, Equiv, Ord, Ordering, PartialEq, PartialOrd};
use core::cmp::{Less, Equal, Greater};
use core::iter::Iterator;
use core::ops;
use core::option::{Option, Some};

use {AsStr, Str, eq_slice};

impl Ord for Str {
    #[inline]
    fn cmp(&self, other: &Str) -> Ordering {
        for (s_b, o_b) in self.bytes().zip(other.bytes()) {
            match s_b.cmp(&o_b) {
                Greater => return Greater,
                Less => return Less,
                Equal => ()
            }
        }

        self.len().cmp(&other.len())
    }
}

impl PartialEq for Str {
    #[inline]
    fn eq(&self, other: &Str) -> bool {
        eq_slice(self, other)
    }
    #[inline]
    fn ne(&self, other: &Str) -> bool { !(*self).eq(other) }
}

impl Eq for Str {}

impl PartialOrd for Str {
    #[inline]
    fn partial_cmp(&self, other: &Str) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<S: AsStr> Equiv<S> for Str {
    #[inline]
    fn equiv(&self, other: &S) -> bool { eq_slice(self, other.as_str()) }
}

impl ops::Slice<uint, Str> for Str {
    #[inline]
    fn as_slice_<'a>(&'a self) -> &'a Str {
        self
    }

    #[inline]
    fn slice_from_or_fail<'a>(&'a self, from: &uint) -> &'a Str {
        self.slice_from(*from)
    }

    #[inline]
    fn slice_to_or_fail<'a>(&'a self, to: &uint) -> &'a Str {
        self.slice_to(*to)
    }

    #[inline]
    fn slice_or_fail<'a>(&'a self, from: &uint, to: &uint) -> &'a Str {
        self.slice(*from, *to)
    }
}
