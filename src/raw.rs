use {Str, is_utf8};

use core::mem;
use core::ptr::RawPtr;
use core::raw::Slice;

/// Converts a slice of bytes to a string slice without checking
/// that the string contains valid UTF-8.
pub unsafe fn from_utf8<'a>(v: &'a [u8]) -> &'a Str {
    mem::transmute(v)
}

/// Form a slice from a C string. Unsafe because the caller must ensure the
/// C string has the static lifetime, or else the return value may be
/// invalidated later.
pub unsafe fn c_str_to_static_slice(s: *const i8) -> &'static Str {
    let s = s as *const u8;
    let mut curr = s;
    let mut len = 0u;
    while *curr != 0u8 {
        len += 1u;
        curr = s.offset(len as int);
    }
    let v = Slice { data: s, len: len };
    assert!(is_utf8(mem::transmute(v)));
    mem::transmute(v)
}

/// Takes a bytewise (not UTF-8) slice from a string.
///
/// Returns the substring from [`begin`..`end`).
///
/// # Panics
///
/// If begin is greater than end.
/// If end is greater than the length of the string.
#[inline]
pub unsafe fn slice_bytes<'a>(s: &'a Str, begin: uint, end: uint) -> &'a Str {
    assert!(begin <= end);
    assert!(end <= s.len());
    slice_unchecked(s, begin, end)
}

/// Takes a bytewise (not UTF-8) slice from a string.
///
/// Returns the substring from [`begin`..`end`).
///
/// Caller must check slice boundaries!
#[inline]
pub unsafe fn slice_unchecked<'a>(s: &'a Str, begin: uint, end: uint) -> &'a Str {
    mem::transmute(Slice {
            data: s.as_ptr().offset(begin as int),
            len: end - begin,
        })
}
