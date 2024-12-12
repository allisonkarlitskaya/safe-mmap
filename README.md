# safe-mmap

## What?

A crate with safe wrappers for `mmap()` of immutable files.  This only works on
Linux, and only in a couple of cases.

## Why?

Accessing memory with `mmap()` is not a safe in Rust's memory model.  The
reason is that Rust requires any memory to be immutable for as long as a shared
reference exists to it (excluding interior mutability).

Crates like [`zerocopy`](https://crates.io/crates/zerocopy) take advantage of
this immutability guarantee to perform checked pointer transmutations where the
data is verified before the transmutation is permitted to occur.  If the data
can change after the check then the transmuted reference is no longer valid and
we're in the territory of [undefined
behaviour](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).

It's generally not possible to guarantee that the memory made visible by
`mmap()` will be immutable or even safe to access at all.  There are a number
of reasons for that:

 - other programs on the system may modify the data inside of the file after
   the mapping is made.  This applies even for "private" mappings: in general,
   if the data hasn't been faulted yet (or if it's evicted under memory
   pressure) then the kernel will load the modified data.
 - it's possible to request a mapping that's larger than the size of the file.
   When the pages beyond the length of the file are faulted, your process will
   receive `SIGBUS`.
 - it's also possible that the mapping was made with the correct size but that
   the file was truncated after the mapping, but before being faulted.

## How?

There are a couple of cases when we can be absolutely certain that a file is
truly immutable and `mmap()` is safe under Rust's memory model:
 - a sealed memfd
 - a file with fs-verity enabled

In those cases the inode is made completely and permanently immutable (in size
and content) for as long as it exists, and will continue to exist for as long
as we have it opened or mapped.

The "safe" APIs in this crate will only operate on one of these two special
cases, and they take care to inspect the size of the file before performing the
mapping to ensure that we're also safe from `SIGBUS`.

There is an `unsafe` API to create mappings from any file descriptor.  In that
case you're on your own to determine that the file is sufficiently immutable.

## Other approaches

There are a couple more approaches which could be used, but are not implemented
here:

 - on copy-on-write filesystems where the process has write access, we could
   use `O_TMPFILE` to create a new inode and `FICLONE` to create a reflink.  If
   the original file was modified, we'd keep our original copy of the pages.
   This new node could potentially still be accessed by `/proc/[pid]/fd`, but
   we could also enable fs-verity on it to prevent that.  All-in-all this is
   probably too complicated to be useful and certainly too complicated to want
   to implement.

 - the "low tech" approach: create an anonymous mapping and ask the kernel to
   `read()` into it. This would work universally but you could also just call
   [`.read_to_end()`](https://doc.rust-lang.org/std/io/trait.Read.html#method.read_to_end).
   If this is ever added to this crate, it will be in the form of a fallback if
   the other options fail.

## Licence

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
