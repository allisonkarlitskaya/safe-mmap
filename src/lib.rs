use thiserror::Error;

use rustix::{
    fd::AsFd,
    fs::{fcntl_get_seals, fstat, FileType, SealFlags},
    io::Errno,
    ioctl::{self, Getter},
    mm::{mmap, munmap, MapFlags, ProtFlags},
};

#[derive(Debug, PartialEq, Error)]
pub enum ImmutableFdError {
    #[error("Error querying immutability: {0:?}")]
    OSError(#[from] Errno),
    #[error("Could not prove immutability of file")]
    ImmutabilityUnproven,
}

/// A mapped memory region
///
/// Just about the only interesting thing to do with this is to call .as_bytes() on it.
///
/// A Drop trait is implemented which calls `munmap()` when the Mapping goes out of scope.
#[derive(PartialEq, Debug)]
pub struct Mapping {
    ptr: *mut core::ffi::c_void,
    len: usize,
}

impl Mapping {
    fn empty() -> Self {
        Self {
            ptr: core::ptr::null_mut(),
            len: 0,
        }
    }

    /// Gets a reference to the underlying memory as a `&[u8]`.
    ///
    /// For as long as this shared reference exists, Rust's borrowing rules require that the memory
    /// must not change.  For that reason, it's only possible to construct a Mapping from an
    /// immutable file.
    pub fn as_bytes(&self) -> &[u8] {
        if self.len == 0 {
            &[] // core::slice::from_raw_parts rejects (null, 0)
        } else {
            unsafe { core::slice::from_raw_parts(self.ptr as *const u8, self.len) }
        }
    }
}

impl Drop for Mapping {
    fn drop(&mut self) {
        unsafe {
            if !self.ptr.is_null() {
                munmap(self.ptr, self.len).expect("munmap failed");
            }
        }
    }
}

/// A file descriptor for an immutable file
///
/// A file is "immutable" if it cannot possibly change size or content, ever.
/// This means that it's impossible for the length or content of the file to be changed from either
/// inside or outside of the program.  This goes beyond the usual "file is read-only" or even
/// `chattr +i` measures because they are reversible.
///
/// The only thing that can be done with an immutable file is unlinking it, but it will continue to
/// exist (and continue to be immutable) for as long as any open file descriptors refer to it.
///
/// There are a number of ways to obtain an immutable file descriptor:
///   - from an fd for a fs-verity enabled file (these files can never be modified once their
///     fs-verity status is enabled)
///   - from an fd for a sealed memfd (which can also never be modified)
///   - from any fd, unsafely
#[derive(Debug)]
pub struct ImmutableFd<F: AsFd> {
    fd: F,
}

impl<F: AsFd> ImmutableFd<F> {
    /// Produces an ImmutableFd from any file descriptor, unsafely.
    ///
    /// # Safety
    ///
    /// This function is only safe if the caller takes the responsibility for verifying that the
    /// underlying file descriptor points to an immutable file.  This means that it's impossible for
    /// the length or content of the file to be changed from either inside or outside of the program.
    pub unsafe fn from_fd(fd: F) -> Self {
        Self { fd }
    }

    /// Produces an ImmutableFd from an fd pointing to an fs-verity-enabled file
    ///
    /// This function confirms that the file is fs-verity enabled before returning.  If this could
    /// not be determined, then an error is returned.
    pub fn from_fs_verity_file(fd: F) -> Result<Self, ImmutableFdError> {
        const FS_VERITY_FL: core::ffi::c_long = 0x00100000; // <linux/fs.h>
        type FsIocGetFlags = ioctl::ReadOpcode<b'f', 1, core::ffi::c_long>;

        let flags =
            unsafe { ioctl::ioctl(&fd, Getter::<FsIocGetFlags, core::ffi::c_long>::new()) }?;

        if (flags & FS_VERITY_FL) != 0 {
            Ok(unsafe { Self::from_fd(fd) })
        } else {
            Err(ImmutableFdError::ImmutabilityUnproven)
        }
    }

    /// Produces an ImmutableFd from a memfd which is sealed for "grow", "shrink", and "write".
    ///
    /// This function confirms that the memfd is sealed.  If this could not be determined, then
    /// an error is returned.
    pub fn from_sealed_memfd(fd: F) -> Result<Self, ImmutableFdError> {
        let seals = fcntl_get_seals(&fd)?;

        if seals.contains(SealFlags::GROW | SealFlags::SHRINK | SealFlags::WRITE) {
            Ok(unsafe { Self::from_fd(fd) })
        } else {
            Err(ImmutableFdError::ImmutabilityUnproven)
        }
    }

    /// Produces a read-only memory mapping of the given length from the given offset into the
    /// given immutable file descriptor.
    ///
    /// The offset must be a multiple of the page size.  The length does not need to be a multiple
    /// of the page size.  When performing the mapping, the length is rounded-up by the kernel to
    /// the next page-size boundary, but the returned Mapping will have the exact length as given.
    ///
    /// This function corresponds exactly to a single `mmap()` syscall.  There is no extra
    /// validation performed on the arguments.  The returned Mapping object has a Drop impl which
    /// will call `munmap()`.
    ///
    /// # Safety
    ///
    /// This function is only safe if the specified byte range is not actually available in the
    /// underlying file, you may receive a SIGBUS signal when attempting to access the memory.  It
    /// is the responsibility of the caller to ensure that the passed range is valid.  Calling this
    /// function on a range that doesn't exist inside of the file produces undefined behaviour.
    pub unsafe fn mmap_with_length_and_offset(
        &self,
        len: usize,
        offset: u64,
    ) -> rustix::io::Result<Mapping> {
        Ok(Mapping {
            ptr: mmap(
                core::ptr::null_mut(),
                len,
                ProtFlags::READ,
                MapFlags::SHARED,
                &self.fd,
                offset,
            )?,
            len,
        })
    }

    /// Produces a read-only memory mapping from the given offset into the given immutable file
    /// descriptor.
    ///
    /// This function uses fstat() to query the size of the file descriptor before mapping it.  The
    /// produced mapping is for the range from the given offset to the end of the file.
    ///
    /// As a convenience, if the size of the file is exactly equal to offset parameter then this will
    /// produce a fake empty mapping.  This is done to improve the ergonomics of the API when dealing
    /// with empty files: it's not valid to call mmap() for a zero-byte range.
    pub fn mmap_with_offset(&self, offset: u64) -> rustix::io::Result<Mapping> {
        let buf = fstat(&self.fd)?;

        if buf.st_size >= 0 && buf.st_size as u64 == offset {
            /* Let's fake it by returning a (null, 0) mapping.
             *
             * For consistency with the syscall, we should check the following error cases:
             *   - fd is not a regular file (EACCES)
             *   - offset is not page aligned (EINVAL)
             * but we actually only enforce the first one (since determining the page size is
             * somewhat complicated).
             */
            if FileType::from_raw_mode(buf.st_mode) != FileType::RegularFile {
                Err(Errno::ACCESS)
            } else {
                Ok(Mapping::empty())
            }
        } else {
            /* We don't try to deal with generating errors for "weird" cases here: instead we willingly
             * call mmap() with non-sense arguments and let it signal the error.
             *   - st_size is meaningless for non-regular files, but mmap() will fail with EACCES anyway
             *   - if the offset is past the end of the file, use a 0 size and mmap() will fail with EINVAL
             */
            let len = if buf.st_size >= 0 && (buf.st_size as u64) > offset {
                (buf.st_size as u64) - offset
            } else {
                0
            } as usize;

            // SAFETY: We've satisfied the safety constraint by ensuring that (offset + len)
            // doesn't extend past the end of the file.
            unsafe { self.mmap_with_length_and_offset(len, offset) }
        }
    }

    /// Produces a read-only memory mapping from the given immutable file descriptor.
    ///
    /// This function uses fstat() to query the size of the file descriptor before mapping it.  The
    /// produced mapping covers the complete file.
    ///
    /// As a convenience, this will produce a fake empty mapping for empty files. This is done to
    /// improve the ergonomics of the API when dealing with empty files: it's not valid to call mmap()
    /// for a zero-byte range.
    pub fn mmap(&self) -> rustix::io::Result<Mapping> {
        self.mmap_with_offset(0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::{fs::create_dir_all, path::PathBuf};

    use rustix::{
        fd::OwnedFd,
        fs::{fcntl_add_seals, memfd_create, MemfdFlags},
    };
    use similar_asserts::assert_eq;

    fn make_test_memfd(data: &[u8], seals: SealFlags) -> OwnedFd {
        let fd = memfd_create("testfile", MemfdFlags::ALLOW_SEALING).expect("memfd_create");
        rustix::io::write(&fd, data).expect("write testfile data");
        if !seals.is_empty() {
            fcntl_add_seals(&fd, seals).expect("F_ADD_SEALS");
        }
        fd
    }

    #[test]
    fn test_unsealed_memfd() {
        let unsealed = make_test_memfd(b"hello", SealFlags::empty());
        assert!(matches!(
            ImmutableFd::from_sealed_memfd(&unsealed),
            Err(ImmutableFdError::ImmutabilityUnproven)
        ));
        assert!(matches!(
            ImmutableFd::from_fs_verity_file(&unsealed),
            Err(ImmutableFdError::ImmutabilityUnproven)
        ));
    }

    #[test]
    fn test_sealed_memfd() {
        let seals = SealFlags::GROW | SealFlags::SHRINK | SealFlags::WRITE;
        let sealed = make_test_memfd(b"hello", seals);

        let _ = ImmutableFd::from_sealed_memfd(&sealed).expect("from sealed memfd");
        assert!(matches!(
            ImmutableFd::from_fs_verity_file(&sealed),
            Err(ImmutableFdError::ImmutabilityUnproven)
        ));
    }

    fn mkmemfd(data: &[u8]) -> ImmutableFd<OwnedFd> {
        let seals = SealFlags::GROW | SealFlags::SHRINK | SealFlags::WRITE;
        ImmutableFd::from_sealed_memfd(make_test_memfd(data, seals)).expect("checking sealed")
    }

    #[test]
    fn test_mmap_with_length_and_offset() {
        let empty = mkmemfd(b"");

        // mapping zero bytes is invalid
        assert_eq!(
            unsafe { empty.mmap_with_length_and_offset(0, 0) },
            Err(Errno::INVAL)
        );

        let hello = mkmemfd(b"Hello, world!\n");
        // mapping past the end of the file is OK, up to the next page boundary, and produces nuls
        let mapping = unsafe { hello.mmap_with_length_and_offset(20, 0) }.unwrap();
        assert_eq!(mapping.as_bytes(), b"Hello, world!\n\0\0\0\0\0\0");
    }

    #[test]
    fn test_mmap_with_offset() {
        let page_size = rustix::param::page_size();

        // "empty"
        let empty = mkmemfd(b"");
        // valid: returns the content of the file
        let mapping = empty.mmap_with_offset(0).unwrap();
        assert_eq!(mapping.as_bytes(), b"");
        // double invalid: non-page aligned offset, and past end of file
        assert_eq!(empty.mmap_with_offset(1), Err(Errno::INVAL));
        // aligned, but past end of file
        assert_eq!(empty.mmap_with_offset(page_size as u64), Err(Errno::INVAL));

        // "hello"
        let hello = mkmemfd(b"Hello, world!\n");
        // valid: returns the content of the file
        let mapping = hello.mmap_with_offset(0).unwrap();
        assert_eq!(mapping.as_bytes(), b"Hello, world!\n");
        // invalid: non-page aligned
        assert_eq!(hello.mmap_with_offset(5), Err(Errno::INVAL));
        // aligned, but past end of file
        assert_eq!(hello.mmap_with_offset(page_size as u64), Err(Errno::INVAL));

        // "one page"
        let one_page = mkmemfd(&vec![0; page_size]);
        // valid: returns the content of the file
        let mapping = one_page.mmap_with_offset(0).unwrap();
        assert_eq!(mapping.as_bytes(), vec![0; page_size]);
        // invalid: non-page aligned
        assert_eq!(
            one_page.mmap_with_offset(page_size as u64 / 2),
            Err(Errno::INVAL)
        );
        // valid: offset is page-aligned and at the end of the file: returns an empty mapping
        let mapping = one_page.mmap_with_offset(page_size as u64).unwrap();
        assert_eq!(mapping.as_bytes(), b"");
        // double invalid: offset is not page-aligned and past the end of the file
        assert_eq!(
            one_page.mmap_with_offset(page_size as u64 * 3 / 2),
            Err(Errno::INVAL)
        );
        // invalid: offset is page-aligned but past the end of the file
        assert_eq!(
            one_page.mmap_with_offset(page_size as u64 * 2),
            Err(Errno::INVAL)
        );

        // "page and a half"
        let page_and_a_half = mkmemfd(&vec![0; page_size * 3 / 2]);
        // valid: returns the content of the file
        let mapping = page_and_a_half.mmap_with_offset(0).unwrap();
        assert_eq!(mapping.as_bytes(), vec![0; page_size * 3 / 2]);
        // valid: offset is page-aligned, returns the rest of the file
        let mapping = page_and_a_half.mmap_with_offset(page_size as u64).unwrap();
        assert_eq!(mapping.as_bytes(), vec![0; page_size / 2]);
        // invalid: non-page aligned
        assert_eq!(
            page_and_a_half.mmap_with_offset(page_size as u64 / 2),
            Err(Errno::INVAL)
        );
        // invalid: non-page-aligned, even though it's at the end of the file
        // BUT: we don't try to detect that case, and therefore it will pass
        let mapping = page_and_a_half
            .mmap_with_offset(page_size as u64 * 3 / 2)
            .unwrap();
        assert_eq!(mapping.as_bytes(), b"");

        // invalid: page-aligned but past the end of the file
        assert_eq!(
            page_and_a_half.mmap_with_offset(page_size as u64 * 2),
            Err(Errno::INVAL)
        );
        // double invalid: non-page-aligned, past the end of the file
        assert_eq!(
            page_and_a_half.mmap_with_offset(page_size as u64 * 5 / 2),
            Err(Errno::INVAL)
        );
    }

    #[test]
    fn test_mmap() {
        // This is the simple API, and the one that everyone should use.  It pretty much doesn't
        // fail.
        let page_size = rustix::param::page_size();

        // "empty"
        assert_eq!(mkmemfd(b"").mmap().unwrap().as_bytes(), b"");

        // "hello"
        assert_eq!(
            mkmemfd(b"Hello, world!").mmap().unwrap().as_bytes(),
            b"Hello, world!"
        );

        // lots of different sizes
        for i in 0..(page_size * 3) {
            assert_eq!(mkmemfd(&vec![0; i]).mmap().unwrap().as_bytes(), vec![0; i]);
        }
    }

    // See /usr/include/linux/fsverity.h
    #[repr(C)]
    pub struct FsVerityEnableArg {
        version: u32,
        hash_algorithm: u32,
        block_size: u32,
        salt_size: u32,
        salt_ptr: u64,
        sig_size: u32,
        __reserved1: u32,
        sig_ptr: u64,
        __reserved2: [u64; 11],
    }

    // #define FS_IOC_ENABLE_VERITY    _IOW('f', 133, struct fsverity_enable_arg)
    type FsIocEnableVerity = ioctl::WriteOpcode<b'f', 133, FsVerityEnableArg>;

    pub fn fs_ioc_enable_verity(fd: impl AsFd) {
        unsafe {
            ioctl::ioctl(
                fd,
                ioctl::Setter::<FsIocEnableVerity, FsVerityEnableArg>::new(FsVerityEnableArg {
                    version: 1,
                    hash_algorithm: 1, // sha256
                    block_size: 4096,
                    salt_size: 0,
                    salt_ptr: 0,
                    sig_size: 0,
                    __reserved1: 0,
                    sig_ptr: 0,
                    __reserved2: [0; 11],
                }),
            )
            .expect("FS_IOC_ENABLE_VERITY");
        }
    }

    fn get_tmpdir() -> PathBuf {
        // We can't use /tmp because that's usually a tmpfs (no fsverity)
        // We also can't use /var/tmp because it's an overlayfs in toolbox (no fsverity)
        // So let's try something in the user's homedir?
        let home = std::env::var("HOME").expect("$HOME unset");
        let tmp = PathBuf::from(home).join(".var/tmp");
        create_dir_all(&tmp).expect("create ~/.var/tmp");
        tmp
    }

    #[test]
    fn test_verity() {
        let dir = tempfile::TempDir::new_in(get_tmpdir()).expect("mkdtemp");

        let tempfile = dir.path().join("xyz");
        std::fs::write(&tempfile, "xyz").expect("write tmpfile");

        let file = std::fs::File::open(tempfile).expect("open tmpfile");
        assert!(matches!(
            ImmutableFd::from_sealed_memfd(&file),
            Err(ImmutableFdError::OSError(Errno::INVAL))
        ));
        assert!(matches!(
            ImmutableFd::from_fs_verity_file(&file),
            Err(ImmutableFdError::ImmutabilityUnproven)
        ));

        fs_ioc_enable_verity(&file);
        assert!(matches!(
            ImmutableFd::from_sealed_memfd(&file),
            Err(ImmutableFdError::OSError(Errno::INVAL))
        ));
        let fd = ImmutableFd::from_fs_verity_file(&file).expect("from verity");
        assert_eq!(fd.mmap().expect("mmap verity file").as_bytes(), b"xyz");
    }
}
