use crate::cmp;
use crate::fmt;
use crate::io::{self, BufRead, Initializer, IoSliceMut, Read, Seek, SeekFrom, DEFAULT_BUF_SIZE};

/// The `BufReader<R>` struct adds buffering to any reader.
///q
/// It can be excessively inefficient to work directly with a [`Read`] instance.
/// For example, every call to [`read`][`TcpStream::read`] on [`TcpStream`]
/// results in a system call. A `BufReader<R>` performs large, infrequent reads on
/// the underlying [`Read`] and maintains an in-memory buffer of the results.
///
/// `BufReader<R>` can improve the speed of programs that make *small* and
/// *repeated* read calls to the same file or network socket. It does not
/// help when reading very large amounts at once, or reading just one or a few
/// times. It also provides no advantage when reading from a source that is
/// already in memory, like a [`Vec`]`<u8>`.
///
/// When the `BufReader<R>` is dropped, the contents of its buffer will be
/// discarded. Creating multiple instances of a `BufReader<R>` on the same
/// stream can cause data loss. Reading from the underlying reader after
/// unwrapping the `BufReader<R>` with [`BufReader::into_inner`] can also cause
/// data loss.
///
/// [`TcpStream::read`]: Read::read
/// [`TcpStream`]: crate::net::TcpStream
///
/// # Examples
///
/// ```no_run
/// use std::io::prelude::*;
/// use std::io::BufReader;
/// use std::fs::File;
///
/// fn main() -> std::io::Result<()> {
///     let f = File::open("log.txt")?;
///     let mut reader = BufReader::new(f);
///
///     let mut line = String::new();
///     let len = reader.read_line(&mut line)?;
///     println!("First line is {} bytes long", len);
///     Ok(())
/// }
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub struct BufReader<R> {
    inner: R,
    buf: Box<[u8]>,
    pos: usize,
    cap: usize,
}

impl<R: Read> BufReader<R> {
    /// Creates a new `BufReader<R>` with a default buffer capacity. The default is currently 8 KB,
    /// but may change in the future.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let reader = BufReader::new(f);
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn new(inner: R) -> BufReader<R> {
        BufReader::with_capacity(DEFAULT_BUF_SIZE, inner)
    }

    /// Creates a new `BufReader<R>` with the specified buffer capacity.
    ///
    /// # Examples
    ///
    /// Creating a buffer with ten bytes of capacity:
    ///
    /// ```no_run
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let reader = BufReader::with_capacity(10, f);
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn with_capacity(capacity: usize, inner: R) -> BufReader<R> {
        unsafe {
            let mut buffer = Vec::with_capacity(capacity);
            buffer.set_len(capacity);
            inner.initializer().initialize(&mut buffer);
            BufReader { inner, buf: buffer.into_boxed_slice(), pos: 0, cap: 0 }
        }
    }
}

impl<R> BufReader<R> {
    /// Gets a reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let reader = BufReader::new(f1);
    ///
    ///     let f2 = reader.get_ref();
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let mut reader = BufReader::new(f1);
    ///
    ///     let f2 = reader.get_mut();
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Returns a reference to the internally buffered data.
    ///
    /// Unlike [`fill_buf`], this will not attempt to fill the buffer if it is empty.
    ///
    /// [`fill_buf`]: BufRead::fill_buf
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::{BufReader, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let mut reader = BufReader::new(f);
    ///     assert!(reader.buffer().is_empty());
    ///
    ///     if reader.fill_buf()?.len() > 0 {
    ///         assert!(!reader.buffer().is_empty());
    ///     }
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "bufreader_buffer", since = "1.37.0")]
    pub fn buffer(&self) -> &[u8] {
        &self.buf[self.pos..self.cap]
    }

    /// Returns the number of bytes the internal buffer can hold at once.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::{BufReader, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f = File::open("log.txt")?;
    ///     let mut reader = BufReader::new(f);
    ///
    ///     let capacity = reader.capacity();
    ///     let buffer = reader.fill_buf()?;
    ///     assert!(buffer.len() <= capacity);
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "buffered_io_capacity", since = "1.46.0")]
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Unwraps this `BufReader<R>`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost. Therefore,
    /// a following read from the underlying reader may lead to data loss.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let f1 = File::open("log.txt")?;
    ///     let reader = BufReader::new(f1);
    ///
    ///     let f2 = reader.into_inner();
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Invalidates all data in the internal buffer.
    #[inline]
    fn discard_buffer(&mut self) {
        self.pos = 0;
        self.cap = 0;
    }
}

impl<R: Seek> BufReader<R> {
    /// Seeks relative to the current position. If the new position lies within the buffer,
    /// the buffer will not be flushed, allowing for more efficient seeks.
    /// This method does not return the location of the underlying reader, so the caller
    /// must track this information themselves if it is required.
    #[unstable(feature = "bufreader_seek_relative", issue = "31100")]
    pub fn seek_relative(&mut self, offset: i64) -> io::Result<()> {
        let pos = self.pos as u64;
        if offset < 0 {
            if let Some(new_pos) = pos.checked_sub((-offset) as u64) {
                self.pos = new_pos as usize;
                return Ok(());
            }
        } else {
            if let Some(new_pos) = pos.checked_add(offset as u64) {
                if new_pos <= self.cap as u64 {
                    self.pos = new_pos as usize;
                    return Ok(());
                }
            }
        }
        self.seek(SeekFrom::Current(offset)).map(drop)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Read> Read for BufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == self.cap && buf.len() >= self.buf.len() {
            self.discard_buffer();
            return self.inner.read(buf);
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read(buf)?
        };
        self.consume(nread);
        Ok(nread)
    }

    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum::<usize>();
        if self.pos == self.cap && total_len >= self.buf.len() {
            self.discard_buffer();
            return self.inner.read_vectored(bufs);
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read_vectored(bufs)?
        };
        self.consume(nread);
        Ok(nread)
    }

    fn is_read_vectored(&self) -> bool {
        self.inner.is_read_vectored()
    }

    // we can't skip unconditionally because of the large buffer case in read.
    unsafe fn initializer(&self) -> Initializer {
        self.inner.initializer()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Read> BufRead for BufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.cap {
            debug_assert!(self.pos == self.cap);
            self.cap = self.inner.read(&mut self.buf)?;
            self.pos = 0;
        }
        Ok(&self.buf[self.pos..self.cap])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = cmp::min(self.pos + amt, self.cap);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<R> fmt::Debug for BufReader<R>
where
    R: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("BufReader")
            .field("reader", &self.inner)
            .field("buffer", &format_args!("{}/{}", self.cap - self.pos, self.buf.len()))
            .finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<R: Seek> Seek for BufReader<R> {
    /// Seek to an offset, in bytes, in the underlying reader.
    ///
    /// The position used for seeking with [`SeekFrom::Current`]`(_)` is the
    /// position the underlying reader would be at if the `BufReader<R>` had no
    /// internal buffer.
    ///
    /// Seeking always discards the internal buffer, even if the seek position
    /// would otherwise fall within it. This guarantees that calling
    /// [`BufReader::into_inner()`] immediately after a seek yields the underlying reader
    /// at the same position.
    ///
    /// To seek without discarding the internal buffer, use [`BufReader::seek_relative`].
    ///
    /// See [`std::io::Seek`] for more details.
    ///
    /// Note: In the edge case where you're seeking with [`SeekFrom::Current`]`(n)`
    /// where `n` minus the internal buffer length overflows an `i64`, two
    /// seeks will be performed instead of one. If the second seek returns
    /// [`Err`], the underlying reader will be left at the same position it would
    /// have if you called `seek` with [`SeekFrom::Current`]`(0)`.
    ///
    /// [`std::io::Seek`]: Seek
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let result: u64;
        if let SeekFrom::Current(n) = pos {
            let remainder = (self.cap - self.pos) as i64;
            // it should be safe to assume that remainder fits within an i64 as the alternative
            // means we managed to allocate 8 exbibytes and that's absurd.
            // But it's not out of the realm of possibility for some weird underlying reader to
            // support seeking by i64::MIN so we need to handle underflow when subtracting
            // remainder.
            if let Some(offset) = n.checked_sub(remainder) {
                result = self.inner.seek(SeekFrom::Current(offset))?;
            } else {
                // seek backwards by our remainder, and then by the offset
                self.inner.seek(SeekFrom::Current(-remainder))?;
                self.discard_buffer();
                result = self.inner.seek(SeekFrom::Current(n))?;
            }
        } else {
            // Seeking with Start/End doesn't care about our buffer length.
            result = self.inner.seek(pos)?;
        }
        self.discard_buffer();
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::BufReader;
    use crate::io::{self, BufRead, Read, Seek, SeekFrom};

    /// A dummy reader intended at testing short-reads propagation.
    pub struct ShortReader {
        lengths: Vec<usize>,
    }

    // FIXME: rustfmt and tidy disagree about the correct formatting of this
    // function. This leads to issues for users with editors configured to
    // rustfmt-on-save.
    impl Read for ShortReader {
        fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
            if self.lengths.is_empty() { Ok(0) } else { Ok(self.lengths.remove(0)) }
        }
    }

    #[test]
    fn test_buffered_reader() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(2, inner);

        let mut buf = [0, 0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 3);
        assert_eq!(buf, [5, 6, 7]);
        assert_eq!(reader.buffer(), []);

        let mut buf = [0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 2);
        assert_eq!(buf, [0, 1]);
        assert_eq!(reader.buffer(), []);

        let mut buf = [0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        assert_eq!(buf, [2]);
        assert_eq!(reader.buffer(), [3]);

        let mut buf = [0, 0, 0];
        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        assert_eq!(buf, [3, 0, 0]);
        assert_eq!(reader.buffer(), []);

        let nread = reader.read(&mut buf);
        assert_eq!(nread.unwrap(), 1);
        assert_eq!(buf, [4, 0, 0]);
        assert_eq!(reader.buffer(), []);

        assert_eq!(reader.read(&mut buf).unwrap(), 0);
    }

    #[test]
    fn test_buffered_reader_seek() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(2, io::Cursor::new(inner));

        assert_eq!(reader.seek(SeekFrom::Start(3)).ok(), Some(3));
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(3));
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert_eq!(reader.seek(SeekFrom::Current(1)).ok(), Some(4));
        assert_eq!(reader.fill_buf().ok(), Some(&[1, 2][..]));
        reader.consume(1);
        assert_eq!(reader.seek(SeekFrom::Current(-2)).ok(), Some(3));
    }

    #[test]
    fn test_buffered_reader_seek_relative() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(2, io::Cursor::new(inner));

        assert!(reader.seek_relative(3).is_ok());
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert!(reader.seek_relative(0).is_ok());
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert!(reader.seek_relative(1).is_ok());
        assert_eq!(reader.fill_buf().ok(), Some(&[1][..]));
        assert!(reader.seek_relative(-1).is_ok());
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1][..]));
        assert!(reader.seek_relative(2).is_ok());
        assert_eq!(reader.fill_buf().ok(), Some(&[2, 3][..]));
    }

    #[test]
    fn test_buffered_reader_invalidated_after_read() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(3, io::Cursor::new(inner));

        assert_eq!(reader.fill_buf().ok(), Some(&[5, 6, 7][..]));
        reader.consume(3);

        let mut buffer = [0, 0, 0, 0, 0];
        assert_eq!(reader.read(&mut buffer).ok(), Some(5));
        assert_eq!(buffer, [0, 1, 2, 3, 4]);

        assert!(reader.seek_relative(-2).is_ok());
        let mut buffer = [0, 0];
        assert_eq!(reader.read(&mut buffer).ok(), Some(2));
        assert_eq!(buffer, [3, 4]);
    }

    #[test]
    fn test_buffered_reader_invalidated_after_seek() {
        let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
        let mut reader = BufReader::with_capacity(3, io::Cursor::new(inner));

        assert_eq!(reader.fill_buf().ok(), Some(&[5, 6, 7][..]));
        reader.consume(3);

        assert!(reader.seek(SeekFrom::Current(5)).is_ok());

        assert!(reader.seek_relative(-2).is_ok());
        let mut buffer = [0, 0];
        assert_eq!(reader.read(&mut buffer).ok(), Some(2));
        assert_eq!(buffer, [3, 4]);
    }

    #[test]
    fn test_buffered_reader_seek_underflow() {
        // gimmick reader that yields its position modulo 256 for each byte
        struct PositionReader {
            pos: u64,
        }
        impl Read for PositionReader {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                let len = buf.len();
                for x in buf {
                    *x = self.pos as u8;
                    self.pos = self.pos.wrapping_add(1);
                }
                Ok(len)
            }
        }
        impl Seek for PositionReader {
            fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
                match pos {
                    SeekFrom::Start(n) => {
                        self.pos = n;
                    }
                    SeekFrom::Current(n) => {
                        self.pos = self.pos.wrapping_add(n as u64);
                    }
                    SeekFrom::End(n) => {
                        self.pos = u64::MAX.wrapping_add(n as u64);
                    }
                }
                Ok(self.pos)
            }
        }

        let mut reader = BufReader::with_capacity(5, PositionReader { pos: 0 });
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 1, 2, 3, 4][..]));
        assert_eq!(reader.seek(SeekFrom::End(-5)).ok(), Some(u64::MAX - 5));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // the following seek will require two underlying seeks
        let expected = 9223372036854775802;
        assert_eq!(reader.seek(SeekFrom::Current(i64::MIN)).ok(), Some(expected));
        assert_eq!(reader.fill_buf().ok().map(|s| s.len()), Some(5));
        // seeking to 0 should empty the buffer.
        assert_eq!(reader.seek(SeekFrom::Current(0)).ok(), Some(expected));
        assert_eq!(reader.get_ref().pos, expected);
    }

    #[test]
    fn test_buffered_reader_seek_underflow_discard_buffer_between_seeks() {
        // gimmick reader that returns Err after first seek
        struct ErrAfterFirstSeekReader {
            first_seek: bool,
        }
        impl Read for ErrAfterFirstSeekReader {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                for x in &mut *buf {
                    *x = 0;
                }
                Ok(buf.len())
            }
        }
        impl Seek for ErrAfterFirstSeekReader {
            fn seek(&mut self, _: SeekFrom) -> io::Result<u64> {
                if self.first_seek {
                    self.first_seek = false;
                    Ok(0)
                } else {
                    Err(io::Error::new(io::ErrorKind::Other, "oh no!"))
                }
            }
        }

        let mut reader = BufReader::with_capacity(5, ErrAfterFirstSeekReader { first_seek: true });
        assert_eq!(reader.fill_buf().ok(), Some(&[0, 0, 0, 0, 0][..]));

        // The following seek will require two underlying seeks.  The first will
        // succeed but the second will fail.  This should still invalidate the
        // buffer.
        assert!(reader.seek(SeekFrom::Current(i64::MIN)).is_err());
        assert_eq!(reader.buffer().len(), 0);
    }

    #[test]
    fn test_read_until() {
        let inner: &[u8] = &[0, 1, 2, 1, 0];
        let mut reader = BufReader::with_capacity(2, inner);
        let mut v = Vec::new();
        reader.read_until(0, &mut v).unwrap();
        assert_eq!(v, [0]);
        v.truncate(0);
        reader.read_until(2, &mut v).unwrap();
        assert_eq!(v, [1, 2]);
        v.truncate(0);
        reader.read_until(1, &mut v).unwrap();
        assert_eq!(v, [1]);
        v.truncate(0);
        reader.read_until(8, &mut v).unwrap();
        assert_eq!(v, [0]);
        v.truncate(0);
        reader.read_until(9, &mut v).unwrap();
        assert_eq!(v, []);
    }

    #[test]
    fn test_read_line() {
        let in_buf: &[u8] = b"a\nb\nc";
        let mut reader = BufReader::with_capacity(2, in_buf);
        let mut s = String::new();
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "a\n");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "b\n");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "c");
        s.truncate(0);
        reader.read_line(&mut s).unwrap();
        assert_eq!(s, "");
    }

    #[test]
    fn test_lines() {
        let in_buf: &[u8] = b"a\nb\nc";
        let reader = BufReader::with_capacity(2, in_buf);
        let mut it = reader.lines();
        assert_eq!(it.next().unwrap().unwrap(), "a".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "b".to_string());
        assert_eq!(it.next().unwrap().unwrap(), "c".to_string());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_short_reads() {
        let inner = ShortReader { lengths: vec![0, 1, 2, 0, 1, 0] };
        let mut reader = BufReader::new(inner);
        let mut buf = [0, 0];
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 2);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 1);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
        assert_eq!(reader.read(&mut buf).unwrap(), 0);
    }

    #[bench]
    fn bench_buffered_reader(b: &mut test::Bencher) {
        b.iter(|| BufReader::new(io::empty()));
    }
}
