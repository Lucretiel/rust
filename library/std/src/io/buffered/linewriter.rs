use crate::fmt;
use crate::io::{self, buffered::LineWriterShim, BufWriter, IntoInnerError, IoSlice, Write};

/// Wraps a writer and buffers output to it, flushing whenever a newline
/// (`0x0a`, `'\n'`) is detected.
///
/// The [`BufWriter`] struct wraps a writer and buffers its output.
/// But it only does this batched write when it goes out of scope, or when the
/// internal buffer is full. Sometimes, you'd prefer to write each line as it's
/// completed, rather than the entire buffer at once. Enter `LineWriter`. It
/// does exactly that.
///
/// Like [`BufWriter`], a `LineWriter`’s buffer will also be flushed when the
/// `LineWriter` goes out of scope or when its internal buffer is full.
///
/// If there's still a partial line in the buffer when the `LineWriter` is
/// dropped, it will flush those contents.
///
/// # Examples
///
/// We can use `LineWriter` to write one line at a time, significantly
/// reducing the number of actual writes to the file.
///
/// ```no_run
/// use std::fs::{self, File};
/// use std::io::prelude::*;
/// use std::io::LineWriter;
///
/// fn main() -> std::io::Result<()> {
///     let road_not_taken = b"I shall be telling this with a sigh
/// Somewhere ages and ages hence:
/// Two roads diverged in a wood, and I -
/// I took the one less traveled by,
/// And that has made all the difference.";
///
///     let file = File::create("poem.txt")?;
///     let mut file = LineWriter::new(file);
///
///     file.write_all(b"I shall be telling this with a sigh")?;
///
///     // No bytes are written until a newline is encountered (or
///     // the internal buffer is filled).
///     assert_eq!(fs::read_to_string("poem.txt")?, "");
///     file.write_all(b"\n")?;
///     assert_eq!(
///         fs::read_to_string("poem.txt")?,
///         "I shall be telling this with a sigh\n",
///     );
///
///     // Write the rest of the poem.
///     file.write_all(b"Somewhere ages and ages hence:
/// Two roads diverged in a wood, and I -
/// I took the one less traveled by,
/// And that has made all the difference.")?;
///
///     // The last line of the poem doesn't end in a newline, so
///     // we have to flush or drop the `LineWriter` to finish
///     // writing.
///     file.flush()?;
///
///     // Confirm the whole poem was written.
///     assert_eq!(fs::read("poem.txt")?, &road_not_taken[..]);
///     Ok(())
/// }
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub struct LineWriter<W: Write> {
    inner: BufWriter<W>,
}

impl<W: Write> LineWriter<W> {
    /// Creates a new `LineWriter`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let file = File::create("poem.txt")?;
    ///     let file = LineWriter::new(file);
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn new(inner: W) -> LineWriter<W> {
        // Lines typically aren't that long, don't use a giant buffer
        LineWriter::with_capacity(1024, inner)
    }

    /// Creates a new `LineWriter` with a specified capacity for the internal
    /// buffer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let file = File::create("poem.txt")?;
    ///     let file = LineWriter::with_capacity(100, file);
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn with_capacity(capacity: usize, inner: W) -> LineWriter<W> {
        LineWriter { inner: BufWriter::with_capacity(capacity, inner) }
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let file = File::create("poem.txt")?;
    ///     let file = LineWriter::new(file);
    ///
    ///     let reference = file.get_ref();
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_ref(&self) -> &W {
        self.inner.get_ref()
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// Caution must be taken when calling methods on the mutable reference
    /// returned as extra writes could corrupt the output stream.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let file = File::create("poem.txt")?;
    ///     let mut file = LineWriter::new(file);
    ///
    ///     // we can use reference just like file
    ///     let reference = file.get_mut();
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn get_mut(&mut self) -> &mut W {
        self.inner.get_mut()
    }

    /// Unwraps this `LineWriter`, returning the underlying writer.
    ///
    /// The internal buffer is written out before returning the writer.
    ///
    /// # Errors
    ///
    /// An [`Err`] will be returned if an error occurs while flushing the buffer.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::fs::File;
    /// use std::io::LineWriter;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let file = File::create("poem.txt")?;
    ///
    ///     let writer: LineWriter<File> = LineWriter::new(file);
    ///
    ///     let file: File = writer.into_inner()?;
    ///     Ok(())
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_inner(self) -> Result<W, IntoInnerError<LineWriter<W>>> {
        self.inner.into_inner().map_err(|err| err.map(|buf| LineWriter { inner: buf }))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<W: Write> Write for LineWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        LineWriterShim::new(&mut self.inner).write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        LineWriterShim::new(&mut self.inner).write_vectored(bufs)
    }

    fn is_write_vectored(&self) -> bool {
        self.inner.is_write_vectored()
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        LineWriterShim::new(&mut self.inner).write_all(buf)
    }

    fn write_all_vectored(&mut self, bufs: &mut [IoSlice<'_>]) -> io::Result<()> {
        LineWriterShim::new(&mut self.inner).write_all_vectored(bufs)
    }

    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> io::Result<()> {
        LineWriterShim::new(&mut self.inner).write_fmt(fmt)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<W: Write> fmt::Debug for LineWriter<W>
where
    W: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("LineWriter")
            .field("writer", &self.get_ref())
            .field(
                "buffer",
                &format_args!("{}/{}", self.inner.buffer().len(), self.inner.capacity()),
            )
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::LineWriter;
    use crate::io::{self, ErrorKind, IoSlice, Write};
    use crate::thread;

    #[test]
    fn test_line_buffer() {
        let mut writer = LineWriter::new(Vec::new());
        writer.write(&[0]).unwrap();
        assert_eq!(*writer.get_ref(), []);
        writer.write(&[1]).unwrap();
        assert_eq!(*writer.get_ref(), []);
        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1]);
        writer.write(&[0, b'\n', 1, b'\n', 2]).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n']);
        writer.flush().unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n', 2]);
        writer.write(&[3, b'\n']).unwrap();
        assert_eq!(*writer.get_ref(), [0, 1, 0, b'\n', 1, b'\n', 2, 3, b'\n']);
    }

    /// A simple `Write` target, designed to be wrapped by `LineWriter` /
    /// `BufWriter` / etc, that can have its `write` & `flush` behavior
    /// configured
    #[derive(Default, Clone)]
    struct ProgrammableSink {
        // Writes append to this slice
        pub buffer: Vec<u8>,

        // Flush sets this flag
        pub flushed: bool,

        // If true, writes will always be an error
        pub always_write_error: bool,

        // If true, flushes will always be an error
        pub always_flush_error: bool,

        // If set, only up to this number of bytes will be written in a single
        // call to `write`
        pub accept_prefix: Option<usize>,

        // If set, counts down with each write, and writes return an error
        // when it hits 0
        pub max_writes: Option<usize>,

        // If set, attempting to write when max_writes == Some(0) will be an
        // error; otherwise, it will return Ok(0).
        pub error_after_max_writes: bool,
    }

    impl Write for ProgrammableSink {
        fn write(&mut self, data: &[u8]) -> io::Result<usize> {
            if self.always_write_error {
                return Err(io::Error::new(io::ErrorKind::Other, "test - always_write_error"));
            }

            match self.max_writes {
                Some(0) if self.error_after_max_writes => {
                    return Err(io::Error::new(io::ErrorKind::Other, "test - max_writes"));
                }
                Some(0) => return Ok(0),
                Some(ref mut count) => *count -= 1,
                None => {}
            }

            let len = match self.accept_prefix {
                None => data.len(),
                Some(prefix) => data.len().min(prefix),
            };

            let data = &data[..len];
            self.buffer.extend_from_slice(data);

            Ok(len)
        }

        fn flush(&mut self) -> io::Result<()> {
            if self.always_flush_error {
                Err(io::Error::new(io::ErrorKind::Other, "test - always_flush_error"))
            } else {
                self.flushed = true;
                Ok(())
            }
        }
    }

    /// Previously the `LineWriter` could successfully write some bytes but
    /// then fail to report that it has done so. Additionally, an erroneous
    /// flush after a successful write was permanently ignored.
    ///
    /// Test that a line writer correctly reports the number of written bytes,
    /// and that it attempts to flush buffered lines from previous writes
    /// before processing new data
    ///
    /// Regression test for #37807
    #[test]
    fn erroneous_flush_retried() {
        let writer = ProgrammableSink {
            // Only write up to 4 bytes at a time
            accept_prefix: Some(4),

            // Accept the first two writes, then error the others
            max_writes: Some(2),
            error_after_max_writes: true,

            ..Default::default()
        };

        // This should write the first 4 bytes. The rest will be buffered, out
        // to the last newline.
        let mut writer = LineWriter::new(writer);
        assert_eq!(writer.write(b"a\nb\nc\nd\ne").unwrap(), 8);

        // This write should attempt to flush "c\nd\n", then buffer "e". No
        // errors should happen here because no further writes should be
        // attempted against `writer`.
        assert_eq!(writer.write(b"e").unwrap(), 1);
        assert_eq!(&writer.get_ref().buffer, b"a\nb\nc\nd\n");
    }

    #[test]
    fn line_vectored() {
        let mut a = LineWriter::new(Vec::new());
        assert_eq!(
            a.write_vectored(&[
                IoSlice::new(&[]),
                IoSlice::new(b"\n"),
                IoSlice::new(&[]),
                IoSlice::new(b"a"),
            ])
            .unwrap(),
            2,
        );
        assert_eq!(a.get_ref(), b"\n");

        assert_eq!(
            a.write_vectored(&[
                IoSlice::new(&[]),
                IoSlice::new(b"b"),
                IoSlice::new(&[]),
                IoSlice::new(b"a"),
                IoSlice::new(&[]),
                IoSlice::new(b"c"),
            ])
            .unwrap(),
            3,
        );
        assert_eq!(a.get_ref(), b"\n");
        a.flush().unwrap();
        assert_eq!(a.get_ref(), b"\nabac");
        assert_eq!(a.write_vectored(&[]).unwrap(), 0);
        assert_eq!(
            a.write_vectored(&[
                IoSlice::new(&[]),
                IoSlice::new(&[]),
                IoSlice::new(&[]),
                IoSlice::new(&[]),
            ])
            .unwrap(),
            0,
        );
        assert_eq!(a.write_vectored(&[IoSlice::new(b"a\nb"),]).unwrap(), 3);
        assert_eq!(a.get_ref(), b"\nabaca\nb");
    }

    #[test]
    fn line_vectored_partial_and_errors() {
        use crate::collections::VecDeque;

        enum Call {
            Write { inputs: Vec<&'static [u8]>, output: io::Result<usize> },
            Flush { output: io::Result<()> },
        }

        #[derive(Default)]
        struct Writer {
            calls: VecDeque<Call>,
        }

        impl Write for Writer {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
                self.write_vectored(&[IoSlice::new(buf)])
            }

            fn write_vectored(&mut self, buf: &[IoSlice<'_>]) -> io::Result<usize> {
                match self.calls.pop_front().expect("unexpected call to write") {
                    Call::Write { inputs, output } => {
                        assert_eq!(inputs, buf.iter().map(|b| &**b).collect::<Vec<_>>());
                        output
                    }
                    Call::Flush { .. } => panic!("unexpected call to write; expected a flush"),
                }
            }

            fn is_write_vectored(&self) -> bool {
                true
            }

            fn flush(&mut self) -> io::Result<()> {
                match self.calls.pop_front().expect("Unexpected call to flush") {
                    Call::Flush { output } => output,
                    Call::Write { .. } => panic!("unexpected call to flush; expected a write"),
                }
            }
        }

        impl Drop for Writer {
            fn drop(&mut self) {
                if !thread::panicking() {
                    assert_eq!(self.calls.len(), 0);
                }
            }
        }

        // partial writes keep going
        let mut a = LineWriter::new(Writer::default());
        a.write_vectored(&[IoSlice::new(&[]), IoSlice::new(b"abc")]).unwrap();

        a.get_mut().calls.push_back(Call::Write { inputs: vec![b"abc"], output: Ok(1) });
        a.get_mut().calls.push_back(Call::Write { inputs: vec![b"bc"], output: Ok(2) });
        a.get_mut().calls.push_back(Call::Write { inputs: vec![b"x", b"\n"], output: Ok(2) });

        a.write_vectored(&[IoSlice::new(b"x"), IoSlice::new(b"\n")]).unwrap();

        a.get_mut().calls.push_back(Call::Flush { output: Ok(()) });
        a.flush().unwrap();

        // erroneous writes stop and don't write more
        a.get_mut().calls.push_back(Call::Write { inputs: vec![b"x", b"\na"], output: Err(err()) });
        a.get_mut().calls.push_back(Call::Flush { output: Ok(()) });
        assert!(a.write_vectored(&[IoSlice::new(b"x"), IoSlice::new(b"\na")]).is_err());
        a.flush().unwrap();

        fn err() -> io::Error {
            io::Error::new(io::ErrorKind::Other, "x")
        }
    }

    /// Test that, in cases where vectored writing is not enabled, the
    /// LineWriter uses the normal `write` call, which more-correctly handles
    /// partial lines
    #[test]
    fn line_vectored_ignored() {
        let writer = ProgrammableSink::default();
        let mut writer = LineWriter::new(writer);

        let content = [
            IoSlice::new(&[]),
            IoSlice::new(b"Line 1\nLine"),
            IoSlice::new(b" 2\nLine 3\nL"),
            IoSlice::new(&[]),
            IoSlice::new(&[]),
            IoSlice::new(b"ine 4"),
            IoSlice::new(b"\nLine 5\n"),
        ];

        let count = writer.write_vectored(&content).unwrap();
        assert_eq!(count, 11);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n");

        let count = writer.write_vectored(&content[2..]).unwrap();
        assert_eq!(count, 11);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\nLine 3\n");

        let count = writer.write_vectored(&content[5..]).unwrap();
        assert_eq!(count, 5);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\nLine 3\n");

        let count = writer.write_vectored(&content[6..]).unwrap();
        assert_eq!(count, 8);
        assert_eq!(
            writer.get_ref().buffer.as_slice(),
            b"Line 1\nLine 2\nLine 3\nLine 4\nLine 5\n".as_ref()
        );
    }

    /// Test that, given this input:
    ///
    /// Line 1\n
    /// Line 2\n
    /// Line 3\n
    /// Line 4
    ///
    /// And given a result that only writes to midway through Line 2
    ///
    /// That only up to the end of Line 3 is buffered
    ///
    /// This behavior is desirable because it prevents flushing partial lines
    #[test]
    fn partial_write_buffers_line() {
        let writer = ProgrammableSink { accept_prefix: Some(13), ..Default::default() };
        let mut writer = LineWriter::new(writer);

        assert_eq!(writer.write(b"Line 1\nLine 2\nLine 3\nLine4").unwrap(), 21);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2");

        assert_eq!(writer.write(b"Line 4").unwrap(), 6);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\nLine 3\n");
    }

    /// Test that, given this input:
    ///
    /// Line 1\n
    /// Line 2\n
    /// Line 3
    ///
    /// And given that the full write of lines 1 and 2 was successful
    /// That data up to Line 3 is buffered
    #[test]
    fn partial_line_buffered_after_line_write() {
        let writer = ProgrammableSink::default();
        let mut writer = LineWriter::new(writer);

        assert_eq!(writer.write(b"Line 1\nLine 2\nLine 3").unwrap(), 20);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\n");

        assert!(writer.flush().is_ok());
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\nLine 3");
    }

    /// Test that, given a partial line that exceeds the length of
    /// LineBuffer's buffer (that is, without a trailing newline), that that
    /// line is written to the inner writer
    #[test]
    fn long_line_flushed() {
        let writer = ProgrammableSink::default();
        let mut writer = LineWriter::with_capacity(5, writer);

        assert_eq!(writer.write(b"0123456789").unwrap(), 10);
        assert_eq!(&writer.get_ref().buffer, b"0123456789");
    }

    /// Test that, given a very long partial line *after* successfully
    /// flushing a complete line, that that line is buffered unconditionally,
    /// and no additional writes take place. This assures the property that
    /// `write` should make at-most-one attempt to write new data.
    #[test]
    fn line_long_tail_not_flushed() {
        let writer = ProgrammableSink::default();
        let mut writer = LineWriter::with_capacity(5, writer);

        // Assert that Line 1\n is flushed, and 01234 is buffered
        assert_eq!(writer.write(b"Line 1\n0123456789").unwrap(), 12);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n");

        // Because the buffer is full, this subsequent write will flush it
        assert_eq!(writer.write(b"5").unwrap(), 1);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n01234");
    }

    /// Test that, if an attempt to pre-flush buffered data returns Ok(0),
    /// this is propagated as an error.
    #[test]
    fn line_buffer_write0_error() {
        let writer = ProgrammableSink {
            // Accept one write, then return Ok(0) on subsequent ones
            max_writes: Some(1),

            ..Default::default()
        };
        let mut writer = LineWriter::new(writer);

        // This should write "Line 1\n" and buffer "Partial"
        assert_eq!(writer.write(b"Line 1\nPartial").unwrap(), 14);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n");

        // This will attempt to flush "partial", which will return Ok(0), which
        // needs to be an error, because we've already informed the client
        // that we accepted the write.
        let err = writer.write(b" Line End\n").unwrap_err();
        assert_eq!(err.kind(), ErrorKind::WriteZero);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n");
    }

    /// Test that, if a write returns Ok(0) after a successful pre-flush, this
    /// is propagated as Ok(0)
    #[test]
    fn line_buffer_write0_normal() {
        let writer = ProgrammableSink {
            // Accept two writes, then return Ok(0) on subsequent ones
            max_writes: Some(2),

            ..Default::default()
        };
        let mut writer = LineWriter::new(writer);

        // This should write "Line 1\n" and buffer "Partial"
        assert_eq!(writer.write(b"Line 1\nPartial").unwrap(), 14);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\n");

        // This will flush partial, which will succeed, but then return Ok(0)
        // when flushing " Line End\n"
        assert_eq!(writer.write(b" Line End\n").unwrap(), 0);
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nPartial");
    }

    /// LineWriter has a custom `write_all`; make sure it works correctly
    #[test]
    fn line_write_all() {
        let writer = ProgrammableSink {
            // Only write 5 bytes at a time
            accept_prefix: Some(5),
            ..Default::default()
        };
        let mut writer = LineWriter::new(writer);

        writer.write_all(b"Line 1\nLine 2\nLine 3\nLine 4\nPartial").unwrap();
        assert_eq!(&writer.get_ref().buffer, b"Line 1\nLine 2\nLine 3\nLine 4\n");
        writer.write_all(b" Line 5\n").unwrap();
        assert_eq!(
            writer.get_ref().buffer.as_slice(),
            b"Line 1\nLine 2\nLine 3\nLine 4\nPartial Line 5\n".as_ref(),
        );
    }

    #[test]
    fn line_write_all_error() {
        let writer = ProgrammableSink {
            // Only accept up to 3 writes of up to 5 bytes each
            accept_prefix: Some(5),
            max_writes: Some(3),
            ..Default::default()
        };

        let mut writer = LineWriter::new(writer);
        let res = writer.write_all(b"Line 1\nLine 2\nLine 3\nLine 4\nPartial");
        assert!(res.is_err());
        // An error from write_all leaves everything in an indeterminate state,
        // so there's nothing else to test here
    }

    /// Under certain circumstances, the old implementation of LineWriter
    /// would try to buffer "to the last newline" but be forced to buffer
    /// less than that, leading to inappropriate partial line writes.
    /// Regression test for that issue.
    #[test]
    fn partial_multiline_buffering() {
        let writer = ProgrammableSink {
            // Write only up to 5 bytes at a time
            accept_prefix: Some(5),
            ..Default::default()
        };

        let mut writer = LineWriter::with_capacity(10, writer);

        let content = b"AAAAABBBBB\nCCCCDDDDDD\nEEE";

        // When content is written, LineWriter will try to write blocks A, B,
        // C, and D. Only block A will succeed. Under the old behavior, LineWriter
        // would then try to buffer B, C and D, but because its capacity is 10,
        // it will only be able to buffer B and C. We don't want to buffer
        // partial lines concurrent with whole lines, so the correct behavior
        // is to buffer only block B (out to the newline)
        assert_eq!(writer.write(content).unwrap(), 11);
        assert_eq!(writer.get_ref().buffer, *b"AAAAA");

        writer.flush().unwrap();
        assert_eq!(writer.get_ref().buffer, *b"AAAAABBBBB\n");
    }

    /// Same as test_partial_multiline_buffering, but in the event NO full lines
    /// fit in the buffer, just buffer as much as possible
    #[test]
    fn partial_multiline_buffering_without_full_line() {
        let writer = ProgrammableSink {
            // Write only up to 5 bytes at a time
            accept_prefix: Some(5),
            ..Default::default()
        };

        let mut writer = LineWriter::with_capacity(5, writer);

        let content = b"AAAAABBBBBBBBBB\nCCCCC\nDDDDD";

        // When content is written, LineWriter will try to write blocks A, B,
        // and C. Only block A will succeed. Under the old behavior, LineWriter
        // would then try to buffer B and C, but because its capacity is 5,
        // it will only be able to buffer part of B. Because it's not possible
        // for it to buffer any complete lines, it should buffer as much of B as
        // possible
        assert_eq!(writer.write(content).unwrap(), 10);
        assert_eq!(writer.get_ref().buffer, *b"AAAAA");

        writer.flush().unwrap();
        assert_eq!(writer.get_ref().buffer, *b"AAAAABBBBB");
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum RecordedEvent {
        Write(String),
        Flush,
    }

    #[derive(Debug, Clone, Default)]
    struct WriteRecorder {
        pub events: Vec<RecordedEvent>,
    }

    impl Write for WriteRecorder {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            use crate::str::from_utf8;

            self.events.push(RecordedEvent::Write(from_utf8(buf).unwrap().to_string()));
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            self.events.push(RecordedEvent::Flush);
            Ok(())
        }
    }

    /// Test that a normal, formatted writeln only results in a single write
    /// call to the underlying writer. A naive implementation of
    /// LineWriter::write_all results in two writes: one of the buffered data,
    /// and another of the final substring in the formatted set
    #[test]
    fn single_formatted_write() {
        let writer = WriteRecorder::default();
        let mut writer = LineWriter::new(writer);

        // Under a naive implementation of LineWriter, this will result in two
        // writes: "hello, world" and "!\n", because write() has to flush the
        // buffer before attempting to write the last "!\n". write_all shouldn't
        // have this limitation.
        writeln!(&mut writer, "{}, {}!", "hello", "world").unwrap();
        assert_eq!(writer.get_ref().events, [RecordedEvent::Write("hello, world!\n".to_string())]);
    }
}
