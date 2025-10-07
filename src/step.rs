/// Result of a computation step, either yielding a value to continue or completing with a final value.
///
/// `Step` is the return type for continuation computations, similar to how `Option` represents
/// optional values and `Result` represents fallible operations.
///
/// # Examples
///
/// ```rust
/// use cont::Step;
///
/// let continuing: Step<i32, String> = Step::Yield(42);
/// let completed: Step<i32, String> = Step::Done("finished".to_string());
///
/// // Using combinators
/// let doubled = continuing.map_yield(|x| x * 2);
/// assert_eq!(doubled, Step::Yield(84));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Step<Y, D> {
    /// Continue computation with an intermediate yield value
    Yield(Y),
    /// Complete computation with a final done value
    Done(D),
}

impl<Y, D> Step<Y, D> {
    /// Returns `true` if the step is `Yield`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert!(x.is_yield());
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert!(!y.is_yield());
    /// ```
    #[inline]
    pub const fn is_yield(&self) -> bool {
        matches!(self, Step::Yield(_))
    }

    /// Returns `true` if the step is `Done`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert!(x.is_done());
    ///
    /// let y: Step<i32, &str> = Step::Yield(42);
    /// assert!(!y.is_done());
    /// ```
    #[inline]
    pub const fn is_done(&self) -> bool {
        matches!(self, Step::Done(_))
    }

    /// Converts from `Step<Y, D>` to `Option<Y>`.
    ///
    /// Converts `self` into an `Option<Y>`, consuming `self`,
    /// and discarding the done value, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.yield_value(), Some(42));
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(y.yield_value(), None);
    /// ```
    #[inline]
    pub fn yield_value(self) -> Option<Y> {
        match self {
            Step::Yield(y) => Some(y),
            Step::Done(_) => None,
        }
    }

    /// Converts from `Step<Y, D>` to `Option<D>`.
    ///
    /// Converts `self` into an `Option<D>`, consuming `self`,
    /// and discarding the yield value, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(x.done_value(), Some("complete"));
    ///
    /// let y: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(y.done_value(), None);
    /// ```
    #[inline]
    pub fn done_value(self) -> Option<D> {
        match self {
            Step::Yield(_) => None,
            Step::Done(d) => Some(d),
        }
    }

    /// Maps a `Step<Y, D>` to `Step<Y, D2>` by applying a function to the done value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, i32> = Step::Done(5);
    /// assert_eq!(x.map_done(|v| v * 2), Step::Done(10));
    ///
    /// let y: Step<i32, i32> = Step::Yield(3);
    /// assert_eq!(y.map_done(|v| v * 2), Step::Yield(3));
    /// ```
    #[inline]
    pub fn map_done<D2, F>(self, f: F) -> Step<Y, D2>
    where
        F: FnOnce(D) -> D2,
    {
        match self {
            Step::Yield(y) => Step::Yield(y),
            Step::Done(d) => Step::Done(f(d)),
        }
    }

    /// Maps a `Step<Y, D>` to `Step<Y2, D>` by applying a function to the yield value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.map_yield(|v| v * 2), Step::Yield(84));
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(y.map_yield(|v: i32| v * 2), Step::Done("complete"));
    /// ```
    #[inline]
    pub fn map_yield<Y2, F>(self, f: F) -> Step<Y2, D>
    where
        F: FnOnce(Y) -> Y2,
    {
        match self {
            Step::Yield(y) => Step::Yield(f(y)),
            Step::Done(d) => Step::Done(d),
        }
    }

    /// Maps a `Step<Y, D>` to `Step<Y2, D2>` by applying functions to both values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, i32> = Step::Yield(42);
    /// assert_eq!(x.map(|y| y * 2, |d| d + 1), Step::Yield(84));
    ///
    /// let y: Step<i32, i32> = Step::Done(10);
    /// assert_eq!(y.map(|y| y * 2, |d| d + 1), Step::Done(11));
    /// ```
    #[inline]
    pub fn map<Y2, D2, FY, FD>(self, fy: FY, fd: FD) -> Step<Y2, D2>
    where
        FY: FnOnce(Y) -> Y2,
        FD: FnOnce(D) -> D2,
    {
        match self {
            Step::Yield(y) => Step::Yield(fy(y)),
            Step::Done(d) => Step::Done(fd(d)),
        }
    }

    /// Returns the yield value or a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.yield_or(0), 42);
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(y.yield_or(0), 0);
    /// ```
    #[inline]
    pub fn yield_or(self, default: Y) -> Y {
        match self {
            Step::Yield(y) => y,
            Step::Done(_) => default,
        }
    }

    /// Returns the yield value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.yield_or_else(|| 0), 42);
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(y.yield_or_else(|| 0), 0);
    /// ```
    #[inline]
    pub fn yield_or_else<F>(self, f: F) -> Y
    where
        F: FnOnce() -> Y,
    {
        match self {
            Step::Yield(y) => y,
            Step::Done(_) => f(),
        }
    }

    /// Returns the done value or a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(x.done_or("default"), "complete");
    ///
    /// let y: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(y.done_or("default"), "default");
    /// ```
    #[inline]
    pub fn done_or(self, default: D) -> D {
        match self {
            Step::Yield(_) => default,
            Step::Done(d) => d,
        }
    }

    /// Returns the done value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(x.done_or_else(|| "default"), "complete");
    ///
    /// let y: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(y.done_or_else(|| "default"), "default");
    /// ```
    #[inline]
    pub fn done_or_else<F>(self, f: F) -> D
    where
        F: FnOnce() -> D,
    {
        match self {
            Step::Yield(_) => f(),
            Step::Done(d) => d,
        }
    }

    /// Converts from `&Step<Y, D>` to `Step<&Y, &D>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, String> = Step::Yield(42);
    /// assert_eq!(x.as_ref(), Step::Yield(&42));
    ///
    /// let y: Step<i32, String> = Step::Done("complete".to_string());
    /// assert_eq!(y.as_ref(), Step::Done(&"complete".to_string()));
    /// ```
    #[inline]
    pub const fn as_ref(&self) -> Step<&Y, &D> {
        match self {
            Step::Yield(y) => Step::Yield(y),
            Step::Done(d) => Step::Done(d),
        }
    }

    /// Converts from `&mut Step<Y, D>` to `Step<&mut Y, &mut D>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let mut x: Step<i32, String> = Step::Yield(42);
    /// if let Step::Yield(y) = x.as_mut() {
    ///     *y = 100;
    /// }
    /// assert_eq!(x, Step::Yield(100));
    /// ```
    #[inline]
    pub fn as_mut(&mut self) -> Step<&mut Y, &mut D> {
        match self {
            Step::Yield(y) => Step::Yield(y),
            Step::Done(d) => Step::Done(d),
        }
    }

    /// Converts from `Step<Y, D>` to `Step<D, Y>` by swapping variants.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.flip(), Step::Done(42));
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(y.flip(), Step::Yield("complete"));
    /// ```
    #[inline]
    pub fn flip(self) -> Step<D, Y> {
        match self {
            Step::Yield(y) => Step::Done(y),
            Step::Done(d) => Step::Yield(d),
        }
    }

    /// Returns `true` if the step is a `Yield` value containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert!(x.contains_yield(&42));
    /// assert!(!x.contains_yield(&100));
    ///
    /// let y: Step<i32, &str> = Step::Done("complete");
    /// assert!(!y.contains_yield(&42));
    /// ```
    #[inline]
    pub fn contains_yield<U>(&self, y: &U) -> bool
    where
        U: PartialEq<Y>,
    {
        matches!(self, Step::Yield(v) if y == v)
    }

    /// Returns `true` if the step is a `Done` value containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert!(x.contains_done(&"complete"));
    /// assert!(!x.contains_done(&"other"));
    ///
    /// let y: Step<i32, &str> = Step::Yield(42);
    /// assert!(!y.contains_done(&"complete"));
    /// ```
    #[inline]
    pub fn contains_done<U>(&self, d: &U) -> bool
    where
        U: PartialEq<D>,
    {
        matches!(self, Step::Done(v) if d == v)
    }

    /// Returns the contained `Yield` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Done` with a custom panic message provided by `msg`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.expect_yield("was done"), 42);
    /// ```
    ///
    /// ```should_panic
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// x.expect_yield("the world is ending"); // panics with "the world is ending"
    /// ```
    #[inline]
    pub fn expect_yield(self, msg: &str) -> Y {
        match self {
            Step::Yield(y) => y,
            Step::Done(_) => panic!("{}", msg),
        }
    }

    /// Returns the contained `Done` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Yield` with a custom panic message provided by `msg`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(x.expect_done("was yielding"), "complete");
    /// ```
    ///
    /// ```should_panic
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// x.expect_done("the world is ending"); // panics with "the world is ending"
    /// ```
    #[inline]
    pub fn expect_done(self, msg: &str) -> D {
        match self {
            Step::Yield(_) => panic!("{}", msg),
            Step::Done(d) => d,
        }
    }

    /// Returns the contained `Yield` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Done`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// assert_eq!(x.unwrap_yield(), 42);
    /// ```
    ///
    /// ```should_panic
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// x.unwrap_yield(); // panics
    /// ```
    #[inline]
    pub fn unwrap_yield(self) -> Y {
        match self {
            Step::Yield(y) => y,
            Step::Done(_) => panic!("called `Step::unwrap_yield()` on a `Done` value"),
        }
    }

    /// Returns the contained `Done` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Yield`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Done("complete");
    /// assert_eq!(x.unwrap_done(), "complete");
    /// ```
    ///
    /// ```should_panic
    /// use cont::Step;
    ///
    /// let x: Step<i32, &str> = Step::Yield(42);
    /// x.unwrap_done(); // panics
    /// ```
    #[inline]
    pub fn unwrap_done(self) -> D {
        match self {
            Step::Yield(_) => panic!("called `Step::unwrap_done()` on a `Yield` value"),
            Step::Done(d) => d,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_yield_and_is_done() {
        let y: Step<i32, &str> = Step::Yield(42);
        let d: Step<i32, &str> = Step::Done("complete");

        assert!(y.is_yield());
        assert!(!y.is_done());
        assert!(d.is_done());
        assert!(!d.is_yield());
    }

    #[test]
    fn test_yield_value_and_done_value() {
        let y: Step<i32, &str> = Step::Yield(42);
        let d: Step<i32, &str> = Step::Done("complete");

        assert_eq!(y.yield_value(), Some(42));
        assert_eq!(y.done_value(), None);
        assert_eq!(d.yield_value(), None);
        assert_eq!(d.done_value(), Some("complete"));
    }

    #[test]
    fn test_map_done() {
        let y: Step<i32, i32> = Step::Yield(42);
        let d: Step<i32, i32> = Step::Done(10);

        assert_eq!(y.map_done(|x| x * 2), Step::Yield(42));
        assert_eq!(d.map_done(|x| x * 2), Step::Done(20));
    }

    #[test]
    fn test_map_yield() {
        let y: Step<i32, &str> = Step::Yield(42);
        let d: Step<i32, &str> = Step::Done("complete");

        assert_eq!(y.map_yield(|x| x * 2), Step::Yield(84));
        assert_eq!(d.map_yield(|x: i32| x * 2), Step::Done("complete"));
    }

    #[test]
    fn test_map() {
        let y: Step<i32, i32> = Step::Yield(42);
        let d: Step<i32, i32> = Step::Done(10);

        assert_eq!(y.map(|x| x * 2, |x| x + 1), Step::Yield(84));
        assert_eq!(d.map(|x| x * 2, |x| x + 1), Step::Done(11));
    }

    #[test]
    fn test_yield_or_and_done_or() {
        let y: Step<i32, i32> = Step::Yield(42);
        let d: Step<i32, i32> = Step::Done(10);

        assert_eq!(y.clone().yield_or(0), 42);
        assert_eq!(d.clone().yield_or(0), 0);
        assert_eq!(y.clone().done_or(0), 0);
        assert_eq!(d.clone().done_or(0), 10);
    }

    #[test]
    fn test_yield_or_else_and_done_or_else() {
        let y: Step<i32, i32> = Step::Yield(42);
        let d: Step<i32, i32> = Step::Done(10);

        assert_eq!(y.clone().yield_or_else(|| 0), 42);
        assert_eq!(d.clone().yield_or_else(|| 0), 0);
        assert_eq!(y.clone().done_or_else(|| 0), 0);
        assert_eq!(d.clone().done_or_else(|| 0), 10);
    }

    #[test]
    fn test_as_ref() {
        let y: Step<i32, String> = Step::Yield(42);
        let d: Step<i32, String> = Step::Done("complete".to_string());

        assert_eq!(y.as_ref(), Step::Yield(&42));
        assert_eq!(d.as_ref(), Step::Done(&"complete".to_string()));
    }

    #[test]
    fn test_as_mut() {
        let mut y: Step<i32, String> = Step::Yield(42);
        if let Step::Yield(v) = y.as_mut() {
            *v = 100;
        }
        assert_eq!(y, Step::Yield(100));

        let mut d: Step<i32, String> = Step::Done("complete".to_string());
        if let Step::Done(v) = d.as_mut() {
            *v = "modified".to_string();
        }
        assert_eq!(d, Step::Done("modified".to_string()));
    }

    #[test]
    fn test_flip() {
        let y: Step<i32, &str> = Step::Yield(42);
        let d: Step<i32, &str> = Step::Done("complete");

        assert_eq!(y.flip(), Step::Done(42));
        assert_eq!(d.flip(), Step::Yield("complete"));
    }

    #[test]
    fn test_contains() {
        let y: Step<i32, &str> = Step::Yield(42);
        let d: Step<i32, &str> = Step::Done("complete");

        assert!(y.contains_yield(&42));
        assert!(!y.contains_yield(&100));
        assert!(!y.contains_done(&"complete"));

        assert!(d.contains_done(&"complete"));
        assert!(!d.contains_done(&"other"));
        assert!(!d.contains_yield(&42));
    }

    #[test]
    fn test_expect_yield() {
        let y: Step<i32, &str> = Step::Yield(42);
        assert_eq!(y.expect_yield("should be yield"), 42);
    }

    #[test]
    #[should_panic(expected = "should be yield")]
    fn test_expect_yield_panics() {
        let d: Step<i32, &str> = Step::Done("complete");
        d.expect_yield("should be yield");
    }

    #[test]
    fn test_expect_done() {
        let d: Step<i32, &str> = Step::Done("complete");
        assert_eq!(d.expect_done("should be done"), "complete");
    }

    #[test]
    #[should_panic(expected = "should be done")]
    fn test_expect_done_panics() {
        let y: Step<i32, &str> = Step::Yield(42);
        y.expect_done("should be done");
    }

    #[test]
    fn test_unwrap_yield() {
        let y: Step<i32, &str> = Step::Yield(42);
        assert_eq!(y.unwrap_yield(), 42);
    }

    #[test]
    #[should_panic(expected = "called `Step::unwrap_yield()` on a `Done` value")]
    fn test_unwrap_yield_panics() {
        let d: Step<i32, &str> = Step::Done("complete");
        d.unwrap_yield();
    }

    #[test]
    fn test_unwrap_done() {
        let d: Step<i32, &str> = Step::Done("complete");
        assert_eq!(d.unwrap_done(), "complete");
    }

    #[test]
    #[should_panic(expected = "called `Step::unwrap_done()` on a `Yield` value")]
    fn test_unwrap_done_panics() {
        let y: Step<i32, &str> = Step::Yield(42);
        y.unwrap_done();
    }
}
