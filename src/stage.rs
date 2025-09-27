use either::Either;

pub trait First<A> {
    type Next: Stage<A>;
    fn first(self) -> (<Self::Next as Stage<A>>::Yield, Self::Next);
}

pub trait Stage<A> {
    type Yield;
    type Resume;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume>;
}

impl<A, Y, R, F> Stage<A> for F
where
    F: FnMut(A) -> Either<Y, R>,
{
    type Yield = Y;
    type Resume = R;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        self(input)
    }
}

impl<A, L, R> Stage<A> for Either<L, R>
where
    L: Stage<A>,
    R: Stage<A, Yield = L::Yield, Resume = L::Resume>,
{
    type Yield = L::Yield;
    type Resume = L::Resume;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        match self {
            Either::Left(l) => l.step(input),
            Either::Right(r) => r.step(input),
        }
    }
}

impl<A, L, R> First<A> for Either<L, R>
where
    L: First<A>,
    R: First<A>,
    R::Next: Stage<A, Resume = <L::Next as Stage<A>>::Resume, Yield = <L::Next as Stage<A>>::Yield>,
{
    type Next = Either<L::Next, R::Next>;
    fn first(self) -> (<Self::Next as Stage<A>>::Yield, Self::Next) {
        match self {
            Either::Left(l) => {
                let (y, next_l) = l.first();
                (y, Either::Left(next_l))
            }
            Either::Right(r) => {
                let (y, next_r) = r.first();
                (y, Either::Right(next_r))
            }
        }
    }
}

pub struct Repeat<F>(F);

impl<A, Y, F> Stage<A> for Repeat<F>
where
    F: FnMut(A) -> Y,
{
    type Yield = Y;
    type Resume = A;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        Either::Left(self.0(input))
    }
}

impl<A, Y, F> First<A> for Repeat<(Y, F)>
where
    F: FnMut(A) -> Y,
{
    type Next = Repeat<F>;

    fn first(self) -> (<Self::Next as Stage<A>>::Yield, Self::Next) {
        let Repeat((y, f)) = self;
        (y, Repeat(f))
    }
}

pub struct Once<F>(Option<F>);

pub fn once<F>(f: F) -> Once<F> {
    Once(Some(f))
}

pub fn first_once<A, Y, F: FnOnce(A) -> Y>(y: Y, f: F) -> Once<(Y, F)> {
    Once(Some((y, f)))
}

impl<F> Once<F> {
    pub fn new(f: F) -> Once<F> {
        Once(Some(f))
    }
}

impl<A, Y, F> First<A> for Once<(Y, F)>
where
    F: FnOnce(A) -> Y,
{
    type Next = Once<F>;

    fn first(self) -> (Y, Self::Next) {
        let (y, f) = self.0.expect("f must be Some");
        (y, Once(Some(f)))
    }
}

impl<A, Y, F> Stage<A> for Once<F>
where
    F: FnOnce(A) -> Y,
{
    type Yield = Y;
    type Resume = A;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        match self.0.take() {
            Some(f) => Either::Left(f(input)),
            None => Either::Right(input),
        }
    }
}

pub fn chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Stage<A, Resume = A>,
    R: Stage<A, Yield = L::Yield>,
{
    Chain(Some(l), r)
}

pub fn first_chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: First<A>,
    L::Next: Stage<A, Resume = A>,
    R: Stage<A, Yield = <L::Next as Stage<A>>::Yield>,
{
    Chain(Some(l), r)
}

pub struct Chain<S1, S2>(Option<S1>, S2);

impl<A, L, R> Stage<A> for Chain<L, R>
where
    L: Stage<A, Resume = A>,
    R: Stage<A, Yield = L::Yield>,
{
    type Yield = L::Yield;
    type Resume = R::Resume;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        match self.0 {
            Some(ref mut l) => match l.step(input) {
                Either::Left(y) => Either::Left(y),
                Either::Right(a) => {
                    self.0 = None; // we drop the old stage when it's done
                    self.1.step(a)
                }
            },
            None => self.1.step(input),
        }
    }
}

impl<A, L, R> First<A> for Chain<L, R>
where
    L: First<A>,
    L::Next: Stage<A, Resume = A>,
    R: Stage<A, Yield = <L::Next as Stage<A>>::Yield>,
{
    type Next = Chain<L::Next, R>;
    fn first(self) -> (<L::Next as Stage<A>>::Yield, Self::Next) {
        let (y, l) = self.0.expect("l must be Some").first();
        (y, Chain(Some(l), self.1))
    }
}

pub struct Convert<S, F> {
    f: F,
    stage: S,
}

impl<A1, A2, S, F> Stage<A1> for Convert<S, F>
where
    S: Stage<A2>,
    F: FnMut(A1) -> A2,
{
    type Yield = S::Yield;
    type Resume = S::Resume;
    fn step(&mut self, input: A1) -> Either<Self::Yield, Self::Resume> {
        let a2 = (self.f)(input);
        self.stage.step(a2)
    }
}

impl<A1, A2, S, F> First<A1> for Convert<S, F>
where
    S: First<A2>,
    F: FnMut(A1) -> A2,
{
    type Next = Convert<S::Next, F>;

    fn first(self) -> (<Self::Next as Stage<A1>>::Yield, Self::Next) {
        let Convert { f, stage } = self;
        let (y, next_stage) = stage.first();
        (
            y,
            Convert {
                f,
                stage: next_stage,
            },
        )
    }
}

pub struct MapYield<S, F> {
    f: F,
    stage: S,
}

impl<A, Y1, Y2, S, F> Stage<A> for MapYield<S, F>
where
    S: Stage<A, Yield = Y1>,
    F: FnMut(Y1) -> Y2,
{
    type Yield = Y2;
    type Resume = S::Resume;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        match self.stage.step(input) {
            Either::Left(y1) => Either::Left((self.f)(y1)),
            Either::Right(a) => Either::Right(a),
        }
    }
}

impl<A, Y1, Y2, S, F> First<A> for MapYield<S, F>
where
    S: Stage<A, Yield = Y1> + First<A>,
    F: FnMut(Y1) -> Y2,
    S::Next: Stage<A, Yield = Y1>,
{
    type Next = MapYield<S::Next, F>;

    fn first(self) -> (<Self::Next as Stage<A>>::Yield, Self::Next) {
        let MapYield { mut f, stage } = self;
        let (y1, next_stage) = stage.first();
        let mapped_y = f(y1);
        (
            mapped_y,
            MapYield {
                f,
                stage: next_stage,
            },
        )
    }
}

pub struct MapResume<S, F> {
    f: F,
    stage: S,
}

impl<A, Y, R1, R2, S, F> Stage<A> for MapResume<S, F>
where
    S: Stage<A, Yield = Y, Resume = R1>,
    F: FnMut(R1) -> R2,
{
    type Yield = Y;
    type Resume = R2;
    fn step(&mut self, input: A) -> Either<Self::Yield, Self::Resume> {
        match self.stage.step(input) {
            Either::Left(y) => Either::Left(y),
            Either::Right(r1) => Either::Right((self.f)(r1)),
        }
    }
}

impl<A, Y, R1, R2, S, F> First<A> for MapResume<S, F>
where
    S: Stage<A, Yield = Y, Resume = R1> + First<A>,
    F: FnMut(R1) -> R2,
    S::Next: Stage<A, Yield = Y, Resume = R1>,
{
    type Next = MapResume<S::Next, F>;

    fn first(self) -> (<Self::Next as Stage<A>>::Yield, Self::Next) {
        let MapResume { f, stage } = self;
        let (y, next_stage) = stage.first();
        (
            y,
            MapResume {
                f,
                stage: next_stage,
            },
        )
    }
}

pub trait StageExt<A>: Stage<A> {
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Stage<A, Resume = A>,
        R: Stage<A, Yield = Self::Yield>,
    {
        chain(self, r)
    }

    fn chain_fn<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Stage<A, Resume = A>,
        F: FnOnce(Self::Resume) -> Self::Yield,
    {
        chain(self, Once::new(f))
    }
}

pub trait FirstExt<A>: First<A> {
    fn chain<S, R>(self, r: R) -> Chain<Self, R>
    where
        S: Stage<A, Resume = A>,
        Self: Sized + First<A, Next = S>,
        R: Stage<A, Yield = S::Yield>,
    {
        first_chain(self, r)
    }

    fn chain_fn<S, F>(self, f: F) -> Chain<Self, Once<F>>
    where
        S: Stage<A, Resume = A>,
        Self: Sized + First<A, Next = S>,
        F: FnOnce(S::Resume) -> S::Yield,
    {
        first_chain(self, Once::new(f))
    }
}

pub fn repeat<A, Y, F: FnMut(A) -> Y>(f: F) -> Repeat<F> {
    Repeat(f)
}

pub fn first_repeat<A, Y, F: FnMut(A) -> Y>(y: Y, f: F) -> Repeat<(Y, F)> {
    Repeat((y, f))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_addition() {
        let mut prev = 1;
        let fib = first_repeat(1, move |n: u128| {
            let next = prev + n;
            prev = next;
            next
        });

        let (_, mut next) = fib.first();
        for i in 1..11 {
            let cur = next.step(1).unwrap_left();
            assert_eq!(i + 1, cur);
        }
    }

    #[test]
    fn test_simple_divider() {
        let mut start = 101323012313805546028676730784521326u128;
        let divider = first_repeat(start, |divisor: u128| {
            start /= divisor;
            start
        });

        assert_eq!(size_of_val(&divider), 32);
        let (mut cur, mut next) = divider.first();
        for i in 2..20 {
            let next_cur = next.step(i).unwrap_left();
            assert_eq!(cur / i, next_cur);
            cur = next_cur;
        }
    }
}
