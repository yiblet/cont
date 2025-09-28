use either::Either;

pub trait First<A> {
    type Next: Cont<A>;
    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done>;
}

impl<A, Y, F> First<A> for (Y, F)
where
    F: Cont<A, Yield = Y>,
{
    type Next = F;
    fn first(self) -> Either<(Y, F), F::Done> {
        Either::Left(self)
    }
}

pub trait Cont<A> {
    type Yield;
    type Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done>;
}

impl<A, Y, D, F> Cont<A> for F
where
    F: FnMut(A) -> Either<Y, D>,
{
    type Yield = Y;
    type Done = D;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        self(input)
    }
}

impl<A, L, R> Cont<A> for Either<L, R>
where
    L: Cont<A>,
    R: Cont<A, Yield = L::Yield, Done = L::Done>,
{
    type Yield = L::Yield;
    type Done = L::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self {
            Either::Left(l) => l.next(input),
            Either::Right(r) => r.next(input),
        }
    }
}

impl<A, L, R> First<A> for Either<L, R>
where
    L: First<A>,
    R: First<A>,
    R::Next: Cont<A, Done = <L::Next as Cont<A>>::Done, Yield = <L::Next as Cont<A>>::Yield>,
{
    type Next = Either<L::Next, R::Next>;
    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        match self {
            Either::Left(l) => match l.first() {
                Either::Left((y, next_l)) => Either::Left((y, Either::Left(next_l))),
                Either::Right(resume) => Either::Right(resume),
            },
            Either::Right(r) => match r.first() {
                Either::Left((y, next_r)) => Either::Left((y, Either::Right(next_r))),
                Either::Right(resume) => Either::Right(resume),
            },
        }
    }
}

pub struct Repeat<F>(F);

impl<A, Y, F> Cont<A> for Repeat<F>
where
    F: FnMut(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        Either::Left(self.0(input))
    }
}

impl<A, Y, F> First<A> for Repeat<(Y, F)>
where
    F: FnMut(A) -> Y,
{
    type Next = Repeat<F>;

    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        let Repeat((y, f)) = self;
        Either::Left((y, Repeat(f)))
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

    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        let (y, f) = self.0.expect("f must be Some");
        Either::Left((y, Once(Some(f))))
    }
}

impl<A, Y, F> Cont<A> for Once<F>
where
    F: FnOnce(A) -> Y,
{
    type Yield = Y;
    type Done = A;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.0.take() {
            Some(f) => Either::Left(f(input)),
            None => Either::Right(input),
        }
    }
}

pub fn chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: Cont<A, Done = A>,
    R: Cont<A, Yield = L::Yield>,
{
    Chain(Some(l), r)
}

pub fn first_chain<A, L, R>(l: L, r: R) -> Chain<L, R>
where
    L: First<A>,
    L::Next: Cont<A, Done = A>,
    R: Cont<A, Yield = <L::Next as Cont<A>>::Yield>,
{
    Chain(Some(l), r)
}

pub struct Chain<S1, S2>(Option<S1>, S2);

impl<A, L, R> Cont<A> for Chain<L, R>
where
    L: Cont<A, Done = A>,
    R: Cont<A, Yield = L::Yield>,
{
    type Yield = L::Yield;
    type Done = R::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.0 {
            Some(ref mut l) => match l.next(input) {
                Either::Left(y) => Either::Left(y),
                Either::Right(a) => {
                    self.0 = None; // we drop the old stage when it's done
                    self.1.next(a)
                }
            },
            None => self.1.next(input),
        }
    }
}

impl<A, L, R> First<A> for Chain<L, R>
where
    L: First<A>,
    L::Next: Cont<A, Done = A>,
    R: Cont<A, Yield = <L::Next as Cont<A>>::Yield>,
{
    type Next = Chain<L::Next, R>;
    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        let Chain(left_stage, mut right_stage) = self;
        let left = left_stage.expect("l must be Some");
        match left.first() {
            Either::Left((y, next_left)) => Either::Left((y, Chain(Some(next_left), right_stage))),
            Either::Right(a) => match right_stage.next(a) {
                Either::Left(y) => Either::Left((y, Chain(None, right_stage))),
                Either::Right(resume) => Either::Right(resume),
            },
        }
    }
}

pub struct MapInput<S, F> {
    f: F,
    stage: S,
}

impl<A1, A2, S, F> Cont<A1> for MapInput<S, F>
where
    S: Cont<A2>,
    F: FnMut(A1) -> A2,
{
    type Yield = S::Yield;
    type Done = S::Done;
    fn next(&mut self, input: A1) -> Either<Self::Yield, Self::Done> {
        let a2 = (self.f)(input);
        self.stage.next(a2)
    }
}

impl<A1, A2, S, F> First<A1> for MapInput<S, F>
where
    S: First<A2>,
    F: FnMut(A1) -> A2,
{
    type Next = MapInput<S::Next, F>;

    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A1>>::Yield, Self::Next), <Self::Next as Cont<A1>>::Done> {
        let MapInput { f, stage } = self;
        match stage.first() {
            Either::Left((y, next_stage)) => Either::Left((
                y,
                MapInput {
                    f,
                    stage: next_stage,
                },
            )),
            Either::Right(resume) => Either::Right(resume),
        }
    }
}

pub struct MapYield<S, F> {
    f: F,
    stage: S,
}

impl<A, Y1, Y2, S, F> Cont<A> for MapYield<S, F>
where
    S: Cont<A, Yield = Y1>,
    F: FnMut(Y1) -> Y2,
{
    type Yield = Y2;
    type Done = S::Done;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Either::Left(y1) => Either::Left((self.f)(y1)),
            Either::Right(a) => Either::Right(a),
        }
    }
}

impl<A, Y1, Y2, S, F> First<A> for MapYield<S, F>
where
    S: Cont<A, Yield = Y1> + First<A>,
    F: FnMut(Y1) -> Y2,
    S::Next: Cont<A, Yield = Y1>,
{
    type Next = MapYield<S::Next, F>;

    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        let MapYield { mut f, stage } = self;
        match stage.first() {
            Either::Left((y1, next_stage)) => {
                let mapped_y = f(y1);
                Either::Left((
                    mapped_y,
                    MapYield {
                        f,
                        stage: next_stage,
                    },
                ))
            }
            Either::Right(resume) => Either::Right(resume),
        }
    }
}

pub struct MapDone<S, F> {
    f: F,
    stage: S,
}

impl<A, Y, D1, D2, S, F> Cont<A> for MapDone<S, F>
where
    S: Cont<A, Yield = Y, Done = D1>,
    F: FnMut(D1) -> D2,
{
    type Yield = Y;
    type Done = D2;
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done> {
        match self.stage.next(input) {
            Either::Left(y) => Either::Left(y),
            Either::Right(r1) => Either::Right((self.f)(r1)),
        }
    }
}

impl<A, Y, D1, D2, S, F> First<A> for MapDone<S, F>
where
    S: Cont<A, Yield = Y, Done = D1> + First<A>,
    F: FnMut(D1) -> D2,
    S::Next: Cont<A, Yield = Y, Done = D1>,
{
    type Next = MapDone<S::Next, F>;

    fn first(
        self,
    ) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done> {
        let MapDone { mut f, stage } = self;
        match stage.first() {
            Either::Left((y, next_stage)) => Either::Left((
                y,
                MapDone {
                    f,
                    stage: next_stage,
                },
            )),
            Either::Right(resume) => Either::Right(f(resume)),
        }
    }
}

pub trait StageExt<A>: Cont<A> {
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Cont<A, Done = A>,
        R: Cont<A, Yield = Self::Yield>,
    {
        chain(self, r)
    }

    fn chain_fn<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Cont<A, Done = A>,
        F: FnOnce(Self::Done) -> Self::Yield,
    {
        chain(self, Once::new(f))
    }
}

pub trait FirstExt<A>: First<A> {
    fn chain<S, R>(self, r: R) -> Chain<Self, R>
    where
        S: Cont<A, Done = A>,
        Self: Sized + First<A, Next = S>,
        R: Cont<A, Yield = S::Yield>,
    {
        first_chain(self, r)
    }

    fn chain_fn<S, F>(self, f: F) -> Chain<Self, Once<F>>
    where
        S: Cont<A, Done = A>,
        Self: Sized + First<A, Next = S>,
        F: FnOnce(S::Done) -> S::Yield,
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

        let (_, mut next) = fib.first().unwrap_left();
        for i in 1..11 {
            let cur = next.next(1).unwrap_left();
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
        let (mut cur, mut next) = divider.first().unwrap_left();
        for i in 2..20 {
            let next_cur = next.next(i).unwrap_left();
            assert_eq!(cur / i, next_cur);
            cur = next_cur;
        }
    }
}
