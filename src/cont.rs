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
    S::Next: Cont<A2>,
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
    S: First<A>,
    S::Next: Cont<A, Yield = Y1>,
    F: FnMut(Y1) -> Y2,
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
    S: First<A>,
    S::Next: Cont<A, Yield = Y, Done = D1>,
    F: FnMut(D1) -> D2,
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

pub trait ContExt<A>: Cont<A> {
    fn chain<R>(self, r: R) -> Chain<Self, R>
    where
        Self: Sized + Cont<A, Done = A>,
        R: Cont<A, Yield = Self::Yield>,
    {
        chain(self, r)
    }

    fn chain_once<F>(self, f: F) -> Chain<Self, Once<F>>
    where
        Self: Sized + Cont<A, Done = A>,
        F: FnOnce(Self::Done) -> Self::Yield,
    {
        chain(self, Once::new(f))
    }

    fn chain_repeat<F>(self, f: F) -> Chain<Self, Repeat<F>>
    where
        Self: Sized + Cont<A, Done = A>,
        F: FnMut(Self::Done) -> Self::Yield,
    {
        chain(self, repeat(f))
    }

    fn map_input<NewInput, F>(self, f: F) -> MapInput<Self, F>
    where
        Self: Sized,
        F: FnMut(NewInput) -> A,
    {
        MapInput { f, stage: self }
    }

    fn map_yield<NewYield, F>(self, f: F) -> MapYield<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Yield) -> NewYield,
    {
        MapYield { f, stage: self }
    }

    fn map_done<NewDone, F>(self, f: F) -> MapDone<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Done) -> NewDone,
    {
        MapDone { f, stage: self }
    }
}

impl<A, T: Cont<A>> ContExt<A> for T {}

pub trait FirstExt<A>: First<A> {
    fn chain<S, R>(self, r: R) -> Chain<Self, R>
    where
        S: Cont<A, Done = A>,
        Self: Sized + First<A, Next = S>,
        R: Cont<A, Yield = S::Yield>,
    {
        first_chain(self, r)
    }

    fn chain_once<S, F>(self, f: F) -> Chain<Self, Once<F>>
    where
        S: Cont<A, Done = A>,
        Self: Sized + First<A, Next = S>,
        F: FnOnce(S::Done) -> S::Yield,
    {
        first_chain(self, once(f))
    }

    fn chain_repeat<S, F>(self, f: F) -> Chain<Self, Repeat<F>>
    where
        S: Cont<A, Done = A>,
        Self: Sized + First<A, Next = S>,
        F: FnMut(S::Done) -> S::Yield,
    {
        first_chain(self, repeat(f))
    }

    fn map_input<NewInput, F>(self, f: F) -> MapInput<Self, F>
    where
        Self: Sized,
        Self::Next: Cont<A>,
        F: FnMut(NewInput) -> A,
    {
        MapInput { f, stage: self }
    }

    fn map_yield<NewYield, F>(self, f: F) -> MapYield<Self, F>
    where
        Self: Sized,
        Self::Next: Cont<A>,
        F: FnMut(<Self::Next as Cont<A>>::Yield) -> NewYield,
    {
        MapYield { f, stage: self }
    }

    fn map_done<NewDone, F>(self, f: F) -> MapDone<Self, F>
    where
        Self: Sized,
        Self::Next: Cont<A>,
        F: FnMut(<Self::Next as Cont<A>>::Done) -> NewDone,
    {
        MapDone { f, stage: self }
    }
}

impl<A, T: First<A>> FirstExt<A> for T {}

pub fn repeat<A, Y, F: FnMut(A) -> Y>(f: F) -> Repeat<F> {
    Repeat(f)
}

pub fn first_repeat<A, Y, F: FnMut(A) -> Y>(y: Y, f: F) -> Repeat<(Y, F)> {
    Repeat((y, f))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add_three(value: i32) -> i32 {
        value + 3
    }

    #[derive(Clone, Copy, Debug)]
    struct ImmediateFirstDone;

    impl Cont<&'static str> for ImmediateFirstDone {
        type Yield = &'static str;
        type Done = &'static str;

        fn next(&mut self, input: &'static str) -> Either<Self::Yield, Self::Done> {
            Either::Right(input)
        }
    }

    impl First<&'static str> for ImmediateFirstDone {
        type Next = Self;

        fn first(
            self,
        ) -> Either<
            (<Self::Next as Cont<&'static str>>::Yield, Self::Next),
            <Self::Next as Cont<&'static str>>::Done,
        > {
            Either::Right("left-done")
        }
    }

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

    #[test]
    fn test_chain_once_into_repeat() {
        let initializer = first_once(10_u32, |input: u32| input + 5);
        let mut multiplier = 2_u32;
        let repeater = repeat(move |input: u32| {
            let output = input * multiplier;
            multiplier += 1;
            output
        });

        let chain = initializer.chain(repeater);
        let (first_yield, mut stage) = chain.first().unwrap_left();
        assert_eq!(10, first_yield);
        assert_eq!(13, stage.next(8).unwrap_left());
        assert_eq!(16, stage.next(8).unwrap_left());
        assert_eq!(24, stage.next(8).unwrap_left());
        assert_eq!(32, stage.next(8).unwrap_left());
    }

    #[test]
    fn test_map_input_and_map_yield_pipeline() {
        let mut total = 0_i64;
        let repeating = first_repeat(0_i64, move |delta: i64| {
            total += delta;
            total
        })
        .map_input(|cmd: &str| -> i64 {
            let mut parts = cmd.split_whitespace();
            let op = parts.next().expect("operation must exist");
            let amount: i64 = parts
                .next()
                .expect("amount must exist")
                .parse()
                .expect("amount must parse");
            match op {
                "add" => amount,
                "sub" => -amount,
                _ => panic!("unsupported op: {op}"),
            }
        })
        .map_yield(|value: i64| format!("total={value}"));

        let (initial_total, mut stage) = repeating.first().unwrap_left();
        assert_eq!("total=0", initial_total);
        assert_eq!("total=5", stage.next("add 5").unwrap_left());
        assert_eq!("total=2", stage.next("sub 3").unwrap_left());
        assert_eq!("total=7", stage.next("add 5").unwrap_left());
    }

    #[test]
    fn test_chain_and_map_done_resume_flow() {
        let initializer = first_once(42_u32, |input: u32| input + 1);
        let finisher = once(|input: u32| input * 3);

        let chain = initializer
            .chain(finisher)
            .map_done(|resume: u32| resume + 7);
        let (first_value, mut stage) = chain.first().unwrap_left();
        assert_eq!(42, first_value);

        assert_eq!(11, stage.next(10).unwrap_left());
        assert_eq!(30, stage.next(10).unwrap_left());
        assert_eq!(17, stage.next(10).unwrap_right());
    }

    #[test]
    fn test_chain_switches_to_second_stage_after_first_done() {
        let mut stage = once(|val: u32| val + 1).chain(repeat(|val: u32| val * 2));

        assert_eq!(stage.next(3).unwrap_left(), 4);
        assert_eq!(stage.next(4).unwrap_left(), 8);
        assert_eq!(stage.next(5).unwrap_left(), 10);
    }

    #[test]
    fn test_chain_propagates_done_from_second_stage() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2));

        assert_eq!(stage.next(2).unwrap_left(), 3);
        assert_eq!(stage.next(3).unwrap_left(), 6);
        assert_eq!(stage.next(4).unwrap_right(), 4);
    }

    #[test]
    fn test_either_first_right_branch_selected() {
        let stage: Either<Repeat<(i32, fn(i32) -> i32)>, Repeat<(i32, fn(i32) -> i32)>> =
            Either::Right(first_repeat(2_i32, add_three));

        let (first_value, mut next_stage) = stage.first().unwrap_left();
        assert_eq!(2, first_value);
        assert_eq!(5, next_stage.next(2).unwrap_left());
        assert_eq!(6, next_stage.next(3).unwrap_left());
    }

    #[test]
    fn test_either_first_left_done_returns_resume() {
        let stage: Either<ImmediateFirstDone, ImmediateFirstDone> =
            Either::Left(ImmediateFirstDone);

        let resume = stage.first().unwrap_right();
        assert_eq!("left-done", resume);
    }

    #[test]
    fn test_map_done_applies_after_chain_completion() {
        let mut stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 2))
            .map_done(|done: u32| format!("resume={done}"));

        assert_eq!(stage.next(5).unwrap_left(), 6);
        assert_eq!(stage.next(6).unwrap_left(), 12);
        assert_eq!(stage.next(7).unwrap_right(), "resume=7".to_string());
    }

    #[test]
    fn test_first_ext_map_input_yield_done() {
        let initializer = first_once(5_u32, |input: u32| input + 2);
        let finisher = once(|value: u32| value * 2);

        let stage = initializer
            .chain(finisher)
            .map_input(|text: &str| text.parse::<u32>().expect("number"))
            .map_yield(|value: u32| format!("value={value}"))
            .map_done(|resume: u32| format!("done={resume}"));

        let (first_value, mut rest) = stage.first().unwrap_left();
        assert_eq!("value=5", first_value);
        assert_eq!("value=9", rest.next("7").unwrap_left());
        assert_eq!("value=16", rest.next("8").unwrap_left());
        assert_eq!("done=9", rest.next("9").unwrap_right());
    }
}
