mod stage;
mod cont;

use either::Either;
use std::marker::PhantomData;

// What I would like is the following api:
//
// let coro = create_coro() ;
// match coro.begin(v) {
//     Either::Left((y, resume)) => resume.step(f(y)),
//     Either::Right(r) => r,
// }
//
// S -> Coro<A, Y, R>
// bind: Coro<A, Y, R> -> (R -> Coro<A, Y, R2>) -> (S -> Coro<A, Y, R2>)

pub struct Coro<L, P>(L, PhantomData<P>);

impl<A, Y, L> Coro<L, (A, Y)> {
    pub fn new(l: L) -> Coro<impl FnMut(A) -> Either<Y, A>, (A, Y)>
    where
        L: FnOnce(A) -> Y,
    {
        let mut l = Some(l);
        let new_l = move |a: A| match l.take() {
            Some(l) => Either::Left(l(a)),
            None => Either::Right(a),
        };

        Coro(new_l, PhantomData)
    }
}

impl<A, Y, L> Coro<L, (A, Y)>
where
    L: FnMut(A) -> Either<Y, A>,
{
    pub fn yield_and<G>(self, g: G) -> Coro<impl FnMut(A) -> Either<Y, A>, (A, Y)>
    where
        G: FnOnce(A) -> Y,
    {
        let Coro(mut l, _) = self;
        let mut r = Some(g);
        let new_l = move |a| match l(a) {
            Either::Left(y) => Either::Left(y),
            Either::Right(a) => match r.take() {
                Some(r) => Either::Left(r(a)),
                None => Either::Right(a),
            },
        };
        Coro(new_l, PhantomData)
    }

    pub fn complete<G, C>(self, g: G) -> Coro<impl FnMut(A) -> Either<Y, C>, (A, Y, C)>
    where
        G: FnOnce(A) -> C,
    {
        let Coro(mut l, _) = self;
        let mut r = Some(g);
        let new_l = move |a| match l(a) {
            Either::Left(y) => Either::Left(y),
            Either::Right(a) => Either::Right(r.take().expect("r must be used only once")(a)),
        };

        Coro(new_l, PhantomData)
    }

    pub fn resume(&mut self, a: A) -> Either<Y, A> {
        let Coro(l, _) = self;
        l(a)
    }
}

impl<A, Y, C, L> Coro<L, (A, Y, C)>
where
    L: FnMut(A) -> Either<Y, C>,
{
    pub fn resume(&mut self, a: A) -> Either<Y, C> {
        let Coro(l, _) = self;
        l(a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coroutine_resume() {
        let mut coro = Coro::new(|x: i32| x * 2);
        let result = coro.resume(5);
        match result {
            Either::Left(y) => assert_eq!(y, 10),
            Either::Right(_) => panic!("Expected Left variant"),
        }
    }

    #[test]
    fn test_coroutine_resume_after_completion() {
        let mut coro = Coro::new(|x: i32| x * 2);
        // First call should yield the result
        let _first = coro.resume(5);
        // Second call should return the input unchanged
        let result = coro.resume(3);
        match result {
            Either::Right(a) => assert_eq!(a, 3),
            Either::Left(_) => panic!("Expected Right variant after completion"),
        }
    }

    #[test]
    fn test_yield_and() {
        let coro = Coro::new(|x: i32| x * 2).yield_and(|x: i32| x + 10);
        let mut extended_coro = coro.yield_and(|x: i32| x + 10);

        // First resume should execute the original function
        let result1 = extended_coro.resume(5);
        match result1 {
            Either::Left(y) => assert_eq!(y, 10),
            Either::Right(_) => panic!("Expected Left variant"),
        }

        // Second resume should execute the yield_and function
        let result2 = extended_coro.resume(3);
        match result2 {
            Either::Left(y) => assert_eq!(y, 13),
            Either::Right(_) => panic!("Expected Left variant"),
        }
    }

    #[test]
    fn test_complete() {
        let coro = Coro::new(|x: i32| x * 2);
        let mut completed_coro = coro.complete(|x: i32| x.to_string());

        // First resume should yield the original result
        let result1 = completed_coro.resume(5);
        match result1 {
            Either::Left(y) => assert_eq!(y, 10),
            Either::Right(_) => panic!("Expected Left variant"),
        }

        // Second resume should complete with the final transformation
        let result2 = completed_coro.resume(7);
        match result2 {
            Either::Right(c) => assert_eq!(c, "7"),
            Either::Left(_) => panic!("Expected Right variant with completion"),
        }
    }

    #[test]
    fn test_chained_operations() {
        let coro = Coro::new(|x: i32| x * 2);
        let extended = coro.yield_and(|x: i32| x + 5);
        let mut completed = extended.complete(|x: i32| format!("Result: {}", x));

        // First call - original function
        let result1 = completed.resume(3);
        match result1 {
            Either::Left(y) => assert_eq!(y, 6),
            Either::Right(_) => panic!("Expected Left variant"),
        }

        // Second call - yield_and function
        let result2 = completed.resume(10);
        match result2 {
            Either::Left(y) => assert_eq!(y, 15),
            Either::Right(_) => panic!("Expected Left variant"),
        }

        // Third call - complete function
        let result3 = completed.resume(20);
        match result3 {
            Either::Right(c) => assert_eq!(c, "Result: 20"),
            Either::Left(_) => panic!("Expected Right variant with completion"),
        }
    }

    #[test]
    fn test_memory_layout_growth() {
        use std::mem::size_of_val;

        let base = Coro::new(|x: i32| x * 2);
        let base_size = size_of_val(&base);

        let yielded_once = base.yield_and(|x: i32| x + 1);
        let yielded_once_size = size_of_val(&yielded_once);

        let completed = yielded_once.complete(|x: i32| x - 1);
        let completed_size = size_of_val(&completed);

        assert_eq!(
            base_size, 1,
            "Coro::new should only store the one-shot option"
        );
        assert_eq!(
            yielded_once_size, 2,
            "yield_and should add exactly one byte of state"
        );
        assert_eq!(
            completed_size, 3,
            "complete should add another byte for its one-shot closure"
        );
    }
}
