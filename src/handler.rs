use crate::cont::{Cont, First};
use either::Either;
use std::future::Future;

/// Drive a `First` stage by synchronously responding to each yield until it finishes.
pub fn handle_first_sync<S, A, R>(stage: S, mut responder: R) -> <S::Next as Cont<A>>::Done
where
    S: First<A>,
    S::Next: Cont<A>,
    R: FnMut(<S::Next as Cont<A>>::Yield) -> A,
{
    match stage.first() {
        Either::Left((yielded, mut next_stage)) => {
            let mut input = responder(yielded);
            loop {
                match next_stage.next(input) {
                    Either::Left(yielded) => {
                        input = responder(yielded);
                    }
                    Either::Right(done) => return done,
                }
            }
        }
        Either::Right(done) => done,
    }
}

/// Drive a continuation by synchronously responding to each yield until it finishes.
pub fn handle_cont_sync<C, A, R>(mut stage: C, mut input: A, mut responder: R) -> C::Done
where
    C: Cont<A>,
    R: FnMut(C::Yield) -> A,
{
    loop {
        match stage.next(input) {
            Either::Left(yielded) => {
                input = responder(yielded);
            }
            Either::Right(done) => return done,
        }
    }
}

/// Drive a continuation by asynchronously responding to each yield until it finishes.
pub async fn handle_cont_async<C, A, R, Fut>(
    mut stage: C,
    mut input: A,
    mut responder: R,
) -> C::Done
where
    C: Cont<A>,
    R: FnMut(C::Yield) -> Fut,
    Fut: Future<Output = A>,
{
    loop {
        match stage.next(input) {
            Either::Left(yielded) => {
                input = responder(yielded).await;
            }
            Either::Right(done) => return done,
        }
    }
}

/// Drive a `First` stage by asynchronously responding to each yield until it finishes.
pub async fn handle_first_async<S, A, R, Fut>(
    stage: S,
    mut responder: R,
) -> <S::Next as Cont<A>>::Done
where
    S: First<A>,
    S::Next: Cont<A>,
    R: FnMut(<S::Next as Cont<A>>::Yield) -> Fut,
    Fut: Future<Output = A>,
{
    match stage.first() {
        Either::Left((yielded, mut next_stage)) => {
            let mut input = responder(yielded).await;
            loop {
                match next_stage.next(input) {
                    Either::Left(yielded) => {
                        input = responder(yielded).await;
                    }
                    Either::Right(done) => return done,
                }
            }
        }
        Either::Right(done) => done,
    }
}

/// Convenience helper that drives any stage implementing `First`.
pub fn handle<S, A, R>(stage: S, responder: R) -> <S::Next as Cont<A>>::Done
where
    S: First<A>,
    S::Next: Cont<A>,
    R: FnMut(<S::Next as Cont<A>>::Yield) -> A,
{
    handle_first_sync(stage, responder)
}

/// Asynchronous variant of [`handle`].
pub async fn handle_async<S, A, R, Fut>(stage: S, responder: R) -> <S::Next as Cont<A>>::Done
where
    S: First<A>,
    S::Next: Cont<A>,
    R: FnMut(<S::Next as Cont<A>>::Yield) -> Fut,
    Fut: Future<Output = A>,
{
    handle_first_async(stage, responder).await
}

/// Bundle a continuation with its first input so it can be treated as a `First` stage.
pub struct Seed<C, A> {
    stage: C,
    input: Option<A>,
}

impl<C, A> Seed<C, A> {
    pub fn new(stage: C, input: A) -> Self {
        Seed {
            stage,
            input: Some(input),
        }
    }
}

pub fn with_input<A, C>(input: A, stage: C) -> Seed<C, A>
where
    C: Cont<A>,
{
    Seed::new(stage, input)
}

impl<A, C> First<A> for Seed<C, A>
where
    C: Cont<A>,
{
    type Next = C;

    fn first(self) -> Either<(C::Yield, C), C::Done> {
        let Seed { mut stage, input } = self;
        let input = input.expect("seed input must exist");
        match stage.next(input) {
            Either::Left(yielded) => Either::Left((yielded, stage)),
            Either::Right(done) => Either::Right(done),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{FirstExt, chain, first_once, once};
    use std::cell::RefCell;
    use std::collections::VecDeque;
    use std::future::{Future, ready};
    use std::rc::Rc;
    use std::sync::Arc;
    use std::task::{Context, Poll, Wake, Waker};

    fn block_on<F: Future>(future: F) -> F::Output {
        struct Noop;
        impl Wake for Noop {
            fn wake(self: Arc<Self>) {}
        }

        let waker = Waker::from(Arc::new(Noop));
        let mut context = Context::from_waker(&waker);
        let mut future = Box::pin(future);

        loop {
            match Future::poll(future.as_mut(), &mut context) {
                Poll::Ready(value) => return value,
                Poll::Pending => std::thread::yield_now(),
            }
        }
    }

    #[test]
    fn test_handle_cont_sync() {
        let stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 3));
        let yields = Rc::new(RefCell::new(Vec::new()));
        let responses = Rc::new(RefCell::new(VecDeque::from(vec![5_u32, 7])));

        let done = handle_cont_sync(stage, 1_u32, {
            let yields = Rc::clone(&yields);
            let responses = Rc::clone(&responses);
            move |value| {
                yields.borrow_mut().push(value);
                responses
                    .borrow_mut()
                    .pop_front()
                    .expect("response must exist")
            }
        });

        assert_eq!(done, 7);
        assert_eq!(&*yields.borrow(), &[2, 15]);
    }

    #[test]
    fn test_handle_cont_async() {
        let stage = chain(once(|val: u32| val + 1), once(|val: u32| val * 3));
        let yields = Rc::new(RefCell::new(Vec::new()));
        let responses = Rc::new(RefCell::new(VecDeque::from(vec![5_u32, 7])));

        let done = block_on(handle_cont_async(stage, 1_u32, {
            let yields = Rc::clone(&yields);
            let responses = Rc::clone(&responses);
            move |value| {
                yields.borrow_mut().push(value);
                let next = responses
                    .borrow_mut()
                    .pop_front()
                    .expect("response must exist");
                ready(next)
            }
        }));

        assert_eq!(done, 7);
        assert_eq!(&*yields.borrow(), &[2, 15]);
    }

    #[test]
    fn test_handle_first_sync() {
        let initializer = first_once(10_u32, |input: u32| input + 2);
        let finisher = once(|value: u32| value * 3);
        let stage = initializer.chain(finisher);

        let yields = Rc::new(RefCell::new(Vec::new()));
        let responses = Rc::new(RefCell::new(VecDeque::from(vec![5_u32, 6, 7])));

        let done = handle_first_sync(stage, {
            let yields = Rc::clone(&yields);
            let responses = Rc::clone(&responses);
            move |value| {
                yields.borrow_mut().push(value);
                responses
                    .borrow_mut()
                    .pop_front()
                    .expect("response must exist")
            }
        });

        assert_eq!(done, 7);
        assert_eq!(&*yields.borrow(), &[10, 7, 18]);
    }

    #[test]
    fn test_handle_first_async() {
        let initializer = first_once(10_u32, |input: u32| input + 2);
        let finisher = once(|value: u32| value * 3);
        let stage = initializer.chain(finisher);

        let yields = Rc::new(RefCell::new(Vec::new()));
        let responses = Rc::new(RefCell::new(VecDeque::from(vec![5_u32, 6, 7])));

        let done = block_on(handle_first_async(stage, {
            let yields = Rc::clone(&yields);
            let responses = Rc::clone(&responses);
            move |value| {
                yields.borrow_mut().push(value);
                let next = responses
                    .borrow_mut()
                    .pop_front()
                    .expect("response must exist");
                ready(next)
            }
        }));

        assert_eq!(done, 7);
        assert_eq!(&*yields.borrow(), &[10, 7, 18]);
    }

    #[test]
    fn test_handle_shortcut_for_first() {
        let initializer = first_once(2_u32, |input: u32| input + 1);
        let finisher = once(|value: u32| value * 2);
        let done = handle(initializer.chain(finisher), |value: u32| value + 1);
        assert_eq!(done, 11);
    }

    #[test]
    fn test_handle_shortcut_for_cont_with_input_helper() {
        let stage = once(|n: u32| n + 2);
        let done = handle(with_input(1_u32, stage), |value: u32| value + 1);
        assert_eq!(done, 4);
    }

    #[test]
    fn test_handle_async_shortcut_for_cont_with_input_helper() {
        let stage = once(|n: u32| n + 2);
        let done = block_on(handle_async(with_input(1_u32, stage), |value: u32| {
            ready(value + 1)
        }));
        assert_eq!(done, 4);
    }
}
