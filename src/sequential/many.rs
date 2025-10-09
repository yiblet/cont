use crate::{Sans, Step};

pub fn many<const N: usize, I, O, S>(rest: [S; N]) -> Many<N, S>
where
    S: Sans<I, O, Return = I>,
{
    Many {
        states: rest.map(|r| Some(r)),
        index: 0,
    }
}

pub struct Many<const N: usize, S> {
    states: [Option<S>; N],
    index: usize,
}

impl<const N: usize, I, O, S> Sans<I, O> for Many<N, S>
where
    S: Sans<I, O, Return = I>,
{
    type Return = S::Return;
    fn next(&mut self, mut input: I) -> Step<O, Self::Return> {
        loop {
            match self.states.get_mut(self.index) {
                Some(Some(s)) => match s.next(input) {
                    Step::Yielded(o) => return Step::Yielded(o),
                    Step::Complete(a) => {
                        self.index += 1;
                        input = a;
                    }
                },
                Some(None) => {
                    self.index += 1;
                }
                None => return Step::Complete(input),
            }
        }
    }
}
