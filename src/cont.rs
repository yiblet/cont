use either::Either;

pub trait Cont<A> {
    type Query;
    type Resume;

    fn query(&mut self) -> Self::Query;
    fn resume(&mut self, a: A) -> Option<Self::Resume>;
}

pub struct FromFn<Q, F>(Q, F);

impl<Q, A, F> Cont<A> for FromFn<Q, F>
where
    Q: Clone,
    F: FnMut(A) -> Either<Q, A>,
{
    type Query = Q;
    type Resume = A;

    fn query(&mut self) -> Self::Query {
        self.0.clone()
    }

    fn resume(&mut self, a: A) -> Option<Self::Resume> {
        match (self.1)(a) {
            Either::Left(q) => {
                self.0 = q;
                None
            }
            Either::Right(a) => Some(a),
        }
    }
}
