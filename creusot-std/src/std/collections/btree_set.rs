#[cfg(creusot)]
use crate::{
    logic::FSet,
    std::ops::{RangeBoundsSpec, between},
};
use crate::{
    prelude::*,
    std::iter::{DoubleEndedIteratorSpec, ExactSizeIteratorSpec, IteratorSpec},
};
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
use std::collections::btree_set::*;
#[cfg(creusot)]
use std::{borrow::Borrow, ops::RangeBounds};

#[cfg(feature = "nightly")]
impl<T: DeepModel, A: Allocator + Clone> View for BTreeSet<T, A> {
    type ViewTy = crate::logic::FSet<T::DeepModelTy>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

/// `seq` is the sequence of the elements of `s`, in increasing order.
#[logic(open)]
pub fn sorted_elems<T: DeepModel<DeepModelTy: OrdLogic>>(
    s: FSet<T::DeepModelTy>,
    seq: Seq<T>,
) -> bool {
    pearlite! {
        seq.len() == s.len()
        && (forall<i, j> 0 <= i && i < j && j < seq.len() ==> seq[i].deep_model() < seq[j].deep_model())
        && (forall<i> 0 <= i && i < seq.len() ==> s.contains(&seq[i].deep_model()))
        && (forall<x: T::DeepModelTy> s.contains(&x) ==> exists<i> 0 <= i && i < seq.len() && seq[i].deep_model() == x)
    }
}

extern_spec! {
    impl<T: DeepModel> BTreeSet<T> {
        #[check(ghost)]
        #[ensures(result@ == FSet::empty())]
        fn new() -> Self;
    }

    impl<T: DeepModel, A: Allocator + Clone> BTreeSet<T, A> {
        #[check(ghost)]
        #[ensures(result@ == self@.len())]
        fn len(&self) -> usize;

        #[check(ghost)]
        #[ensures(result == (self@.len() == 0))]
        fn is_empty(&self) -> bool;

        #[ensures((^self)@ == FSet::empty())]
        fn clear(&mut self);
    }

    impl<T: DeepModel<DeepModelTy: OrdLogic>, A: Allocator + Clone> BTreeSet<T, A> {
        #[ensures(result == self@.contains(&value.deep_model()))]
        fn contains<Q: ?Sized + Ord + DeepModel<DeepModelTy = T::DeepModelTy>>(&self, value: &Q) -> bool
        where
            T: Borrow<Q> + Ord;

        #[ensures(match result {
            Some(r) => r.deep_model() == value.deep_model() && self@.contains(&value.deep_model()),
            None => !self@.contains(&value.deep_model()),
        })]
        fn get<'a, Q: ?Sized + Ord + DeepModel<DeepModelTy = T::DeepModelTy>>(&'a self, value: &Q) -> Option<&'a T>
        where
            T: Borrow<Q> + Ord;

        #[ensures(result == !self@.contains(&value.deep_model()))]
        #[ensures((^self)@ == self@.add(value.deep_model()))]
        fn insert(&mut self, value: T) -> bool
        where
            T: Ord;

        #[ensures(result == self@.contains(&value.deep_model()))]
        #[ensures((^self)@ == self@.remove(value.deep_model()))]
        fn remove<Q: ?Sized + Ord + DeepModel<DeepModelTy = T::DeepModelTy>>(&mut self, value: &Q) -> bool
        where
            T: Borrow<Q> + Ord;

        #[ensures(result == self@.disjoint(other@))]
        fn is_disjoint(&self, other: &BTreeSet<T, A>) -> bool
        where
            T: Ord;

        #[ensures(result == self@.is_subset(other@))]
        fn is_subset(&self, other: &BTreeSet<T, A>) -> bool
        where
            T: Ord;

        #[ensures(result == self@.is_superset(other@))]
        fn is_superset(&self, other: &BTreeSet<T, A>) -> bool
        where
            T: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some(x) => self@.contains(&x.deep_model())
                && forall<y: T::DeepModelTy> self@.contains(&y) ==> x.deep_model() <= y,
            None => self@.len() == 0,
        })]
        fn first(&self) -> Option<&T>
        where
            T: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some(x) => self@.contains(&x.deep_model())
                && forall<y: T::DeepModelTy> self@.contains(&y) ==> y <= x.deep_model(),
            None => self@.len() == 0,
        })]
        fn last(&self) -> Option<&T>
        where
            T: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some(x) => self@.contains(&x.deep_model())
                && (forall<y: T::DeepModelTy> self@.contains(&y) ==> x.deep_model() <= y)
                && (^self)@ == self@.remove(x.deep_model()),
            None => self@.len() == 0 && ^self == *self,
        })]
        fn pop_first(&mut self) -> Option<T>
        where
            T: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some(x) => self@.contains(&x.deep_model())
                && (forall<y: T::DeepModelTy> self@.contains(&y) ==> y <= x.deep_model())
                && (^self)@ == self@.remove(x.deep_model()),
            None => self@.len() == 0 && ^self == *self,
        })]
        fn pop_last(&mut self) -> Option<T>
        where
            T: Ord;

        #[check(ghost)]
        #[ensures(sorted_elems(self@, result@))]
        fn iter(&self) -> Iter<'_, T>;

        #[requires(crate::std::collections::btree_map::valid_range(
            range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()))]
        #[ensures(sorted_elems(
            self@.filter(|x| between(range.start_bound_logic().deep_model(), x, range.end_bound_logic().deep_model())),
            result@
        ))]
        fn range<K: ?Sized + Ord + DeepModel<DeepModelTy = T::DeepModelTy>, R: RangeBounds<K> + RangeBoundsSpec<K>>(&self, range: R) -> Range<'_, T>
        where
            T: Borrow<K> + Ord;

        #[ensures(sorted_elems(self@.difference(other@), result@))]
        fn difference<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Difference<'a, T, A>
        where
            T: Ord;

        #[ensures(sorted_elems(self@.difference(other@).union(other@.difference(self@)), result@))]
        fn symmetric_difference<'a>(&'a self, other: &'a BTreeSet<T, A>) -> SymmetricDifference<'a, T>
        where
            T: Ord;

        #[ensures(sorted_elems(self@.intersection(other@), result@))]
        fn intersection<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Intersection<'a, T, A>
        where
            T: Ord;

        #[ensures(sorted_elems(self@.union(other@), result@))]
        fn union<'a>(&'a self, other: &'a BTreeSet<T, A>) -> Union<'a, T>
        where
            T: Ord;
    }

    impl<T: DeepModel> Default for BTreeSet<T> {
        #[check(ghost)]
        #[ensures(result@ == FSet::empty())]
        fn default() -> Self;
    }

    impl<T: DeepModel<DeepModelTy: OrdLogic>, A: Allocator + Clone> IntoIterator for BTreeSet<T, A> {
        #[check(ghost)]
        #[ensures(sorted_elems(self@, result@))]
        fn into_iter(self) -> IntoIter<T, A>;
    }

    impl<'a, T: DeepModel<DeepModelTy: OrdLogic>, A: Allocator + Clone> IntoIterator for &'a BTreeSet<T, A> {
        #[check(ghost)]
        #[ensures(sorted_elems(self@, result@))]
        fn into_iter(self) -> Iter<'a, T>;
    }

    impl<T: Ord + DeepModel> FromIterator<T> for BTreeSet<T> {
        #[requires(I::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: I::IntoIter, prod: Seq<T>, done: &mut I::IntoIter>
            I::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(prod, *done) && done.completed() && resolve(^done) &&
            forall<x: T::DeepModelTy>
                result@.contains(&x) == exists<x1: T> x1.deep_model() == x && prod.contains(x1)
        )]
        fn from_iter<I: IntoIterator<Item = T, IntoIter: IteratorSpec>>(iter: I) -> Self;
    }
}

seq_iterator!([<'a, T>] Iter<'a, T>, &'a T);
seq_iterator_exact_double_ended!([<'a, T>] Iter<'a, T>);

// `Range` does not have a precise `size_hint`, so it does not implement
// `DoubleEndedIteratorSpec`.
seq_iterator!([<'a, T>] Range<'a, T>, &'a T);

seq_iterator!([<'a, T: Ord>] Union<'a, T>, &'a T);
seq_iterator!([<'a, T: Ord>] SymmetricDifference<'a, T>, &'a T);

seq_iterator!(#[cfg(feature = "nightly")] [<'a, T: Ord, A: Allocator + Clone>] Intersection<'a, T, A>, &'a T);
seq_iterator!(#[cfg(feature = "nightly")] [<'a, T: Ord, A: Allocator + Clone>] Difference<'a, T, A>, &'a T);

seq_iterator!(#[cfg(feature = "nightly")] [<T, A: Allocator + Clone>] IntoIter<T, A>, T);
seq_iterator_exact_double_ended!(#[cfg(feature = "nightly")] [<T, A: Allocator + Clone>] IntoIter<T, A>);

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
mod impls {
    use crate::{
        logic::FSet,
        prelude::*,
        std::iter::{DoubleEndedIteratorSpec, ExactSizeIteratorSpec},
    };
    use std::collections::btree_set::{BTreeSet, Difference, Intersection, IntoIter};

    impl<T: DeepModel> View for BTreeSet<T> {
        type ViewTy = FSet<T::DeepModelTy>;
    }

    impl<'a, T: Ord> View for Intersection<'a, T> {
        type ViewTy = Seq<&'a T>;
    }
    impl<'a, T: Ord> IteratorSpec for Intersection<'a, T> {}

    impl<'a, T: Ord> View for Difference<'a, T> {
        type ViewTy = Seq<&'a T>;
    }
    impl<'a, T: Ord> IteratorSpec for Difference<'a, T> {}

    impl<T> View for IntoIter<T> {
        type ViewTy = Seq<T>;
    }
    impl<T> IteratorSpec for IntoIter<T> {}
    impl<T> ExactSizeIteratorSpec for IntoIter<T> {}
    impl<T> DoubleEndedIteratorSpec for IntoIter<T> {}
}
