extern crate creusot_std;
use creusot_std::prelude::*;
use std::collections::BTreeSet;

// Basic operations: `insert`, `contains`, `remove`, `len`
pub fn basic() {
    let mut s: BTreeSet<u32> = BTreeSet::new();
    assert!(s.is_empty());
    assert!(s.insert(2));
    assert!(s.insert(1));
    assert!(!s.insert(2));
    assert!(s.len() == 2);
    assert!(s.contains(&1));
    assert!(!s.contains(&3));
    assert!(s.remove(&1));
    assert!(!s.remove(&1));
    assert!(s.len() == 1);
    assert!(s.get(&2) == Some(&2));
    s.clear();
    assert!(s.is_empty());
}

// `first`, `last`, `pop_first` and `pop_last`
pub fn first_last() {
    let mut s: BTreeSet<u32> = BTreeSet::new();
    s.insert(5);
    s.insert(1);
    s.insert(3);
    proof_assert!(forall<x: Int> s@.contains(&x) ==> x == 1 || x == 3 || x == 5);
    assert!(s.first() == Some(&1));
    assert!(s.last() == Some(&5));
    assert!(s.pop_first() == Some(1));
    assert!(s.pop_last() == Some(5));
    assert!(s.pop_first() == Some(3));
}

// Set relations
pub fn subset() {
    let mut a: BTreeSet<u32> = BTreeSet::new();
    let mut b: BTreeSet<u32> = BTreeSet::new();
    a.insert(1);
    b.insert(1);
    b.insert(2);
    assert!(a.is_subset(&b));
    assert!(b.is_superset(&a));
    assert!(!a.is_disjoint(&b));
}

// Iteration happens in increasing order
#[ensures(forall<i> 0 <= i && i < result@.len() ==> s@.contains(&result[i]@))]
#[ensures(forall<i, j> 0 <= i && i < j && j < result@.len() ==> result[i]@ < result[j]@)]
pub fn to_sorted_vec(s: &BTreeSet<u64>) -> Vec<u64> {
    let mut res: Vec<u64> = Vec::new();
    let it = s.iter();
    let it0 = snapshot!(it);
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i] == it0@[i])]
    #[invariant(res@.len() == produced.len())]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> res[i] == *produced[i])]
    for x in it {
        res.push(*x);
    }
    res
}

// Elements produced by `intersection` are in both sets
#[ensures(forall<i> 0 <= i && i < result@.len() ==> a@.contains(&result[i]@) && b@.contains(&result[i]@))]
pub fn intersection_vec(a: &BTreeSet<u64>, b: &BTreeSet<u64>) -> Vec<u64> {
    let mut res: Vec<u64> = Vec::new();
    let it = a.intersection(b);
    let it0 = snapshot!(it);
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i] == it0@[i])]
    #[invariant(res@.len() == produced.len())]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> res[i] == *produced[i])]
    for x in it {
        res.push(*x);
    }
    res
}

#[ensures(result@ == xs@)]
pub fn roundtrip_into_iter(xs: BTreeSet<u64>) -> BTreeSet<u64> {
    xs.into_iter().collect()
}
