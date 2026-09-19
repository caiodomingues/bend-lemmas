# bend-lemmas: List. Base's List.append recurses on its first list and
# List.reverse is List.reverse.go with an accumulator, so a lemma is
# an induction on the first list, and a lemma about reverse is stated
# over reverse.go with the accumulator generalized until the induction
# hypothesis is the goal. Lists are as reusable as their elements
# (Kind(a)), so a generic lemma may hand a list to one lemma only;
# Data lists (&2) get +xs and may compose freely (see the last one).
#
#   bend list.bend

import Base
import ./nat.bend as N

# Append
# ------

def append_nil(a, -A: Kind(a), xs: List<a, A>) -> {List.append(a, A, xs, Nil{}) == xs : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

def append_assoc(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -zs: List<a, A>)
  -> {List.append(a, A, xs, List.append(a, A, ys, zs)) == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(a, A, t, ys, zs) : {h <> List.append(a, A, t, List.append(a, A, ys, zs)) == h <> _ : List<a, A>}
      {==}

def length_append(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>)
  -> {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(a, A, t, ys) : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

# Reverse
# -------

# reverse.go onto acc1, then append acc2, is reverse.go onto their append
def rev_go_app(a, -A: Kind(a), xs: List<a, A>, -acc1: List<a, A>, -acc2: List<a, A>)
  -> {List.append(a, A, List.reverse.go(a, A, xs, acc1), acc2) == List.reverse.go(a, A, xs, List.append(a, A, acc1, acc2)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_go_app(a, A, t, h <> acc1, acc2)

# reverse.go onto acc is the plain reverse, appended to acc
def rev_acc(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>)
  -> {List.append(a, A, List.reverse(a, A, xs), acc) == List.reverse.go(a, A, xs, acc) : List<a, A>}:
  rev_go_app(a, A, xs, Nil{}, acc)

# reversing twice, generalized: the acc side reverses back onto xs
def rev_rev_go(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>)
  -> {List.reverse(a, A, List.reverse.go(a, A, xs, acc)) == List.reverse.go(a, A, acc, xs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_rev_go(a, A, t, h <> acc)

def rev_rev(a, -A: Kind(a), xs: List<a, A>) -> {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}:
  rev_rev_go(a, A, xs, Nil{})

# Length of a reverse: this one needs a second lemma on the same list,
# so it is stated for Data lists (&2), whose +xs may be used twice.
# reverse.go's length is both lengths added, and add_succ moves the
# accumulator's cons out to the front
def length_rev_go(-A: Data, +xs: List<&2, A>, -acc: List<&2, A>)
  -> {List.length(&2, A, List.reverse.go(&2, A, xs, acc)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %N.add_succ(List.length(&2, A, t), List.length(&2, A, acc)) : {List.length(&2, A, List.reverse.go(&2, A, t, h <> acc)) == _ : Nat}
      length_rev_go(A, t, h <> acc)

def length_reverse(-A: Data, +xs: List<&2, A>) -> {List.length(&2, A, List.reverse(&2, A, xs)) == List.length(&2, A, xs) : Nat}:
  %N.add_zero(List.length(&2, A, xs)) : {List.length(&2, A, List.reverse(&2, A, xs)) == _ : Nat}
  length_rev_go(A, xs, Nil{})
