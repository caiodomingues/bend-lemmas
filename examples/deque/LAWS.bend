# bend-deque: the laws. The human states them; PROOF.bend must prove
# them. Every law is stated on to_list, the elements front to back: a
# push_front conses, a push_back appends, a pop hands back the end it
# took from, and the rest in order.

import Base
import ./main.bend as D

# Pop.front(xs, r): r is the pop_front of a deque listing xs: None when
# xs is empty, else its head beside a deque listing its tail
def Pop.front(a, -A: Kind(a), xs: List<a, A>, r: Maybe<a, Sigma<a, a, A, _ => D.Deque<a, A>>>) -> Type:
  match r:
    case None{}:
      {xs == Nil{} : List<a, A>}
    case Some{p}:
      (x, d) = p
      {x <> D.to_list(a, A, d) == xs : List<a, A>}

# Pop.back(xs, r): the mirror: r is the last of xs beside a deque
# listing the rest
def Pop.back(a, -A: Kind(a), xs: List<a, A>, r: Maybe<a, Sigma<a, a, A, _ => D.Deque<a, A>>>) -> Type:
  match r:
    case None{}:
      {xs == Nil{} : List<a, A>}
    case Some{p}:
      (x, d) = p
      {List.append(a, A, D.to_list(a, A, d), [x]) == xs : List<a, A>}

# LAW: from_list lists back what it was given
law from_list_spec:
  for -a  : Quant
  for -A  : Kind(a)
  for  xs : List<a, A>
  {D.to_list(a, A, D.from_list(a, A, xs)) == xs : List<a, A>}

# LAW: push_front puts x first
law push_front_spec:
  for -a : Quant
  for -A : Kind(a)
  for -x : A
  for  d : D.Deque<a, A>
  {D.to_list(a, A, D.push_front(a, A, x, d)) == x <> D.to_list(a, A, d) : List<a, A>}

# LAW: push_back puts x last
law push_back_spec:
  for -a : Quant
  for -A : Kind(a)
  for -x : A
  for  d : D.Deque<a, A>
  {D.to_list(a, A, D.push_back(a, A, x, d)) == List.append(a, A, D.to_list(a, A, d), [x]) : List<a, A>}

# LAW: pop_front takes the first element and keeps the rest in order
law pop_front_spec:
  for -a : Quant
  for -A : Kind(a)
  for  d : D.Deque<a, A>
  Pop.front(a, A, D.to_list(a, A, d), D.pop_front(a, A, d))

# LAW: pop_back takes the last element and keeps the rest in order
law pop_back_spec:
  for -a : Quant
  for -A : Kind(a)
  for  d : D.Deque<a, A>
  Pop.back(a, A, D.to_list(a, A, d), D.pop_back(a, A, d))
