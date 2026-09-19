# bend-deque: the proofs, by induction on lists. to_list is
# append(front, reverse(back)), so every law comes down to three facts
# from bend-lemmas: append_nil, append_assoc and rev_acc (reversing
# onto an accumulator is a reverse then an append).

import Base
import ./main.bend as D
import ./LAWS.bend as Laws
import ../../list.bend as L

# Laws
# ----

def Laws.from_list_spec(a, A, xs):
  L.append_nil(a, A, xs)

def Laws.push_front_spec(a, A, x, d):
  match d:
    case D.DQ{f, b}:
      {==}

def Laws.push_back_spec(a, A, x, d):
  match d:
    case D.DQ{f, b}:
      %L.rev_acc(a, A, b, [x]) : {List.append(a, A, f, _) == List.append(a, A, List.append(a, A, f, List.reverse.go(a, A, b, Nil{})), [x]) : List<a, A>}
      L.append_assoc(a, A, f, List.reverse.go(a, A, b, Nil{}), [x])

# pop.fin on a list ys pops the head of ys itself
def pop_fin_spec(a, -A: Kind(a), ys: List<a, A>) -> Laws.Pop.front(a, A, ys, D.pop.fin(a, A, ys)):
  match ys:
    case Nil{}:
      {==}
    case h <> t:
      %L.append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

def Laws.pop_front_spec(a, A, d):
  match d:
    case D.DQ{Nil{}, b}:
      pop_fin_spec(a, A, List.reverse(a, A, b))
    case D.DQ{h <> t, b}:
      {==}

# pop_back.fin on a list ys pops the last of its reverse
def pop_back_fin_spec(a, -A: Kind(a), ys: List<a, A>) -> Laws.Pop.back(a, A, List.reverse(a, A, ys), D.pop_back.fin(a, A, ys)):
  match ys:
    case Nil{}:
      {==}
    case h <> t:
      L.rev_acc(a, A, t, [h])

# the empty-back case, generalized over the part of the front already
# reversed into acc, so the step is its own induction hypothesis
def pop_back_nil(a, -A: Kind(a), f: List<a, A>, acc: List<a, A>)
  -> Laws.Pop.back(a, A, List.reverse.go(a, A, acc, List.append(a, A, f, Nil{})), D.pop_back.fin(a, A, List.reverse.go(a, A, f, acc))):
  match f:
    case Nil{}:
      pop_back_fin_spec(a, A, acc)
    case h <> t:
      pop_back_nil(a, A, t, h <> acc)

def Laws.pop_back_spec(a, A, d):
  match d:
    case D.DQ{f, Nil{}}:
      pop_back_nil(a, A, f, Nil{})
    case D.DQ{f, h <> t}:
      %L.rev_acc(a, A, t, [h]) : {List.append(a, A, List.append(a, A, f, List.reverse.go(a, A, t, Nil{})), [h]) == List.append(a, A, f, _) : List<a, A>}
      %L.append_assoc(a, A, f, List.reverse.go(a, A, t, Nil{}), [h]) : {_ == List.append(a, A, f, List.append(a, A, List.reverse.go(a, A, t, Nil{}), [h])) : List<a, A>}
      {==}
