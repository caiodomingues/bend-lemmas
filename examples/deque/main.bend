# bend-deque: a double-ended queue as two lists, front and back. A push
# conses onto its end, O(1). A pop takes from its end, O(1), unless that
# end is empty: then it reverses the other list into place, O(n). Used
# as a queue or a stack that is O(1) amortized; alternating ends on a
# one-sided deque pays the reversal on every pop. LAWS.bend states the
# order each operation keeps, through to_list; PROOF.bend proves it.
#
#   bend main.bend

import Base

type Deque<a, -A: Kind(a)> is Kind(a):
  DQ{front: List<a, A>, back: List<a, A>}

def new(a, -A: Kind(a)) -> Deque<a, A>:
  DQ{Nil{}, Nil{}}

def push_front(a, -A: Kind(a), x: A, d: Deque<a, A>) -> Deque<a, A>:
  match d:
    case DQ{f, b}:
      DQ{x <> f, b}

def push_back(a, -A: Kind(a), x: A, d: Deque<a, A>) -> Deque<a, A>:
  match d:
    case DQ{f, b}:
      DQ{f, x <> b}

# the pop once the other list has been reversed into this end
def pop.fin(a, -A: Kind(a), xs: List<a, A>) -> Maybe<a, Sigma<a, a, A, _ => Deque<a, A>>>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{(h, DQ{t, Nil{}})}

def pop_front(a, -A: Kind(a), d: Deque<a, A>) -> Maybe<a, Sigma<a, a, A, _ => Deque<a, A>>>:
  match d:
    case DQ{Nil{}, b}:
      pop.fin(a, A, List.reverse(a, A, b))
    case DQ{h <> t, b}:
      Some{(h, DQ{t, b})}

# the mirror of pop.fin: the rest goes to the back
def pop_back.fin(a, -A: Kind(a), xs: List<a, A>) -> Maybe<a, Sigma<a, a, A, _ => Deque<a, A>>>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{(h, DQ{Nil{}, t})}

def pop_back(a, -A: Kind(a), d: Deque<a, A>) -> Maybe<a, Sigma<a, a, A, _ => Deque<a, A>>>:
  match d:
    case DQ{f, Nil{}}:
      pop_back.fin(a, A, List.reverse(a, A, f))
    case DQ{f, h <> t}:
      Some{(h, DQ{f, t})}

def is_empty(a, -A: Kind(a), d: Deque<a, A>) -> Bool:
  match d:
    case DQ{Nil{}, Nil{}}:
      True{}
    case DQ{f, b}:
      False{}

def length(a, -A: Kind(a), d: Deque<a, A>) -> Nat:
  match d:
    case DQ{f, b}:
      Nat.add(List.length(a, A, f), List.length(a, A, b))

# the elements in order, front to back: the spec every law is stated on
def to_list(a, -A: Kind(a), d: Deque<a, A>) -> List<a, A>:
  match d:
    case DQ{f, b}:
      List.append(a, A, f, List.reverse(a, A, b))

def from_list(a, -A: Kind(a), xs: List<a, A>) -> Deque<a, A>:
  DQ{xs, Nil{}}

def main() -> List<&2, U32>:
  d = from_list(&2, U32, [2, 3])
  d = push_front(&2, U32, 1, d)
  d = push_back(&2, U32, 4, d)
  to_list(&2, U32, d)
