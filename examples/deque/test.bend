# bend-deque: the tests. main normalizes to the line below: two pops
# from the back and three from the front, each end reversed into once
# it runs empty, then the length. A pop's result is matched by a def
# of its own, since a match reads a parameter, never a computed value.
#
#   bend test.bend

import Base
import ./main.bend as Deque

def Dq() -> Data:
  Deque.Deque<&2, U32>

def Popped() -> Data:
  Maybe<&2, Sigma<&2, &2, U32, _ => Dq()>>

# the popped element consed onto the log, or 0 when there was none
def took(r: Popped(), log: List<&2, U32>) -> List<&2, U32> & Dq():
  match r:
    case None{}:
      (0 <> log, Deque.new(&2, U32))
    case Some{p}:
      (x, d) = p
      (x <> log, d)

def pop_back_into(p: List<&2, U32> & Dq()) -> List<&2, U32> & Dq():
  (log, d) = p
  took(Deque.pop_back(&2, U32, d), log)

def pop_front_into(p: List<&2, U32> & Dq()) -> List<&2, U32> & Dq():
  (log, d) = p
  took(Deque.pop_front(&2, U32, d), log)

def report(p: List<&2, U32> & Dq()) -> List<&2, U32>:
  (log, d) = p
  List.append(&2, U32, List.reverse(&2, U32, log), [U32.from_nat(Deque.length(&2, U32, d))])

def main() -> List<&2, U32>:
  d = Deque.from_list(&2, U32, [2, 3])
  d = Deque.push_front(&2, U32, 1, d)   # [1, 2, 3]
  d = Deque.push_back(&2, U32, 4, d)    # [1, 2, 3, 4]
  p = pop_back_into((Nil{}, d))         # 4: back was [4]
  p = pop_back_into(p)                  # 3: back empty, front reversed
  p = pop_front_into(p)                 # 1: front empty, back reversed
  p = pop_front_into(p)                 # 2
  p = pop_front_into(p)                 # 0: empty
  report(p)                             # ... and 0 left

#|[4, 3, 1, 2, 0, 0]
