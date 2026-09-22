import Base
import ../list.bend as L
import ../nat.bend as N

def Fn() -> Type:
  U32 -> U32

def call(f: Fn()) -> U32:
  f(7)

def identity(xs: List<Fn()>)
  -> {List.map(~(Fn()), ~(Fn()), ~(x => x), xs) == xs : List<Fn()>}:
  L.map_identity(~(Fn()), xs)

def length(xs: List<Fn()>)
  -> {List.length(&1, U32, List.map(~(Fn()), ~U32, ~call, xs)) == List.length(&1, Fn(), xs) : Nat}:
  L.length_map(~(Fn()), ~U32, ~call, xs)

def append(xs: List<Fn()>, -ys: List<Fn()>)
  -> {List.map(~(Fn()), ~U32, ~call, List.append(&1, Fn(), xs, ys)) == List.append(&1, U32, List.map(~(Fn()), ~U32, ~call, xs), List.map(~(Fn()), ~U32, ~call, ys)) : List<U32>}:
  L.map_append(~(Fn()), ~U32, ~call, xs, ys)

def closure(x: U32) -> Fn():
  y => (x + y : U32)

def compose(xs: List<U32>)
  -> {List.map(~(Fn()), ~U32, ~call, List.map(~U32, ~(Fn()), ~closure, xs)) == List.map(~U32, ~U32, ~(x => call(closure(x))), xs) : List<U32>}:
  L.map_compose(~U32, ~(Fn()), ~U32, ~closure, ~call, xs)

def keep(x: U32) -> Bool:
  U32.is_even(x)

def filtered(xs: List<&2, U32>, -ys: List<&2, U32>)
  -> {List.filter(~U32, ~keep, List.append(&2, U32, xs, ys)) == List.append(&2, U32, List.filter(~U32, ~keep, xs), List.filter(~U32, ~keep, ys)) : List<&2, U32>}:
  L.filter_append(~U32, ~keep, xs, ys)

def bounded(+xs: List<&2, U32>)
  -> N.LE(List.length(&2, U32, List.filter(~U32, ~keep, xs)), List.length(&2, U32, xs)):
  L.length_filter_le(~U32, ~keep, xs)

def step_left(acc: Fn(), f: Fn()) -> Fn():
  x => f(acc(x))

def left(xs: List<Fn()>, -ys: List<Fn()>, -acc: Fn())
  -> {List.foldl(~&1, ~(Fn()), ~(Fn()), ~step_left, List.append(&1, Fn(), xs, ys), acc) == List.foldl(~&1, ~(Fn()), ~(Fn()), ~step_left, ys, List.foldl(~&1, ~(Fn()), ~(Fn()), ~step_left, xs, acc)) : Fn()}:
  L.foldl_append(~&1, ~(Fn()), ~(Fn()), ~step_left, xs, ys, acc)

def step_right(f: Fn(), acc: Fn()) -> Fn():
  x => f(acc(x))

def right(xs: List<Fn()>, -ys: List<Fn()>, -acc: Fn())
  -> {List.foldr(~&1, ~(Fn()), ~(Fn()), ~step_right, List.append(&1, Fn(), xs, ys), acc) == List.foldr(~&1, ~(Fn()), ~(Fn()), ~step_right, xs, List.foldr(~&1, ~(Fn()), ~(Fn()), ~step_right, ys, acc)) : Fn()}:
  L.foldr_append(~&1, ~(Fn()), ~(Fn()), ~step_right, xs, ys, acc)

def data_fold(xs: List<&2, U32>, -ys: List<&2, U32>, -acc: U32)
  -> {List.foldl(~&2, ~U32, ~U32, ~U32.add, List.append(&2, U32, xs, ys), acc) == List.foldl(~&2, ~U32, ~U32, ~U32.add, ys, List.foldl(~&2, ~U32, ~U32, ~U32.add, xs, acc)) : U32}:
  L.foldl_append(~&2, ~U32, ~U32, ~U32.add, xs, ys, acc)
