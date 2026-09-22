import Base

def offset(x: U32) -> U32:
  (x + 1 : U32)

def scale(x: U32) -> U32:
  (x * 3 : U32)

def pipeline(xs: List<U32>) -> List<U32>:
  List.map(~U32, ~U32, ~scale, List.map(~U32, ~U32, ~offset, xs))

def batch(xs: List<U32>) -> List<U32>:
  List.map(~U32, ~U32, ~(x => scale(offset(x))), xs)

def chunks(xs: List<U32>, ys: List<U32>) -> List<U32>:
  a b = batch(xs) batch(ys)
  List.append(&1, U32, a, b)

def decimal(acc: U32, digit: U32) -> U32:
  ((acc * 10 : U32) + digit : U32)

def feed(xs: List<U32>, acc: U32) -> U32:
  List.foldl(~&1, ~U32, ~U32, ~decimal, xs, acc)

def feed_chunks(xs: List<U32>, ys: List<U32>, acc: U32) -> U32:
  feed(ys, feed(xs, acc))

def main() -> List<U32>:
  List.append(&1, U32, chunks([1, 2], [3, 4]), [feed_chunks([1, 2], [3, 4], 0)])

#|[6, 9, 12, 15, 1234]
