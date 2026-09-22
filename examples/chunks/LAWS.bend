import Base
import ./main.bend as C

law fused:
  for xs: List<U32>
  {C.pipeline(xs) == C.batch(xs) : List<U32>}

law chunked:
  for xs: List<U32>
  for -ys: List<U32>
  {C.batch(List.append(&1, U32, xs, ys)) == C.chunks(xs, ys) : List<U32>}

law resumed:
  for xs: List<U32>
  for -ys: List<U32>
  for -acc: U32
  {C.feed(List.append(&1, U32, xs, ys), acc) == C.feed_chunks(xs, ys, acc) : U32}
