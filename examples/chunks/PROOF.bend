import Base
import ./main.bend as C
import ./LAWS.bend as Laws
import ../../list.bend as L

def Laws.fused(xs):
  L.map_compose(~U32, ~U32, ~U32, ~C.offset, ~C.scale, xs)

def Laws.chunked(xs, ys):
  L.map_append(~U32, ~U32, ~(x => C.scale(C.offset(x))), xs, ys)

def Laws.resumed(xs, ys, acc):
  L.foldl_append(~&1, ~U32, ~U32, ~C.decimal, xs, ys, acc)
