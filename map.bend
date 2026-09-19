# bend-lemmas: Map. Base's Map is a Patricia trie on the bits of the
# key (Map.bit), and Map.get hands the map back beside the value. The
# claims a program needs are stated here; the one proven so far is the
# empty map's, which is what a first set followed by a get computes
# to, plus String's cmp_refl. The general get_set is an open law: it
# needs (a) a well-formedness predicate, WF, saying every key under a
# node's lo/hi has that bit clear/set, (b) set preserves WF, and (c)
# get follows the same bits set did, through Map.bit and Nat.divmod.
# This file is not in all.bend, since an open law fails a check by
# design: `bend map.bend` prints the TODOs.
#
#   bend map.bend

import Base
import ./string.bend as S

# get after set on the empty map: the leaf it made, and its value
def get_set_empty(-V: Data, +d: V, +k: String, +v: V) -> {Map.get(V, d, Map.set(&2, V, MTip{}, k, v), k) == (MLeaf{k, v}, v) : Map<&2, V> & V}:
  %Equal.sym((String & String) & Cmp, String.cmp(k, k), ((k, k), EQ{}), S.cmp_refl(k)) : {Map.get.leaf(V, d, v, _) == (MLeaf{k, v}, v) : Map<&2, V> & V}
  {==}

# LAW: get after set answers the value set, on any map (open)
law get_set:
  for -V : Data
  for +d : V
  for +m : Map<&2, V>
  for +k : String
  for +v : V
  {Pair.snd(Map<&2, V>, V, Map.get(V, d, Map.set(&2, V, m, k, v), k)) == v : V}

# LAW: set leaves other keys alone (open)
law get_set_other:
  for -V : Data
  for +d : V
  for +m : Map<&2, V>
  for +k : String
  for +j : String
  for +v : V
  for ne : {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(k, j))) == False{} : Bool}
  {Pair.snd(Map<&2, V>, V, Map.get(V, d, Map.set(&2, V, m, k, v), j)) == Pair.snd(Map<&2, V>, V, Map.get(V, d, m, j)) : V}
