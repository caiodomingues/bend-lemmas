# bend-lemmas: String. Base's String is its own type (SNil, SCon), not
# a List of Char, and String.append recurses on its first string, so
# the list proofs carry over one for one. String is Data.
#
#   bend string.bend

import Base
import ./nat.bend as N

def append_nil(+s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %append_nil(t) : {SCon{h, String.append(t, SNil{})} == SCon{h, _} : String}
      {==}

def append_assoc(+a: String, +b: String, +c: String) -> {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %append_assoc(t, b, c) : {SCon{h, String.append(t, String.append(b, c))} == SCon{h, _} : String}
      {==}

def length_append(+a: String, +b: String) -> {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %length_append(t, b) : {1n+String.length(String.append(t, b)) == 1n+_ : Nat}
      {==}

# ++ is String.append: the operator form of the same facts
def concat_assoc(+a: String, +b: String, +c: String) -> {(a ++ (b ++ c)) == ((a ++ b) ++ c) : String}:
  append_assoc(a, b, c)

# Comparison of a value with itself, from the bits up: Word, U32, Char,
# String. String.cmp hands both strings back beside the verdict.
def bool_cmp_refl(+b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def word_cmp_refl(n: Nat, +w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          bool_cmp_refl(b)

def u32_cmp_refl(+x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      word_cmp_refl(32n, w)

def char_cmp_refl(+c: Char) -> {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}:
  match c:
    case Chr{x}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_cmp_refl(x)) : {((Chr{x}, Chr{x}), _) == ((Chr{x}, Chr{x}), EQ{}) : (Char & Char) & Cmp}
      {==}

def cmp_refl(+s: String) -> {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym((Char & Char) & Cmp, Char.cmp(h, h), ((h, h), EQ{}), char_cmp_refl(h)) : {String.cmp.fin(t, t, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      %Equal.sym((String & String) & Cmp, String.cmp(t, t), ((t, t), EQ{}), cmp_refl(t)) : {String.cmp.rec(h, h, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      {==}
