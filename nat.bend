# bend-lemmas: Nat. Base defines Nat.add by recursion on its first
# argument and Nat.mul as repeated Nat.add, so every lemma here is an
# induction on that argument. Nat is Data, so a lemma may use a
# number as often as it likes (+x).
#
#   bend nat.bend

import Base

# Addition
# --------

def add_zero(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(+x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def add_comm(+x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      %add_zero(y) : {_ == Nat.add(y, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), add_succ(y, p)) : {1n+Nat.add(p, y) == _ : Nat}
      %add_comm(p, y) : {1n+Nat.add(p, y) == 1n+_ : Nat}
      {==}

def add_assoc(+x: Nat, -y: Nat, -z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(Nat.add(x, y), z) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, y, z) : {1n+Nat.add(p, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

def add_left_comm(+x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  %Equal.sym(Nat, Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(x, y), z), add_assoc(x, y, z)) : {_ == Nat.add(y, Nat.add(x, z)) : Nat}
  %Equal.sym(Nat, Nat.add(y, Nat.add(x, z)), Nat.add(Nat.add(y, x), z), add_assoc(y, x, z)) : {Nat.add(Nat.add(x, y), z) == _ : Nat}
  %add_comm(x, y) : {Nat.add(Nat.add(x, y), z) == Nat.add(_, z) : Nat}
  {==}

# (a + b) + (c + d) == (a + c) + (b + d)
def add_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %add_assoc(a, b, Nat.add(c, d)) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %add_assoc(a, c, Nat.add(b, d)) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %add_left_comm(b, c, d) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == Nat.add(a, _) : Nat}
  {==}

# Subtraction
# -----------

def sub_zero(+x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_self(+x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# (x + y) - y == x
def add_sub(+x: Nat, +y: Nat) -> {Nat.sub(Nat.add(x, y), y) == x : Nat}:
  match y:
    case 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x)) : {Nat.sub(_, 0n) == x : Nat}
      sub_zero(x)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p), add_succ(x, p)) : {Nat.sub(_, 1n+p) == x : Nat}
      add_sub(x, p)

# Multiplication
# --------------

def mul_zero(+x: Nat) -> {Nat.mul(x, 0n) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_one(+x: Nat) -> {Nat.mul(x, 1n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

def mul_succ(+x: Nat, +y: Nat) -> {Nat.mul(x, 1n+y) == Nat.add(x, Nat.mul(x, y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+y), Nat.add(p, Nat.mul(p, y)), mul_succ(p, y)) : {1n+Nat.add(y, _) == 1n+Nat.add(p, Nat.add(y, Nat.mul(p, y))) : Nat}
      %add_left_comm(y, p, Nat.mul(p, y)) : {1n+Nat.add(y, Nat.add(p, Nat.mul(p, y))) == 1n+_ : Nat}
      {==}

def mul_comm(+x: Nat, +y: Nat) -> {Nat.mul(x, y) == Nat.mul(y, x) : Nat}:
  match x:
    case 0n:
      %Equal.sym(Nat, Nat.mul(y, 0n), 0n, mul_zero(y)) : {0n == _ : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(y, 1n+p), Nat.add(y, Nat.mul(y, p)), mul_succ(y, p)) : {Nat.add(y, Nat.mul(p, y)) == _ : Nat}
      %mul_comm(p, y) : {Nat.add(y, Nat.mul(p, y)) == Nat.add(y, _) : Nat}
      {==}

# x * (y + z) == x * y + x * z
def mul_add(+x: Nat, +y: Nat, +z: Nat) -> {Nat.mul(x, Nat.add(y, z)) == Nat.add(Nat.mul(x, y), Nat.mul(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, Nat.add(y, z)), Nat.add(Nat.mul(p, y), Nat.mul(p, z)), mul_add(p, y, z)) : {Nat.add(Nat.add(y, z), _) == Nat.add(Nat.add(y, Nat.mul(p, y)), Nat.add(z, Nat.mul(p, z))) : Nat}
      add_swap(y, z, Nat.mul(p, y), Nat.mul(p, z))

# Order
# -----

# LE(a, b) is the type of proofs of a <= b: Unit when it holds, Empty
# when it does not, so a proof is a value and a refutation a match with
# no cases
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

def le_refl(x: Nat) -> LE(x, x):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

def le_succ(x: Nat) -> LE(x, 1n+x):
  match x:
    case 0n:
      Unit{}
    case 1n+p:
      le_succ(p)


def le_trans(x: Nat, y: Nat, z: Nat, xy: LE(x, y), yz: LE(y, z)) -> LE(x, z):
  match x y z:
    case 0n b c:
      Unit{}
    case 1n+a 0n c:
      match xy:
    case 1n+a 1n+b 0n:
      match yz:
    case 1n+a 1n+b 1n+c:
      le_trans(a, b, c, xy, yz)

# the decider: a comparison that returns its evidence, so a proof can
# branch on the fact the program did
def le_case(x: Nat, y: Nat) -> Or(LE(x, y), LE(y, x)):
  match x y:
    case 0n b:
      Inl{Unit{}}
    case 1n+a 0n:
      Inr{Unit{}}
    case 1n+a 1n+b:
      le_case(a, b)

# Between evidence and Bool: the comparison a program runs and the
# proof a law wants agree
def cmp_refl(+x: Nat) -> {Nat.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

def is_le_of_le(x: Nat, y: Nat, e: LE(x, y)) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      match e:
    case 1n+a 1n+b:
      is_le_of_le(a, b, e)

# the motive that refutes {False{} == True{} : Bool}
def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def le_of_is_le(x: Nat, y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> LE(x, y):
  match x y:
    case 0n 0n:
      Unit{}
    case 0n 1n+b:
      Unit{}
    case 1n+a 0n:
      %e : Bool.disc(_)
      Unit{}
    case 1n+a 1n+b:
      le_of_is_le(a, b, e)
