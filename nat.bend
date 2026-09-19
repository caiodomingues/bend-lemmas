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
