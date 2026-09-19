# bend-lemmas

Proven lemmas for [Bend](https://bend-lang.com) 2: the facts about `Nat`,
`List` and `Bool` that every `PROOF.bend` ends up re-proving. Base ships six
(`Equal.cong`, `Equal.sym`, `Equal.trans` and the primitives); this is the rest.

```python
import Base
import ./list.bend as L

law my_claim:
  for xs: List<&2, U32>
  {List.reverse(&2, U32, List.reverse(&2, U32, xs)) == xs : List<&2, U32>}

def my_claim(xs):
  L.rev_rev(&2, U32, xs)
```

Every lemma is a `def` whose type is the claim, so it is applied like a
function and its result is a proof. `bend all.bend` checks the whole library.

## Lemmas

| `nat.bend` | claim |
| --- | --- |
| `add_zero(x)` | `Nat.add(x, 0n) == x` |
| `add_succ(x, y)` | `Nat.add(x, 1n+y) == 1n+Nat.add(x, y)` |
| `add_comm(x, y)` | `Nat.add(x, y) == Nat.add(y, x)` |
| `add_assoc(x, y, z)` | `Nat.add(x, Nat.add(y, z)) == Nat.add(Nat.add(x, y), z)` |
| `mul_zero(x)` | `Nat.mul(x, 0n) == 0n` |
| `mul_one(x)` | `Nat.mul(x, 1n) == x` |
| `LE(a, b)` | the type of proofs of `a <= b` (`Unit` or `Empty`) |
| `le_refl(x)` | `LE(x, x)` |
| `le_succ(x)` | `LE(x, 1n+x)` |
| `le_trans(x, y, z, xy, yz)` | `LE(x, z)` |
| `le_case(x, y)` | `Or(LE(x, y), LE(y, x))`: a comparison that returns its evidence |

| `list.bend` (generic in the element kind) | claim |
| --- | --- |
| `append_nil(a, A, xs)` | `List.append(xs, Nil{}) == xs` |
| `append_assoc(a, A, xs, ys, zs)` | `append(xs, append(ys, zs)) == append(append(xs, ys), zs)` |
| `length_append(a, A, xs, ys)` | `length(append(xs, ys)) == Nat.add(length(xs), length(ys))` |
| `rev_go_app(a, A, xs, acc1, acc2)` | `append(reverse.go(xs, acc1), acc2) == reverse.go(xs, append(acc1, acc2))` |
| `rev_acc(a, A, xs, acc)` | `append(reverse(xs), acc) == reverse.go(xs, acc)` |
| `rev_rev_go(a, A, xs, acc)` | `reverse(reverse.go(xs, acc)) == reverse.go(acc, xs)` |
| `rev_rev(a, A, xs)` | `reverse(reverse(xs)) == xs` |

| `list.bend` (Data elements, `&2`) | claim |
| --- | --- |
| `length_rev_go(A, xs, acc)` | `length(reverse.go(xs, acc)) == Nat.add(length(xs), length(acc))` |
| `length_reverse(A, xs)` | `length(reverse(xs)) == length(xs)` |

| `bool.bend` | claim |
| --- | --- |
| `not_not(b)` | `Bool.not(Bool.not(b)) == b` |
| `and_true(b)`, `and_false(b)`, `or_false(b)`, `or_true(b)` | the units and absorbers |
| `and_comm(a, b)`, `or_comm(a, b)` | commutativity |
| `and_assoc(a, b, c)`, `or_assoc(a, b, c)` | associativity |
| `not_and(a, b)`, `not_or(a, b)` | de Morgan |

## How the lemmas are shaped

Bend has no tactics and its proofs are affine, so these rules set the shape
of every lemma here; follow them to add one.

- **A rewrite goes right to left.** `%e : P` with `e : {a == b : T}` needs `P`
  to be the goal with `_` on `b`, and turns those spots into `a`. When the
  goal holds `a` instead, pass `Equal.sym(T, a, b, e)` (it accepts Data types).
- **A generic list goes to one lemma.** A `List<a, A>` variable is affine, so
  a lemma's step may consume it once: state the lemma so the induction
  hypothesis *is* the goal, generalizing the accumulator (`rev_rev_go`). A
  claim that needs two lemmas on the same list is stated for Data lists
  (`-A: Data`, `+xs: List<&2, A>`), which may be used freely (`length_reverse`).
- **An erased parameter cannot be matched.** The induction variable is live
  and comes first, so the termination check sees it shrink.
- **No lemmas about `List.map`, `List.filter` or the folds.** They are
  templates, and a law cannot quantify over a template argument ("a def
  parameter is not comptime"). Prove such facts per concrete function.
- **Predicates are types, deciders return evidence.** `LE(a, b)` is `Unit` or
  `Empty`; `le_case` answers `Or(LE(x, y), LE(y, x))`, so a proof can branch
  on the comparison the program made (the pattern of `demos/proof_insertion_sort`).

## Run

    bend all.bend      # All terms check.

On Windows, `bun <bend checkout>/bend2/main.ts all.bend` does the same natively.
