# bend-lemmas

Proven lemmas for [Bend](https://bend-lang.com) 2: the facts about `Nat`,
`List` and `Bool` that every `PROOF.bend` ends up re-proving. Base ships
`Equal.cong`, `Equal.sym`, `Equal.trans`, `Word.add_comm` and `U32.add_comm`;
this is the rest.

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
| `add_succ(x, -y)` | `Nat.add(x, 1n+y) == 1n+Nat.add(x, y)` |
| `add_comm(x, y)` | `Nat.add(x, y) == Nat.add(y, x)` |
| `add_assoc(x, -y, -z)` | `Nat.add(x, Nat.add(y, z)) == Nat.add(Nat.add(x, y), z)` |
| `add_left_comm(x, y, z)` | `Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z))` |
| `add_swap(a, b, c, d)` | `Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d))` |
| `sub_zero(x)`, `sub_self(x)` | `Nat.sub(x, 0n) == x`, `Nat.sub(x, x) == 0n` |
| `add_sub(x, y)` | `Nat.sub(Nat.add(x, y), y) == x` |
| `mul_zero(x)` | `Nat.mul(x, 0n) == 0n` |
| `mul_one(x)` | `Nat.mul(x, 1n) == x` |
| `mul_succ(x, y)` | `Nat.mul(x, 1n+y) == Nat.add(x, Nat.mul(x, y))` |
| `mul_comm(x, y)` | `Nat.mul(x, y) == Nat.mul(y, x)` |
| `mul_add(x, y, z)` | `Nat.mul(x, Nat.add(y, z)) == Nat.add(Nat.mul(x, y), Nat.mul(x, z))` |
| `LE(a, b)` | the type of proofs of `a <= b` (`Unit` or `Empty`) |
| `le_refl(x)` | `LE(x, x)` |
| `le_succ(x)` | `LE(x, 1n+x)` |
| `le_trans(x, y, z, xy, yz)` | `LE(x, z)` |
| `le_case(x, y)` | `Or(LE(x, y), LE(y, x))`: a comparison that returns its evidence |
| `cmp_refl(x)` | `Nat.cmp(x, x) == EQ{}` |
| `is_le_of_le(x, y, e)` | `LE(x, y)` gives `Nat.is_le(x, y) == True{}` |
| `le_of_is_le(x, y, e)` | `Nat.is_le(x, y) == True{}` gives `LE(x, y)`: a program's check feeds a proof |

| `list.bend` (generic in the element kind) | claim |
| --- | --- |
| `append_nil(a, A, xs)` | `List.append(xs, Nil{}) == xs` |
| `append_assoc(a, A, xs, ys, zs)` | `append(xs, append(ys, zs)) == append(append(xs, ys), zs)` |
| `length_append(a, A, xs, ys)` | `length(append(xs, ys)) == Nat.add(length(xs), length(ys))` |
| `rev_go_app(a, A, xs, acc1, acc2)` | `append(reverse.go(xs, acc1), acc2) == reverse.go(xs, append(acc1, acc2))` |
| `rev_acc(a, A, xs, acc)` | `append(reverse(xs), acc) == reverse.go(xs, acc)` |
| `rev_rev_go(a, A, xs, acc)` | `reverse(reverse.go(xs, acc)) == reverse.go(acc, xs)` |
| `rev_rev(a, A, xs)` | `reverse(reverse(xs)) == xs` |
| `length_take_le(a, A, xs, n)` | `LE(length(take(xs, n)), n)` |
| `length_zip_le(a, A, b, B, xs, ys)` | `LE(length(zip(xs, ys)), length(xs))` |

| `list.bend` (Data elements, `&2`) | claim |
| --- | --- |
| `length_rev_go(A, xs, acc)` | `length(reverse.go(xs, acc)) == Nat.add(length(xs), length(acc))` |
| `length_reverse(A, xs)` | `length(reverse(xs)) == length(xs)` |
| `take_drop(A, xs, n)` | `append(take(xs, n), drop(xs, n)) == xs` |
| `length_replicate(A, n, x)` | `length(replicate(n, x)) == n` |
| `length_range_go(n, acc)`, `length_range(n)` | `length(range(n)) == n` |

| `list.bend` (Nat lists) | claim |
| --- | --- |
| `In(x, xs)` | the type of proofs that `x` is in `xs` |
| `in_append_l(x, xs, ys, e)`, `in_append_r(x, xs, ys, e)` | membership survives `append`, from either side |
| `count(x, xs)`, `bump(b, n)` | occurrences of `x`, as in `demos/proof_insertion_sort` |
| `count_append(x, xs, ys)` | `count(x, append(xs, ys)) == Nat.add(count(x, xs), count(x, ys))` |
| `bump_add(b, n, m)`, `bump_swap(a, b, n)` | `bump` moves through `add` and commutes with itself |
| `Perm(xs, ys)` | `@x: Nat -> {count(x, xs) == count(x, ys)}`: a permutation, by counts |
| `perm_refl`, `perm_sym`, `perm_trans` | an equivalence |
| `perm_swap(a, b, t)`, `perm_cons(h, xs, ys, p)` | `a <> b <> t ~ b <> a <> t`; a shared head keeps a permutation |

| `string.bend` | claim |
| --- | --- |
| `append_nil(s)`, `append_assoc(a, b, c)`, `concat_assoc(a, b, c)` | as for lists; `++` is `String.append` |
| `length_append(a, b)` | `String.length(a ++ b) == Nat.add(String.length(a), String.length(b))` |
| `bool_cmp_refl`, `word_cmp_refl(n, w)`, `u32_cmp_refl(x)`, `char_cmp_refl(c)` | a value compares `EQ{}` with itself, from the bits up |
| `cmp_refl(s)` | `String.cmp(s, s) == ((s, s), EQ{})` |

| `map.bend` (not in `all.bend`) | claim |
| --- | --- |
| `get_set_empty(V, d, k, v)` | `Map.get(d, Map.set(MTip{}, k, v), k) == (MLeaf{k, v}, v)` |
| `get_set` | **open**: `Map.get` after `Map.set` answers the value, on any map |
| `get_set_other` | **open**: `Map.set` leaves other keys alone |

The two open laws need a well-formedness predicate on the trie, its
preservation by `set`, and that `get` follows the bits `set` did through
`Map.bit`. `bend map.bend` reports them as TODOs by design.

| `bool.bend` | claim |
| --- | --- |
| `not_not(b)` | `Bool.not(Bool.not(b)) == b` |
| `and_true(b)`, `and_false(b)`, `or_false(b)`, `or_true(b)` | the units and absorbers |
| `and_comm(a, b)`, `or_comm(a, b)` | commutativity |
| `and_assoc(a, b, c)`, `or_assoc(a, b, c)` | associativity |
| `not_and(a, b)`, `not_or(a, b)` | de Morgan |
| `xor_false(b)`, `xor_true(b)`, `xor_comm(a, b)` | xor's unit, its negation and commutativity |

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
- **An erased parameter cannot be matched.** The induction variable is the
  first live parameter (erased ones like `a, -A` may precede it), so the
  termination check, which reads live arguments left to right, sees it shrink.
  A parameter that only reaches the type and the recursive call is erased
  (`add_succ(x, -y)`), so passing it costs the caller no live use.
- **No lemmas about `List.map`, `List.filter` or the folds.** They are
  templates, and a law cannot quantify over a template argument ("a def
  parameter is not comptime"). Prove such facts per concrete function.
- **Predicates are types, deciders return evidence.** `LE(a, b)` is `Unit` or
  `Empty`; `le_case` answers `Or(LE(x, y), LE(y, x))`, so a proof can branch
  on the comparison the program made (the pattern of `demos/proof_insertion_sort`).

## Example

`examples/deque/` is a double-ended queue whose five laws are proven with
this library: its `PROOF.bend` went from 106 lines with four local lemmas to
69 importing `list.bend`. It is also the drift check: `bend examples/deque/PROOF.bend`
fails if a lemma here changes shape.

## Run

    bend all.bend                    # All terms check.
    bend examples/deque/PROOF.bend   # All terms check.
    bend map.bend                    # Error: 2 TODOs found (the open laws)

On Windows, `bun <bend checkout>/bend2/main.ts all.bend` does the same natively.
