/-
# A037223 — Pérez Herrero's totient-product formula is false

## OEIS source (retrieved with `oeis show A037223`, 2026-10-21)

```
NAME:     Number of solutions to non-attacking rooks problem on n X n board
          that are invariant under 180-degree rotation.
TERMS:    1,1,2,2,8,8,48,48,384,384,3840,3840,46080,46080,645120,645120,...
FORMULA:  a(2n) = a(2n+1) = n!*2^n.
COMMENT (the conjecture, with the later retraction in the same comment):
  Conjecture: a(n) = Product_{i=1..n and phi(i)<=floor(i/2)} i.
  - _Enrique Pérez Herrero_, May 31 2012. This conjecture is WRONG,
  counterexample is n=105. - _Vaclav Kotesovec_, Sep 07 2012
```

## Status

Known false: the entry itself records Kotesovec's counterexample `n = 105`.
This module kernel-checks that refutation.

## Mathematics

For `i ≤ 104` the condition `φ(i) ≤ ⌊i/2⌋` holds exactly for the even `i`, so
the product equals `2·4·…·(2⌊n/2⌋) = 2^⌊n/2⌋ ⌊n/2⌋!`.  The first odd `i` with
`φ(i) ≤ ⌊i/2⌋` is `105 = 3·5·7`, where `φ(105) = 48 ≤ 52`.  Hence the product
at `n = 105` is `105` times the product at `n = 104`, while
`a(105) = a(104)`.  The argument below uses only these two facts, so it
refutes the conjecture for every sequence with `a(104) = a(105)`, in
particular for the rook-count definition (centre row of the odd board is
forced to its centre square).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A037223Refutation

open Nat

/-- The rook-count definition of A037223: the number of permutations `σ` of
`Fin n` (non-attacking rook placements on an `n × n` board) invariant under
180-degree rotation, i.e. `σ (n-1-i) = n-1-σ(i)` for every `i`. -/
def rookSym (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i, σ (Fin.rev i) = Fin.rev (σ i)}

/-- A037223 via the entry's closed form `a(2m) = a(2m+1) = m! * 2^m`. -/
def a (n : ℕ) : ℕ := (n / 2)! * 2 ^ (n / 2)

/-- Pérez Herrero's product: `∏_{1 ≤ i ≤ n, φ(i) ≤ ⌊i/2⌋} i`
(`i / 2` is natural-number floor division). -/
def perezProduct (n : ℕ) : ℕ :=
  ∏ i ∈ (Finset.Icc 1 n).filter (fun i => φ i ≤ i / 2), i

/-! ## Ground truth against the listed terms -/

example : (List.range 5).map rookSym = [1, 1, 2, 2, 8] := by decide

example : (List.range 16).map a =
    [1, 1, 2, 2, 8, 8, 48, 48, 384, 384, 3840, 3840, 46080, 46080, 645120, 645120] := by
  decide

example : (List.range 12).map perezProduct =
    [1, 1, 2, 2, 8, 8, 48, 48, 384, 384, 3840, 3840] := by
  decide

/-! ## The conjecture -/

/-- **Pérez Herrero's conjecture (A037223, May 31 2012).**
Verbatim: "Conjecture: a(n) = Product_{i=1..n and phi(i)<=floor(i/2)} i." -/
def Conjecture : Prop := ∀ n : ℕ, a n = perezProduct n

/-- `105 = 3·5·7` satisfies `φ(105) = 48 ≤ ⌊105/2⌋ = 52`. -/
theorem totient_105_le : φ 105 ≤ 105 / 2 := by decide

/-- The product picks up the factor `105` at `n = 105`. -/
theorem perezProduct_105 : perezProduct 105 = perezProduct 104 * 105 := by
  unfold perezProduct
  rw [Finset.prod_filter, Finset.prod_filter,
    Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 104 + 1), if_pos totient_105_le]

/-- The product is always positive (all factors are `≥ 1`). -/
theorem perezProduct_pos (n : ℕ) : 0 < perezProduct n := by
  unfold perezProduct
  refine Finset.prod_pos fun i hi => ?_
  have hmem : i ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hi).1
  exact (Finset.mem_Icc.mp hmem).1

/-- No sequence `b` with `b 104 = b 105` equals Pérez Herrero's product for
all `n`; the product at `105` is `105` times the product at `104`. -/
theorem not_forall_eq_perezProduct_of_eq (b : ℕ → ℕ) (hb : b 104 = b 105) :
    ¬ ∀ n, b n = perezProduct n := by
  intro h
  have h104 := h 104
  have h105 := h 105
  have hpos := perezProduct_pos 104
  rw [perezProduct_105, ← hb, h104] at h105
  omega

/-- **Refutation of Pérez Herrero's conjecture for A037223.**
Counterexample `n = 105` (Kotesovec, Sep 07 2012): `a(105) = a(104) = 52!·2^52`,
but `φ(105) = 48 ≤ 52` puts `105` in the product, which therefore equals
`105 · 52! · 2^52`.  The intended statement is the product of the even
`i ≤ n`, i.e. `a(n) = ∏_{i=1..⌊n/2⌋} 2i`, which the formula section of the entry
records. -/
theorem conjecture_false : ¬ Conjecture :=
  not_forall_eq_perezProduct_of_eq a (by decide)

/-- The rook-count definition also refutes the identity at `n = 105`, given
the (unproved here) centre-forcing identity `rookSym 104 = rookSym 105`. -/
theorem rookSym_not_forall_eq_perezProduct (h : rookSym 104 = rookSym 105) :
    ¬ ∀ n, rookSym n = perezProduct n :=
  not_forall_eq_perezProduct_of_eq rookSym h

set_option maxRecDepth 100000 in
/-- **Agreement below the counterexample.** Pérez Herrero's identity holds for
every `n ≤ 104` (there `φ(i) ≤ ⌊i/2⌋` selects exactly the even `i`), so
`n = 105` is the least counterexample. -/
theorem a_eq_perezProduct_of_le (n : ℕ) (hn : n ≤ 104) : a n = perezProduct n := by
  interval_cases n <;> decide

end Candidates.A037223Refutation
