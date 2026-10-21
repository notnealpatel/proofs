/-
# A267610 — Wiseman: `a(n) = A267700(n) - n` (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A267610`,
## `oeis show A267700`, `oeis show A160720` and the live entries
## https://oeis.org/A267610/internal, https://oeis.org/A267700/internal)

```
A267610
NAME:     Total number of OFF (white) cells after n iterations of the
          "Rule 182" elementary cellular automaton starting with a single
          ON (black) cell.
OFFSET:   0,3
TERMS:    0,0,2,2,4,6,12,12,14,16,22,24,30,36,50,50,52,54,60,62,68,74,88,...
PROGRAM (Mathematica, the counting convention): row k of the evolution is
          truncated to the 2k+1 cells of the light cone, the OFF cells of
          each truncated row are counted, and the counts of rows 0..n are
          summed.
FORMULA (the conjecture):
          Conjecture: a(n) = A267700(n) - n. - _Gus Wiseman_, Mar 30 2019
FORMULA:  G.f.: (1/x)*(A(x)/x - (x+1)/(1-x)^2) where A(x) is the g.f. for
          A006046 (conjectured). - _John Tyler Rascoe_, Jul 08 2024
AUTHOR:   _Robert Price_, Jan 18 2016

A267700
NAME:     "Tree" sequence in a 90-degree sector of the cellular automaton
          of A160720.
OFFSET:   0,3
TERMS:    0,1,2,5,6,9,12,19,20,23,26,33,36,43,50,65,66,69,72,79,82,89,...
FORMULA:  a(n) = (A160720(n+1) - 1)/4.
FORMULA:  (Conjecture) a(n) = A267610(n) + n. - _Gus Wiseman_, Mar 31 2019
AUTHOR:   _Omar E. Pol_, Jan 19 2016

A160720
NAME:     Number of "ON" cells at n-th stage in 2-dimensional cellular
          automaton (see Comments for precise definition).
TERMS:    0,1,5,9,21,25,37,49,77,81,93,105,133,145,173,201,261,265,...
COMMENT:  We work on the vertices of the square grid Z^2, and define the
          neighbors of a cell to be the four closest cells along the
          diagonals.  We start at stage 0 with all cells in OFF state.  At
          stage 1, we turn ON a single cell at the origin.  Once a cell is
          ON it stays ON.  At each subsequent stage, a cell in turned ON if
          exactly one of its neighboring cells that are no further from the
          origin is ON.
```

No later comment in either entry retracts the conjecture.  This module
**refutes** it.

## Status (refuted, kernel-checked)

Both entries have offset 0.  The identity holds at `n = 0, 1` but fails at
`n = 2`: `A267610(2) = 2`, while `A267700(2) - 2 = 2 - 2 = 0`.  The
intended statement is the index-shifted form
`A267610(n) = A267700(n+1) - (n+1)`, checked here for `n ≤ 2` only.

Re-validation (python, 2026-10-21): exact simulation of Rule 182 and of the
A160720 automaton reproduces the listed terms of A267610, A160720 and
A267700 (n < 40); the literal identity fails for `n = 2, 4, 5, 6, 8, ...`;
the shifted form holds for all `n < 39`; and `A267700(n)` equals
`∑_{k ≤ n} (2^{s₂(k)} - 1)` for `n < 44` (`s₂` = binary digit sum).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A267610Refutation

/-! ## Definition layer: Rule 182 and A267610 -/

/-- The elementary cellular automaton with Wolfram code `r`: a cell whose
left neighbour, own state and right neighbour are `l, c, x` takes the state
given by bit `4l + 2c + x` of `r`. -/
def ruleStep (r : ℕ) (l c x : Bool) : Bool :=
  Nat.testBit r (4 * l.toNat + 2 * c.toNat + x.toNat)

/-- The Wolfram rule table of Rule 182 (`182 = 0b10110110`), listed for the
neighbourhoods `000, 001, 010, 011, 100, 101, 110, 111`. -/
example :
    [ruleStep 182 false false false, ruleStep 182 false false true,
      ruleStep 182 false true false, ruleStep 182 false true true,
      ruleStep 182 true false false, ruleStep 182 true false true,
      ruleStep 182 true true false, ruleStep 182 true true true] =
    [false, true, true, false, true, true, false, true] := by decide

/-- The state of cell `i` after `n` steps of Rule 182 started from a single
ON cell at `0` on an otherwise OFF line (`true` = ON). -/
def ca182 : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => ruleStep 182 (ca182 n (i - 1)) (ca182 n i) (ca182 n (i + 1))

/-- The number of OFF cells in row `n` of the light cone, i.e. among the
`2n + 1` cells `-n ≤ i ≤ n`.  (Marked `noncomputable` only because the
elaborated order instance on `ℤ` passes through a noncomputable structure;
the kernel evaluates it.) -/
noncomputable def offCount (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n).filter (fun i => ca182 n i = false)).card

/-- A267610(n): the total number of OFF cells in rows `0, …, n` of the light
cone of Rule 182 started from a single ON cell. -/
noncomputable def a267610 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), offCount k

/-- Ground truth: the first eight listed terms of A267610. -/
example : (List.range 8).map a267610 = [0, 0, 2, 2, 4, 6, 12, 12] := by decide

/-! ## Definition layer: the automaton of A160720 and A267700 -/

/-- The four diagonal neighbour offsets of a cell of `ℤ²`. -/
def diag : List (ℤ × ℤ) := [(-1, -1), (-1, 1), (1, -1), (1, 1)]

/-- Squared Euclidean distance of a cell from the origin. -/
def normSq (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + p.2 ^ 2

/-- The state of cell `p` at stage `n` of the A160720 automaton: nothing is
ON at stage `0`; only the origin at stage `1`; afterwards a cell stays ON once
ON, and an OFF cell turns ON when exactly one of its four diagonal neighbours
that are no further from the origin is ON. -/
def on160720 : ℕ → ℤ × ℤ → Bool
  | 0 => fun _ => false
  | 1 => fun p => decide (p = (0, 0))
  | n + 2 => fun p => on160720 (n + 1) p ||
      decide (((diag.map (fun d => p + d)).filter
        (fun q => decide (normSq q ≤ normSq p) && on160720 (n + 1) q)).length = 1)

/-- The square `[-n, n]²` of `ℤ²`. -/
noncomputable def box (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

/-- Every cell that is ON at stage `n` of the A160720 automaton lies in the
square `[-n, n]²`. -/
theorem mem_box_of_on160720 :
    ∀ (n : ℕ) (p : ℤ × ℤ), on160720 n p = true → p ∈ box n
  | 0, p, h => by simp [on160720] at h
  | 1, p, h => by
      have hp : p = (0, 0) := by simpa [on160720] using h
      subst hp
      simp [box]
  | n + 2, p, h => by
      simp only [on160720, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hold | hone
      · have hp := mem_box_of_on160720 (n + 1) p hold
        simp only [box, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        push_cast at hp ⊢
        omega
      · obtain ⟨q, hq⟩ : ∃ q, q ∈ (diag.map (fun d => p + d)).filter
            (fun q => decide (normSq q ≤ normSq p) && on160720 (n + 1) q) := by
          rcases hl : (diag.map (fun d => p + d)).filter
            (fun q => decide (normSq q ≤ normSq p) && on160720 (n + 1) q) with _ | ⟨q, _⟩
          · rw [hl] at hone
            simp at hone
          · exact ⟨q, by simp⟩
        rw [List.mem_filter, Bool.and_eq_true] at hq
        obtain ⟨hqmem, -, hqon⟩ := hq
        have hqbox := mem_box_of_on160720 (n + 1) q hqon
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqmem
        simp only [diag, List.mem_cons, List.not_mem_nil, or_false] at hd
        simp only [box, Finset.mem_product, Finset.mem_Icc, Prod.fst_add,
          Prod.snd_add] at hqbox ⊢
        push_cast at hqbox ⊢
        rcases hd with rfl | rfl | rfl | rfl <;> simp only at hqbox ⊢ <;> omega

/-- A160720(n): the number of ON cells of `ℤ²` at stage `n` (counted over the
whole plane). -/
noncomputable def a160720 (n : ℕ) : ℕ := Set.ncard {p : ℤ × ℤ | on160720 n p = true}

/-- The ON cells at stage `n` can be counted inside the square `[-n, n]²`. -/
theorem a160720_eq_card (n : ℕ) :
    a160720 n = ((box n).filter (fun p => on160720 n p = true)).card := by
  rw [a160720, ← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, iff_and_self]
  exact mem_box_of_on160720 n p

/-- Ground truth: the first five listed terms `0, 1, 5, 9, 21` of A160720
(kernel evaluation of the automaton inside the square `[-n, n]²`). -/
theorem a160720_le_four : a160720 0 = 0 ∧ a160720 1 = 1 ∧ a160720 2 = 5 ∧
    a160720 3 = 9 ∧ a160720 4 = 21 := by
  simp only [a160720_eq_card]
  decide +kernel

/-- A267700(n) = (A160720(n+1) - 1)/4, the defining formula printed in the
entry.  The `ℕ` subtraction and division are exact on every value used here
(`A160720(n+1) ≡ 1 mod 4`, checked below for `n ≤ 3`). -/
noncomputable def a267700 (n : ℕ) : ℕ := (a160720 (n + 1) - 1) / 4

/-- Ground truth: the first four listed terms `0, 1, 2, 5` of A267700. -/
theorem a267700_le_three :
    a267700 0 = 0 ∧ a267700 1 = 1 ∧ a267700 2 = 2 ∧ a267700 3 = 5 := by
  obtain ⟨-, h1, h2, h3, h4⟩ := a160720_le_four
  simp only [a267700, h1, h2, h3, h4]
  norm_num

/-- The `ℕ` subtraction and division in `a267700` are exact for `n ≤ 3`. -/
example : ∀ n < 4, 4 * a267700 n + 1 = a160720 (n + 1) := by
  obtain ⟨-, h1, h2, h3, h4⟩ := a160720_le_four
  obtain ⟨g0, g1, g2, g3⟩ := a267700_le_three
  intro n hn
  interval_cases n <;> simp [h1, h2, h3, h4, g0, g1, g2, g3]

/-- Cross-check against the independent description of A267700 as partial
sums of `2^{s₂(k)} - 1` (A038573, confirmed by Sloane), for `n ≤ 3`: the
refutation does not hinge on the reading of the 2D automaton. -/
example :
    ∀ n < 4, a267700 n = ∑ k ∈ Finset.range (n + 1), (2 ^ (Nat.digits 2 k).sum - 1) := by
  obtain ⟨g0, g1, g2, g3⟩ := a267700_le_three
  intro n hn
  interval_cases n <;> simp [g0, g1, g2, g3, Finset.sum_range_succ]

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A267610, Gus Wiseman, Mar 30 2019).**

Verbatim: "Conjecture: a(n) = A267700(n) - n."

Formalized at the common offset `0` of both entries, with the subtraction
taken in `ℤ` (cast before subtracting). -/
def Conjecture : Prop := ∀ n : ℕ, (a267610 n : ℤ) = (a267700 n : ℤ) - n

/-! ## The counterexample `n = 2` -/

/-- `A267610(2) = 2`: rows `0, 1, 2` are `1`, `111`, `10101`. -/
theorem a267610_two : a267610 2 = 2 := by decide

/-- `A267700(2) = 2`, since `A160720(3) = 9`. -/
theorem a267700_two : a267700 2 = 2 := a267700_le_three.2.2.1

/-- **Wiseman's conjecture is false**: at `n = 2`, `A267610(2) = 2` but
`A267700(2) - 2 = 0`.  (It holds at `n = 0, 1`.)  The intended identity is
almost certainly the index-shifted `A267610(n) = A267700(n+1) - (n+1)`; see
`shifted_identity_of_le_two`. -/
theorem a267610_conjecture_false : ¬ Conjecture := by
  intro hconj
  have h2 := hconj 2
  rw [a267610_two, a267700_two] at h2
  norm_num at h2

/-! ## The shifted identity on small indices -/

/-- The probably intended form `A267610(n) = A267700(n+1) - (n+1)` holds for
`n ≤ 2` (kernel check).  The general statement, which follows from
`#OFF cells in row n = 2^{s₂(n+1)} - 2` and Glaisher's theorem, is not proved
here. -/
theorem shifted_identity_of_le_two :
    ∀ n ≤ 2, (a267610 n : ℤ) = (a267700 (n + 1) : ℤ) - (n + 1 : ℕ) := by
  obtain ⟨-, g1, g2, g3⟩ := a267700_le_three
  have f0 : a267610 0 = 0 := by decide
  have f1 : a267610 1 = 0 := by decide
  intro n hn
  interval_cases n <;> simp [g1, g2, g3, f0, f1, a267610_two]

end Candidates.A267610Refutation
