/-
# Oddtown theorem (Berlekamp)

## Source (recorded 2026-10-21)

* E. R. Berlekamp, "On subsets with intersections of even cardinality",
  Canad. Math. Bull. 12 (1969) 471–474.
* L. Babai and P. Frankl, *Linear Algebra Methods in Combinatorics*, §1.1
  ("Oddtown").

## Informal statement (verbatim from the target spec)

```
If A_1,…,A_m ⊆ [n] have every |A_i| odd and every |A_i ∩ A_j| (i≠j) even,
then m ≤ n.
```

## Formal reading

The ground set `[n]` is `Fin n`; the family `A_1, …, A_m` of *distinct*
clubs is a `Finset (Finset (Fin n))` with `m = #𝒜`.  (Distinctness is
automatic: two equal odd clubs would have odd intersection.)

## Proof

Characteristic vectors over `ZMod 2`: the dot product of the vectors of `s`
and `t` is `#(s ∩ t) mod 2`, which is `1` on the diagonal and `0` off it, so
the vectors are linearly independent in `Fin n → ZMod 2`, a space of
dimension `n`.
-/
import Mathlib

set_option autoImplicit false

namespace Combinatorics.Oddtown

open Finset

/-- The characteristic vector of `s ⊆ Fin n` over `ZMod 2`. -/
def charVec {n : ℕ} (s : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ s then 1 else 0

example : charVec ({0, 2} : Finset (Fin 3)) = ![1, 0, 1] := by decide

/-- The `ZMod 2` dot product of two characteristic vectors is the size of the
intersection, reduced mod 2. -/
theorem sum_charVec_mul_charVec {n : ℕ} (s t : Finset (Fin n)) :
    ∑ i, charVec s i * charVec t i = ((#(s ∩ t) : ℕ) : ZMod 2) := by
  have hpt : ∀ i, charVec s i * charVec t i = if i ∈ s ∩ t then 1 else 0 := by
    intro i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [charVec, hs, ht]
  simp_rw [hpt]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Oddtown linear independence.** In an oddtown family the characteristic
vectors over `ZMod 2` are linearly independent. -/
theorem linearIndependent_charVec {n : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (hodd : ∀ s ∈ 𝒜, Odd #s)
    (hev : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even #(s ∩ t)) :
    LinearIndependent (ZMod 2) (fun s : 𝒜 => charVec (s : Finset (Fin n))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  have hdot : ∑ i, (∑ s : 𝒜, g s • charVec (s : Finset (Fin n))) i
      * charVec (t : Finset (Fin n)) i = 0 := by
    rw [hg]; simp
  have hexp : ∑ i, (∑ s : 𝒜, g s • charVec (s : Finset (Fin n))) i
      * charVec (t : Finset (Fin n)) i
      = ∑ s : 𝒜, g s * ((#((s : Finset (Fin n)) ∩ t) : ℕ) : ZMod 2) := by
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      ← sum_charVec_mul_charVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  have hdiag : ∑ s : 𝒜, g s * ((#((s : Finset (Fin n)) ∩ t) : ℕ) : ZMod 2) = g t := by
    rw [Finset.sum_eq_single t]
    · rw [Finset.inter_self, (ZMod.natCast_eq_one_iff_odd).2 (hodd t t.2), mul_one]
    · intro s _ hst
      have hne : (s : Finset (Fin n)) ≠ t := fun h => hst (Subtype.ext h)
      rw [(ZMod.natCast_eq_zero_iff_even).2 (hev s s.2 t t.2 hne), mul_zero]
    · intro h; exact absurd (Finset.mem_univ t) h
  rw [← hdiag, ← hexp, hdot]

/-- **Oddtown theorem** (Berlekamp 1969).  If `𝒜` is a family of subsets of
`[n]` in which every member has odd size and any two distinct members have an
intersection of even size, then `𝒜` has at most `n` members. -/
theorem card_le_of_odd_of_even_inter {n : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (hodd : ∀ s ∈ 𝒜, Odd #s)
    (hev : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even #(s ∩ t)) :
    #𝒜 ≤ n := by
  have h := (linearIndependent_charVec 𝒜 hodd hev).fintype_card_le_finrank
  rwa [Fintype.card_coe, Module.finrank_fin_fun] at h

/-- Non-vacuity: the singletons of `Fin 3` form an oddtown family of size
exactly `3`, so the bound is attained and the hypotheses are jointly
satisfiable. -/
example : let 𝒜 : Finset (Finset (Fin 3)) := {{0}, {1}, {2}}
    (∀ s ∈ 𝒜, Odd #s) ∧ (∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even #(s ∩ t)) ∧ #𝒜 = 3 := by
  decide

end Combinatorics.Oddtown
