/-
# Nonuniform Fisher inequality (Majumdar 1953; Isbell 1959)

## Source (recorded 2026-10-21)

* K. N. Majumdar, "On some theorems in combinatorics relating to incomplete
  block designs", Ann. Math. Stat. 24 (1953) 377–389.
* J. R. Isbell, "An inequality for incidence matrices", Canad. Math. Bull. 2
  (1959) 25–26.
* L. Babai and P. Frankl, *Linear Algebra Methods in Combinatorics*, Ch. 4
  ("nonuniform Fisher inequality"); S. Jukna, *Extremal Combinatorics*, Ch. 13.

## Informal statement (verbatim from the target spec)

```
Let λ ≥ 1 and let 𝒜 be a family of distinct subsets of [n] in which every two
distinct members meet in exactly λ elements. Then |𝒜| ≤ n.
```

## Formal reading

The ground set `[n]` is `Fin n`; the family is a `Finset (Finset (Fin n))`, and
"every two distinct members meet in exactly `λ` elements" is Mathlib's
`Set.IsIntersectingOf {λ} 𝒜`.  We write `ℓ` for `λ` (a reserved token).

**Boundary hypothesis added.**  The verbatim statement is false at `n = 0`:
`𝒜 = {∅}` has one member and no pairs, so the intersection condition holds
vacuously while `#𝒜 = 1 > 0 = n` (see `not_card_le_zero_of_n_eq_zero` below).
The classical sources tacitly take `n ≥ 1`; we add `0 < n` explicitly.

## Proof

Characteristic vectors over `ℚ`.  If `∑ g_A v_A = 0`, pairing with `v_T`
gives `ℓ S + g_T (|T| - ℓ) = 0` for every `T`, where `S = ∑ g_A`.  Multiplying
by `g_T` and summing yields `ℓ S² + ∑ g_T² (|T| - ℓ) = 0`; all terms are
nonnegative because `|T| ≥ ℓ` (when `𝒜` has two members), so `S = 0`, whence
`g_T = 0` whenever `|T| > ℓ`.  At most one member has `|T| = ℓ` (two such would
both equal their intersection), and its coefficient equals `S = 0`.  Linear
independence in `Fin n → ℚ` gives `#𝒜 ≤ n`.
-/
import Mathlib

set_option autoImplicit false

namespace Combinatorics.NonuniformFisher

open Finset

/-- The characteristic vector of `s ⊆ Fin n` over `ℚ`. -/
def charVec {n : ℕ} (s : Finset (Fin n)) : Fin n → ℚ :=
  fun i => if i ∈ s then 1 else 0

example : charVec ({0, 2} : Finset (Fin 3)) = ![1, 0, 1] := by
  ext i; fin_cases i <;> simp [charVec]

/-- The rational dot product of two characteristic vectors is the size of the
intersection. -/
theorem sum_charVec_mul_charVec {n : ℕ} (s t : Finset (Fin n)) :
    ∑ i, charVec s i * charVec t i = ((#(s ∩ t) : ℕ) : ℚ) := by
  have hpt : ∀ i, charVec s i * charVec t i = if i ∈ s ∩ t then 1 else 0 := by
    intro i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [charVec, hs, ht]
  simp_rw [hpt]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Two sets of size `ℓ` meeting in `ℓ` elements are equal. -/
theorem eq_of_card_inter_eq {n ℓ : ℕ} {s t : Finset (Fin n)}
    (hs : #s = ℓ) (ht : #t = ℓ) (hst : #(s ∩ t) = ℓ) : s = t := by
  have h1 : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  rw [← h1, h2]

/-- **Key linear-independence step.**  If `0 < ℓ`, every member of `𝒜` has at
least `ℓ` elements, and any two distinct members meet in exactly `ℓ` elements,
then the rational characteristic vectors of the members of `𝒜` are linearly
independent. -/
theorem linearIndependent_charVec {n ℓ : ℕ} (hℓ : 0 < ℓ) (𝒜 : Finset (Finset (Fin n)))
    (hsize : ∀ s ∈ 𝒜, ℓ ≤ #s)
    (hinter : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → #(s ∩ t) = ℓ) :
    LinearIndependent ℚ (fun s : 𝒜 => charVec (s : Finset (Fin n))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set S : ℚ := ∑ s : 𝒜, g s with hS
  -- pairing the vanishing combination with `v_t`
  have heq : ∀ t : 𝒜, (ℓ : ℚ) * S + g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) = 0 := by
    intro t
    have hdot : ∑ i, (∑ s : 𝒜, g s • charVec (s : Finset (Fin n))) i
        * charVec (t : Finset (Fin n)) i = 0 := by
      rw [hg]; simp
    have hexp : ∑ i, (∑ s : 𝒜, g s • charVec (s : Finset (Fin n))) i
        * charVec (t : Finset (Fin n)) i
        = ∑ s : 𝒜, g s * ((#((s : Finset (Fin n)) ∩ t) : ℕ) : ℚ) := by
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
        ← sum_charVec_mul_charVec, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    have hsplit : ∀ s : 𝒜, g s * ((#((s : Finset (Fin n)) ∩ t) : ℕ) : ℚ)
        = g s * ℓ + if s = t then g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) else 0 := by
      intro s
      by_cases hst : s = t
      · subst hst; simp only [Finset.inter_self, if_true]; ring
      · have hne : (s : Finset (Fin n)) ≠ t := fun h => hst (Subtype.ext h)
        rw [hinter s s.2 t t.2 hne, if_neg hst, add_zero]
    rw [hexp] at hdot
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ t),
      ← Finset.sum_mul] at hdot
    rw [← hdot]; ring
  -- the quadratic identity `ℓ S² + ∑ g_t² (|t| - ℓ) = 0`
  have hquad : (ℓ : ℚ) * (S * S)
      + ∑ t : 𝒜, g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) = 0 := by
    have h0 : ∑ t : 𝒜, g t * ((ℓ : ℚ) * S + g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ)) = 0 := by
      simp [heq]
    calc (ℓ : ℚ) * (S * S) + ∑ t : 𝒜, g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ)
        = (ℓ : ℚ) * S * S + ∑ t : 𝒜, g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) := by ring
      _ = ∑ t : 𝒜, ((ℓ : ℚ) * S * g t + g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ t : 𝒜, g t * ((ℓ : ℚ) * S + g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ)) :=
        Finset.sum_congr rfl fun t _ => by ring
      _ = 0 := h0
  have hnonneg : ∀ t : 𝒜, 0 ≤ g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) := by
    intro t
    have hle : (ℓ : ℚ) ≤ (#(t : Finset (Fin n)) : ℚ) := by exact_mod_cast hsize t t.2
    exact mul_nonneg (mul_self_nonneg _) (sub_nonneg.2 hle)
  have hsum_nonneg : 0 ≤ ∑ t : 𝒜, g t * g t * ((#(t : Finset (Fin n)) : ℚ) - ℓ) :=
    Finset.sum_nonneg fun t _ => hnonneg t
  have hℓq : (0 : ℚ) < ℓ := by exact_mod_cast hℓ
  have hS0 : S = 0 := by
    have hSS : (ℓ : ℚ) * (S * S) ≤ 0 := by linarith
    have hSS' : S * S ≤ 0 := by
      by_contra hpos
      rw [not_le] at hpos
      linarith [mul_pos hℓq hpos]
    exact mul_self_eq_zero.1 (le_antisymm hSS' (mul_self_nonneg S))
  -- coefficients of members larger than `ℓ` vanish
  have hbig : ∀ t : 𝒜, #(t : Finset (Fin n)) ≠ ℓ → g t = 0 := by
    intro t ht
    have h := heq t
    rw [hS0, mul_zero, zero_add] at h
    have hne : ((#(t : Finset (Fin n)) : ℚ) - ℓ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast ht
    exact (mul_eq_zero.1 h).resolve_right hne
  intro t
  by_cases ht : #(t : Finset (Fin n)) = ℓ
  · -- the unique member of size `ℓ` carries all of `S = 0`
    have hrest : ∀ s : 𝒜, s ≠ t → g s = 0 := by
      intro s hst
      apply hbig s
      intro hs
      have hne : (s : Finset (Fin n)) ≠ t := fun h => hst (Subtype.ext h)
      exact hne (eq_of_card_inter_eq hs ht (hinter s s.2 t t.2 hne))
    have hsingle : S = g t := by
      rw [hS, Finset.sum_eq_single t (fun s _ hst => hrest s hst)
        (fun h => absurd (Finset.mem_univ t) h)]
    rw [← hsingle, hS0]
  · exact hbig t ht

/-- **Nonuniform Fisher inequality** (Majumdar 1953; Isbell 1959).  Let
`0 < ℓ` and `0 < n`.  If `𝒜` is a family of distinct subsets of `[n]` in which
every two distinct members meet in exactly `ℓ` elements, then `#𝒜 ≤ n`.

The hypothesis `0 < n` is added to the verbatim source statement: at `n = 0`
the family `{∅}` is a counterexample (`not_card_le_zero_of_n_eq_zero`). -/
theorem card_le_of_isIntersectingOf_singleton {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ)
    (𝒜 : Finset (Finset (Fin n)))
    (h : Set.IsIntersectingOf {ℓ} (𝒜 : Set (Finset (Fin n)))) :
    #𝒜 ≤ n := by
  have hinter : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → #(s ∩ t) = ℓ := fun s hs t ht hst =>
    h (Finset.mem_coe.2 hs) (Finset.mem_coe.2 ht) hst
  by_cases hsmall : #𝒜 ≤ 1
  · omega
  · have hsize : ∀ s ∈ 𝒜, ℓ ≤ #s := by
      intro s hs
      obtain ⟨t, ht, hts⟩ := Finset.exists_mem_ne (by omega : 1 < #𝒜) s
      rw [← hinter s hs t ht (Ne.symm hts)]
      exact Finset.card_le_card Finset.inter_subset_left
    have hli := (linearIndependent_charVec hℓ 𝒜 hsize hinter).fintype_card_le_finrank
    rwa [Fintype.card_coe, Module.finrank_fin_fun] at hli

/-- The added hypothesis `0 < n` is necessary: over `Fin 0` the family `{∅}`
satisfies the intersection condition vacuously but has `1 > 0` members. -/
theorem not_card_le_zero_of_n_eq_zero :
    Set.IsIntersectingOf {1} (({∅} : Finset (Finset (Fin 0))) : Set (Finset (Fin 0))) ∧
      ¬ #({∅} : Finset (Finset (Fin 0))) ≤ 0 := by
  refine ⟨?_, by simp⟩
  intro s hs t ht hst
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hs ht
  exact absurd (hs.trans ht.symm) hst

/-- Non-vacuity: the edges of the triangle on `Fin 3`,
`{0,1}, {0,2}, {1,2}`, pairwise meet in exactly `1` element, so the hypotheses
are jointly satisfiable at `n = 3`, `ℓ = 1` and the bound `#𝒜 = 3 = n` is
attained. -/
example : let 𝒜 : Finset (Finset (Fin 3)) := {{0, 1}, {0, 2}, {1, 2}}
    Set.IsIntersectingOf {1} (𝒜 : Set (Finset (Fin 3))) ∧ #𝒜 = 3 := by
  refine ⟨?_, by decide⟩
  intro s hs t ht hst
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> first
    | exact absurd rfl hst
    | decide

end Combinatorics.NonuniformFisher
