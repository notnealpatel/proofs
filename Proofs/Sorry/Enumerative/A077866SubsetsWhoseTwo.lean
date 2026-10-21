/-
# A077866 — Kimberling: subsets whose two least elements sum to the maximum

## OEIS source (retrieved with `oeis show A077866`, 2026-10-21)

```
NAME:     Expansion of (1-x)^(-1)/(1 - x - 2*x^2 + 2*x^3).
TERMS:    1,2,5,8,15,22,37,52,83,114,177,240,367,494,749,1004,1515,2026,3049,
          4072,6119,8166,12261,16356,24547,32738,49121,65504,98271,131038,...
FORMULA:  G.f.: 1/((1 - x)^2 * (1 - 2*x^2)). - _Michael Somos_, Aug 11 2021
COMMENT (the conjecture):
  Conjecture:  let b(n) be the number of subsets S of {1,2,...,n} having more
  than one element such that (sum of least two elements of S) = max(S).  Then
  b(0) = b(1) = b(2) = 0 and b(n+3) = a(n) for n >= 0.
  - _Clark Kimberling_ Sep 27 2022
```

Note `(1-x)(1 - x - 2x^2 + 2x^3) = (1-x)^2 (1-2x^2)`, so the NAME and the
Somos g.f. agree.

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Computational evidence before this file: brute force for
`n + 3 ≤ 18`, the pair-sum formula for `n + 3 ≤ 44`.

## Proof (kernel-checked below)

Fix the two least elements `x < y` of `S`.  Then `max S = x + y > y`, and the
remaining elements form an arbitrary subset of the open interval `(y, x + y)`,
which has `x - 1` integers.  Hence `b(N) = ∑_{1 ≤ x < y, x + y ≤ N} 2^(x-1)`
(`b_eq_s`).  Splitting off `x = 1` and shifting `(x, y) ↦ (x - 1, y - 1)`
gives `b(N + 2) = 2 b(N) + N` (`s_add_two`), which is the recurrence
`a(n + 2) = 2 a(n) + n + 3` obtained by multiplying the g.f. by `1 - 2x^2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A077866SubsetsWhoseTwo

open Finset PowerSeries

/-! ## Definition layer -/

/-- A finset of naturals with at least two elements is nonempty. -/
theorem nonempty_of_two_le_card {S : Finset ℕ} (h : 2 ≤ S.card) : S.Nonempty :=
  Finset.card_pos.mp (by omega)

/-- Removing the least element of a finset with at least two elements leaves a
nonempty finset. -/
theorem erase_min'_nonempty {S : Finset ℕ} (h : 2 ≤ S.card) :
    (S.erase (S.min' (nonempty_of_two_le_card h))).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]
  omega

/-- Kimberling's predicate: `S` has more than one element and the sum of its two
least elements (`S.min'`, and the least element of `S` with `S.min'` removed)
equals `max(S)`. -/
def LeastTwoSumEqMax (S : Finset ℕ) : Prop :=
  ∃ h : 2 ≤ S.card,
    S.min' (nonempty_of_two_le_card h) + (S.erase (S.min' _)).min' (erase_min'_nonempty h) =
      S.max' (nonempty_of_two_le_card h)

/-- Decidability of `LeastTwoSumEqMax`, used to form the counting filter. -/
instance : DecidablePred LeastTwoSumEqMax := fun S => by
  unfold LeastTwoSumEqMax; infer_instance

/-- Kimberling's `b(N)`: the number of subsets `S` of `{1, …, N}` having more than
one element such that the sum of the two least elements of `S` equals `max(S)`. -/
def b (N : ℕ) : ℕ := ((Finset.Icc 1 N).powerset.filter LeastTwoSumEqMax).card
/-- A077866 as the coefficient sequence of `1/((1-x)^2 (1-2x^2))`, computed by the
recurrence `a(n+2) = 2 a(n) + (n + 3)` (multiply the g.f. by `1 - 2x^2`; the
coefficients of `1/(1-x)^2` are `n + 1`).  `a_eq_coeff_inv` proves that these
are exactly the power-series coefficients. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * a n + (n + 3)

/-! ## Ground truth -/

-- The first twelve terms of the OEIS DATA line.
example : (List.range 12).map a = [1, 2, 5, 8, 15, 22, 37, 52, 83, 114, 177, 240] := by decide

-- Kimberling's `b(0), …, b(4)` by direct enumeration of subsets.
example : (List.range 5).map b = [0, 0, 0, 1, 2] := by decide

-- The predicate is satisfiable and not trivial: `{1, 2, 3}` qualifies,
-- `{1, 2}` (two elements: `1 + 2 ≠ 2`) and `{5}` (one element) do not.
example : LeastTwoSumEqMax {1, 2, 3} ∧ ¬ LeastTwoSumEqMax {1, 2} ∧
    ¬ LeastTwoSumEqMax {5} := by decide

/-! ## Structure of the qualifying sets -/

/-- The set `{x, y, x + y} ∪ T`. -/
def build (x y : ℕ) (T : Finset ℕ) : Finset ℕ := insert x (insert y (insert (x + y) T))

/-- Membership in `build x y T`. -/
theorem mem_build {x y t : ℕ} {T : Finset ℕ} :
    t ∈ build x y T ↔ t = x ∨ t = y ∨ t = x + y ∨ t ∈ T := by
  simp [build]

/-- If `0 < x < y` and `T ⊆ (y, x + y)`, then `{x, y, x + y} ∪ T` has two least
elements `x, y` summing to its maximum `x + y`. -/
theorem leastTwoSumEqMax_build {x y : ℕ} {T : Finset ℕ} (hx : 0 < x) (hxy : x < y)
    (hT : T ⊆ Ioo y (x + y)) : LeastTwoSumEqMax (build x y T) := by
  have hTmem : ∀ t ∈ T, y < t ∧ t < x + y := fun t ht => Finset.mem_Ioo.mp (hT ht)
  have hcard : 2 ≤ (build x y T).card := by
    have hsub : ({x, y} : Finset ℕ) ⊆ build x y T := by
      intro t ht
      rw [mem_build]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      tauto
    have h2 : ({x, y} : Finset ℕ).card = 2 := Finset.card_pair hxy.ne
    exact h2 ▸ Finset.card_le_card hsub
  refine ⟨hcard, ?_⟩
  have h1 : (build x y T).min' (nonempty_of_two_le_card hcard) = x := by
    rw [Finset.min'_eq_iff]
    refine ⟨mem_build.mpr (Or.inl rfl), fun t ht => ?_⟩
    rcases mem_build.mp ht with h | h | h | h
    · omega
    · omega
    · omega
    · have := hTmem t h; omega
  have h2 : ((build x y T).erase ((build x y T).min' (nonempty_of_two_le_card hcard))).min'
      (erase_min'_nonempty hcard) = y := by
    rw [Finset.min'_eq_iff, h1]
    refine ⟨Finset.mem_erase.mpr ⟨hxy.ne', mem_build.mpr (Or.inr (Or.inl rfl))⟩, fun t ht => ?_⟩
    obtain ⟨htx, ht⟩ := Finset.mem_erase.mp ht
    rcases mem_build.mp ht with h | h | h | h
    · omega
    · omega
    · omega
    · have := hTmem t h; omega
  have h3 : (build x y T).max' (nonempty_of_two_le_card hcard) = x + y := by
    rw [Finset.max'_eq_iff]
    refine ⟨mem_build.mpr (Or.inr (Or.inr (Or.inl rfl))), fun t ht => ?_⟩
    rcases mem_build.mp ht with h | h | h | h
    · omega
    · omega
    · omega
    · have := hTmem t h; omega
  rw [h2, h1, h3]

/-- Conversely, a qualifying set avoiding `0` is `{x, y, x + y} ∪ T` with
`0 < x < y` its two least elements and `T` its elements strictly between `y`
and `x + y`. -/
theorem exists_build_of_leastTwoSumEqMax {S : Finset ℕ} (h0 : 0 ∉ S)
    (hS : LeastTwoSumEqMax S) :
    ∃ x y, 0 < x ∧ x < y ∧ x + y ∈ S ∧
      S = build x y (S.filter fun t => y < t ∧ t < x + y) := by
  obtain ⟨hcard, heq⟩ := hS
  have hm := Finset.min'_mem S (nonempty_of_two_le_card hcard)
  have hmle : ∀ t ∈ S, S.min' (nonempty_of_two_le_card hcard) ≤ t :=
    fun t ht => Finset.min'_le S t ht
  have hm2 := Finset.min'_mem _ (erase_min'_nonempty hcard)
  have hm2le : ∀ t ∈ S.erase (S.min' (nonempty_of_two_le_card hcard)),
      (S.erase (S.min' (nonempty_of_two_le_card hcard))).min' (erase_min'_nonempty hcard) ≤ t :=
    fun t ht => Finset.min'_le _ t ht
  have hM := Finset.max'_mem S (nonempty_of_two_le_card hcard)
  have hMle : ∀ t ∈ S, t ≤ S.max' (nonempty_of_two_le_card hcard) :=
    fun t ht => Finset.le_max' S t ht
  generalize (S.erase (S.min' (nonempty_of_two_le_card hcard))).min'
    (erase_min'_nonempty hcard) = y at heq hm2 hm2le
  generalize S.min' (nonempty_of_two_le_card hcard) = x at heq hm hmle hm2 hm2le
  generalize S.max' (nonempty_of_two_le_card hcard) = M at heq hM hMle
  subst heq
  obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hm2
  have hx0 : 0 < x := Nat.pos_of_ne_zero fun h => h0 (h ▸ hm)
  have hxy : x < y := lt_of_le_of_ne (hmle y hyS) (Ne.symm hyx)
  refine ⟨x, y, hx0, hxy, hM, ?_⟩
  ext t
  rw [mem_build, Finset.mem_filter]
  constructor
  · intro ht
    by_cases htx : t = x
    · exact Or.inl htx
    · have hyt : y ≤ t := hm2le t (Finset.mem_erase.mpr ⟨htx, ht⟩)
      have htM : t ≤ x + y := hMle t ht
      rcases Nat.lt_or_ge y t with h | h
      · rcases Nat.lt_or_ge t (x + y) with h' | h'
        · exact Or.inr (Or.inr (Or.inr ⟨ht, h, h'⟩))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inl (by omega))
  · rintro (h | h | h | ⟨h, -⟩)
    · exact h ▸ hm
    · exact h ▸ hyS
    · exact h ▸ hM
    · exact h

/-! ## Counting -/

/-- Admissible pairs `(x, y)` of two least elements: `1 ≤ x < y` and `x + y ≤ N`. -/
def pairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p => p.1 < p.2 ∧ p.1 + p.2 ≤ N

/-- Parameter set: an admissible pair `(x, y)` and a subset `T` of the open interval
`(y, x + y)`. -/
def idx (N : ℕ) : Finset (Σ _ : ℕ × ℕ, Finset ℕ) :=
  (pairs N).sigma fun p => (Ioo p.2 (p.1 + p.2)).powerset

theorem mem_pairs {N : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs N ↔ (1 ≤ p.1 ∧ p.1 ≤ N) ∧ (1 ≤ p.2 ∧ p.2 ≤ N) ∧ p.1 < p.2 ∧ p.1 + p.2 ≤ N := by
  simp [pairs, Finset.mem_product, and_assoc]

/-- In `build x y T`, every element is at least `x`, and every element other
than `x` is at least `y`. -/
theorem le_of_mem_build {x y t : ℕ} {T : Finset ℕ} (hxy : x < y) (hT : T ⊆ Ioo y (x + y))
    (ht : t ∈ build x y T) : x ≤ t ∧ (t ≠ x → y ≤ t) := by
  rcases mem_build.mp ht with h | h | h | h
  · omega
  · omega
  · omega
  · have := Finset.mem_Ioo.mp (hT h); omega

/-- `T` is recovered from `build x y T` as the elements strictly between `y`
and `x + y`. -/
theorem filter_build {x y : ℕ} {T : Finset ℕ} (hxy : x < y) (hT : T ⊆ Ioo y (x + y)) :
    (build x y T).filter (fun t => y < t ∧ t < x + y) = T := by
  ext t
  rw [Finset.mem_filter, mem_build]
  constructor
  · rintro ⟨h | h | h | h, h1, h2⟩
    · omega
    · omega
    · omega
    · exact h
  · intro h
    have := Finset.mem_Ioo.mp (hT h)
    exact ⟨Or.inr (Or.inr (Or.inr h)), this⟩

/-- `b(N)` counts the parameter set `idx N`, via `(x, y, T) ↦ {x, y, x + y} ∪ T`. -/
theorem b_eq_card_idx (N : ℕ) : b N = (idx N).card := by
  symm
  apply Finset.card_nbij (fun q => build q.1.1 q.1.2 q.2)
  · rintro ⟨⟨x, y⟩, T⟩ hq
    rw [Finset.mem_coe, idx, Finset.mem_sigma, mem_pairs, Finset.mem_powerset] at hq
    obtain ⟨⟨⟨hx1, hxN⟩, ⟨hy1, hyN⟩, hxy, hxyN⟩, hT⟩ := hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun t ht => ?_, leastTwoSumEqMax_build (by omega) hxy hT⟩
    rw [Finset.mem_Icc]
    rcases mem_build.mp ht with h | h | h | h
    · omega
    · omega
    · omega
    · have := Finset.mem_Ioo.mp (hT h); omega
  · rintro ⟨⟨x, y⟩, T⟩ hq ⟨⟨x', y'⟩, T'⟩ hq' heq
    rw [Finset.mem_coe, idx, Finset.mem_sigma, mem_pairs, Finset.mem_powerset] at hq hq'
    obtain ⟨⟨-, -, hxy, -⟩, hT⟩ := hq
    obtain ⟨⟨-, -, hxy', -⟩, hT'⟩ := hq'
    dsimp only at heq hT hT' hxy hxy'
    have hxm : x ∈ build x' y' T' := heq ▸ mem_build.mpr (Or.inl rfl)
    have hxm' : x' ∈ build x y T := heq.symm ▸ mem_build.mpr (Or.inl rfl)
    have hx : x = x' := le_antisymm (le_of_mem_build hxy hT hxm').1
      (le_of_mem_build hxy' hT' hxm).1
    subst hx
    have hym : y ∈ build x y' T' := heq ▸ mem_build.mpr (Or.inr (Or.inl rfl))
    have hym' : y' ∈ build x y T := heq.symm ▸ mem_build.mpr (Or.inr (Or.inl rfl))
    have hy : y = y' := le_antisymm ((le_of_mem_build hxy hT hym').2 (by omega))
      ((le_of_mem_build hxy' hT' hym).2 (by omega))
    subst hy
    have hTT : T = T' := by
      rw [← filter_build hxy hT, ← filter_build hxy' hT', heq]
    rw [hTT]
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, hS⟩ := hS
    have h0 : 0 ∉ S := fun h => by
      have := Finset.mem_Icc.mp (hsub h); omega
    obtain ⟨x, y, hx0, hxy, hxyS, hSeq⟩ := exists_build_of_leastTwoSumEqMax h0 hS
    have hyS : y ∈ S := hSeq ▸ mem_build.mpr (Or.inr (Or.inl rfl))
    have hyN := Finset.mem_Icc.mp (hsub hyS)
    have hxyN := Finset.mem_Icc.mp (hsub hxyS)
    refine ⟨⟨(x, y), S.filter fun t => y < t ∧ t < x + y⟩, ?_, hSeq.symm⟩
    rw [Finset.mem_coe, idx, Finset.mem_sigma, mem_pairs, Finset.mem_powerset]
    dsimp only
    refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hxy, by omega⟩, fun t ht => ?_⟩
    rw [Finset.mem_filter] at ht
    exact Finset.mem_Ioo.mpr ht.2

/-- The weighted pair sum `s(N) = ∑_{x < y, x + y ≤ N} 2^(x-1)`. -/
def s (N : ℕ) : ℕ := ∑ p ∈ pairs N, 2 ^ (p.1 - 1)

/-- The cardinality of `idx N` is the weighted pair sum `s N`. -/
theorem card_idx (N : ℕ) : (idx N).card = s N := by
  rw [idx, Finset.card_sigma, s]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.card_powerset, Nat.card_Ioo]
  congr 1
  omega

/-- The pair-sum recurrence `s(N + 2) = 2 s(N) + N`: pairs with `x = 1` contribute
`N` (namely `y ∈ [2, N + 1]`), and the shift `(x, y) ↦ (x - 1, y - 1)` maps the
remaining pairs onto `pairs N` while halving the weight. -/
theorem s_add_two (N : ℕ) : s (N + 2) = 2 * s N + N := by
  rw [s, ← Finset.sum_filter_add_sum_filter_not (pairs (N + 2)) (fun p => p.1 = 1)]
  have hone : ∑ p ∈ (pairs (N + 2)).filter (fun p => p.1 = 1), 2 ^ (p.1 - 1) = N := by
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2], pow_zero,
      Finset.sum_const, smul_eq_mul, mul_one]
    refine (Finset.card_nbij' (fun p => p.2 - 2) (fun k => (1, k + 2)) ?_ ?_ ?_ ?_).trans
      (Finset.card_range N)
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_pairs] at hp
      rw [Finset.mem_coe, Finset.mem_range]
      dsimp only
      omega
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_range] at hk
      rw [Finset.mem_coe, Finset.mem_filter, mem_pairs]
      dsimp only
      omega
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_pairs] at hp
      ext <;> dsimp only <;> omega
    · intro k _
      dsimp only
      omega
  have hrest : ∑ p ∈ (pairs (N + 2)).filter (fun p => ¬ p.1 = 1), 2 ^ (p.1 - 1) =
      2 * ∑ p ∈ pairs N, 2 ^ (p.1 - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun p => (p.1 - 1, p.2 - 1)) (fun p => (p.1 + 1, p.2 + 1))
    · intro p hp
      rw [Finset.mem_filter, mem_pairs] at hp
      rw [mem_pairs]
      dsimp only
      omega
    · intro p hp
      rw [mem_pairs] at hp
      rw [Finset.mem_filter, mem_pairs]
      dsimp only
      omega
    · intro p hp
      rw [Finset.mem_filter, mem_pairs] at hp
      ext <;> dsimp only <;> omega
    · intro p _
      rfl
    · intro p hp
      rw [Finset.mem_filter, mem_pairs] at hp
      dsimp only
      rw [← pow_succ']
      congr 1
      omega
  rw [hone, hrest, s, add_comm]

/-- The pair sum at `n + 3` is `a(n)`. -/
theorem s_add_three (n : ℕ) : s (n + 3) = a n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 _ =>
    rw [show n + 2 + 3 = (n + 3) + 2 by ring, s_add_two, ih0, a]

/-! ## The generating function -/

/-- The coefficients of `1/(1-x)^2` are `n + 1`: `(∑ (n+1) xⁿ) (1 - x)^2 = 1`. -/
theorem mk_succ_mul_one_sub_X_sq :
    (PowerSeries.mk fun n => ((n : ℚ) + 1)) * (1 - X) ^ 2 = 1 := by
  ext n
  rw [show (1 - X : ℚ⟦X⟧) ^ 2 = 1 - C (2 : ℚ) * X ^ 1 + X ^ 2 by rw [map_ofNat]; ring]
  rw [mul_add, mul_sub, mul_one, mul_left_comm, map_add, map_sub, coeff_C_mul,
    coeff_mul_X_pow', coeff_mul_X_pow', coeff_mk]
  rcases n with _ | _ | n
  · simp
  · norm_num
  · rw [if_pos (by omega), if_pos (by omega), coeff_mk, coeff_one, if_neg (by omega),
      show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
    simp only [coeff_mk]
    push_cast
    ring

/-- Multiplying the series of `a` by `1 - 2x^2` gives `∑ (n+1) xⁿ`; this is the
recurrence `a(n+2) - 2 a(n) = n + 3`. -/
theorem mk_a_mul_one_sub_two_X_sq :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 2 * X ^ 2) =
      PowerSeries.mk fun n => ((n : ℚ) + 1) := by
  ext n
  rw [show (1 - 2 * X ^ 2 : ℚ⟦X⟧) = 1 - C (2 : ℚ) * X ^ 2 by rw [map_ofNat]]
  rw [mul_sub, mul_one, mul_left_comm, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk,
    coeff_mk]
  rcases n with _ | _ | n
  · simp [a]
  · norm_num [a]
  · rw [if_pos (by omega), show n + 2 - 2 = n by omega, a]
    simp only [coeff_mk]
    push_cast
    ring

/-- `a(n)` is the coefficient of `xⁿ` in `1/((1-x)^2 (1-2x^2))` (Somos's g.f.,
equivalently the entry's NAME `(1-x)^(-1)/(1 - x - 2x^2 + 2x^3)`). -/
theorem a_eq_coeff_inv (n : ℕ) :
    (a n : ℚ) = PowerSeries.coeff n (((1 - X) ^ 2 * (1 - 2 * X ^ 2) : ℚ⟦X⟧)⁻¹) := by
  have hinv : (PowerSeries.mk fun n => (a n : ℚ)) = ((1 - X) ^ 2 * (1 - 2 * X ^ 2) : ℚ⟦X⟧)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
    rw [mul_comm ((1 - X : ℚ⟦X⟧) ^ 2), ← mul_assoc, mk_a_mul_one_sub_two_X_sq,
      mk_succ_mul_one_sub_X_sq]
  rw [← hinv, coeff_mk]

/-! ## Kimberling's conjecture -/

/-- `b(N)` equals the weighted pair sum `∑_{1 ≤ x < y, x + y ≤ N} 2^(x-1)`. -/
theorem b_eq_s (N : ℕ) : b N = s N := by
  rw [b_eq_card_idx, card_idx]

/-- **Kimberling's conjecture, first part (A077866, Sep 27 2022).**
`b(0) = b(1) = b(2) = 0`: no subset of `{1, 2}` qualifies. -/
theorem b_eq_zero_of_lt_three {N : ℕ} (hN : N < 3) : b N = 0 := by
  interval_cases N <;> decide

/-- **Kimberling's conjecture, second part (A077866, Sep 27 2022).**
For every `n ≥ 0`, the number `b(n + 3)` of subsets `S ⊆ {1, …, n + 3}` with more
than one element whose two least elements sum to `max(S)` equals `a(n)`. -/
theorem b_add_three (n : ℕ) : b (n + 3) = a n := by
  rw [b_eq_s, s_add_three]

/-- **Kimberling's conjecture in g.f. form.**  For every `n ≥ 0`, the number of
subsets `S ⊆ {1, …, n + 3}` with `|S| ≥ 2` whose two least elements sum to
`max(S)` equals the coefficient of `xⁿ` in `1/((1-x)^2 (1-2x^2))`. -/
theorem card_filter_eq_coeff_inv (n : ℕ) :
    ((((Finset.Icc 1 (n + 3)).powerset.filter LeastTwoSumEqMax).card : ℕ) : ℚ) =
      PowerSeries.coeff n (((1 - X) ^ 2 * (1 - 2 * X ^ 2) : ℚ⟦X⟧)⁻¹) := by
  rw [← a_eq_coeff_inv, ← b_add_three, b]

end Candidates.A077866SubsetsWhoseTwo
