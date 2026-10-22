/-
# A069187 — core(k) = ceiling(sqrt(k)): characterization (Stephan's conjecture)

## OEIS source (retrieved with `oeis show A069187`, 2026-10-21)

```
NAME:     Numbers k such that core(k) = ceiling(sqrt(k)) where core(k) is the
          squarefree part of k (the smallest integer such that k*core(k) is a
          square).
TERMS:    1,2,20,90,272,650,1332,4160,6642,10100,14762,20880,28730,38612,50850,
          65792,83810,130682,160400,194922,234740,280370,332352,391250,457652,
          532170,615440,708122,810900,924482,1187010,1337492,1501850,1680912,
          1875530,2314962,2561600
KEYWORDS: nonn
XREFS:    Cf. A007913, A049532, A071253.
COMMENT (the conjecture):
  Conjecture: sequence is A071253 minus those entries of A071253 that have
  their index in A049532, i.e., a(n) is of form n^2*(n^2+1) for all n not in
  A049532. - _Ralf Stephan_, Aug 18 2004
```

Cross-referenced entries:

* A071253: `a(n) = n^2*(n^2+1)`, terms `0,2,20,90,272,...` (index from `0`).
* A049532: numbers `k` such that `k^2 + 1` is not squarefree.

## Status

Triage: open (no proof in the entry or the literature found by the triage).
Computation (`k ≤ 3·10^6`, 37 terms) matches `{1} ∪ {s^2(s^2+1) : s ≥ 1,
s^2+1 squarefree}` exactly.

Read literally, the printed form is off at the boundary: A071253 contains `0`
(index `0`, not in A049532), which is not a positive term, and the term `1`
of A069187 is not of the form `n^2(n^2+1)`.  The intended statement, proved
below as `a069187_iff`, is: for positive `k`,
`core k = ⌈√k⌉ ↔ k = 1 ∨ ∃ s ≥ 1, s^2+1 squarefree ∧ k = s^2(s^2+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A069187PositiveSatisfyCore

/-! ## Definition layer -/

/-- Existence witness for `core`: `k * max k 1` is a perfect square. -/
theorem exists_pos_isSquare_mul (k : ℕ) : ∃ c, 0 < c ∧ IsSquare (k * c) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact ⟨1, Nat.one_pos, ⟨0, by simp [hk]⟩⟩
  · exact ⟨k, hk, ⟨k, rfl⟩⟩

/-- `core k` (OEIS A007913, as in the entry's name): the smallest positive
integer `c` such that `k * c` is a perfect square. -/
noncomputable def core (k : ℕ) : ℕ := Nat.find (exists_pos_isSquare_mul k)

/-- The OEIS predicate of A069187: `k` is positive and `core k = ⌈√k⌉`. -/
def IsA069187 (k : ℕ) : Prop := 0 < k ∧ core k = ⌈Real.sqrt k⌉₊

/-! ## Squarefree-part lemmas -/

/-- Cancelling a positive square factor preserves being a square. -/
theorem isSquare_of_isSquare_sq_mul {s x : ℕ} (hs : 0 < s) (h : IsSquare (s ^ 2 * x)) :
    IsSquare x := by
  obtain ⟨t, ht⟩ := h
  have hdvd : s ^ 2 ∣ t ^ 2 := ⟨x, by rw [sq t, ← ht]⟩
  obtain ⟨u, rfl⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp hdvd
  refine ⟨u, ?_⟩
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  have key : s ^ 2 * x = s ^ 2 * (u * u) := by rw [ht]; ring
  exact Nat.eq_of_mul_eq_mul_left hs2 key

/-- If `m` is squarefree, `0 < c`, and `m * c` is a square, then `m ≤ c`. -/
theorem le_of_squarefree_of_isSquare_mul {m c : ℕ} (hm : Squarefree m) (hc : 0 < c)
    (h : IsSquare (m * c)) : m ≤ c := by
  obtain ⟨t, ht⟩ := h
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have hdvd : m ∣ t ^ 2 := ⟨c, by rw [sq, ← ht]⟩
  obtain ⟨u, rfl⟩ := (hm.dvd_pow_iff_dvd two_ne_zero).mp hdvd
  have hcu : c = m * (u * u) := by
    apply Nat.eq_of_mul_eq_mul_left hm0
    rw [ht]; ring
  have hu : u ≠ 0 := by
    rintro rfl
    simp [hcu] at hc
  calc m = m * 1 := (mul_one m).symm
    _ ≤ m * (u * u) := Nat.mul_le_mul_left m (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hu hu))
    _ = c := hcu.symm

/-- If `k = s^2 * m` with `0 < s` and `m` squarefree, then `core k = m`. -/
theorem core_eq_of_sq_mul {k s m : ℕ} (hs : 0 < s) (hm : Squarefree m) (hk : k = s ^ 2 * m) :
    core k = m := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  unfold core
  rw [Nat.find_eq_iff]
  refine ⟨⟨hm0, ⟨s * m, by rw [hk]; ring⟩⟩, ?_⟩
  rintro n hn ⟨hn0, hsq⟩
  rw [hk, mul_assoc] at hsq
  have hle := le_of_squarefree_of_isSquare_mul hm hn0 (isSquare_of_isSquare_sq_mul hs hsq)
  omega

/-! ## Ceiling of the square root -/

/-- `⌈√k⌉ = n + 1` iff `n^2 < k ≤ (n+1)^2`. -/
theorem ceil_sqrt_eq_succ_iff (k n : ℕ) :
    ⌈Real.sqrt k⌉₊ = n + 1 ↔ n ^ 2 < k ∧ k ≤ (n + 1) ^ 2 := by
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero n), Nat.succ_sub_one]
  have h1 : ((n : ℝ) < Real.sqrt k) ↔ n ^ 2 < k := by
    rw [Real.lt_sqrt (Nat.cast_nonneg n)]
    exact_mod_cast Iff.rfl
  have h2 : (Real.sqrt k ≤ ((n + 1 : ℕ) : ℝ)) ↔ k ≤ (n + 1) ^ 2 := by
    rw [Real.sqrt_le_left (Nat.cast_nonneg _)]
    exact_mod_cast Iff.rfl
  rw [h1, h2]

/-! ## Ground truth -/

example : core 20 = 5 :=
  core_eq_of_sq_mul (s := 2) (by norm_num) Nat.prime_five.prime.squarefree (by norm_num)
example : ⌈Real.sqrt (20 : ℕ)⌉₊ = 5 := (ceil_sqrt_eq_succ_iff 20 4).mpr (by norm_num)
example : core 12 = 3 :=
  core_eq_of_sq_mul (s := 2) (by norm_num) Nat.prime_three.prime.squarefree (by norm_num)
example : ⌈Real.sqrt (12 : ℕ)⌉₊ = 4 := (ceil_sqrt_eq_succ_iff 12 3).mpr (by norm_num)
example : IsA069187 2 :=
  ⟨by norm_num, by
    rw [core_eq_of_sq_mul (s := 1) (m := 2) (by norm_num)
      Nat.prime_two.prime.squarefree (by norm_num)]
    exact ((ceil_sqrt_eq_succ_iff 2 1).mpr (by norm_num)).symm⟩
example : ¬ IsA069187 3 := by
  rintro ⟨-, h⟩
  rw [core_eq_of_sq_mul (s := 1) (m := 3) (by norm_num)
      Nat.prime_three.prime.squarefree (by norm_num),
    eq_comm, ceil_sqrt_eq_succ_iff 3 2] at h
  norm_num at h

/-! ## The characterization -/

/-- Arithmetic core: if `t * (n+1) ≤ (n+1)^2` and `n^2 < t * (n+1)`, then
`n + 1 = t` or `n + 1 = t + 1`. -/
theorem eq_or_eq_succ_of_bounds {t n : ℕ} (hup : t * (n + 1) ≤ (n + 1) ^ 2)
    (hlo : n ^ 2 < t * (n + 1)) : n + 1 = t ∨ n + 1 = t + 1 := by
  have ht : t ≤ n + 1 := by
    rw [sq] at hup
    exact Nat.le_of_mul_le_mul_right hup (Nat.succ_pos n)
  have hn : n ≤ t := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    have hmul : (t + 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) hcon
    nlinarith
  omega

/-- **Stephan's conjecture for A069187 (Ralf Stephan, Aug 18 2004), boundary-corrected.**

For a positive integer `k`, `core k = ⌈√k⌉` (with `core k` the smallest positive `c`
making `k * c` a square) holds iff `k = 1` or `k = s^2 * (s^2 + 1)` for some `s ≥ 1`
with `s^2 + 1` squarefree.  Since A071253 is `n ↦ n^2(n^2+1)` and A049532 lists the
`n` with `n^2 + 1` not squarefree, this is the printed statement "A071253 minus the
entries indexed by A049532", with the boundary terms corrected (the printed form
includes `0 = A071253(0)` and omits the term `1`). -/
theorem a069187_iff {k : ℕ} (hk : 0 < k) :
    core k = ⌈Real.sqrt k⌉₊ ↔
      k = 1 ∨ ∃ s : ℕ, 0 < s ∧ Squarefree (s ^ 2 + 1) ∧ k = s ^ 2 * (s ^ 2 + 1) := by
  constructor
  · intro h
    obtain ⟨m, s, hm0, hs0, hks, hm⟩ := Nat.sq_mul_squarefree_of_pos hk
    have hcore : core k = m := core_eq_of_sq_mul hs0 hm hks.symm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hcore, eq_comm, ceil_sqrt_eq_succ_iff, ← hks] at h
    obtain ⟨hlo, hup⟩ := h
    rcases eq_or_eq_succ_of_bounds (t := s ^ 2) (n := n) hup hlo with hm2 | hm2
    · -- `m = s^2` squarefree forces `s = 1`, hence `k = 1`.
      left
      rw [hm2] at hm
      have hs1 : s = 1 := by
        by_contra hne
        exact absurd ((Nat.squarefree_pow_iff hne two_ne_zero).mp hm).2 (by norm_num)
      subst hs1
      rw [← hks, hm2]
      norm_num
    · right
      refine ⟨s, hs0, hm2 ▸ hm, ?_⟩
      rw [← hks, hm2]
  · rintro (rfl | ⟨s, hs0, hsq, rfl⟩)
    · rw [core_eq_of_sq_mul (s := 1) (m := 1) Nat.one_pos squarefree_one (by norm_num),
        eq_comm, ceil_sqrt_eq_succ_iff 1 0]
      norm_num
    · rw [core_eq_of_sq_mul hs0 hsq rfl, eq_comm, ceil_sqrt_eq_succ_iff]
      have hs2 : 0 < s ^ 2 := pow_pos hs0 2
      constructor
      · nlinarith
      · nlinarith

/-- Membership form: `k` is a term of A069187 iff `k = 1` or `k = s^2(s^2+1)` with
`s ≥ 1` and `s^2 + 1` squarefree (`s ∉ A049532`). -/
theorem isA069187_iff (k : ℕ) :
    IsA069187 k ↔
      k = 1 ∨ ∃ s : ℕ, 0 < s ∧ Squarefree (s ^ 2 + 1) ∧ k = s ^ 2 * (s ^ 2 + 1) := by
  constructor
  · rintro ⟨hk, h⟩
    exact (a069187_iff hk).mp h
  · intro h
    have hk : 0 < k := by
      rcases h with rfl | ⟨s, hs0, -, rfl⟩
      · exact Nat.one_pos
      · positivity
    exact ⟨hk, (a069187_iff hk).mpr h⟩

/-- The printed form is off at the boundary: `1` is a term of A069187 but is not of the
form `n^2 (n^2 + 1)` (an entry of A071253). -/
theorem one_mem_not_A071253 : IsA069187 1 ∧ ∀ n : ℕ, n ^ 2 * (n ^ 2 + 1) ≠ 1 := by
  refine ⟨(isA069187_iff 1).mpr (Or.inl rfl), fun n hn => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · norm_num at hn
  · have h1 : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
    nlinarith

end Candidates.A069187PositiveSatisfyCore
