/-
# Mu–Welker coefficient conjecture `h_i ≤ g_i` in degree 3

## Source

* Lili Mu and Volkmar Welker, *On a question about real-rooted polynomials and
  f-polynomials of simplicial complexes*, arXiv:2503.24076, Section 3
  ("Second approach"), Conjecture 3.8 (`con:second`) and the Proposition
  right after it.
* Feihu Liu, Ying Wang and Zihao Zhang, *Counterexamples to the Mu–Welker
  recursive decomposition in every degree*, arXiv:2609.23694 (they refute the
  companion real-rootedness Question 3.10 for every degree `d ≥ 3` and state
  explicitly that Conjecture 3.8 "is a separate issue and [is] not
  contradicted by our result").

Recorded 2026-10-21.

## Verbatim informal claim (Mu–Welker, Conjecture 3.8)

Let `f(t) = 1 + f_0 t + ⋯ + f_{d-1} t^d ∈ ℕ[t]`.  For `i ≥ 1` let
`f_{i-1} = C(a_i, i) + C(a_{i-1}, i-1) + ⋯ + C(a_j, j)`,
`a_i > ⋯ > a_j ≥ j ≥ 1`, be the `i`-th binomial expansion of `f_{i-1}`, and
define `g_i = C(a_i - 1, i) + ⋯ + C(a_j - 1, j)` and
`h_{i-1} = C(a_i - 1, i - 1) + ⋯ + C(a_j - 1, j - 1)`, so that
`f(t) = g(t) + t h(t)` (the *recursive decomposition*).

> **Conjecture 3.8.** Let `f(t) = 1 + f_0 t + ⋯ + f_{d-1} t^d ∈ ℕ[t]` have
> only real roots and recursive decomposition `f(t) = g(t) + t h(t)`, with
> `g(t) = 1 + g_1 t + ⋯ + g_d t^d`, `h(t) = 1 + h_1 t + ⋯ + h_{d-1} t^{d-1}`.
> Then for `i = 1, …, d-1`, we have `h_i ≤ g_i`.

Mu–Welker show (Proposition after Conjecture 3.8) that the conjecture implies
a positive answer to the Bell–Skandera question (a real-rooted `f` with
positive integer coefficients is the `f`-polynomial of a simplicial complex).

## Status

Open in the source (stated as a conjecture, all degrees).  This module proves
the **degree `d = 3` case** (`i = 1, 2`) unconditionally; in fact it proves the
stronger statement that only the two Newton inequalities
`3 c₂ ≤ c₁²`, `3 c₁ c₃ ≤ c₂²` and `0 < c₂` are needed.  No source settling
degree 3 was located (one web search plus the two papers); this is not a
novelty claim.  Note that Liu–Wang–Zhang's colex argument shows
`h_i ≤ g_i` whenever `(1, c₁, …, c_d)` is an `f`-vector, so in each degree the
conjecture is equivalent to the Bell–Skandera question there.

## Encoding

Coefficients are indexed as `c_i = f_{i-1}`, the coefficient of `t^i`.
`cascade m i` is the greedy `i`-th binomial expansion of `m` as the list of
pairs `(a_r, r)`; `mwG m i` and `mwH m i` are the paper's `g_i` and `h_{i-1}`
computed from the `i`-th expansion of `m = c_i`.  So the conjecture's
`h_i ≤ g_i` reads `mwH c_{i+1} (i+1) ≤ mwG c_i i`.
"Only real roots" for `f ∈ ℕ[t]` of degree 3 is the statement that its image
in `ℝ[t]` has as many real roots (with multiplicity) as its degree.
-/
import Mathlib

set_option autoImplicit false

namespace MuWelkerDegreeThree

open Polynomial

/-- Leading index of the `r`-th binomial expansion of `m`: the greatest `a ≤ m + r` with
`C(a, r) ≤ m`.  For `0 < m` and `0 < r` this is the unique `a` with
`C(a, r) ≤ m < C(a + 1, r)` (see `leadIdx_spec`). -/
def leadIdx (m r : ℕ) : ℕ := Nat.findGreatest (fun a => a.choose r ≤ m) (m + r)

/-- The `i`-th binomial (Kruskal–Katona cascade) expansion of `m`, as the list of pairs
`(a_r, r)` with `m = ∑ C(a_r, r)`, `a_i > a_{i-1} > ⋯ > a_j ≥ j ≥ 1`, computed greedily:
take the leading index at level `r`, subtract, and descend to level `r - 1` until the
remainder is `0`. -/
def cascade : ℕ → ℕ → List (ℕ × ℕ)
  | _, 0 => []
  | m, i + 1 =>
      if m = 0 then [] else
        (leadIdx m (i + 1), i + 1) :: cascade (m - (leadIdx m (i + 1)).choose (i + 1)) i

/-- Mu–Welker's `g_i`: for the `i`-th binomial expansion `m = ∑ C(a_r, r)` of
`m = f_{i-1}`, `g_i = ∑ C(a_r - 1, r)`. -/
def mwG (m i : ℕ) : ℕ := ((cascade m i).map fun p => (p.1 - 1).choose p.2).sum

/-- Mu–Welker's `h_{i-1}`: for the `i`-th binomial expansion `m = ∑ C(a_r, r)` of
`m = f_{i-1}`, `h_{i-1} = ∑ C(a_r - 1, r - 1)`. -/
def mwH (m i : ℕ) : ℕ := ((cascade m i).map fun p => (p.1 - 1).choose (p.2 - 1)).sum

/-! ### Ground truth: the example `f = (1 + 3t)^3 = 1 + 9t + 27t² + 27t³` from the papers.

Mu–Welker (end of Section 3) and Liu–Wang–Zhang record the recursive decomposition
`g = (1 + t)(1 + 7t + 13t²) = 1 + 8t + 20t² + 13t³` and `h = 1 + 7t + 14t²`. -/

example : cascade 27 3 = [(6, 3), (4, 2), (1, 1)] := by decide
example : cascade 27 2 = [(7, 2), (6, 1)] := by decide
example : cascade 9 1 = [(9, 1)] := by decide
example : mwG 9 1 = 8 ∧ mwG 27 2 = 20 ∧ mwG 27 3 = 13 := by decide
example : mwH 9 1 = 1 ∧ mwH 27 2 = 7 ∧ mwH 27 3 = 14 := by decide
/- `f_{i-1} = g_i + h_{i-1}` on a few values. -/
example : ∀ m < 30, ∀ i < 4, 0 < i → mwG m i + mwH m i = m ∨ m = 0 := by decide

/-! ### The greedy leading index -/

/-- For `0 < r`, `m < C(m + r + 1, r)`; so the search bound `m + r` in `leadIdx` is enough. -/
theorem lt_choose_add_add_one {m r : ℕ} (hr : 0 < r) : m < (m + r + 1).choose r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hsymm : (m + k + 1 + 1).choose (k + 1) = (m + k + 1 + 1).choose (m + 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hmono : (m + 2).choose (m + 1) ≤ (m + k + 1 + 1).choose (m + 1) :=
    Nat.choose_le_choose _ (by omega)
  have hval : (m + 2).choose (m + 1) = m + 2 := by
    rw [Nat.choose_symm_of_eq_add (show m + 2 = (m + 1) + 1 by omega)]
    exact Nat.choose_one_right _
  have hidx : m + k + 1 + 1 = m + (k + 1) + 1 := by omega
  rw [← hidx, hsymm]
  omega

/-- For `0 < m` and `0 < r`, the leading index `a = leadIdx m r` satisfies `r ≤ a` and
`C(a, r) ≤ m < C(a + 1, r)`. -/
theorem leadIdx_spec {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    r ≤ leadIdx m r ∧ (leadIdx m r).choose r ≤ m ∧ m < (leadIdx m r + 1).choose r := by
  have hP : r.choose r ≤ m := by rw [Nat.choose_self]; omega
  refine ⟨Nat.le_findGreatest (by omega) hP,
    Nat.findGreatest_spec (P := fun a => a.choose r ≤ m) (by omega : r ≤ m + r) hP, ?_⟩
  by_contra hcon
  push Not at hcon
  rcases Nat.lt_or_ge (leadIdx m r) (m + r) with hlt | hge
  · exact Nat.findGreatest_is_greatest (P := fun a => a.choose r ≤ m) (k := leadIdx m r + 1)
      (Nat.lt_succ_self _) hlt hcon
  · have hle : leadIdx m r ≤ m + r := Nat.findGreatest_le _
    have heq : leadIdx m r = m + r := le_antisymm hle hge
    rw [heq] at hcon
    have hbig := lt_choose_add_add_one (m := m) hr
    omega

/-- The first binomial expansion of `0 < m` has leading index `m`. -/
theorem leadIdx_one {m : ℕ} (hm : 0 < m) : leadIdx m 1 = m := by
  obtain ⟨_, h2, h3⟩ := leadIdx_spec hm Nat.one_pos
  simp only [Nat.choose_one_right] at h2 h3
  omega

/-- The first binomial expansion of `0 < m` is `m = C(m, 1)`. -/
theorem cascade_one {m : ℕ} (hm : 0 < m) : cascade m 1 = [(m, 1)] := by
  rw [cascade, if_neg hm.ne', leadIdx_one hm, Nat.choose_one_right, Nat.sub_self, cascade]

/-! ### Closed forms of `g_i`, `h_{i-1}` at levels 1, 2, 3 -/

/-- `g_1 = c₁ - 1`. -/
theorem mwG_one (m : ℕ) : mwG m 1 = m - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · decide
  · simp [mwG, cascade_one hm]

/-- Level 2: writing `m = C(a, 2) + b` with `a = leadIdx m 2`, `h_1 = (a - 1) + [b ≠ 0]`. -/
theorem mwH_two_eq {m : ℕ} (hm : 0 < m) :
    mwH m 2 = (leadIdx m 2 - 1) + (if m - (leadIdx m 2).choose 2 = 0 then 0 else 1) := by
  rcases Nat.eq_zero_or_pos (m - (leadIdx m 2).choose 2) with hb | hb
  · simp [mwH, cascade, if_neg hm.ne', hb]
  · simp [mwH, cascade, if_neg hm.ne', hb.ne', leadIdx_one hb]

/-- Level 2: writing `m = C(a, 2) + b` with `a = leadIdx m 2`, `g_2 = C(a - 1, 2) + (b - 1)`
(truncated subtraction: the `b`-term is absent when `b = 0`). -/
theorem mwG_two_eq {m : ℕ} (hm : 0 < m) :
    mwG m 2 = (leadIdx m 2 - 1).choose 2 + (m - (leadIdx m 2).choose 2 - 1) := by
  rcases Nat.eq_zero_or_pos (m - (leadIdx m 2).choose 2) with hb | hb
  · simp [mwG, cascade, if_neg hm.ne', hb]
  · simp [mwG, cascade, if_neg hm.ne', hb.ne', leadIdx_one hb]

/-- Level 3: with `p = leadIdx m 3`, `h_2 = C(p - 1, 2) + h_1(m - C(p, 3))`. -/
theorem mwH_three_eq {m : ℕ} (hm : 0 < m) :
    mwH m 3 = (leadIdx m 3 - 1).choose 2 + mwH (m - (leadIdx m 3).choose 3) 2 := by
  simp [mwH, cascade, if_neg hm.ne']

/-- If `m < C(p, 2)` then the level-2 `h` value of `m` is at most `p - 1`. -/
theorem mwH_two_add_one_le {m p : ℕ} (hmp : m < p.choose 2) : mwH m 2 + 1 ≤ p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hp : 1 ≤ p := by
      rcases p with _ | p
      · simp at hmp
      · omega
    simpa [mwH, cascade] using hp
  · obtain ⟨_, hca, _⟩ := leadIdx_spec hm (by norm_num : 0 < 2)
    have hap : leadIdx m 2 < p := by
      by_contra h
      push Not at h
      have hmono := Nat.choose_le_choose 2 h
      omega
    rw [mwH_two_eq hm]
    split_ifs <;> omega

/-- Level 3: `h_2 ≤ C(p, 2)` where `p = leadIdx m 3`. -/
theorem mwH_three_le {m : ℕ} (hm : 0 < m) : mwH m 3 ≤ (leadIdx m 3).choose 2 := by
  rw [mwH_three_eq hm]
  obtain ⟨hp3, hcp, hcq⟩ := leadIdx_spec hm (by norm_num : 0 < 3)
  set p := leadIdx m 3 with hp
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hsucc : (p + 1).choose 3 = p.choose 2 + p.choose 3 := Nat.choose_succ_succ' p 2
  have hr : m - p.choose 3 < p.choose 2 := by omega
  have hH := mwH_two_add_one_le hr
  have hp2 : p.choose 2 = q.choose 1 + q.choose 2 := by
    rw [hq]; exact Nat.choose_succ_succ' q 1
  rw [Nat.choose_one_right] at hp2
  rw [hq, Nat.add_sub_cancel]
  rw [hq] at hH hp2
  omega

/-- Level 2: `C(a - 1, 2) ≤ g_2` where `a = leadIdx m 2`. -/
theorem choose_le_mwG_two {m : ℕ} (hm : 0 < m) : (leadIdx m 2 - 1).choose 2 ≤ mwG m 2 := by
  rw [mwG_two_eq hm]
  exact Nat.le_add_right _ _

/-! ### Arithmetic helpers -/

/-- `2 C(k + 1, 2) = (k + 1) k`. -/
theorem two_mul_choose_two (k : ℕ) : 2 * (k + 1).choose 2 = (k + 1) * k := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 1) 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_two] at h
  rw [← h, Nat.add_sub_cancel, Nat.sub_zero]
  ring

/-- `6 C(k + 2, 3) = (k + 2)(k + 1) k`. -/
theorem six_mul_choose_three (k : ℕ) : 6 * (k + 2).choose 3 = (k + 2) * (k + 1) * k := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 2) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  rw [show (3 : ℕ).factorial = 6 by decide] at h
  rw [← h, Nat.sub_zero, show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  ring

/-- The two Newton inequalities with `0 < c₂` give `27 c₃² ≤ c₂³`. -/
theorem newton_cube {c₁ c₂ c₃ : ℕ} (h₂ : 0 < c₂) (n₁ : 3 * c₂ ≤ c₁ ^ 2)
    (n₂ : 3 * c₁ * c₃ ≤ c₂ ^ 2) : 27 * c₃ ^ 2 ≤ c₂ ^ 3 := by
  have hsq : (3 * c₁ * c₃) ^ 2 ≤ (c₂ ^ 2) ^ 2 := Nat.pow_le_pow_left n₂ 2
  have hmul : 3 * c₂ * (3 * c₃ ^ 2) ≤ c₁ ^ 2 * (3 * c₃ ^ 2) := Nat.mul_le_mul_right _ n₁
  have key : c₂ * (27 * c₃ ^ 2) ≤ c₂ * c₂ ^ 3 := by nlinarith
  exact Nat.le_of_mul_le_mul_left key h₂

/-- For `a = x + 6 ≥ 6`: `(a(a + 1))³ ≤ 6 (a(a - 1)(a - 2))²`. -/
theorem cube_le_six_mul_sq (x : ℕ) :
    ((x + 6) * (x + 7)) ^ 3 ≤ 6 * ((x + 6) * (x + 5) * (x + 4)) ^ 2 := by
  have h : 6 * ((x + 6) * (x + 5) * (x + 4)) ^ 2 = ((x + 6) * (x + 7)) ^ 3 +
      (x + 6) ^ 2 * (5 * x ^ 4 + 81 * x ^ 3 + 453 * x ^ 2 + 935 * x + 342) := by ring
  rw [h]
  exact Nat.le_add_right _ _

/-- Finite check (kernel `decide`): for `c₂ < 15`, `0 < c₃ < 11` and `27 c₃² ≤ c₂³`, the
inequality `h_2 ≤ g_2` holds. -/
theorem h_two_le_g_two_of_small : ∀ c₂ < 15, ∀ c₃ < 11, 0 < c₃ → 27 * c₃ ^ 2 ≤ c₂ ^ 3 →
    mwH c₃ 3 ≤ mwG c₂ 2 := by
  decide

/-! ### The two coefficient inequalities -/

/-- Case `i = 1` of Conjecture 3.8 in degree 3: `h_1 ≤ g_1`, from `3 c₂ ≤ c₁²` and `0 < c₂`. -/
theorem h_one_le_g_one {c₁ c₂ : ℕ} (h₂ : 0 < c₂) (n₁ : 3 * c₂ ≤ c₁ ^ 2) :
    mwH c₂ 2 ≤ mwG c₁ 1 := by
  rw [mwG_one, mwH_two_eq h₂]
  obtain ⟨ha2, hca, hcb⟩ := leadIdx_spec h₂ (by norm_num : 0 < 2)
  set a := leadIdx c₂ 2 with ha
  obtain ⟨k, hk⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
  have hc2 : 2 * a.choose 2 = (k + 2) * (k + 1) := by
    rw [hk, show k + 2 = (k + 1) + 1 by omega, two_mul_choose_two]
  have hsucc : (a + 1).choose 2 = a.choose 2 + a := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    ring
  set b := c₂ - a.choose 2 with hb
  have hbc : c₂ = a.choose 2 + b := by omega
  have hba : b < a := by omega
  rw [hk] at hba hbc hc2
  split_ifs with hb0
  · -- `b = 0`: need `a ≤ c₁`
    by_contra hcon
    have hc1 : c₁ ≤ k + 1 := by omega
    have hsq : c₁ ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left hc1 2
    nlinarith
  · -- `b ≥ 1`: need `a + 1 ≤ c₁`
    by_contra hcon
    have hc1 : c₁ ≤ k + 2 := by omega
    have hsq : c₁ ^ 2 ≤ (k + 2) ^ 2 := Nat.pow_le_pow_left hc1 2
    have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
    nlinarith

/-- Case `i = 2` of Conjecture 3.8 in degree 3: `h_2 ≤ g_2`, from the two Newton inequalities
and `0 < c₂`. -/
theorem h_two_le_g_two {c₁ c₂ c₃ : ℕ} (h₂ : 0 < c₂) (n₁ : 3 * c₂ ≤ c₁ ^ 2)
    (n₂ : 3 * c₁ * c₃ ≤ c₂ ^ 2) : mwH c₃ 3 ≤ mwG c₂ 2 := by
  rcases Nat.eq_zero_or_pos c₃ with rfl | h₃
  · simp [mwH, cascade]
  have hcube := newton_cube h₂ n₁ n₂
  rcases Nat.lt_or_ge c₂ 15 with hsmall | hlarge
  · have hc3 : c₃ < 11 := by nlinarith
    exact h_two_le_g_two_of_small c₂ hsmall c₃ hc3 h₃ hcube
  obtain ⟨ha2, hca, hcb⟩ := leadIdx_spec h₂ (by norm_num : 0 < 2)
  obtain ⟨hp3, hcp, hcq⟩ := leadIdx_spec h₃ (by norm_num : 0 < 3)
  set a := leadIdx c₂ 2 with ha
  set p := leadIdx c₃ 3 with hp
  have ha6 : 6 ≤ a := by
    by_contra hcon
    have hmono : (a + 1).choose 2 ≤ (6 : ℕ).choose 2 := Nat.choose_le_choose 2 (by omega)
    have h62 : (6 : ℕ).choose 2 = 15 := by decide
    omega
  rcases Nat.lt_or_ge p a with hpa | hap
  · -- generic case: `h₂ ≤ C(p, 2) ≤ C(a - 1, 2) ≤ g₂`
    calc mwH c₃ 3 ≤ p.choose 2 := mwH_three_le h₃
      _ ≤ (a - 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      _ ≤ mwG c₂ 2 := choose_le_mwG_two h₂
  · -- impossible for `a ≥ 6`: `C(a, 3) ≤ c₃` contradicts `27 c₃² ≤ c₂³ < (C(a + 1, 2))³`
    exfalso
    obtain ⟨x, hx⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
    have hca3 : a.choose 3 ≤ c₃ := (Nat.choose_le_choose 3 hap).trans hcp
    have h6 : 6 * a.choose 3 = (x + 6) * (x + 5) * (x + 4) := by
      rw [hx, show x + 6 = (x + 4) + 2 by omega, six_mul_choose_three]
    have h2 : 2 * (a + 1).choose 2 = (x + 7) * (x + 6) := by
      rw [hx, show x + 6 + 1 = (x + 6) + 1 by omega, two_mul_choose_two]
    have hc2 : 2 * c₂ < (x + 6) * (x + 7) := by nlinarith
    have hcube2 : (2 * c₂) ^ 3 < ((x + 6) * (x + 7)) ^ 3 :=
      Nat.pow_lt_pow_left hc2 (by norm_num)
    have hsq3 : (6 * a.choose 3) ^ 2 ≤ (6 * c₃) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpoly := cube_le_six_mul_sq x
    rw [h6] at hsq3
    nlinarith

/-! ### Real-rootedness gives the Newton inequalities -/

/-- A degree-3 polynomial `f = 1 + c₁ t + c₂ t² + c₃ t³ ∈ ℕ[t]` with only real roots satisfies
`0 < c₂` and the Newton inequalities `3 c₂ ≤ c₁²` and `3 c₁ c₃ ≤ c₂²` (via Vieta). -/
theorem newton_of_real_rooted (f : ℕ[X]) (hdeg : f.natDegree = 3) (hconst : f.coeff 0 = 1)
    (hreal : Multiset.card (f.map (Nat.castRingHom ℝ)).roots = f.natDegree) :
    0 < f.coeff 2 ∧ 3 * f.coeff 2 ≤ f.coeff 1 ^ 2 ∧
      3 * f.coeff 1 * f.coeff 3 ≤ f.coeff 2 ^ 2 := by
  set F := f.map (Nat.castRingHom ℝ) with hF
  have hFdeg : F.natDegree = 3 := by
    rw [hF, natDegree_map_eq_of_injective Nat.cast_injective f, hdeg]
  have hcoeff : ∀ k, F.coeff k = (f.coeff k : ℝ) := fun k => by simp [hF]
  have hlead : F.leadingCoeff = (f.coeff 3 : ℝ) := by
    rw [leadingCoeff, hFdeg, hcoeff]
  have hcard : Multiset.card F.roots = F.natDegree := by rw [hFdeg, hreal, hdeg]
  obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp (hcard.trans hFdeg)
  have vieta : ∀ k ≤ 3, (f.coeff k : ℝ) =
      (f.coeff 3 : ℝ) * (-1) ^ (3 - k) * ({x, y, z} : Multiset ℝ).esymm (3 - k) := by
    intro k hk
    rw [← hcoeff, coeff_eq_esymm_roots_of_card hcard (by omega), hlead, hFdeg, hxyz]
  set c₁ : ℝ := (f.coeff 1 : ℝ) with hc₁
  set c₂ : ℝ := (f.coeff 2 : ℝ) with hc₂
  set c₃ : ℝ := (f.coeff 3 : ℝ) with hc₃
  have v0 : (1 : ℝ) = c₃ * (-1) ^ 3 * (x * (y * z)) := by
    simpa [Multiset.esymm, Multiset.powersetCard_one, hconst] using vieta 0 (by norm_num)
  have v1 : c₁ = c₃ * (x * z + (y * z + x * y)) := by
    simpa [Multiset.esymm, Multiset.powersetCard_one] using vieta 1 (by norm_num)
  have v2 : c₂ = -(c₃ * (z + (y + x))) := by
    simpa [Multiset.esymm, Multiset.powersetCard_one] using vieta 2 (by norm_num)
  have hc₃0 : 0 ≤ c₃ := Nat.cast_nonneg _
  have N1 : c₁ ^ 2 - 3 * c₂ = c₃ ^ 2 * ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 +
      (z * x - x * y) ^ 2) / 2 := by
    linear_combination (c₁ + c₃ * (x * z + (y * z + x * y))) * v1 - 3 * c₂ * v0 +
      3 * c₃ * (x * (y * z)) * v2
  have N2 : c₂ ^ 2 - 3 * c₁ * c₃ = c₃ ^ 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2 := by
    linear_combination (c₂ - c₃ * (z + (y + x))) * v2 - 3 * c₃ * v1
  refine ⟨?_, ?_, ?_⟩
  · have h : 0 < c₂ := by
      rcases (Nat.cast_nonneg (f.coeff 2) : (0 : ℝ) ≤ _).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hc20 : c₂ = 0 := heq.symm
        have hc3pos : 0 < c₃ := by
          rcases hc₃0.lt_or_eq with h3 | h3
          · exact h3
          · rw [← h3] at v0
            norm_num at v0
        have he1 : z + (y + x) = 0 := by
          have hprod : c₃ * (z + (y + x)) = 0 := by linarith
          rcases mul_eq_zero.mp hprod with h0 | h0
          · linarith
          · exact h0
        have hc₁0 : 0 ≤ c₁ := Nat.cast_nonneg _
        have he2 : 0 ≤ x * z + (y * z + x * y) := by
          by_contra hneg
          push Not at hneg
          nlinarith
        have hid : x ^ 2 + y ^ 2 + z ^ 2 = (z + (y + x)) ^ 2 - 2 * (x * z + (y * z + x * y)) := by
          ring
        have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
        rw [hx] at v0
        norm_num at v0
    rw [hc₂] at h
    exact_mod_cast h
  · have h : 3 * c₂ ≤ c₁ ^ 2 := by
      have hS : 0 ≤ c₃ ^ 2 * ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 +
          (z * x - x * y) ^ 2) / 2 := by positivity
      linarith
    rw [hc₁, hc₂] at h
    exact_mod_cast h
  · have h : 3 * c₁ * c₃ ≤ c₂ ^ 2 := by
      have hS : 0 ≤ c₃ ^ 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2 := by positivity
      linarith
    rw [hc₁, hc₂, hc₃] at h
    exact_mod_cast h

/-! ### Main results -/

/-- **Degree-3 Mu–Welker inequalities under Newton's inequalities.**  If `c₁, c₂, c₃ ∈ ℕ`,
`0 < c₂`, `3 c₂ ≤ c₁²` and `3 c₁ c₃ ≤ c₂²`, then the recursive decomposition of
`1 + c₁ t + c₂ t² + c₃ t³` satisfies `h_1 ≤ g_1` and `h_2 ≤ g_2`.  (Strengthening of the
degree-3 case of Mu–Welker, arXiv:2503.24076, Conjecture 3.8: Newton's inequalities are
implied by real-rootedness, see `newton_of_real_rooted`.) -/
theorem h_le_g_of_newton {c₁ c₂ c₃ : ℕ} (h₂ : 0 < c₂) (n₁ : 3 * c₂ ≤ c₁ ^ 2)
    (n₂ : 3 * c₁ * c₃ ≤ c₂ ^ 2) : mwH c₂ 2 ≤ mwG c₁ 1 ∧ mwH c₃ 3 ≤ mwG c₂ 2 :=
  ⟨h_one_le_g_one h₂ n₁, h_two_le_g_two h₂ n₁ n₂⟩

/-- **Mu–Welker Conjecture 3.8 in degree 3** (arXiv:2503.24076, Section 3).  Let
`f(t) = 1 + f_0 t + f_1 t² + f_2 t³ ∈ ℕ[t]` have degree 3 and only real roots, and let
`f = g + t h` be its recursive decomposition.  Then `h_i ≤ g_i` for `i = 1, 2`; here
`h_1 = mwH f_1 2`, `g_1 = mwG f_0 1`, `h_2 = mwH f_2 3`, `g_2 = mwG f_1 2`, and
`f_{i-1} = f.coeff i`. -/
theorem mu_welker_conj_3_8_degree_three (f : ℕ[X]) (hdeg : f.natDegree = 3)
    (hconst : f.coeff 0 = 1)
    (hreal : Multiset.card (f.map (Nat.castRingHom ℝ)).roots = f.natDegree) :
    mwH (f.coeff 2) 2 ≤ mwG (f.coeff 1) 1 ∧ mwH (f.coeff 3) 3 ≤ mwG (f.coeff 2) 2 := by
  obtain ⟨h₂, n₁, n₂⟩ := newton_of_real_rooted f hdeg hconst hreal
  exact h_le_g_of_newton h₂ n₁ n₂

/-! ### Non-vacuity: `(1 + t)³` satisfies every hypothesis of the main theorem. -/

example : ((X + 1) ^ 3 : ℕ[X]).natDegree = 3 ∧ ((X + 1) ^ 3 : ℕ[X]).coeff 0 = 1 ∧
    Multiset.card (((X + 1) ^ 3 : ℕ[X]).map (Nat.castRingHom ℝ)).roots =
      ((X + 1) ^ 3 : ℕ[X]).natDegree := by
  have hdeg : ((X + 1) ^ 3 : ℕ[X]).natDegree = 3 := by
    rw [natDegree_pow, ← C_1, natDegree_X_add_C]
  refine ⟨hdeg, by simp [coeff_zero_eq_eval_zero], ?_⟩
  rw [hdeg, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    ← C_1, roots_pow, roots_X_add_C]
  simp

/-- Non-vacuity of the Newton form at the paper's example `(1 + 3t)³ = 1 + 9t + 27t² + 27t³`. -/
example : 0 < 27 ∧ 3 * 27 ≤ 9 ^ 2 ∧ 3 * 9 * 27 ≤ 27 ^ 2 := by norm_num

end MuWelkerDegreeThree
