/-
# Profiles of dynamical systems: the profile semiring has no prime elements

## Source

C. Gaze-Maillot and A. E. Porreca, *Profiles of dynamical systems and their algebra*,
arXiv 2008.00843. Definitions: Section 1 (profile of a dynamical system), Section 2
(Definition `def:product`, Lemma `thm:count-points`, Theorem: `(P, +, ×)` is a commutative
semiring with unit `(1)`). The question sits in Section `sec:conclusions`, last sentence,
verbatim:

  "And, from a more algebraic perspective, what are the prime elements of P? Do they exist
  at all?"

The product is `(p × q)_i = p_i * |q|_{≤ i} + q_i * |p|_{≤ i} - p_i * q_i` (the printed
formula writes `∑_{j=0}^i q_i`; the intended summand is `q_j`, as Lemma `thm:count-points`
and the multiplication table of Fig. `fig:products` confirm).

## Status

Open in the paper (posed as a question). This module answers it: there are
no prime elements. For every profile `p ∉ {(0), (1)}` there are profiles `q, r` with
`p ∣ q × r`, `p ∤ q`, `p ∤ r` (`exists_not_prime_witness`, hence `not_pPrime`). The key
lemma `pre_pmul` says prefix sums turn `×` into the pointwise product. Witnesses, with
`c = |p| ≥ 2` and `h` the height of `p`:
* `h = 0` (`p = (c)`): `q = (1, c - 1)`, `r = (c, 1)`, quotient `(1, c)`;
* `h ≥ 1`: `q = (c)`, `r` with prefix sums `(i + 1) |p|_{≤ i}` for `i < h` and `c h + 1` from
  `h` on; the quotient has prefix sums `c (i + 1)` then `c h + 1`.
Also proved: the only unit is `(1)` (`pIsUnit_iff`) and there are no zero divisors
(`pmul_eq_zero`).

Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace DynamicalProfiles

open Finset

/-- A profile is an eventually null sequence of naturals that is positive exactly on an initial
segment `[0, h]` (or is identically zero): eventually zero, and a nonzero entry is preceded by a
nonzero entry. -/
def IsProfile (p : ℕ → ℕ) : Prop :=
  (∃ N, ∀ i, N ≤ i → p i = 0) ∧ ∀ i, p (i + 1) ≠ 0 → p i ≠ 0

/-- `pre p n = p 0 + ⋯ + p (n - 1)`, the sum of the first `n` entries; `pre p (i + 1)` is the
paper's `|A|_{≤ i}`. -/
def pre (p : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, p j

/-- The product of profiles (Definition `def:product`, read with the evident summation index):
`(p × q)_i = p_i * (q_0 + ⋯ + q_i) + q_i * (p_0 + ⋯ + p_i) - p_i * q_i`. -/
def pmul (p q : ℕ → ℕ) (i : ℕ) : ℕ :=
  p i * ∑ j ∈ range (i + 1), q j + q i * ∑ j ∈ range (i + 1), p j - p i * q i

/-- Divisibility in the profile semiring: `p ∣ x` iff `x = p × s` for some profile `s`. -/
def PDvd (p x : ℕ → ℕ) : Prop := ∃ s, IsProfile s ∧ pmul p s = x

/-- The unit profile `(1)`, the profile of a single fixed point. -/
def one : ℕ → ℕ := Pi.single 0 1

/-- A profile is a unit when it divides `(1)`. -/
def PIsUnit (p : ℕ → ℕ) : Prop := PDvd p one

/-- A prime element of the profile semiring: a nonzero non-unit profile `p` such that
`p ∣ q × r` implies `p ∣ q` or `p ∣ r` for all profiles `q, r`. -/
def PPrime (p : ℕ → ℕ) : Prop :=
  IsProfile p ∧ p ≠ 0 ∧ ¬ PIsUnit p ∧
    ∀ q r, IsProfile q → IsProfile r → PDvd p (pmul q r) → PDvd p q ∨ PDvd p r

/-- The profile written as a finite list, padded by zeros. -/
def ofList (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

/-! Ground truth: entries of the paper's multiplication table (Fig. `fig:products`). -/

example : (List.range 4).map (pmul (ofList [1, 1]) (ofList [1, 1, 1])) = [1, 3, 2, 0] := by
  decide

example : (List.range 3).map (pmul (ofList [1, 2]) (ofList [2, 1])) = [2, 7, 0] := by
  decide

example : (List.range 4).map (pmul (ofList [1, 1, 1]) (ofList [1, 1, 1])) = [1, 3, 5, 0] := by
  decide

example : (List.range 2).map (pmul (ofList [2]) (ofList [3])) = [6, 0] := by
  decide

/-- The two factorisations of `(2,4)` from the paper's non-UFD theorem. -/
example : (List.range 3).map (pmul (ofList [2]) (ofList [1, 2])) = [2, 4, 0] ∧
    (List.range 3).map (pmul (ofList [1, 1]) (ofList [2, 1])) = [2, 4, 0] := by
  decide

example : IsProfile (ofList [8, 7, 8, 4]) := by
  refine ⟨⟨4, fun i hi => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    simp [ofList]
  · match i, hi with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | i + 3, hi => exact absurd (by simp [ofList]) hi

example : ¬ IsProfile (ofList [1, 0, 1]) := fun h => h.2 1 (by decide) (by decide)

/-! ## The prefix-sum model -/

/-- Prefix sums satisfy `pre p (n + 1) = pre p n + p n`. -/
theorem pre_succ (p : ℕ → ℕ) (n : ℕ) : pre p (n + 1) = pre p n + p n :=
  sum_range_succ p n

/-- The empty prefix sum vanishes. -/
@[simp] theorem pre_zero (p : ℕ → ℕ) : pre p 0 = 0 := sum_range_zero p

/-- Prefix sums are monotone in the length. -/
theorem pre_mono (p : ℕ → ℕ) : Monotone (pre p) := fun _ _ hab =>
  sum_le_sum_of_subset (range_subset_range.mpr hab)

/-- The product, rewritten without truncated subtraction. -/
theorem pmul_eq (p q : ℕ → ℕ) (n : ℕ) :
    pmul p q n = p n * pre q n + q n * pre p n + p n * q n := by
  change p n * pre q (n + 1) + q n * pre p (n + 1) - p n * q n = _
  rw [pre_succ, pre_succ]
  exact Nat.sub_eq_of_eq_add (by ring)

/-- Key lemma: prefix sums turn the profile product into the pointwise product,
`|p × q|_{< n} = |p|_{< n} * |q|_{< n}`. -/
theorem pre_pmul (p q : ℕ → ℕ) (n : ℕ) : pre (pmul p q) n = pre p n * pre q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pre_succ, ih, pmul_eq, pre_succ p, pre_succ q]
    ring

/-- Sequences with the same prefix sums coincide. -/
theorem eq_of_pre_eq {x y : ℕ → ℕ} (h : ∀ n, pre x n = pre y n) : x = y := by
  funext i
  have hi := h (i + 1)
  rw [pre_succ, pre_succ, h i] at hi
  omega

/-- A divisibility `p ∣ x` gives a profile quotient `s` with `P_n S_n = X_n` for prefix sums. -/
theorem pre_of_pdvd {p x : ℕ → ℕ} (h : PDvd p x) :
    ∃ s, IsProfile s ∧ ∀ n, pre p n * pre s n = pre x n := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, hs, fun n => (pre_pmul p s n).symm⟩

/-- Conversely, a profile `s` with `P_n S_n = X_n` for all prefix sums witnesses `p ∣ x`. -/
theorem pdvd_of_pre {p x s : ℕ → ℕ} (hs : IsProfile s)
    (h : ∀ n, pre p n * pre s n = pre x n) : PDvd p x :=
  ⟨s, hs, eq_of_pre_eq fun n => by rw [pre_pmul]; exact h n⟩

/-- A sequence `X` with `X 0 = 0`, strictly increasing on `[0, h + 1]` and constant afterwards is
the prefix-sum sequence of the profile of its differences. -/
theorem ofPrefix (X : ℕ → ℕ) (h : ℕ) (h0 : X 0 = 0) (hlt : ∀ i, i ≤ h → X i < X (i + 1))
    (heq : ∀ i, h < i → X (i + 1) = X i) :
    IsProfile (fun i => X (i + 1) - X i) ∧ ∀ n, pre (fun i => X (i + 1) - X i) n = X n := by
  have hmono : Monotone X := by
    refine monotone_nat_of_le_succ fun i => ?_
    rcases le_or_gt i h with hi | hi
    · exact (hlt i hi).le
    · exact (heq i hi).ge
  refine ⟨⟨⟨h + 1, fun i hi => ?_⟩, fun i hi => ?_⟩, fun n => ?_⟩
  · simp only [heq i (by omega), Nat.sub_self]
  · have hle : i + 1 ≤ h := by
      by_contra hcon
      exact hi (by simp only [heq (i + 1) (by omega), Nat.sub_self])
    have hlt' := hlt i (by omega)
    show X (i + 1) - X i ≠ 0
    omega
  · rw [pre, sum_range_tsub hmono, h0, Nat.sub_zero]

/-- Every nonzero profile has a height `h`: it is positive on `[0, h]` and zero beyond. -/
theorem exists_height {p : ℕ → ℕ} (hp : IsProfile p) (h0 : p ≠ 0) :
    ∃ h, (∀ i, i ≤ h → p i ≠ 0) ∧ ∀ i, h < i → p i = 0 := by
  classical
  obtain ⟨hN, hdown⟩ := hp
  obtain ⟨N, hspec, hmin⟩ : ∃ N, (∀ i, N ≤ i → p i = 0) ∧
      ∀ m, m < N → ¬ ∀ i, m ≤ i → p i = 0 :=
    ⟨Nat.find hN, Nat.find_spec hN, fun m hm => Nat.find_min hN hm⟩
  have hNpos : N ≠ 0 := by
    intro hN0
    apply h0
    funext i
    exact hspec i (by omega)
  have htop : p (N - 1) ≠ 0 := by
    have hm := hmin (N - 1) (by omega)
    push Not at hm
    obtain ⟨i, hi, hpi⟩ := hm
    have hiN : i < N := by
      by_contra hc
      exact hpi (hspec i (by omega))
    rwa [show i = N - 1 by omega] at hpi
  have hall : ∀ k, p (N - 1 - k) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using htop
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (N - 1 - k) with hz | hpos
      · rwa [show N - 1 - (k + 1) = N - 1 - k by omega]
      · apply hdown
        rwa [show N - 1 - (k + 1) + 1 = N - 1 - k by omega]
  refine ⟨N - 1, fun i hi => ?_, fun i hi => hspec i (by omega)⟩
  have hk := hall (N - 1 - i)
  rwa [show N - 1 - (N - 1 - i) = i by omega] at hk

/-- **Main theorem (no primes).** For every profile `p` other than `(0)` and `(1)` there are
profiles `q, r` with `p ∣ q × r`, `p ∤ q` and `p ∤ r`. This answers the question of
Gaze-Maillot and Porreca (arXiv 2008.00843, Conclusions): the profile semiring has no prime
elements. -/
theorem exists_not_prime_witness (p : ℕ → ℕ) (hp : IsProfile p) (h0 : p ≠ 0) (h1 : p ≠ one) :
    ∃ q r, IsProfile q ∧ IsProfile r ∧ PDvd p (pmul q r) ∧ ¬ PDvd p q ∧ ¬ PDvd p r := by
  obtain ⟨h, hpos, hzero⟩ := exists_height hp h0
  obtain ⟨c, hc_def⟩ : ∃ c, c = pre p (h + 1) := ⟨_, rfl⟩
  have hconst : ∀ n, h + 1 ≤ n → pre p n = c := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hc_def.symm
    | succ n hn ih => rw [pre_succ, ih, hzero n (by omega), add_zero]
  have hp1 : pre p 1 = p 0 := by simp [pre]
  have hpos1 : ∀ n, 1 ≤ n → 1 ≤ pre p n := by
    intro n hn
    have hp0 := hpos 0 (Nat.zero_le _)
    exact (show 1 ≤ pre p 1 by omega).trans (pre_mono p hn)
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · -- height `0`: `p = (c)` with `c ≥ 2`; take `q = (1, c - 1)` and `r = (c, 1)`.
    have hc : 2 ≤ c := by
      have hc0 : c = p 0 := hc_def.trans hp1
      have hne : p 0 ≠ 1 := by
        intro hp01
        apply h1
        funext i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp [one, hp01]
        · simp [one, hzero i hi, hi.ne']
      have := hpos 0 le_rfl
      omega
    obtain ⟨hq, hQ⟩ := ofPrefix (fun n => if n = 0 then 0 else if n = 1 then 1 else c) 1
      (by simp) (by intro i hi; split_ifs <;> first | omega | contradiction)
      (by intro i hi; split_ifs <;> first | omega | contradiction)
    obtain ⟨hr, hR⟩ := ofPrefix (fun n => if n = 0 then 0 else if n = 1 then c else c + 1) 1
      (by simp) (by intro i hi; split_ifs <;> first | omega | contradiction)
      (by intro i hi; split_ifs <;> omega)
    obtain ⟨hs, hS⟩ := ofPrefix (fun n => if n = 0 then 0 else if n = 1 then 1 else c + 1) 1
      (by simp) (by intro i hi; split_ifs <;> first | omega | contradiction)
      (by intro i hi; split_ifs <;> omega)
    refine ⟨_, _, hq, hr, pdvd_of_pre hs fun n => ?_, fun hd => ?_, fun hd => ?_⟩
    · rw [pre_pmul, hQ, hR, hS]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [hconst n hn]
        split_ifs <;> omega
    · obtain ⟨s, -, hpre⟩ := pre_of_pdvd hd
      have h1' := hpre 1
      rw [hconst 1 le_rfl, hQ] at h1'
      have hc1 : c = 1 := Nat.eq_one_of_mul_eq_one_right (by simpa using h1')
      omega
    · obtain ⟨s, -, hpre⟩ := pre_of_pdvd hd
      have h2 := hpre 2
      rw [hconst 2 (by omega), hR] at h2
      have hdvd : c ∣ c + 1 := ⟨_, by simpa using h2.symm⟩
      have hc1 := Nat.le_of_dvd one_pos ((Nat.dvd_add_right (dvd_refl c)).mp hdvd)
      omega
  · -- height `h ≥ 1`: take `q = (c)` and `r` with prefix sums `(i + 1) P_i`, then `c h + 1`.
    have hlt1 : pre p 1 < c := by
      have hm := pre_mono p (show 1 ≤ h by omega)
      have hph := hpos h le_rfl
      have hcs : c = pre p h + p h := by rw [hc_def, pre_succ]
      omega
    have hc : 2 ≤ c := by
      have := hpos1 1 le_rfl
      omega
    obtain ⟨hq, hQ⟩ := ofPrefix (fun n => if n = 0 then 0 else c) 0
      (by simp) (by intro i hi; split_ifs <;> first | omega | contradiction)
      (by intro i hi; split_ifs <;> first | omega | contradiction)
    obtain ⟨hr, hR⟩ := ofPrefix (fun n => if n ≤ h then n * pre p n else c * h + 1) h
      (by simp) (by
        intro i hi
        have hm : pre p i ≤ pre p (i + 1) := pre_mono p (Nat.le_succ i)
        have hp' := hpos1 (i + 1) (by omega)
        rcases lt_or_eq_of_le hi with hih | rfl
        · rw [if_pos hi, if_pos (by omega)]
          nlinarith
        · rw [if_pos le_rfl, if_neg (by omega), ← hconst (i + 1) le_rfl]
          nlinarith)
      (by intro i hi; split_ifs <;> omega)
    obtain ⟨hs, hS⟩ := ofPrefix (fun n => if n ≤ h then c * n else c * h + 1) h
      (by simp) (by
        intro i hi
        rcases lt_or_eq_of_le hi with hih | rfl
        · rw [if_pos hi, if_pos (by omega)]
          nlinarith
        · rw [if_pos le_rfl, if_neg (by omega)]
          omega)
      (by intro i hi; split_ifs <;> omega)
    refine ⟨_, _, hq, hr, pdvd_of_pre hs fun n => ?_, fun hd => ?_, fun hd => ?_⟩
    · rw [pre_pmul, hQ, hR, hS]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg hn.ne']
        split_ifs with hnh
        · ring
        · rw [hconst n (by omega)]
    · obtain ⟨s, -, hpre⟩ := pre_of_pdvd hd
      have htop := hpre (h + 1)
      have hbot := hpre 1
      rw [hconst (h + 1) le_rfl, hQ, if_neg (show h + 1 ≠ 0 by omega)] at htop
      rw [hQ, if_neg (show (1 : ℕ) ≠ 0 by omega)] at hbot
      have hs1 : pre s (h + 1) = 1 := by
        have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < c) (htop.trans (mul_one c).symm)
        exact this
      have hsle : pre s 1 ≤ 1 := hs1 ▸ pre_mono s (by omega)
      have hle : pre p 1 * pre s 1 ≤ pre p 1 := by nlinarith
      omega
    · obtain ⟨s, -, hpre⟩ := pre_of_pdvd hd
      have htop := hpre (h + 1)
      rw [hconst (h + 1) le_rfl, hR, if_neg (show ¬ h + 1 ≤ h by omega)] at htop
      have hdvd : c ∣ c * h + 1 := ⟨_, htop.symm⟩
      have hc1 := Nat.le_of_dvd one_pos ((Nat.dvd_add_right (dvd_mul_right c h)).mp hdvd)
      omega

/-! ## Units, zero divisors, and the answer -/

/-- Prefix sums of the unit profile: `0` for the empty prefix, `1` otherwise. -/
theorem pre_one (n : ℕ) : pre one n = if n = 0 then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pre_succ, ih]
    rcases n with _ | n <;> simp [one]

/-- `(1)` is a profile. -/
theorem isProfile_one : IsProfile one :=
  ⟨⟨1, fun i hi => by simp only [one, Pi.single_apply]; exact if_neg (by omega)⟩,
    fun i hi => absurd (by simp [one]) hi⟩

/-- `(1)` is a unit. -/
theorem pIsUnit_one : PIsUnit one :=
  ⟨one, isProfile_one, eq_of_pre_eq fun n => by
    rw [pre_pmul, pre_one]
    split_ifs <;> rfl⟩

/-- The only unit of the profile semiring is `(1)`. -/
theorem pIsUnit_iff (p : ℕ → ℕ) : PIsUnit p ↔ p = one := by
  refine ⟨fun hu => ?_, fun h => h ▸ pIsUnit_one⟩
  obtain ⟨s, -, hpre⟩ := pre_of_pdvd hu
  refine eq_of_pre_eq fun n => ?_
  rw [pre_one]
  split_ifs with hn
  · rw [hn, pre_zero]
  · have hn' := hpre n
    rw [pre_one, if_neg hn] at hn'
    exact Nat.eq_one_of_mul_eq_one_right hn'

/-- A profile with `p 0 = 0` is the zero profile. -/
theorem eq_zero_of_head_eq_zero {p : ℕ → ℕ} (hp : IsProfile p) (h : p 0 = 0) : p = 0 := by
  funext i
  induction i with
  | zero => exact h
  | succ i ih =>
    by_contra hne
    exact hp.2 i hne ih

/-- The profile semiring has no zero divisors, so `(0)` generates a prime ideal (it is excluded
from being a prime element only by the convention that primes are nonzero). -/
theorem pmul_eq_zero {q r : ℕ → ℕ} (hq : IsProfile q) (hr : IsProfile r) (h : pmul q r = 0) :
    q = 0 ∨ r = 0 := by
  have h1 := pre_pmul q r 1
  rw [h] at h1
  have h0 : q 0 * r 0 = 0 := by simpa [pre] using h1.symm
  rcases Nat.mul_eq_zero.mp h0 with hq0 | hr0
  · exact Or.inl (eq_zero_of_head_eq_zero hq hq0)
  · exact Or.inr (eq_zero_of_head_eq_zero hr hr0)

/-- **Answer to the question of Gaze-Maillot and Porreca** (arXiv 2008.00843, Conclusions:
"what are the prime elements of P? Do they exist at all?"): the profile semiring has no prime
elements. -/
theorem not_pPrime (p : ℕ → ℕ) : ¬ PPrime p := by
  rintro ⟨hp, h0, hu, hprime⟩
  have h1 : p ≠ one := fun h => hu (h ▸ pIsUnit_one)
  obtain ⟨q, r, hq, hr, hd, hnq, hnr⟩ := exists_not_prime_witness p hp h0 h1
  rcases hprime q r hq hr hd with h | h
  · exact hnq h
  · exact hnr h

/-- Non-vacuity: the hypotheses of `exists_not_prime_witness` hold jointly, e.g. at `(1, 2)`. -/
example : IsProfile (ofList [1, 2]) ∧ ofList [1, 2] ≠ 0 ∧ ofList [1, 2] ≠ one := by
  refine ⟨⟨⟨2, fun i hi => ?_⟩, fun i hi => ?_⟩, fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    simp [ofList]
  · match i, hi with
    | 0, _ => decide
    | i + 1, hi => exact absurd (by simp [ofList]) hi
  · simpa [ofList] using congrFun h 1
  · simpa [ofList, one] using congrFun h 1

end DynamicalProfiles
