/-
# Ruzsa pseudo-polynomials: Hall's lcm characterization of the Newton coefficients

R. R. Hall, “On pseudo-polynomials”, Mathematika 18 (1971):
`f : ℕ → ℤ` preserves congruences iff `lcm(1,…,k)` divides its `k`-th
Newton coefficient `(Δ^k f)(0)` for every `k`. See also
Cegielski–Grigorieff–Guessarian on congruence-preserving functions
and V. Dimitrov's MathOverflow proposal, https://mathoverflow.net/a/219702 .
A nonzero Newton coefficient satisfies `2^k ≤ (k+1)|a_k|`.
This module does not prove Ruzsa's growth conjecture, nor the `e-1`
theorem, which needs the asymptotic `lcm(1,…,k)^{1/k} → e`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.RuzsaPseudoPolynomialNewton

open Finset

/-- `f : ℕ → ℤ` *preserves congruences* (is a Ruzsa pseudo-polynomial): `k ∣ f (n + k) - f n`
for all `n k : ℕ`, i.e. `(a - b) ∣ f a - f b` for all `b ≤ a`. -/
def IsPseudoPoly (f : ℕ → ℤ) : Prop := ∀ n k : ℕ, (k : ℤ) ∣ f (n + k) - f n

/-- Bridge to the source's formulation: `IsPseudoPoly f` holds iff `(n - m) ∣ f n - f m` for all
`n m : ℕ` (difference taken in `ℤ`). -/
theorem isPseudoPoly_iff_forall_sub_dvd (f : ℕ → ℤ) :
    IsPseudoPoly f ↔ ∀ n m : ℕ, ((n : ℤ) - m) ∣ f n - f m := by
  constructor
  · intro hf n m
    rcases le_total m n with hmn | hnm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have hk : ((m + k : ℕ) : ℤ) - m = k := by push_cast; ring
      rw [hk]
      exact hf m k
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have hk : (n : ℤ) - ((n + k : ℕ) : ℤ) = -k := by push_cast; ring
      rw [hk, neg_dvd, ← neg_sub, dvd_neg]
      exact hf n k
  · intro h n k
    have hnk := h (n + k) n
    rwa [show ((n + k : ℕ) : ℤ) - n = k by push_cast; ring] at hnk

/-- The absorption step: if `1 ≤ j` and `j ∣ L`, then `d ∣ L * C(d, j)`. -/
theorem dvd_mul_choose_of_dvd {L d j : ℕ} (hj : 1 ≤ j) (hjL : j ∣ L) : d ∣ L * d.choose j := by
  obtain ⟨q, rfl⟩ := hjL
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rcases d with _ | e
  · simp
  · have habs : (e + 1) * e.choose i = (e + 1).choose (i + 1) * (i + 1) :=
      Nat.add_one_mul_choose_eq e i
    exact ⟨q * e.choose i, by rw [mul_comm (i + 1) q, mul_assoc, mul_comm (i + 1), ← habs]; ring⟩

/-- Key divisibility: `d ∣ lcm(1..k) * (C(m + d, k) - C(m, k))`. -/
theorem dvd_lcmUpto_mul_choose_sub (k m d : ℕ) :
    (d : ℤ) ∣ (Nat.lcmUpto k : ℤ) * ((m + d).choose k : ℤ) -
      (Nat.lcmUpto k : ℤ) * (m.choose k : ℤ) := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [Nat.add_choose_eq]
  push_cast
  rw [Finset.mul_sum, Finset.sum_eq_single (k, 0)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : 1 ≤ j := by
      by_contra hj0
      obtain rfl : j = 0 := by omega
      exact hne (Prod.ext (by simpa using hij) rfl)
    have hjk : j ∣ Nat.lcmUpto k :=
      Finset.dvd_lcm (f := id) (mem_Icc.2 ⟨hj, by omega⟩)
    have hz : ((Nat.lcmUpto k * d.choose j : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_choose_of_dvd hj hjk)
    push_cast at hz
    calc (Nat.lcmUpto k : ZMod d) * ((m.choose (i, j).1 : ZMod d) * (d.choose (i, j).2 : ZMod d))
        = (m.choose i : ZMod d) * ((Nat.lcmUpto k : ZMod d) * (d.choose j : ZMod d)) := by ring
      _ = 0 := by rw [hz, mul_zero]
  · intro h; simp at h

/-- Pseudo-polynomials are closed under subtraction. -/
theorem IsPseudoPoly.sub {f g : ℕ → ℤ} (hf : IsPseudoPoly f) (hg : IsPseudoPoly g) :
    IsPseudoPoly (fun n => f n - g n) := fun n k => by
  have h := dvd_sub (hf n k) (hg n k)
  rwa [show f (n + k) - f n - (g (n + k) - g n) = f (n + k) - g (n + k) - (f n - g n) by ring]
    at h

/-- Pseudo-polynomials are closed under multiplication by an integer constant. -/
theorem IsPseudoPoly.const_mul {f : ℕ → ℤ} (hf : IsPseudoPoly f) (c : ℤ) :
    IsPseudoPoly (fun n => c * f n) := fun n k => by
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right (hf n k) c

/-- Pseudo-polynomials are closed under finite sums. -/
theorem isPseudoPoly_sum {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℤ)
    (hg : ∀ i ∈ s, IsPseudoPoly (g i)) : IsPseudoPoly (fun n => ∑ i ∈ s, g i n) := fun n k => by
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i hi => hg i hi n k

/-- `n ↦ lcm(1..k) * C(n, k)` is a pseudo-polynomial. -/
theorem isPseudoPoly_lcmUpto_mul_choose (k : ℕ) :
    IsPseudoPoly (fun n => (Nat.lcmUpto k : ℤ) * (n.choose k : ℤ)) := fun n d =>
  dvd_lcmUpto_mul_choose_sub k n d

/-- If `lcm(1..k) ∣ c`, then `n ↦ c * C(n, k)` is a pseudo-polynomial. -/
theorem isPseudoPoly_mul_choose_of_dvd {k : ℕ} {c : ℤ} (hc : (Nat.lcmUpto k : ℤ) ∣ c) :
    IsPseudoPoly (fun n => c * (n.choose k : ℤ)) := by
  obtain ⟨b, rfl⟩ := hc
  have h := (isPseudoPoly_lcmUpto_mul_choose k).const_mul b
  convert h using 2 with n
  ring

/-- Newton's forward-difference expansion, truncated at any `N > n`:
`f n = ∑_{j < N} C(n, j) (Δ^j f)(0)`. -/
theorem eq_sum_choose_mul_fwdDiff_iter (f : ℕ → ℤ) {n N : ℕ} (hnN : n < N) :
    f n = ∑ j ∈ range N, (n.choose j : ℤ) * (fwdDiff 1)^[j] f 0 := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at h
  rw [h]
  refine Finset.sum_subset (fun j hj => by simp only [mem_range] at hj ⊢; omega) fun j _ hj => ?_
  simp only [mem_range, not_lt] at hj
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- Hall's characterization, direction `⇐`: if `lcm(1..k)` divides every Newton coefficient
`(Δ^k f)(0)`, then `f` is a pseudo-polynomial. -/
theorem isPseudoPoly_of_forall_lcmUpto_dvd {f : ℕ → ℤ}
    (h : ∀ k : ℕ, (Nat.lcmUpto k : ℤ) ∣ (fwdDiff 1)^[k] f 0) : IsPseudoPoly f := by
  intro n d
  set N := n + d + 1 with hN
  have hF : IsPseudoPoly (fun x => ∑ j ∈ range N, (fwdDiff 1)^[j] f 0 * (x.choose j : ℤ)) :=
    isPseudoPoly_sum _ _ fun j _ => isPseudoPoly_mul_choose_of_dvd (h j)
  have hexp : ∀ x, x < N → f x = ∑ j ∈ range N, (fwdDiff 1)^[j] f 0 * (x.choose j : ℤ) :=
    fun x hx => by
      rw [eq_sum_choose_mul_fwdDiff_iter f hx]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hexp (n + d) (by omega), hexp n (by omega)]
  exact hF n d

/-- Hall's characterization, direction `⇒`: the `k`-th Newton coefficient of a
pseudo-polynomial is divisible by `lcm(1..k)`. -/
theorem lcmUpto_dvd_fwdDiff_iter_of_isPseudoPoly {f : ℕ → ℤ} (hf : IsPseudoPoly f) (k : ℕ) :
    (Nat.lcmUpto k : ℤ) ∣ (fwdDiff 1)^[k] f 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set a : ℕ → ℤ := fun j => (fwdDiff 1)^[j] f 0 with ha
  -- the remainder after subtracting the first `k` Newton terms
  set g : ℕ → ℤ := fun x => f x - ∑ j ∈ range k, a j * (x.choose j : ℤ) with hg
  have hgP : IsPseudoPoly g :=
    hf.sub (isPseudoPoly_sum _ _ fun j hj => isPseudoPoly_mul_choose_of_dvd
      (ih j (mem_range.1 hj)))
  have hexp : ∀ x, x < k + 1 →
      f x = ∑ j ∈ range (k + 1), a j * (x.choose j : ℤ) := fun x hx => by
    rw [eq_sum_choose_mul_fwdDiff_iter f hx]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hg_lt : ∀ i, i < k → g i = 0 := fun i hi => by
    simp only [hg]
    rw [hexp i (by omega), Finset.sum_range_succ, Nat.choose_eq_zero_of_lt hi]
    simp
  have hg_k : g k = a k := by
    simp only [hg]
    rw [hexp k (by omega), Finset.sum_range_succ, Nat.choose_self]
    simp
  have hdvd : ∀ i ∈ Icc 1 k, i ∣ (a k).natAbs := fun i hi => by
    obtain ⟨hi1, hik⟩ := mem_Icc.1 hi
    have h1 := hgP (k - i) i
    rw [Nat.sub_add_cancel hik, hg_k, hg_lt (k - i) (by omega), sub_zero] at h1
    exact Int.natCast_dvd.1 h1
  exact Int.natCast_dvd.2 (Finset.lcm_dvd hdvd)

/-- **Hall's characterization of pseudo-polynomials** (Hall 1971; see also
Cegielski–Grigorieff–Guessarian).  A map `f : ℕ → ℤ` preserves congruences,
`k ∣ f (n + k) - f n` for all `n k`, if and only if `lcm(1, …, k)` divides the `k`-th Newton
coefficient `(Δ^k f)(0)` for every `k`.  This is the lemma underlying Ruzsa's conjecture
(MathOverflow answer 219702). -/
theorem isPseudoPoly_iff (f : ℕ → ℤ) :
    IsPseudoPoly f ↔ ∀ k : ℕ, (Nat.lcmUpto k : ℤ) ∣ (fwdDiff 1)^[k] f 0 :=
  ⟨lcmUpto_dvd_fwdDiff_iter_of_isPseudoPoly, isPseudoPoly_of_forall_lcmUpto_dvd⟩

/-- Growth corollary: a nonzero `k`-th Newton coefficient `a_k` of a pseudo-polynomial satisfies
`2^k ≤ (k + 1) * |a_k|`, since `lcm(1..k) ∣ a_k` and `2^k ≤ (k + 1) * lcm(1..k)`. -/
theorem two_pow_le_succ_mul_natAbs_fwdDiff_iter {f : ℕ → ℤ} (hf : IsPseudoPoly f) {k : ℕ}
    (hk : (fwdDiff 1)^[k] f 0 ≠ 0) : 2 ^ k ≤ (k + 1) * ((fwdDiff 1)^[k] f 0).natAbs := by
  have hdvd : Nat.lcmUpto k ∣ ((fwdDiff 1)^[k] f 0).natAbs :=
    Int.natCast_dvd.1 (lcmUpto_dvd_fwdDiff_iter_of_isPseudoPoly hf k)
  have hle : Nat.lcmUpto k ≤ ((fwdDiff 1)^[k] f 0).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.2 hk) hdvd
  calc 2 ^ k ≤ (k + 1) * Nat.lcmUpto k := Chebyshev.two_pow_le_mul_lcmUpto k
    _ ≤ (k + 1) * ((fwdDiff 1)^[k] f 0).natAbs := Nat.mul_le_mul_left _ hle

/-! ## Examples -/

example : Nat.lcmUpto 4 = 12 := by decide

example : Nat.lcmUpto 6 = 60 := rfl

/-- `n ↦ n²` is a pseudo-polynomial: `(n + k)² - n² = k (2n + k)`. -/
theorem isPseudoPoly_sq : IsPseudoPoly (fun n => (n : ℤ) ^ 2) := fun n k =>
  ⟨2 * n + k, by push_cast; ring⟩

/-- `n ↦ C(n, 2)` is not a pseudo-polynomial: `C(2, 2) - C(0, 2) = 1` is odd. -/
theorem not_isPseudoPoly_choose_two : ¬ IsPseudoPoly (fun n => (n.choose 2 : ℤ)) := by
  intro h
  have h2 := h 0 2
  norm_num at h2

/-- The second Newton coefficient of `C(n, 2)` is `1`, not divisible by `lcm(1, 2) = 2`. -/
example : (fwdDiff 1)^[2] (fun n : ℕ => (n.choose 2 : ℤ)) 0 = 1 := by
  rw [fwdDiff_iter_choose_zero]; rfl

/-- The second Newton coefficient of `n²` is `2`, divisible by `lcm(1, 2) = 2`. -/
example : (fwdDiff 1)^[2] (fun n : ℕ => (n : ℤ) ^ 2) 0 = 2 := by
  rw [fwdDiff_iter_eq_sum_shift]; decide

/-- Non-vacuity of the `⇒` direction at `n²`. -/
example (k : ℕ) : (Nat.lcmUpto k : ℤ) ∣ (fwdDiff 1)^[k] (fun n : ℕ => (n : ℤ) ^ 2) 0 :=
  (isPseudoPoly_iff _).1 isPseudoPoly_sq k

/-- Non-vacuity of the `⇐` direction: `n ↦ lcm(1..3) C(n, 3)` is a pseudo-polynomial whose
third Newton coefficient is `6 ≠ 0`. -/
example : IsPseudoPoly (fun n => (Nat.lcmUpto 3 : ℤ) * (n.choose 3 : ℤ)) ∧
    (fwdDiff 1)^[3] (fun n => (Nat.lcmUpto 3 : ℤ) * (n.choose 3 : ℤ)) 0 = 6 := by
  refine ⟨isPseudoPoly_lcmUpto_mul_choose 3, ?_⟩
  rw [fwdDiff_iter_eq_sum_shift]; decide

end Candidates.RuzsaPseudoPolynomialNewton
