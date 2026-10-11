import Enumerative.FubiniMod

/-!
# Ordinary-integral input and exponential coefficient periodicity

For an arbitrary sequence `a : ℕ → ℤ` of ordinary coefficients, the canonical
factorial-weighted Stirling transform is eventually periodic modulo every
positive `k`, with positive eventual period `Nat.totient k`.

The proof uses factorial truncation, a forward-difference proof of the
alternating-power formula for `m! S(n,m)`, and Euler/nilpotence followed by
Chinese remaindering. The prime-power arithmetic is reused from `FubiniMod`.
The threshold is deliberately not optimized.

This module proves the coefficient theorem, not a formal-power-series
composition identity for `G(exp X - 1)`. Ordinary integrality is essential;
unrestricted integral divided-power inputs do not satisfy this theorem.
-/

set_option autoImplicit false

open Finset

namespace OrdinaryIntegralEGF

private lemma diff_mul (f : ℕ → ℤ) (m x : ℕ) :
    (fwdDiff 1)^[m + 1] (fun y : ℕ => (y : ℤ) * f y) x =
      ((x : ℤ) + m + 1) * (fwdDiff 1)^[m + 1] f x +
        (m + 1 : ℤ) * (fwdDiff 1)^[m] f x := by
  induction m generalizing x with
  | zero =>
    change ((x + 1 : ℕ) : ℤ) * f (x + 1) - (x : ℤ) * f x =
      ((x : ℤ) + 0 + 1) * (f (x + 1) - f x) + (0 + 1 : ℤ) * f x
    push_cast
    ring
  | succ m ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih, ih]
    simp only [Function.iterate_succ_apply', fwdDiff,
      Nat.cast_add, Nat.cast_one]
    ring

private lemma diff_pow (n m : ℕ) :
    (fwdDiff 1)^[m] (fun y : ℕ => (y : ℤ) ^ n) 0 =
      (m.factorial : ℤ) * (n.stirlingSecond m : ℤ) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [Nat.stirlingSecond]
    | succ m =>
      rw [Function.iterate_succ_apply]
      simp [fwdDiff_const, fwdDiff_iter_eq_sum_shift, Nat.stirlingSecond]
  | succ n ih =>
    cases m with
    | zero => simp [Nat.stirlingSecond]
    | succ m =>
      have hf : (fun y : ℕ => (y : ℤ) ^ (n + 1)) =
          (fun y : ℕ => (y : ℤ) * (y : ℤ) ^ n) := by
        funext y
        rw [pow_succ, mul_comm]
      rw [hf, diff_mul, ih, ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

/-- The factorial-weighted canonical Stirling number is the finite alternating
binomial sum of powers, including at degree zero and above the diagonal. -/
theorem factorial_mul_stirlingSecond (n m : ℕ) :
    (m.factorial : ℤ) * (n.stirlingSecond m : ℤ) =
      ∑ j ∈ range (m + 1), (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * (j : ℤ) ^ n := by
  rw [← diff_pow, fwdDiff_iter_eq_sum_shift]
  simp

private lemma pow_modEq_mul {q N P : ℕ}
    (h : ∀ n, N ≤ n → ∀ j : ℕ, j ^ (n + P) ≡ j ^ n [MOD q]) :
    ∀ t n, N ≤ n → ∀ j : ℕ, j ^ (n + t * P) ≡ j ^ n [MOD q] := by
  intro t
  induction t with
  | zero => intro n _ j; simpa using Nat.ModEq.refl (j ^ n)
  | succ t ih =>
    intro n hn j
    have hstep := h (n + t * P) (le_trans hn (Nat.le_add_right _ _)) j
    have hidx : n + (t + 1) * P = n + t * P + P := by ring
    rw [hidx]
    exact hstep.trans (ih n hn j)

private lemma powers_eventuallyPeriodic (k : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ P, Nat.totient k ∣ P →
      ∀ j : ℕ, j ^ (n + P) ≡ j ^ n [MOD k] := by
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p m hp hm =>
    refine ⟨m, fun n hn P hP j => ?_⟩
    obtain ⟨t, rfl⟩ := hP
    rw [mul_comm]
    exact pow_modEq_mul (fun n' hn' j' =>
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
        push_cast
        exact A000670.pow_add_totient_prime_pow hp hn' j')) t n hn j
  | zero =>
    refine ⟨0, fun n _ P hP j => ?_⟩
    have hP0 : P = 0 := Nat.eq_zero_of_zero_dvd (by simpa using hP)
    rw [hP0, Nat.add_zero]
  | one => exact ⟨0, fun n _ P _ j => Nat.modEq_one⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨Na, hNa⟩ := iha
    obtain ⟨Nb, hNb⟩ := ihb
    refine ⟨max Na Nb, fun n hn P hP j => ?_⟩
    rw [Nat.totient_mul hab] at hP
    have hPa : Nat.totient a ∣ P := (Dvd.intro _ rfl).trans hP
    have hPb : Nat.totient b ∣ P := (Dvd.intro_left _ rfl).trans hP
    exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp
      ⟨hNa n (le_of_max_le_left hn) P hPa j,
        hNb n (le_of_max_le_right hn) P hPb j⟩

/-- The canonical exponential coefficient sequence obtained from ordinary
integer input coefficients: `b_n = ∑_{m≤n} a_m m! S(n,m)`. -/
def weightedStirlingTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ range (n + 1), a m * (m.factorial : ℤ) * (n.stirlingSecond m : ℤ)

example (a : ℕ → ℤ) : weightedStirlingTransform a 0 = a 0 := by
  simp [weightedStirlingTransform, Nat.stirlingSecond]

example : weightedStirlingTransform (fun _ => 1) 3 = 13 := by
  decide

private lemma transform_truncated (a : ℕ → ℤ) (k n : ℕ)
    (hk : 1 ≤ k) (hn : k ≤ n) :
    (weightedStirlingTransform a n : ZMod k) =
      ∑ m ∈ range k, (a m : ZMod k) * (m.factorial : ZMod k) *
        (n.stirlingSecond m : ZMod k) := by
  unfold weightedStirlingTransform
  push_cast
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro m hm hmk
  have hkm : k ≤ m := by simpa using hmk
  have hfact : (m.factorial : ZMod k) = 0 := by
    exact (ZMod.natCast_eq_zero_iff m.factorial k).mpr
      (Nat.dvd_factorial (by omega) hkm)
  rw [hfact, mul_zero, zero_mul]

/-- For arbitrary ordinary integer input coefficients, the canonical weighted
Stirling transform has eventual period `φ(k)` modulo every positive `k`.
No restriction on signs, growth, or support of the input is imposed. -/
theorem weightedStirlingTransform_eventuallyPeriodic (a : ℕ → ℤ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (weightedStirlingTransform a (n + Nat.totient k) : ZMod k) =
        (weightedStirlingTransform a n : ZMod k) := by
  obtain ⟨N, hN⟩ := powers_eventuallyPeriodic k
  refine ⟨max k N, fun n hn => ?_⟩
  have hkn : k ≤ n := le_of_max_le_left hn
  have hNn : N ≤ n := le_of_max_le_right hn
  rw [transform_truncated a k _ hk (le_trans hkn (Nat.le_add_right _ _)),
    transform_truncated a k n hk hkn]
  apply Finset.sum_congr rfl
  intro m hm
  have hexpand (r : ℕ) :
      (m.factorial : ZMod k) * (r.stirlingSecond m : ZMod k) =
        ∑ j ∈ range (m + 1), (-1 : ZMod k) ^ (m - j) *
          (m.choose j : ZMod k) * (j : ZMod k) ^ r := by
    have h := congrArg (fun z : ℤ => (z : ZMod k))
      (factorial_mul_stirlingSecond r m)
    push_cast at h
    exact h
  rw [mul_assoc, mul_assoc, hexpand, hexpand]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : (j : ZMod k) ^ (n + Nat.totient k) = (j : ZMod k) ^ n := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN n hNn _ dvd_rfl j)
    push_cast at h
    exact h
  rw [hpow]

example : (weightedStirlingTransform (fun _ => 1) 0,
    weightedStirlingTransform (fun _ => 1) 1,
    weightedStirlingTransform (fun _ => 1) 2,
    weightedStirlingTransform (fun _ => 1) 3) = (1, 1, 3, 13) := by
  decide

example : weightedStirlingTransform (fun m => if m = 1 then -1 else 0) 2 = -1 := by
  decide

example : 0 < Nat.totient 1 ∧
    ∀ n : ℕ, (weightedStirlingTransform (fun _ => 1) (n + Nat.totient 1) : ZMod 1) =
      (weightedStirlingTransform (fun _ => 1) n : ZMod 1) := by
  constructor
  · decide
  · intro n
    exact Subsingleton.elim _ _

example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (weightedStirlingTransform (fun _ => 1) (n + Nat.totient 2) : ZMod 2) =
      (weightedStirlingTransform (fun _ => 1) n : ZMod 2) :=
  weightedStirlingTransform_eventuallyPeriodic (fun _ => 1) 2 (by decide)

end OrdinaryIntegralEGF
