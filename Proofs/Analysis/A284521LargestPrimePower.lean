/-
# A284521 — sum of largest prime power factors is O(n^2 / log n)

## OEIS source (retrieved with `oeis show A284521`, 2026-10-21)

```
NAME:     Sum of largest prime power factors of numbers <= n.
TERMS:    1,3,6,10,15,18,25,33,42,47,58,62,75,82,87,103,120,129,148,153,160,
          171,194,202,227,240,267,274,303,308,339,371,382,399,406,415,452,471,
          484,492,533,540,583,594,603,626,673,689,738,763,780,793,846,873,884,
          892,911,940,999,1004,1065,1096,1105,1169,1182
COMMENT:  Partial sums of A034699.
FORMULA (the conjecture; the local store carries no author/date on the line):
  Conjecture: a(n) = O(n^2/log(n)).
```

A034699 is "largest prime power factor of n" with A034699(1) = 1.

## Status

Triage status: open — neither the entry nor a web search turned up a printed
proof of this prime-power version.  (Alladi–Erdős give `∑ P(k) ~ π²/12 ·
n²/log n` for the largest prime factor `P(k)`.)  Numerically (re-checked here
up to 3·10^6) `a(n) log n / n^2` is 1.033 at 10^3, 0.900 at 10^6 and 0.893 at
3·10^6, with maximum 1.256 at n = 32 over 2 ≤ n ≤ 3·10^6.

## Proof route (elementary, Chebyshev-level)

Every `k ≥ 2` has `L(k)` equal to a prime power `q ≤ n` dividing `k`, so
`a(n) ≤ n + ∑_{q ≤ n prime power} q · ⌊n/q⌋ ≤ n + n · Π(n)` where `Π(n)` counts
prime powers in `[1, n]`.  Then `Π(n) ≤ π(n) + ⌊√n⌋ · ⌊log₂ n⌋`, and Mathlib's
`Chebyshev.pi_le_log4_mul_div` together with `log x ≤ x^ε/ε` gives
`a(n) ≤ (3 + 2 log 4 + 16 / log 2) · n^2 / log n` for every `n ≥ 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A284521LargestPrimePower

open Finset

/-! ## Definition layer -/

/-- A034699: the largest prime power dividing `k`, with the value `1` when `k`
has no prime power divisor (`k = 1`; also `k = 0` by the `Nat.divisors 0 = ∅`
convention, which the sum below never uses). -/
def largestPrimePowerDivisor (k : ℕ) : ℕ :=
  max 1 ((k.divisors.filter IsPrimePow).sup id)

/-- A284521: `a(n) = ∑_{k=1}^{n} L(k)` with `L` = `largestPrimePowerDivisor`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, largestPrimePowerDivisor k

/-- Ground truth: `L(12) = 4`. -/
example : largestPrimePowerDivisor 12 = 4 := by decide +kernel

/-- Ground truth: the first twenty terms of A034699. -/
example : (List.range 20).map (fun i => largestPrimePowerDivisor (i + 1)) =
    [1, 2, 3, 4, 5, 3, 7, 8, 9, 5, 11, 4, 13, 7, 5, 16, 17, 9, 19, 5] := by
  decide +kernel

/-- Ground truth: all sixty-five listed terms of A284521. -/
example : (List.range 65).map (fun i => a (i + 1)) =
    [1, 3, 6, 10, 15, 18, 25, 33, 42, 47, 58, 62, 75, 82, 87, 103, 120, 129, 148, 153, 160,
      171, 194, 202, 227, 240, 267, 274, 303, 308, 339, 371, 382, 399, 406, 415, 452, 471,
      484, 492, 533, 540, 583, 594, 603, 626, 673, 689, 738, 763, 780, 793, 846, 873, 884,
      892, 911, 940, 999, 1004, 1065, 1096, 1105, 1169, 1182] := by
  decide +kernel

/-! ## Combinatorial reduction -/

/-- `Π(n)`: the number of prime powers in `[1, n]`. -/
def primePowCount (n : ℕ) : ℕ := #((Icc 1 n).filter IsPrimePow)

/-- For `1 ≤ k ≤ n`, `L(k) ≤ 1 + ∑_{q ≤ n prime power, q ∣ k} q`. -/
theorem largestPrimePowerDivisor_le_one_add_sum {n k : ℕ} (hk : k ∈ Icc 1 n) :
    largestPrimePowerDivisor k ≤
      1 + ∑ q ∈ (Icc 1 n).filter IsPrimePow, if q ∣ k then q else 0 := by
  unfold largestPrimePowerDivisor
  have hk' := mem_Icc.mp hk
  refine max_le (Nat.le_add_right 1 _) ?_
  refine le_add_left (Finset.sup_le fun q hq => ?_)
  obtain ⟨hqd, hqpp⟩ := mem_filter.mp hq
  have hqk : q ∣ k := Nat.dvd_of_mem_divisors hqd
  have hqn : q ∈ (Icc 1 n).filter IsPrimePow := by
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hqpp.one_lt.le, ?_⟩, hqpp⟩
    exact (Nat.le_of_dvd (by omega) hqk).trans hk'.2
  have hsingle := Finset.single_le_sum (f := fun q => if q ∣ k then q else 0)
    (fun _ _ => Nat.zero_le _) hqn
  simpa [hqk] using hsingle

/-- For fixed `q ≥ 0`, `∑_{k=1}^{n} [q ∣ k] q = q ⌊n / q⌋ ≤ n`. -/
theorem sum_ite_dvd_le (n q : ℕ) :
    ∑ k ∈ Icc 1 n, (if q ∣ k then q else 0) ≤ n := by
  have hIcc : Icc 1 n = Ioc 0 n := by
    ext x
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hIcc,
    Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.div_mul_le_self n q

/-- `a(n) ≤ n + n · Π(n)`. -/
theorem a_le (n : ℕ) : a n ≤ n + n * primePowCount n := by
  unfold a primePowCount
  calc ∑ k ∈ Icc 1 n, largestPrimePowerDivisor k
      ≤ ∑ k ∈ Icc 1 n, (1 + ∑ q ∈ (Icc 1 n).filter IsPrimePow,
          if q ∣ k then q else 0) :=
        Finset.sum_le_sum fun k hk => largestPrimePowerDivisor_le_one_add_sum hk
    _ = n + ∑ q ∈ (Icc 1 n).filter IsPrimePow, ∑ k ∈ Icc 1 n,
          (if q ∣ k then q else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp
    _ ≤ n + ∑ _q ∈ (Icc 1 n).filter IsPrimePow, n := by
        gcongr with q hq
        exact sum_ite_dvd_le n q
    _ = n + n * #((Icc 1 n).filter IsPrimePow) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `Π(n) ≤ π(n) + ⌊√n⌋ · ⌊log₂ n⌋`: a prime power `p^e ≤ n` is a prime or has
`e ≥ 2`, whence `p ≤ ⌊√n⌋` and `e ≤ ⌊log₂ n⌋`. -/
theorem primePowCount_le (n : ℕ) :
    primePowCount n ≤ Nat.primeCounting n + Nat.sqrt n * Nat.log 2 n := by
  unfold primePowCount
  have hsub : (Icc 1 n).filter IsPrimePow ⊆ Nat.primesLE n ∪
      (Icc 1 (Nat.sqrt n) ×ˢ Icc 1 (Nat.log 2 n)).image (fun x => x.1 ^ x.2) := by
    intro q hq
    obtain ⟨hqI, hqpp⟩ := mem_filter.mp hq
    have hqn : q ≤ n := (mem_Icc.mp hqI).2
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hqpp
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · have he1 : e = 1 := by omega
      subst he1
      exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨by simpa using hqn, by simpa using hp⟩)
    · refine mem_union_right _ (mem_image.mpr ⟨(p, e), ?_, rfl⟩)
      have hp2 : p ^ 2 ≤ n :=
        (Nat.pow_le_pow_right hp.pos he2).trans hqn
      have h2e : 2 ^ e ≤ n :=
        (Nat.pow_le_pow_left hp.two_le e).trans hqn
      simp only [mem_product, mem_Icc]
      exact ⟨⟨hp.one_le, Nat.le_sqrt'.mpr hp2⟩,
        ⟨by omega, Nat.le_log_of_pow_le (by norm_num) h2e⟩⟩
  calc #((Icc 1 n).filter IsPrimePow)
      ≤ #(Nat.primesLE n ∪
          (Icc 1 (Nat.sqrt n) ×ˢ Icc 1 (Nat.log 2 n)).image (fun x => x.1 ^ x.2)) :=
        card_le_card hsub
    _ ≤ #(Nat.primesLE n) +
          #((Icc 1 (Nat.sqrt n) ×ˢ Icc 1 (Nat.log 2 n)).image (fun x => x.1 ^ x.2)) :=
        card_union_le _ _
    _ ≤ #(Nat.primesLE n) + #(Icc 1 (Nat.sqrt n) ×ˢ Icc 1 (Nat.log 2 n)) := by
        gcongr
        exact card_image_le
    _ = Nat.primeCounting n + Nat.sqrt n * Nat.log 2 n := by
        rw [Nat.primesLE_card_eq_primeCounting, card_product, Nat.card_Icc, Nat.card_Icc]
        simp

/-! ## Analytic estimate -/

/-- The explicit constant `3 + 2 log 4 + 16 / log 2`. -/
noncomputable def C₀ : ℝ := 3 + 2 * Real.log 4 + 16 / Real.log 2

/-- For `n ≥ 2`, `n + n (π(n) + ⌊√n⌋ ⌊log₂ n⌋) ≤ C₀ n² / log n`. -/
theorem real_bound (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) + n * ((Nat.primeCounting n : ℝ) + (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ))
      ≤ C₀ * (n : ℝ) ^ 2 / Real.log n := by
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hx0
  have hs0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  -- Chebyshev: `π(n) ≤ log 4 · n / log √n + √n`, with `log √n = log n / 2`.
  have hpi : (Nat.primeCounting n : ℝ) ≤ Real.log 4 * n / (Real.log n / 2) + √(n : ℝ) := by
    have h := Chebyshev.pi_le_log4_mul_div (x := (n : ℝ)) (by linarith)
    rwa [Nat.floor_natCast, Real.log_sqrt hx0] at h
  -- `√n · log n ≤ 2n`, from `log n ≤ 2 n^{1/2}`.
  have hsqrtL : √(n : ℝ) * Real.log n ≤ 2 * n := by
    have h := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  -- `(log n)^2 ≤ 16 √n`, from `log n ≤ 4 n^{1/4}`.
  have hL2 : Real.log n ^ 2 ≤ 16 * √(n : ℝ) := by
    have h := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 4)
    have h4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √(n : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
      norm_num
    have hpos : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0 _
    have hle : Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
    nlinarith
  have hsqrt : (Nat.sqrt n : ℝ) ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hlog2 : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    have h := Real.natLog_le_logb n 2
    rwa [Real.logb, Nat.cast_ofNat] at h
  have hLx : Real.log n ≤ n := Real.log_le_self hx0
  -- Product form of each piece.
  have hpiL : (Nat.primeCounting n : ℝ) * Real.log n ≤ 2 * Real.log 4 * n + 2 * n := by
    have h := mul_le_mul_of_nonneg_right hpi hL.le
    have he : (Real.log 4 * n / (Real.log n / 2) + √(n : ℝ)) * Real.log n =
        2 * Real.log 4 * n + √(n : ℝ) * Real.log n := by
      field_simp
    linarith
  have hsl : (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) * Real.log n ≤ 16 * n / Real.log 2 := by
    have hlog2' : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
      rwa [le_div_iff₀ hl2] at hlog2
    rw [le_div_iff₀ hl2]
    calc (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) * Real.log n * Real.log 2
        = (Nat.sqrt n : ℝ) * ((Nat.log 2 n : ℝ) * Real.log 2) * Real.log n := by ring
      _ ≤ √(n : ℝ) * Real.log n * Real.log n := by
        gcongr
      _ = √(n : ℝ) * Real.log n ^ 2 := by ring
      _ ≤ √(n : ℝ) * (16 * √(n : ℝ)) := by gcongr
      _ = 16 * n := by linear_combination 16 * hss
  rw [C₀, le_div_iff₀ hL]
  have hxL : (n : ℝ) * Real.log n ≤ (n : ℝ) ^ 2 := by nlinarith
  have hdiv : (n : ℝ) * (16 * n / Real.log 2) = 16 / Real.log 2 * (n : ℝ) ^ 2 := by ring
  calc ((n : ℝ) + n * ((Nat.primeCounting n : ℝ) + (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ)))
        * Real.log n
      = (n : ℝ) * Real.log n + n * ((Nat.primeCounting n : ℝ) * Real.log n)
          + n * ((Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) * Real.log n) := by ring
    _ ≤ (n : ℝ) ^ 2 + n * (2 * Real.log 4 * n + 2 * n) + n * (16 * n / Real.log 2) := by
        gcongr
    _ = (3 + 2 * Real.log 4 + 16 / Real.log 2) * (n : ℝ) ^ 2 := by rw [hdiv]; ring

/-! ## The conjecture -/

/-- **A284521 conjecture** (OEIS A284521 FORMULA line "Conjecture:
a(n) = O(n^2/log(n))."): there is a constant `C` with
`a(n) ≤ C · n² / log n` for every `n ≥ 2`, where `a(n) = ∑_{k ≤ n} L(k)` and
`L(k)` is the largest prime power dividing `k`.  The guard `2 ≤ n` keeps
`log n > 0`. -/
theorem a_le_const_mul_sq_div_log :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (a n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.log n := by
  refine ⟨C₀, fun n hn => ?_⟩
  have h1 : (a n : ℝ) ≤ n + n * primePowCount n := by exact_mod_cast a_le n
  have h2 : (primePowCount n : ℝ) ≤ Nat.primeCounting n + Nat.sqrt n * Nat.log 2 n := by
    exact_mod_cast primePowCount_le n
  calc (a n : ℝ) ≤ n + n * primePowCount n := h1
    _ ≤ n + n * ((Nat.primeCounting n : ℝ) + (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ)) := by
        gcongr
    _ ≤ C₀ * (n : ℝ) ^ 2 / Real.log n := real_bound n hn

/-- **A284521 conjecture, Landau form**: `a(n) = O(n² / log n)` as `n → ∞`. -/
theorem a_isBigO :
    (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2 / Real.log n) := by
  obtain ⟨C, hC⟩ := a_le_const_mul_sq_div_log
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hq : 0 ≤ (n : ℝ) ^ 2 / Real.log n := by positivity
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hq, ← mul_div_assoc]
  exact hC n hn

end Candidates.A284521LargestPrimePower
