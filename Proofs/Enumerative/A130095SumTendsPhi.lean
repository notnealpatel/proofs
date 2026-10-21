/-
# A130095 — ratio of consecutive terms tends to φ²

## OEIS source (retrieved 2026-10-21 with `oeis show A130095` and the live
## entry `https://oeis.org/A130095/internal`)

```
NAME:     Inverse Möbius transform of odd-indexed Fibonacci numbers.
TERMS:    1,3,6,16,35,97,234,626,1603,4218,10947,28767,75026,196654,514269,
          1346895,3524579,9229159,24157818,63250217,...
COMMENT:  Original name was: A051731 * A007436.
COMMENT (the conjecture):
          Conjecture: a(n)/a(n-1) tends to phi^2.
AUTHOR:   Gary W. Adamson, May 06 2007 (the conjecture line carries no separate
          attribution, so it is the author's, May 06 2007)
FORMULA:  From Peter Bala, Mar 26 2015: a(n) = sum {d | n} Fibonacci(2*d - 1).
```

## Status

Triage: "open" (no proof in the entry or the literature as far as the triage
could tell).  The argument is elementary: `F(2n-1) ≤ a(n) ≤ F(2n-1) + F(n)`,
and Binet's formula gives `a(n) / φ^(2n) → 1 / (√5 φ)`.  This file proves it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A130095SumTendsPhi

open Filter Topology Finset

/-- A130095: `a(n) = ∑_{d ∣ n} F(2d - 1)` (Peter Bala's formula; the inverse
Möbius transform of the odd-indexed Fibonacci numbers `F(1), F(3), F(5), …`).
Every divisor satisfies `d ≥ 1`, so the truncated subtraction `2 * d - 1` never
hits its junk value.  Offset 1: `a 0 = 0` (empty divisor set) is not a term. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, Nat.fib (2 * d - 1)

-- Ground truth: the first twelve listed terms.
example : (List.range 12).map (fun n => a (n + 1)) =
    [1, 3, 6, 16, 35, 97, 234, 626, 1603, 4218, 10947, 28767] := by
  decide

/-! ## Elementary bounds -/

/-- The odd-indexed Fibonacci numbers telescope: `∑_{d=1}^{m} F(2d-1) = F(2m)`. -/
theorem sum_Icc_fib_two_mul_sub_one (m : ℕ) :
    ∑ d ∈ Icc 1 m, Nat.fib (2 * d - 1) = Nat.fib (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h1, h2, Nat.fib_add_two]

/-- A proper divisor `d` of `n` lies in `[1, n / 2]`. -/
theorem properDivisors_subset_Icc (n : ℕ) : n.properDivisors ⊆ Icc 1 (n / 2) := by
  intro d hd
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨k, hk⟩, hlt⟩ := hd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; omega
    · exact h
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · omega
    · omega
    · omega
  rw [Finset.mem_Icc]
  refine ⟨hdpos, ?_⟩
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc d * 2 ≤ d * k := Nat.mul_le_mul_left d hk2
    _ = n := hk.symm

/-- Lower bound: the top divisor `d = n` alone gives `F(2n-1) ≤ a(n)` for `n ≠ 0`. -/
theorem fib_le_a {n : ℕ} (hn : n ≠ 0) : Nat.fib (2 * n - 1) ≤ a n :=
  Finset.single_le_sum (f := fun d => Nat.fib (2 * d - 1)) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn)

/-- Upper bound: the proper divisors contribute at most `F(n)`, so
`a(n) ≤ F(2n-1) + F(n)`. -/
theorem a_le (n : ℕ) : a n ≤ Nat.fib (2 * n - 1) + Nat.fib n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [a]
  have hsplit : a n = (∑ d ∈ n.properDivisors, Nat.fib (2 * d - 1)) + Nat.fib (2 * n - 1) := by
    rw [a, ← Nat.cons_self_properDivisors h.ne', Finset.sum_cons, add_comm]
  have hprop : ∑ d ∈ n.properDivisors, Nat.fib (2 * d - 1) ≤ Nat.fib n :=
    calc ∑ d ∈ n.properDivisors, Nat.fib (2 * d - 1)
        ≤ ∑ d ∈ Icc 1 (n / 2), Nat.fib (2 * d - 1) :=
          Finset.sum_le_sum_of_subset (properDivisors_subset_Icc n)
      _ = Nat.fib (2 * (n / 2)) := sum_Icc_fib_two_mul_sub_one _
      _ ≤ Nat.fib n := Nat.fib_mono (Nat.mul_div_le n 2)
  omega

/-! ## Asymptotics via Binet -/

open Real goldenRatio in
/-- Binet asymptotic: `F(m) / φ^m → 1 / √5`. -/
theorem tendsto_fib_div_goldenRatio_pow :
    Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / φ ^ m) atTop (𝓝 (1 / √5)) := by
  have hφ : φ ≠ 0 := goldenRatio_pos.ne'
  have habs : |ψ / φ| < 1 := by
    rw [abs_div, abs_of_pos goldenRatio_pos, div_lt_one goldenRatio_pos,
      abs_of_neg goldenConj_neg]
    linarith [neg_one_lt_goldenConj, one_lt_goldenRatio]
  have hlim : Tendsto (fun m : ℕ => (1 - (ψ / φ) ^ m) / √5) atTop (𝓝 ((1 - 0) / √5)) :=
    ((tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)).div_const _)
  rw [sub_zero] at hlim
  refine hlim.congr fun m => ?_
  rw [coe_fib_eq, div_pow]
  have hpow : φ ^ m ≠ 0 := pow_ne_zero m hφ
  field_simp

open Real goldenRatio in
/-- The normalised sequence `a(n+1) / φ^(2n+2)` tends to `1 / (√5 φ)`. -/
theorem tendsto_a_div_goldenRatio_pow :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / φ ^ (2 * n + 2)) atTop (𝓝 (1 / √5 / φ)) := by
  have hφpos : 0 < φ := goldenRatio_pos
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    show n ≤ 2 * n + 1
    omega
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  -- lower envelope `F(2n+1) / φ^(2n+2)`
  have hlow : Tendsto (fun n : ℕ => (Nat.fib (2 * n + 1) : ℝ) / φ ^ (2 * n + 2)) atTop
      (𝓝 (1 / √5 / φ)) := by
    refine ((tendsto_fib_div_goldenRatio_pow.comp hodd).div_const φ).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [div_div, ← pow_succ]
  -- error term `F(n+1) / φ^(2n+2) → 0`
  have herr : Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / φ ^ (2 * n + 2)) atTop (𝓝 0) := by
    have hinv : |φ⁻¹| < 1 := by
      rw [abs_inv, abs_of_pos hφpos]
      exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio
    have h := (tendsto_fib_div_goldenRatio_pow.comp hshift).mul
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hinv).comp hshift)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    have hsplit : 2 * n + 2 = (n + 1) + (n + 1) := by omega
    rw [hsplit, inv_pow, ← div_eq_mul_inv, div_div, ← pow_add]
  have hup := hlow.add herr
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
  · have h := fib_le_a (Nat.succ_ne_zero n)
    have hidx : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [hidx] at h
    have hR : (Nat.fib (2 * n + 1) : ℝ) ≤ (a (n + 1) : ℝ) := Nat.cast_le.mpr h
    exact div_le_div_of_nonneg_right hR (by positivity)
  · have h := a_le (n + 1)
    have hidx : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [hidx] at h
    have hR : (a (n + 1) : ℝ) ≤ (Nat.fib (2 * n + 1) : ℝ) + (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast h
    rw [← add_div]
    exact div_le_div_of_nonneg_right hR (by positivity)

/-! ## The conjecture -/

/-- **A130095 conjecture (Gary W. Adamson, May 06 2007), proved.**

Verbatim: "Conjecture: a(n)/a(n-1) tends to phi^2."  Here
`a(n) = ∑_{d ∣ n} F(2d - 1)` and `phi = (1 + √5)/2 = Real.goldenRatio`.

Stated as `a(n+1) / a(n) → φ²` over `ℕ`, which is the entry's `a(n)/a(n-1)`
with the index shifted by one.  The only junk value of the real division is at
`n = 0` (`a 0 = 0`, outside the offset-1 range); a single index does not affect
the limit, and `a n ≥ 1` for every `n ≥ 1`. -/
theorem tendsto_a_succ_div_a :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 (Real.goldenRatio ^ 2)) := by
  open Real goldenRatio in
  have hφ : φ ≠ 0 := goldenRatio_pos.ne'
  set b : ℕ → ℝ := fun n => (a (n + 1) : ℝ) / φ ^ (2 * n + 2) with hb_def
  have hb : Tendsto b atTop (𝓝 (1 / √5 / φ)) := tendsto_a_div_goldenRatio_pow
  have hc : (1 / √5 / φ) ≠ 0 := by positivity
  have hratio : Tendsto (fun n : ℕ => φ ^ 2 * (b (n + 1) / b n)) atTop
      (𝓝 (φ ^ 2 * ((1 / √5 / φ) / (1 / √5 / φ)))) :=
    ((hb.comp (tendsto_add_atTop_nat 1)).div hb hc).const_mul (φ ^ 2)
  rw [div_self hc, mul_one] at hratio
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hratio.congr fun n => ?_
  have hpos : (0 : ℝ) < a (n + 1) := by
    have h := fib_le_a (Nat.succ_ne_zero n)
    have hfib : 0 < Nat.fib (2 * (n + 1) - 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast hfib.trans_le h
  simp only [hb_def]
  have hidx : 2 * (n + 1) + 2 = (2 * n + 2) + 2 := by ring
  rw [hidx, pow_add]
  field_simp

end Candidates.A130095SumTendsPhi
