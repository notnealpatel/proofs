/-
# Elementary lower Mertens bound: `∑_{p ≤ N} 1/p ≥ log log N - 1`

## Source (recorded 2026-10-21)

F. Mertens, "Ein Beitrag zur analytischen Zahlentheorie", J. reine angew.
Math. 78 (1874), 46–62, proves the full asymptotic
`∑_{p ≤ x} 1/p = log log x + M + O(1/log x)`; see Hardy & Wright,
*An Introduction to the Theory of Numbers*, Thm 427, and Apostol,
*Introduction to Analytic Number Theory*, Thm 4.12.  The lower bound alone
is the Euler-product argument of Hardy & Wright §22.1 and Apostol Ch. 4.

## Informal statement (verbatim from the target card)

  For every integer N >= 3, sum_{p <= N prime} 1/p >= log log N - 1.
  Numerically, the minimum of sum 1/p - log log N over 3 <= N <= 10^6
  is 0.2615.

## Mathlib absence

`Mathlib/NumberTheory/SumPrimeReciprocals.lean` has only divergence
(`Nat.Primes.not_summable_one_div`, `one_half_le_sum_primes_ge_one_div`);
no `log log` lower bound exists (re-checked with `leandoc` and `grep`,
2026-10-21).  Consumer: `Proofs/Sorry/Erdos/E856.lean`.

## Proof

`log (N+1) ≤ H_N ≤ ∏_{p ≤ N} ∑_{k ≤ N} p^{-k} ≤ ∏_{p ≤ N} (1 - 1/p)⁻¹`
(every `n ≤ N` is determined by its factorization over primes `≤ N`);
take logs, use `log x ≤ x - 1` to get `log (1 - 1/p)⁻¹ ≤ 1/(p-1)`, and
bound `∑_p (1/(p-1) - 1/p) ≤ ∑_{n ≥ 2} (1/(n-1) - 1/n) ≤ 1` by telescoping.
No new definitions: the statement uses Mathlib's `Nat.primesLE` and
`Real.log` directly.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MertensLowerBound

open Finset

/-- Ground truth for the Mathlib notion used in the statement: the primes `≤ 10`. -/
example : Nat.primesLE 10 = {2, 3, 5, 7} := by decide

/-- Every `n ∈ [1, N]` is a product of prime powers `p ^ e` with `p ≤ N` and `e ≤ N`, so the
harmonic sum `∑_{n ≤ N} 1/n` is at most `∏_{p ≤ N} ∑_{k ≤ N} p^{-k}`. -/
theorem sum_Icc_inv_le_prod_geom (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ ≤
      ∏ p ∈ Nat.primesLE N, ∑ k ∈ range (N + 1), ((p : ℝ)⁻¹) ^ k := by
  set P := Nat.primesLE N
  rw [← Finset.prod_coe_sort P, Finset.prod_univ_sum]
  let φ : ℕ → P → ℕ := fun n p => n.factorization p
  have hsupp : ∀ n ∈ Icc 1 N, n.factorization.support ⊆ P := by
    intro n hn p hp
    rw [Nat.support_factorization] at hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hnN := (mem_Icc.mp hn).2
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (by omega) hp'.2.1).trans hnN, hp'.1⟩
  have hinj : Set.InjOn φ (Icc 1 N : Set ℕ) := by
    intro n hn m hm hnm
    have hn' : n ∈ Icc 1 N := hn
    have hm' : m ∈ Icc 1 N := hm
    apply Nat.factorization_inj (by simp only [Set.mem_ofPred_eq]; have := (mem_Icc.mp hn').1; omega)
      (by simp only [Set.mem_ofPred_eq]; have := (mem_Icc.mp hm').1; omega)
    ext p
    by_cases hpP : p ∈ P
    · exact congr_fun hnm ⟨p, hpP⟩
    · rw [Finsupp.notMem_support_iff.mp (fun h => hpP (hsupp n hn' h)),
        Finsupp.notMem_support_iff.mp (fun h => hpP (hsupp m hm' h))]
  have hterm : ∀ n ∈ Icc 1 N, ∏ i : P, ((i : ℝ)⁻¹) ^ (φ n i) = (n : ℝ)⁻¹ := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp only [φ, inv_pow, Finset.prod_inv_distrib]
    congr 1
    rw [Finset.prod_coe_sort P (fun i => (i : ℝ) ^ n.factorization i)]
    have h := Finsupp.prod_of_support_subset n.factorization (hsupp n hn)
      (fun p k => p ^ k) (fun _ _ => pow_zero _)
    rw [Nat.prod_factorization_pow_eq_self hn0] at h
    have h2 : (n : ℝ) = ∏ x ∈ P, (x : ℝ) ^ n.factorization x := by exact_mod_cast h
    exact h2.symm
  calc ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹
      = ∑ x ∈ (Icc 1 N).image φ, ∏ i : P, ((i : ℝ)⁻¹) ^ (x i) := by
        rw [Finset.sum_image hinj]
        exact (Finset.sum_congr rfl hterm).symm
    _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : P => range (N + 1)), ∏ i : P, ((i : ℝ)⁻¹) ^ (x i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
          have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
          rw [Fintype.mem_piFinset]
          intro i
          rw [mem_range]
          have := Nat.factorization_lt (i : ℕ) hn0
          have := (mem_Icc.mp hn).2
          simp only [φ]
          omega
        · intro x _ _
          exact Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _

/-- Geometric comparison: `∏_{p ≤ N} ∑_{k ≤ N} p^{-k} ≤ ∏_{p ≤ N} (1 - 1/p)⁻¹`. -/
theorem prod_geom_le_prod_inv_one_sub (N : ℕ) :
    ∏ p ∈ Nat.primesLE N, ∑ k ∈ range (N + 1), ((p : ℝ)⁻¹) ^ k ≤
      ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
  apply Finset.prod_le_prod
  · intro p _
    exact Finset.sum_nonneg fun k _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) h0 h1
    rwa [← Finset.range_eq_Ico, pow_zero, one_div] at h

/-- Telescoping: `∑_{n < M} (1/(n+1) - 1/(n+2)) = 1 - 1/(M+1)`. -/
theorem sum_range_inv_sub_inv (M : ℕ) :
    ∑ n ∈ range M, (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) = 1 - ((M : ℝ) + 1)⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The prime-square error is bounded: `∑_{p ≤ N} (1/(p-1) - 1/p) ≤ 1`. -/
theorem sum_primesLE_inv_pred_sub_inv_le_one (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) ≤ 1 := by
  have hsub : Nat.primesLE N ⊆ (range N).image (fun m : ℕ => m + 2) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primesLE hp
    have hpN := (Nat.mem_primesLE.mp hp).1
    have hp2 := hpr.two_le
    exact Finset.mem_image.mpr ⟨p - 2, mem_range.mpr (by omega), by omega⟩
  have hnonneg : ∀ n ∈ (range N).image (fun m : ℕ => m + 2), n ∉ Nat.primesLE N →
      0 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
    intro n hn _
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [sub_nonneg]
    gcongr
    · linarith
    · linarith
  calc ∑ p ∈ Nat.primesLE N, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹)
      ≤ ∑ n ∈ (range N).image (fun m : ℕ => m + 2), (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = ∑ n ∈ range N, (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := by
        rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        rw [show (n : ℝ) + 2 - 1 = n + 1 by ring]
    _ = 1 - ((N : ℝ) + 1)⁻¹ := sum_range_inv_sub_inv N
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
        linarith

/-- For a prime `p`, `log (1 - 1/p)⁻¹ ≤ 1/p + (1/(p-1) - 1/p)`. -/
theorem log_inv_one_sub_inv_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤ (p : ℝ)⁻¹ + (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply inv_pos.mpr
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have heq : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = (p : ℝ)⁻¹ + (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [← heq]
  exact Real.log_le_sub_one_of_pos hpos

/-- **Elementary lower Mertens bound.** For every integer `N ≥ 3`,
`∑_{p ≤ N, p prime} 1/p ≥ log log N - 1`. -/
theorem log_log_sub_one_le_sum_inv_primes (N : ℕ) (hN : 3 ≤ N) :
    Real.log (Real.log N) - 1 ≤ ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p := by
  set P := Nat.primesLE N
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hharm : Real.log ((N : ℝ) + 1) ≤ ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    exact h
  have hprod_pos : ∀ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    exact inv_ne_zero (by linarith)
  have hlogsum : Real.log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      ∑ p ∈ P, (p : ℝ)⁻¹ + ∑ p ∈ P, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
    rw [Real.log_prod hprod_pos, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p hp =>
      log_inv_one_sub_inv_le p (Nat.prime_of_mem_primesLE hp).two_le
  have hlogN1 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  calc Real.log (Real.log N) - 1
      ≤ Real.log (Real.log ((N : ℝ) + 1)) - 1 := by
        have := Real.log_le_log hlogN
          (Real.log_le_log (by linarith : (0 : ℝ) < N) (by linarith : (N : ℝ) ≤ N + 1))
        linarith
    _ ≤ Real.log (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) - 1 := by
        have := Real.log_le_log hlogN1 hharm
        linarith
    _ ≤ Real.log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) - 1 := by
        have := Real.log_le_log (hlogN1.trans_le hharm)
          ((sum_Icc_inv_le_prod_geom N).trans (prod_geom_le_prod_inv_one_sub N))
        linarith
    _ ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
        have := sum_primesLE_inv_pred_sub_inv_le_one N
        linarith
    _ = ∑ p ∈ P, (1 : ℝ) / p := by simp only [one_div]

/-- Non-vacuity: the hypothesis `3 ≤ N` is satisfied at `N = 3`. -/
example : Real.log (Real.log 3) - 1 ≤ ∑ p ∈ Nat.primesLE 3, (1 : ℝ) / p :=
  log_log_sub_one_le_sum_inv_primes 3 le_rfl

end Candidates.MertensLowerBound
