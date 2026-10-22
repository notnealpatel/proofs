/-
Eventual periodicity of OEIS A080253 (Peter Bala, Dec 31 2025).

The sequence is defined by a(n)=1+∑_{r=1}^n 2^r C(n,r) a(n-r), including a(0)=1.
It equals ∑_j S(n,j) j! A001333(j+1) (Vladeta Jovovic, Sep 28 2003).
The weighted-Stirling-transform theorem then gives φ(k) as an eventual
period modulo each positive k. The recurrence and transform provide a
formula-level treatment; no separate Coxeter-complex counting bridge is proved.
The entry also gives the e.g.f. exp(x)/(2-exp(2x))
(Antonio G. Astudillo, Feb 14 2003).
-/
import Enumerative.OrdinaryIntegralEGF

set_option autoImplicit false

namespace Candidates.A080253CellsCoxeterComplex

open Finset OrdinaryIntegralEGF

/-! ## Definition layer -/

/-- OEIS A080253, by the entry's recurrence
`a(n) = 1 + Σ_{r=1..n} 2^r · C(n,r) · a(n-r)` (so `a 0 = 1`).  The `attach`
only exposes `1 ≤ r ≤ n` to the termination proof; see `a_eq` for the
attach-free form. -/
def a (n : ℕ) : ℕ :=
  1 + ∑ r ∈ (Icc 1 n).attach, 2 ^ (r : ℕ) * n.choose r * a (n - r)
decreasing_by
  have hr := Finset.mem_Icc.mp r.2
  omega

/-- The entry's recurrence, in attach-free form. -/
theorem a_eq (n : ℕ) :
    a n = 1 + ∑ r ∈ Icc 1 n, 2 ^ r * n.choose r * a (n - r) := by
  rw [a, Finset.sum_attach (Icc 1 n) (fun r => 2 ^ r * n.choose r * a (n - r))]

/-- `a 0 = 1` (first listed term). -/
example : a 0 = 1 := by decide +kernel
/-- `a 1 = 3`. -/
example : a 1 = 3 := by decide +kernel
/-- `a 2 = 17`. -/
example : a 2 = 17 := by decide +kernel
/-- `a 3 = 147`. -/
example : a 3 = 147 := by decide +kernel
/-- `a 4 = 1697`. -/
example : a 4 = 1697 := by decide +kernel
/-- `a 5 = 24483`. -/
example : a 5 = 24483 := by decide +kernel
/-- `a 6 = 423857`. -/
example : a 6 = 423857 := by decide +kernel
/-- `a 7 = 8560947`. -/
example : a 7 = 8560947 := by decide +kernel
/-- `a 8 = 197613377`. -/
example : a 8 = 197613377 := by decide +kernel

/-- The ordinary coefficients `c k = A001333(k+1)` of `G(u) = (1+u)/(1-2u-u²)`,
for which `G(e^x - 1) = e^x/(2 - e^{2x})`: `c 0 = 1`, `c 1 = 3`,
`c (k+2) = 2 c (k+1) + c k`. -/
def c : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | k + 2 => 2 * c (k + 1) + c k

/-- `c` lists `A001333(1..6) = 1, 3, 7, 17, 41, 99`. -/
example : (c 0, c 1, c 2, c 3, c 4, c 5) = (1, 3, 7, 17, 41, 99) := by decide

/-- `D k n = k! · S(n,k)`, the number of surjections from an `n`-set onto a
`k`-set. -/
def D (k n : ℕ) : ℤ := (k.factorial : ℤ) * (n.stirlingSecond k : ℤ)

/-- `D 2 3 = 2! · S(3,2) = 6`. -/
example : D 2 3 = 6 := by decide

/-- Jovovic's formula as a sequence: `b n = Σ_{k≤n} c k · k! · S(n,k)`. -/
def b (n : ℕ) : ℤ := weightedStirlingTransform c n

/-- `b` matches the first listed terms. -/
example : (b 0, b 1, b 2, b 3, b 4) = (1, 3, 17, 147, 1697) := by decide

/-! ## Surjection numbers -/

/-- `D k n` is the alternating binomial sum `Σ_j (-1)^(k-j) C(k,j) j^n`. -/
lemma D_eq_sum (k n : ℕ) :
    D k n = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ n :=
  factorial_mul_stirlingSecond n k

/-- `D k n` is the `k`-th forward difference of `y ↦ y^n` at `0`. -/
lemma D_eq_fwdDiff (k n : ℕ) :
    D k n = (fwdDiff 1)^[k] (fun y : ℕ => (y : ℤ) ^ n) 0 := by
  rw [D_eq_sum, fwdDiff_iter_eq_sum_shift]
  simp

/-- `D k n = 0` above the diagonal. -/
lemma D_eq_zero {k n : ℕ} (h : n < k) : D k n = 0 := by
  simp [D, Nat.stirlingSecond_eq_zero_of_lt h]

/-- `D 0 n + D 1 n = 0^n + (1 - 0^n) = 1`. -/
lemma D_zero_add_D_one (n : ℕ) : D 0 n + D 1 n = 1 := by
  simp [D_eq_sum, Finset.sum_range_succ]

/-- Shifting the evaluation point of an iterated forward difference:
`Δ^k g (x+1) = Δ^k g x + Δ^(k+1) g x`. -/
lemma fwdDiff_iter_succ_point (g : ℕ → ℤ) (k x : ℕ) :
    (fwdDiff 1)^[k] g (x + 1) = (fwdDiff 1)^[k] g x + (fwdDiff 1)^[k + 1] g x := by
  rw [Function.iterate_succ_apply', fwdDiff]
  ring

/-- The key binomial identity (`E² = (1 + Δ)²`):
`Σ_{r≤n} C(n,r) 2^r D_k(n-r) = D_k(n) + 2 D_{k+1}(n) + D_{k+2}(n)`. -/
lemma binomial_shift (k n : ℕ) :
    ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * D k (n - r) =
      D k n + 2 * D (k + 1) n + D (k + 2) n := by
  have hshift : ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * D k (n - r) =
      (fwdDiff 1)^[k] (fun y : ℕ => (y : ℤ) ^ n) 2 := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp_rw [D_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_mul, mul_one]
    push_cast
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have h2 := fwdDiff_iter_succ_point (fun y : ℕ => (y : ℤ) ^ n) k 1
  have h1 := fwdDiff_iter_succ_point (fun y : ℕ => (y : ℤ) ^ n) k 0
  have h1' := fwdDiff_iter_succ_point (fun y : ℕ => (y : ℤ) ^ n) (k + 1) 0
  simp only [zero_add] at h1 h1'
  rw [hshift, D_eq_fwdDiff, D_eq_fwdDiff, D_eq_fwdDiff,
    show (2 : ℕ) = 1 + 1 from rfl, h2, h1, h1']
  ring

/-! ## The Jovovic sum satisfies the entry's recurrence -/

/-- Telescoping with the Pell recurrence of `c`, for an arbitrary sequence `E`:
`2 Σ_{k≤N} c_k E_k - Σ_{k≤N} c_k (E_k + 2E_{k+1} + E_{k+2})
  = E_0 + E_1 - c_{N+1} E_{N+1} - c_N E_{N+2}`. -/
lemma telescope (E : ℕ → ℤ) (N : ℕ) :
    2 * ∑ k ∈ range (N + 1), c k * E k -
        ∑ k ∈ range (N + 1), c k * (E k + 2 * E (k + 1) + E (k + 2)) =
      E 0 + E 1 - c (N + 1) * E (N + 1) - c N * E (N + 2) := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, c, one_mul]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ,
      Finset.sum_range_succ (fun k => c k * (E k + 2 * E (k + 1) + E (k + 2)))]
    have hc : c (N + 2) = 2 * c (N + 1) + c N := rfl
    linear_combination ih + hc * E (N + 2)

/-- The Jovovic sum may be taken over any range `N ≥ n + 1`. -/
lemma b_eq_sum {n N : ℕ} (h : n + 1 ≤ N) : b n = ∑ k ∈ range N, c k * D k n := by
  unfold b weightedStirlingTransform
  simp_rw [mul_assoc]
  apply Finset.sum_subset (Finset.range_mono h)
  intro k _ hk
  have hnk : n < k := by simpa using hk
  rw [← D, D_eq_zero hnk, mul_zero]

/-- The Jovovic sum satisfies `Σ_{r=0..n} C(n,r) 2^r b(n-r) = 2 b(n) - 1`,
i.e. the entry's recurrence `b(n) = 1 + Σ_{r=1..n} 2^r C(n,r) b(n-r)`. -/
lemma b_recurrence (n : ℕ) :
    ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * b (n - r) = 2 * b n - 1 := by
  have hexp : ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * b (n - r) =
      ∑ k ∈ range (n + 2 + 1), c k * (D k n + 2 * D (k + 1) n + D (k + 2) n) := by
    calc ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * b (n - r)
        = ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r *
            ∑ k ∈ range (n + 2 + 1), c k * D k (n - r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [b_eq_sum (N := n + 2 + 1) (by omega)]
      _ = ∑ k ∈ range (n + 2 + 1), c k *
            ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * D k (n - r) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
          ring
      _ = _ := by
          simp_rw [binomial_shift]
  have ht := telescope (fun k => D k n) (n + 2)
  rw [D_eq_zero (by omega : n < n + 2 + 1), D_eq_zero (by omega : n < n + 2 + 2),
    D_zero_add_D_one, ← b_eq_sum (by omega)] at ht
  rw [hexp]
  linear_combination -ht

/-- Splitting off the `r = 0` term: `Σ_{r≤n} f r = f 0 + Σ_{r∈[1,n]} f r`. -/
lemma sum_range_succ_eq_add_sum_Icc (f : ℕ → ℤ) (n : ℕ) :
    ∑ r ∈ range (n + 1), f r = f 0 + ∑ r ∈ Icc 1 n, f r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

/-- **Jovovic's formula** (OEIS A080253, Sep 28 2003):
`a(n) = Σ_{k=0..n} S(n,k) · k! · A001333(k+1)`. -/
theorem a_eq_b (n : ℕ) : (a n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec := b_recurrence n
    rw [sum_range_succ_eq_add_sum_Icc] at hrec
    rw [a_eq]
    push_cast
    have hsum : ∑ r ∈ Icc 1 n, (2 : ℤ) ^ r * (n.choose r : ℤ) * (a (n - r) : ℤ) =
        ∑ r ∈ Icc 1 n, (n.choose r : ℤ) * 2 ^ r * b (n - r) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr1 := Finset.mem_Icc.mp hr
      rw [ih (n - r) (by omega)]
      ring
    rw [hsum]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, mul_one,
      one_mul] at hrec
    linear_combination hrec

/-! ## The conjecture -/

/-- For every positive `k`, `φ(k)` is an eventual period of A080253
(Peter Bala, Dec 31 2025), by `a_eq_b` and
`OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic`. -/
theorem bala_conjecture (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  obtain ⟨N, hN⟩ := weightedStirlingTransform_eventuallyPeriodic c k hk
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [← b, ← b, ← a_eq_b, ← a_eq_b] at h
  push_cast at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

/-! ## Sanity layer -/

/-- The period `φ k` is positive for every `k ≥ 1`, so the
conclusion is not the trivial shift by `0`. -/
example (k : ℕ) (hk : 0 < k) : 0 < Nat.totient k := Nat.totient_pos.mpr hk

/-- The entry's mod-7 example: `a 1 ≡ a 7 (mod 7)` (both `≡ 3`), shift `φ 7 = 6`. -/
example : a (1 + Nat.totient 7) ≡ a 1 [MOD 7] := by
  rw [show Nat.totient 7 = 6 from Nat.totient_prime (by norm_num)]
  decide +kernel

end Candidates.A080253CellsCoxeterComplex
