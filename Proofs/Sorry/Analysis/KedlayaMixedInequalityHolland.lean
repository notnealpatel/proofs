/-
# Kedlaya's mixed AM-GM inequality (Holland's conjecture) and Nam's analogues

## Source (retrieved with `fetch 2401.10234`, 2026-10-21)

Kyumin Nam, *On a Mixed Arithmetic-Mean, Geometric-Mean, Harmonic-Mean
Inequality*, arXiv:2401.10234.  Lemma 1 and Proposition 2 are quoted there from
K. Kedlaya, *Proof of a mixed arithmetic-mean, geometric-mean inequality*,
Amer. Math. Monthly 101 (1994) 355-357; the inequality was conjectured by
F. Holland (Mathematics Competitions 5 (1992) 60-64).

Verbatim (LaTeX) from the paper:

```
Lemma 1. The vectors a(i,j) = (a_1(i,j), ..., a_n(i,j)) given by
  a_k(i,j) = {n-i \choose j-k} {i-1 \choose k-1} / {n-1 \choose j-1}
satisfy  i. a_k(i,j) >= 0;  ii. a_k(i,j) = 0 for k > min(i,j);
  iii. a_k(i,j) = a_k(j,i);  iv. \sum_{k=1}^n a_k(i,j) = 1;
  v. \sum_{i=1}^n a_k(i,j) = n/j for k <= j, and 0 for k > j.

Proposition 2. Let x_1,...,x_n be positive real numbers. Then
  ( \prod_{j=1}^{n} (x_1 + ... + x_j)/j )^{1/n}
      >= (1/n) \sum_{i=1}^{n} \sqrt[i]{x_1 x_2 ... x_i}.

Proposition 3. Let x_1,...,x_n be positive real numbers. Then
  [ (1/n) \sum_{j=1}^{n} ((x_1 + ... + x_j)/j)^{-1} ]^{-1}
      >= (1/n) \sum_{i=1}^{n} i / (1/x_1 + ... + 1/x_i).

Proposition 4. Let x_1,...,x_n be positive real numbers. Then
  [ (1/n) \sum_{j=1}^{n} (\sqrt[j]{x_1 ... x_j})^{-1} ]^{-1}
      >= ( \prod_{i=1}^{n} i / (1/x_1 + ... + 1/x_i) )^{1/n}.

Theorem 5. (the chain obtained from Propositions 2, 3, 4).
```

(The equality cases "iff x_1 = ... = x_n" are not formalized.)

## Status

Proved in the literature: Proposition 2 by Kedlaya (1994); Propositions 3, 4
and Theorem 5 in arXiv:2401.10234.  This module proves Lemma 1, Propositions
2, 3, 4 and the inequality chain of Theorem 5 completely (no `sorry`).

## Formalization notes

Everything is 0-indexed: the paper's `x_1, …, x_n` are `x 0, …, x (n-1)` and
`a_k(i,j)` is `weight n (i-1) (j-1) (k-1)`.  The paper invokes Hölder and
Minkowski; here the two superadditivity steps are proved directly, from the
unweighted AM-GM inequality (`Real.geom_mean_le_arith_mean_weighted`) and from
Sedrakyan's form of Cauchy–Schwarz (`Finset.sq_sum_div_le_sum_sq_div`).  The
upper-index Vandermonde identity needed for Lemma 1 (v) is proved by induction.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.KedlayaMixedInequalityHolland

/-! ## Binomial identities -/

/-- `C(M,a) C(M-a,b) = C(M,b) C(M-b,a)` (both are the trinomial coefficient). -/
theorem choose_mul_choose_sub_comm (M a b : ℕ) :
    M.choose a * (M - a).choose b = M.choose b * (M - b).choose a := by
  have h1 := Nat.choose_mul (n := M) (k := a + b) (s := a) (Nat.le_add_right a b)
  have h2 := Nat.choose_mul (n := M) (k := a + b) (s := b) (Nat.le_add_left b a)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel] at h2
  rw [← h1, ← h2, Nat.choose_symm_add]

/-- Cross-multiplied symmetry of Kedlaya's weights:
`C(N-i, j-k) C(i,k) C(N,i) = C(N-j, i-k) C(j,k) C(N,j)` for `k ≤ i, j`. -/
theorem weight_cross (N i j k : ℕ) (hki : k ≤ i) (hkj : k ≤ j) :
    (N - i).choose (j - k) * i.choose k * N.choose i
      = (N - j).choose (i - k) * j.choose k * N.choose j := by
  have hi := Nat.choose_mul (n := N) (k := i) (s := k) hki
  have hj := Nat.choose_mul (n := N) (k := j) (s := k) hkj
  have hNi : N - i = (N - k) - (i - k) := by omega
  have hNj : N - j = (N - k) - (j - k) := by omega
  have hc := choose_mul_choose_sub_comm (N - k) (i - k) (j - k)
  calc (N - i).choose (j - k) * i.choose k * N.choose i
      = N.choose k * ((N - k).choose (i - k) * ((N - k) - (i - k)).choose (j - k)) := by
        rw [mul_assoc, mul_comm (i.choose k), hi, hNi]; ring
    _ = N.choose k * ((N - k).choose (j - k) * ((N - k) - (j - k)).choose (i - k)) := by
        rw [hc]
    _ = (N - j).choose (i - k) * j.choose k * N.choose j := by
        rw [mul_assoc, mul_comm (j.choose k), hj, hNj]; ring

/-- Upper-index Vandermonde identity:
`∑_{a+c=m} C(a,k) C(c,b) = C(m+1, k+b+1)`. -/
theorem sum_antidiagonal_choose_mul_choose (m k b : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose k * p.2.choose b = (m + 1).choose (k + b + 1) := by
  induction m generalizing b with
  | zero =>
    rcases Nat.eq_zero_or_pos k with hk | hk <;> rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hk; subst hb; simp
    · simp only [HasAntidiagonal.antidiagonal_zero, sum_singleton, Nat.choose_eq_zero_of_lt hb,
        mul_zero, zero_add]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
    · simp only [HasAntidiagonal.antidiagonal_zero, sum_singleton, Nat.choose_eq_zero_of_lt hk,
        zero_mul, zero_add]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
    · simp only [HasAntidiagonal.antidiagonal_zero, sum_singleton, Nat.choose_eq_zero_of_lt hk,
        zero_mul, zero_add]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ']
    cases b with
    | zero =>
      simp only [Nat.choose_zero_right, mul_one]
      have h0 := ih 0
      simp only [Nat.choose_zero_right, mul_one, add_zero] at h0
      rw [h0, add_zero, Nat.choose_succ_succ' (m + 1) k]
    | succ b =>
      simp only [Nat.choose_zero_succ, mul_zero, zero_add, Nat.choose_succ_succ' _ b, mul_add,
        Finset.sum_add_distrib, ih]
      rw [show k + (b + 1) + 1 = (k + b + 1) + 1 by ring, Nat.choose_succ_succ' (m + 1)]

/-- Ground truth for the upper Vandermonde identity: `∑_{a+b=3} C(a,1) C(b,1) = C(4,3)`. -/
example : ∑ p ∈ antidiagonal 3, p.1.choose 1 * p.2.choose 1 = (3 + 1).choose (1 + 1 + 1) := by
  decide

/-- Kedlaya's weights, 0-indexed: `weight n i j k = a_{k+1}(i+1, j+1)` where
`a_k(i,j) = C(n-i, j-k) C(i-1, k-1) / C(n-1, j-1)` (Lemma 1 of arXiv 2401.10234,
quoted from Kedlaya 1994).  The paper's convention `C(m, negative) = 0` is
encoded by the guard `k ≤ j`, since ℕ-subtraction would otherwise truncate. -/
noncomputable def weight (n i j k : ℕ) : ℝ :=
  if k ≤ j then (((n - 1 - i).choose (j - k) * i.choose k : ℕ) : ℝ) / ((n - 1).choose j : ℕ)
  else 0

/-- Paper check (n = 3): `a_1(2,2) = C(1,1) C(1,0) / C(2,1) = 1/2`. -/
example : weight 3 1 1 0 = 1 / 2 := by norm_num [weight, Nat.choose]

/-- Paper check (n = 3): `a_2(2,2) = C(1,0) C(1,1) / C(2,1) = 1/2`. -/
example : weight 3 1 1 1 = 1 / 2 := by norm_num [weight, Nat.choose]

/-- Paper check (n = 3): `a_3(2,3) = 0` since `k > min(i,j)`. -/
example : weight 3 1 2 2 = 0 := by norm_num [weight, Nat.choose]

/-- Paper check (n = 4): `a_2(3,2) = C(1,0) C(2,1) / C(3,1) = 2/3`. -/
example : weight 4 2 1 1 = 2 / 3 := by norm_num [weight, Nat.choose]

/-- Lemma 1 (i): the weights are nonnegative. -/
theorem weight_nonneg (n i j k : ℕ) : 0 ≤ weight n i j k := by
  unfold weight; split_ifs <;> positivity

/-- Lemma 1 (ii): `a_k(i,j) = 0` for `k > min(i,j)`. -/
theorem weight_eq_zero_of_lt (n i j k : ℕ) (h : min i j < k) : weight n i j k = 0 := by
  unfold weight
  split_ifs with hkj
  · rw [Nat.choose_eq_zero_of_lt (show i < k by omega)]; simp
  · rfl

/-- A sum over `range m` of terms guarded by `k ≤ j` (with `j < m`) is a sum over
`range (j+1)`. -/
theorem sum_range_ite_le (f : ℕ → ℝ) {j m : ℕ} (hj : j < m) :
    ∑ k ∈ range m, (if k ≤ j then f k else 0) = ∑ k ∈ range (j + 1), f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

/-- Lemma 1 (iii): `a_k(i,j) = a_k(j,i)`. -/
theorem weight_symm {n i j : ℕ} (hi : i < n) (hj : j < n) (k : ℕ) :
    weight n i j k = weight n j i k := by
  unfold weight
  by_cases hki : k ≤ i <;> by_cases hkj : k ≤ j
  · rw [if_pos hkj, if_pos hki]
    have hNi : 0 < (n - 1).choose i := Nat.choose_pos (by omega)
    have hNj : 0 < (n - 1).choose j := Nat.choose_pos (by omega)
    have hc := weight_cross (n - 1) i j k hki hkj
    rw [div_eq_div_iff (by positivity) (by positivity)]
    exact_mod_cast hc
  · rw [if_neg hkj, if_pos hki, Nat.choose_eq_zero_of_lt (show j < k by omega)]; simp
  · rw [if_pos hkj, if_neg hki, Nat.choose_eq_zero_of_lt (show i < k by omega)]; simp
  · rw [if_neg hkj, if_neg hki]

/-- Lemma 1 (iv): `∑_k a_k(i,j) = 1` (Vandermonde). -/
theorem sum_weight_k {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ range n, weight n i j k = 1 := by
  unfold weight
  rw [sum_range_ite_le _ hj, ← Finset.sum_div]
  have hpos : (0 : ℝ) < ((n - 1).choose j : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [div_eq_one_iff_eq hpos.ne']
  have hv : ∑ k ∈ range (j + 1), (n - 1 - i).choose (j - k) * i.choose k = (n - 1).choose j := by
    have h := Nat.add_choose_eq i (n - 1 - i) j
    rw [show i + (n - 1 - i) = n - 1 by omega,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => i.choose a * (n - 1 - i).choose b)] at h
    rw [h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [← hv]
  push_cast
  rfl

/-- Lemma 1 (v): `∑_i a_k(i,j) = n/j` for `k ≤ j` and `0` for `k > j` (upper Vandermonde). -/
theorem sum_weight_i {n j : ℕ} (hj : j < n) (k : ℕ) :
    ∑ i ∈ range n, weight n i j k = if k ≤ j then (n : ℝ) / (j + 1) else 0 := by
  unfold weight
  split_ifs with hkj
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [← Finset.sum_div]
    have hv : ∑ i ∈ range (N + 1), (N - i).choose (j - k) * i.choose k = (N + 1).choose (j + 1) := by
      have h := sum_antidiagonal_choose_mul_choose N k (j - k)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => a.choose k * b.choose (j - k)),
        show k + (j - k) + 1 = j + 1 by omega] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hm := Nat.add_one_mul_choose_eq N j
    have hpos : (0 : ℝ) < (N.choose j : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
    rw [div_eq_div_iff hpos.ne' (by positivity)]
    rw [← Nat.cast_sum, hv]
    push_cast
    have hm' : ((N : ℝ) + 1) * (N.choose j : ℝ) = ((N + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast hm
    linarith
  · exact Finset.sum_eq_zero fun i _ => rfl

/-- Lemma 1 (v) transposed via (iii): `∑_j a_k(i,j) = n/i` for `k ≤ i`, else `0`. -/
theorem sum_weight_j {n i : ℕ} (hi : i < n) (k : ℕ) :
    ∑ j ∈ range n, weight n i j k = if k ≤ i then (n : ℝ) / (i + 1) else 0 := by
  rw [← sum_weight_i hi k]
  exact Finset.sum_congr rfl fun j hj => weight_symm hi (mem_range.mp hj) k


/-- Superadditivity of the `n`-fold geometric mean (the Hölder step (4)), in averaged
form: `(1/n) ∑_i ∏_j G_ij^{1/n} ≤ ∏_j ((1/n) ∑_i G_ij)^{1/n}` for `G ≥ 0`.
Proved from the unweighted AM-GM inequality applied to `G_ij / S_j`. -/
theorem mean_prod_rpow_le_prod_mean_rpow {n : ℕ} (hn : 0 < n) (G : ℕ → ℕ → ℝ)
    (hG : ∀ i < n, ∀ j < n, 0 ≤ G i j) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, ∏ j ∈ range n, G i j ^ (1 / (n : ℝ)) ≤
      ∏ j ∈ range n, ((1 / (n : ℝ)) * ∑ i ∈ range n, G i j) ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : ∀ j < n, 0 ≤ (1 / (n : ℝ)) * ∑ i ∈ range n, G i j := fun j hj =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => hG i (mem_range.mp hi) j hj)
  have hRHS : 0 ≤ ∏ j ∈ range n, ((1 / (n : ℝ)) * ∑ i ∈ range n, G i j) ^ (1 / (n : ℝ)) :=
    Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hS0 j (mem_range.mp hj)) _
  by_cases hz : ∃ j < n, ∑ i ∈ range n, G i j = 0
  · obtain ⟨j₀, hj₀, hsum⟩ := hz
    have hcol : ∀ i ∈ range n, G i j₀ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i hi => hG i (mem_range.mp hi) j₀ hj₀).mp hsum
    have hrow : ∀ i ∈ range n, ∏ j ∈ range n, G i j ^ (1 / (n : ℝ)) = 0 := fun i hi =>
      Finset.prod_eq_zero (mem_range.mpr hj₀) (by
        rw [hcol i hi, Real.zero_rpow (by positivity)])
    rw [Finset.sum_eq_zero hrow, mul_zero]
    exact hRHS
  · push Not at hz
    set S : ℕ → ℝ := fun j => (1 / (n : ℝ)) * ∑ i ∈ range n, G i j with hS_def
    have hSpos : ∀ j < n, 0 < S j := fun j hj =>
      mul_pos (by positivity) (lt_of_le_of_ne
        (Finset.sum_nonneg fun i hi => hG i (mem_range.mp hi) j hj) (hz j hj).symm)
    set P : ℝ := ∏ j ∈ range n, S j ^ (1 / (n : ℝ)) with hP_def
    have hP : 0 ≤ P := Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hSpos j (mem_range.mp hj)).le _
    -- each row: factor out `P` and apply AM-GM to the ratios `G_ij / S_j`
    have hrow : ∀ i ∈ range n, ∏ j ∈ range n, G i j ^ (1 / (n : ℝ)) ≤
        P * ∑ j ∈ range n, (1 / (n : ℝ)) * (G i j / S j) := by
      intro i hi
      have hi' := mem_range.mp hi
      have hfac : ∏ j ∈ range n, G i j ^ (1 / (n : ℝ)) =
          P * ∏ j ∈ range n, (G i j / S j) ^ (1 / (n : ℝ)) := by
        rw [hP_def, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hj' := mem_range.mp hj
        rw [← Real.mul_rpow (hSpos j hj').le (div_nonneg (hG i hi' j hj') (hSpos j hj').le),
          mul_div_cancel₀ _ (hSpos j hj').ne']
      rw [hfac]
      refine mul_le_mul_of_nonneg_left ?_ hP
      refine Real.geom_mean_le_arith_mean_weighted (range n) (fun _ => 1 / (n : ℝ))
        (fun j => G i j / S j) (fun j _ => by positivity) ?_ (fun j hj => ?_)
      · rw [Finset.sum_const, card_range, nsmul_eq_mul]; field_simp
      · exact div_nonneg (hG i hi' j (mem_range.mp hj)) (hSpos j (mem_range.mp hj)).le
    have hsum : (1 / (n : ℝ)) * ∑ i ∈ range n, ∑ j ∈ range n, (1 / (n : ℝ)) * (G i j / S j) = 1 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      have hcol : ∀ j ∈ range n,
          (1 / (n : ℝ)) * ∑ i ∈ range n, (1 / (n : ℝ)) * (G i j / S j) = 1 / (n : ℝ) := by
        intro j hj
        have hj' := (hSpos j (mem_range.mp hj)).ne'
        rw [← Finset.mul_sum, ← Finset.sum_div, ← mul_assoc, mul_comm (1 / (n : ℝ)) (1 / (n : ℝ)),
          mul_assoc, mul_div_assoc', show (1 / (n : ℝ)) * ∑ i ∈ range n, G i j = S j from rfl,
          div_self hj', mul_one]
      rw [Finset.sum_congr rfl hcol, Finset.sum_const, card_range, nsmul_eq_mul]
      field_simp
    calc (1 / (n : ℝ)) * ∑ i ∈ range n, ∏ j ∈ range n, G i j ^ (1 / (n : ℝ))
        ≤ (1 / (n : ℝ)) * ∑ i ∈ range n, P * ∑ j ∈ range n, (1 / (n : ℝ)) * (G i j / S j) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (by positivity)
      _ = P * ((1 / (n : ℝ)) * ∑ i ∈ range n, ∑ j ∈ range n, (1 / (n : ℝ)) * (G i j / S j)) := by
          rw [← Finset.mul_sum]; ring
      _ = P := by rw [hsum, mul_one]


/-- Product analogue of `sum_range_ite_le`. -/
theorem prod_range_ite_le (f : ℕ → ℝ) {j m : ℕ} (hj : j < m) :
    ∏ k ∈ range m, (if k ≤ j then f k else 1) = ∏ k ∈ range (j + 1), f k := by
  rw [← Finset.prod_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

/-- Kedlaya's weighted geometric means `𝒢(i,j) = ∏_k x_k^{a_k(i,j)}` (0-indexed). -/
noncomputable def kedlayaG (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∏ k ∈ range n, x k ^ weight n i j k

/-- Step (2)-(3): `(1/n) ∑_i 𝒢(i,j) ≤ (x_1 + ⋯ + x_j)/j`, via weighted AM-GM and
Lemma 1 (iv), (v). -/
theorem mean_kedlayaG_le {n : ℕ} (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) {j : ℕ} (hj : j < n) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaG n x i j ≤
      (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hAM : ∀ i ∈ range n, kedlayaG n x i j ≤ ∑ k ∈ range n, weight n i j k * x k :=
    fun i hi => Real.geom_mean_le_arith_mean_weighted (range n) (weight n i j) x
      (fun k _ => weight_nonneg n i j k) (sum_weight_k (mem_range.mp hi) hj)
      (fun k hk => (hx k (mem_range.mp hk)).le)
  have hcol : ∑ i ∈ range n, ∑ k ∈ range n, weight n i j k * x k =
      (n : ℝ) / (j + 1) * ∑ k ∈ range (j + 1), x k := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_weight_i hj, ite_mul, zero_mul]
    rw [sum_range_ite_le (fun k => (n : ℝ) / (j + 1) * x k) hj, Finset.mul_sum]
  calc (1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaG n x i j
      ≤ (1 / (n : ℝ)) * ∑ i ∈ range n, ∑ k ∈ range n, weight n i j k * x k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hAM) (by positivity)
    _ = (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1) := by
        rw [hcol]; field_simp

/-- Step (5): `∏_j 𝒢(i,j)^{1/n} = (x_1 ⋯ x_i)^{1/i}`, via Lemma 1 (iii), (v). -/
theorem prod_kedlayaG_rpow {n : ℕ} (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) {i : ℕ} (hi : i < n) :
    ∏ j ∈ range n, kedlayaG n x i j ^ (1 / (n : ℝ)) =
      (∏ k ∈ range (i + 1), x k) ^ (1 / ((i : ℝ) + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : ∀ k ∈ range n, 0 ≤ x k := fun k hk => (hx k (mem_range.mp hk)).le
  calc ∏ j ∈ range n, kedlayaG n x i j ^ (1 / (n : ℝ))
      = ∏ j ∈ range n, ∏ k ∈ range n, x k ^ (weight n i j k * (1 / (n : ℝ))) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        unfold kedlayaG
        rw [← Real.finsetProd_rpow _ _ (fun k hk => Real.rpow_nonneg (hx0 k hk) _)]
        exact Finset.prod_congr rfl fun k hk => (Real.rpow_mul (hx0 k hk) _ _).symm
    _ = ∏ k ∈ range n, x k ^ (∑ j ∈ range n, weight n i j k * (1 / (n : ℝ))) := by
        rw [Finset.prod_comm]
        exact Finset.prod_congr rfl fun k hk =>
          (Real.rpow_sum_of_pos (hx k (mem_range.mp hk)) _ _).symm
    _ = ∏ k ∈ range n, (if k ≤ i then x k ^ (1 / ((i : ℝ) + 1)) else 1) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul, sum_weight_j hi]
        split_ifs
        · congr 1; field_simp
        · rw [zero_mul, Real.rpow_zero]
    _ = ∏ k ∈ range (i + 1), x k ^ (1 / ((i : ℝ) + 1)) := prod_range_ite_le _ hi
    _ = (∏ k ∈ range (i + 1), x k) ^ (1 / ((i : ℝ) + 1)) :=
        Real.finsetProd_rpow _ _ (fun k hk => (hx k (by
          have := mem_range.mp hk; omega)).le) _

/-- **Kedlaya's theorem (Holland's conjecture)**, Proposition 2 of arXiv 2401.10234
(Kedlaya, Amer. Math. Monthly 101 (1994)): for positive reals `x_1, …, x_n`,
`(1/n) ∑_{i=1}^n (x_1 ⋯ x_i)^{1/i} ≤ (∏_{j=1}^n (x_1 + ⋯ + x_j)/j)^{1/n}`.
Stated 0-indexed: `x 0, …, x (n-1)`. -/
theorem kedlaya_mixed_am_gm {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, (∏ k ∈ range (i + 1), x k) ^ (1 / ((i : ℝ) + 1)) ≤
      (∏ j ∈ range n, (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1)) ^ (1 / (n : ℝ)) := by
  have hG : ∀ i < n, ∀ j < n, 0 ≤ kedlayaG n x i j := fun i _ j _ =>
    Finset.prod_nonneg fun k hk => Real.rpow_nonneg (hx k (mem_range.mp hk)).le _
  have hA : ∀ j ∈ range n, 0 ≤ (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1) := fun j hj =>
    div_nonneg (Finset.sum_nonneg fun k hk => (hx k (by
      have := mem_range.mp hk; have := mem_range.mp hj; omega)).le) (by positivity)
  calc (1 / (n : ℝ)) * ∑ i ∈ range n, (∏ k ∈ range (i + 1), x k) ^ (1 / ((i : ℝ) + 1))
      = (1 / (n : ℝ)) * ∑ i ∈ range n, ∏ j ∈ range n, kedlayaG n x i j ^ (1 / (n : ℝ)) := by
        congr 1
        exact Finset.sum_congr rfl fun i hi => (prod_kedlayaG_rpow x hx (mem_range.mp hi)).symm
    _ ≤ ∏ j ∈ range n, ((1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaG n x i j) ^ (1 / (n : ℝ)) :=
        mean_prod_rpow_le_prod_mean_rpow hn _ hG
    _ ≤ ∏ j ∈ range n, ((∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1)) ^ (1 / (n : ℝ)) := by
        refine Finset.prod_le_prod (fun j hj => Real.rpow_nonneg ?_ _) (fun j hj => ?_)
        · exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun i hi => hG i (mem_range.mp hi) j (mem_range.mp hj))
        · exact Real.rpow_le_rpow (mul_nonneg (by positivity)
            (Finset.sum_nonneg fun i hi => hG i (mem_range.mp hi) j (mem_range.mp hj)))
            (mean_kedlayaG_le x hx (mem_range.mp hj)) (by positivity)
    _ = (∏ j ∈ range n, (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1)) ^ (1 / (n : ℝ)) :=
        Real.finsetProd_rpow _ _ hA _


/-- Weighted harmonic-mean / geometric-mean inequality, with positivity of the
reciprocal mean: for `w ≥ 0`, `∑ w = 1`, `z > 0`,
`0 < ∑ w_k / z_k` and `(∑ w_k / z_k)⁻¹ ≤ ∏ z_k ^ w_k`. -/
theorem weighted_harm_le_geom {s : Finset ℕ} (w z : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k)
    (hw' : ∑ k ∈ s, w k = 1) (hz : ∀ k ∈ s, 0 < z k) :
    0 < ∑ k ∈ s, w k / z k ∧ (∑ k ∈ s, w k / z k)⁻¹ ≤ ∏ k ∈ s, z k ^ w k := by
  have hGpos : 0 < ∏ k ∈ s, z k ^ w k :=
    Finset.prod_pos fun k hk => Real.rpow_pos_of_pos (hz k hk) _
  have hinv : (∏ k ∈ s, z k ^ w k)⁻¹ ≤ ∑ k ∈ s, w k / z k := by
    have h := Real.geom_mean_le_arith_mean_weighted s w (fun k => (z k)⁻¹) hw hw'
      (fun k hk => (inv_pos.mpr (hz k hk)).le)
    rw [← Finset.prod_inv_distrib]
    calc ∏ k ∈ s, (z k ^ w k)⁻¹ = ∏ k ∈ s, (z k)⁻¹ ^ w k :=
          Finset.prod_congr rfl fun k hk => (Real.inv_rpow (hz k hk).le _).symm
      _ ≤ ∑ k ∈ s, w k * (z k)⁻¹ := h
      _ = ∑ k ∈ s, w k / z k := Finset.sum_congr rfl fun k _ => (div_eq_mul_inv _ _).symm
  have hpos : 0 < ∑ k ∈ s, w k / z k := lt_of_lt_of_le (inv_pos.mpr hGpos) hinv
  refine ⟨hpos, ?_⟩
  calc (∑ k ∈ s, w k / z k)⁻¹ ≤ ((∏ k ∈ s, z k ^ w k)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hGpos) hinv
    _ = ∏ k ∈ s, z k ^ w k := inv_inv _

/-- Weighted harmonic-mean / arithmetic-mean inequality, with positivity of the
reciprocal mean: for `w ≥ 0`, `∑ w = 1`, `z > 0`,
`0 < ∑ w_k / z_k` and `(∑ w_k / z_k)⁻¹ ≤ ∑ w_k z_k`. -/
theorem weighted_harm_le_arith {s : Finset ℕ} (w z : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k)
    (hw' : ∑ k ∈ s, w k = 1) (hz : ∀ k ∈ s, 0 < z k) :
    0 < ∑ k ∈ s, w k / z k ∧ (∑ k ∈ s, w k / z k)⁻¹ ≤ ∑ k ∈ s, w k * z k := by
  obtain ⟨hpos, hHG⟩ := weighted_harm_le_geom w z hw hw' hz
  exact ⟨hpos, hHG.trans (Real.geom_mean_le_arith_mean_weighted s w z hw hw'
    (fun k hk => (hz k hk).le))⟩

/-- Superadditivity of the harmonic mean (the Minkowski step (9)), in averaged form:
for `h > 0`, `(1/n) ∑_i ((1/n) ∑_j h_ij⁻¹)⁻¹ ≤ ((1/n) ∑_j ((1/n) ∑_i h_ij)⁻¹)⁻¹`.
Proved from the Cauchy–Schwarz (Sedrakyan) inequality. -/
theorem mean_harm_le_harm_mean {n : ℕ} (hn : 0 < n) (h : ℕ → ℕ → ℝ)
    (hh : ∀ i < n, ∀ j < n, 0 < h i j) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, ((1 / (n : ℝ)) * ∑ j ∈ range n, (h i j)⁻¹)⁻¹ ≤
      ((1 / (n : ℝ)) * ∑ j ∈ range n, ((1 / (n : ℝ)) * ∑ i ∈ range n, h i j)⁻¹)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (range n).Nonempty := ⟨0, mem_range.mpr hn⟩
  set S : ℕ → ℝ := fun j => (1 / (n : ℝ)) * ∑ i ∈ range n, h i j with hS_def
  have hSpos : ∀ j ∈ range n, 0 < S j := fun j hj =>
    mul_pos (by positivity) (Finset.sum_pos (fun i hi => hh i (mem_range.mp hi) j (mem_range.mp hj)) hne)
  set D : ℕ → ℝ := fun i => ∑ j ∈ range n, (h i j)⁻¹ with hD_def
  have hDpos : ∀ i ∈ range n, 0 < D i := fun i hi =>
    Finset.sum_pos (fun j hj => inv_pos.mpr (hh i (mem_range.mp hi) j (mem_range.mp hj))) hne
  set Q : ℝ := ∑ j ∈ range n, (S j)⁻¹ with hQ_def
  have hQpos : 0 < Q := Finset.sum_pos (fun j hj => inv_pos.mpr (hSpos j hj)) hne
  -- Sedrakyan for each row
  have hT : ∀ i ∈ range n, Q ^ 2 / D i ≤ ∑ j ∈ range n, ((S j)⁻¹) ^ 2 * h i j := by
    intro i hi
    have h1 := Finset.sq_sum_div_le_sum_sq_div (range n) (fun j => (S j)⁻¹)
      (g := fun j => (h i j)⁻¹) (fun j hj => inv_pos.mpr (hh i (mem_range.mp hi) j (mem_range.mp hj)))
    refine h1.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [div_inv_eq_mul]
  have hsumT : Q ^ 2 * ∑ i ∈ range n, (D i)⁻¹ ≤ n * Q := by
    calc Q ^ 2 * ∑ i ∈ range n, (D i)⁻¹ = ∑ i ∈ range n, Q ^ 2 / D i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (div_eq_mul_inv _ _).symm
      _ ≤ ∑ i ∈ range n, ∑ j ∈ range n, ((S j)⁻¹) ^ 2 * h i j := Finset.sum_le_sum hT
      _ = ∑ j ∈ range n, ((S j)⁻¹) ^ 2 * (n * S j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, hS_def]
          field_simp
      _ = n * Q := by
          rw [hQ_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have := (hSpos j hj).ne'
          field_simp
  have hbound : ∑ i ∈ range n, (D i)⁻¹ ≤ n / Q := by
    rw [le_div_iff₀ hQpos]
    have hQ2 : Q ^ 2 * ∑ i ∈ range n, (D i)⁻¹ = Q * ((∑ i ∈ range n, (D i)⁻¹) * Q) := by ring
    rw [hQ2] at hsumT
    rw [mul_comm (n : ℝ) Q] at hsumT
    exact le_of_mul_le_mul_left hsumT hQpos
  calc (1 / (n : ℝ)) * ∑ i ∈ range n, ((1 / (n : ℝ)) * D i)⁻¹
      = ∑ i ∈ range n, (D i)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_inv, one_div, inv_inv, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
    _ ≤ n / Q := hbound
    _ = ((1 / (n : ℝ)) * Q)⁻¹ := by
        rw [mul_inv, one_div, inv_inv, div_eq_mul_inv]

/-- The averaged column identity shared by both mixed-mean inequalities:
`(1/n) ∑_i ∑_k a_k(i,j) y_k = (y_1 + ⋯ + y_j)/j` (Lemma 1 (v)). -/
theorem mean_sum_weight_mul_col {n j : ℕ} (hj : j < n) (y : ℕ → ℝ) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, ∑ k ∈ range n, weight n i j k * y k =
      (∑ k ∈ range (j + 1), y k) / ((j : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_weight_i hj, ite_mul, zero_mul]
  rw [sum_range_ite_le (fun k => (n : ℝ) / (j + 1) * y k) hj, ← Finset.mul_sum]
  field_simp

/-- Row version of `mean_sum_weight_mul_col`, via the symmetry Lemma 1 (iii):
`(1/n) ∑_j ∑_k a_k(i,j) y_k = (y_1 + ⋯ + y_i)/i`. -/
theorem mean_sum_weight_mul_row {n i : ℕ} (hi : i < n) (y : ℕ → ℝ) :
    (1 / (n : ℝ)) * ∑ j ∈ range n, ∑ k ∈ range n, weight n i j k * y k =
      (∑ k ∈ range (i + 1), y k) / ((i : ℝ) + 1) := by
  rw [← mean_sum_weight_mul_col hi y]
  congr 1
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k _ => ?_
  rw [weight_symm hi (mem_range.mp hj)]

/-- Kedlaya's weighted harmonic means `ℋ(i,j) = (∑_k a_k(i,j) / x_k)⁻¹` (0-indexed). -/
noncomputable def kedlayaH (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (∑ k ∈ range n, weight n i j k / x k)⁻¹

/-- **Mixed arithmetic-mean / harmonic-mean inequality**, Proposition 3 of
arXiv 2401.10234 (Nam): for positive reals `x_1, …, x_n`,
`(1/n) ∑_{i=1}^n i / (1/x_1 + ⋯ + 1/x_i) ≤ [(1/n) ∑_{j=1}^n ((x_1 + ⋯ + x_j)/j)⁻¹]⁻¹`.
Stated 0-indexed: `x 0, …, x (n-1)`. -/
theorem mixed_am_hm {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) :
    (1 / (n : ℝ)) * ∑ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹ ≤
      ((1 / (n : ℝ)) * ∑ j ∈ range n, ((∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1))⁻¹)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (range n).Nonempty := ⟨0, mem_range.mpr hn⟩
  have hxs : ∀ k ∈ range n, 0 < x k := fun k hk => hx k (mem_range.mp hk)
  have hHM : ∀ i < n, ∀ j < n, 0 < (∑ k ∈ range n, weight n i j k / x k) ∧
      kedlayaH n x i j ≤ ∑ k ∈ range n, weight n i j k * x k := fun i hi j hj =>
    weighted_harm_le_arith (weight n i j) x (fun k _ => weight_nonneg n i j k)
      (sum_weight_k hi hj) hxs
  have hHpos : ∀ i < n, ∀ j < n, 0 < kedlayaH n x i j := fun i hi j hj =>
    inv_pos.mpr (hHM i hi j hj).1
  -- (a) column means of `ℋ` are bounded by the prefix arithmetic means
  have hcol : ∀ j ∈ range n, (1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaH n x i j ≤
      (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1) := by
    intro j hj
    rw [← mean_sum_weight_mul_col (mem_range.mp hj) x]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi =>
      (hHM i (mem_range.mp hi) j (mem_range.mp hj)).2) (by positivity)
  have hcolpos : ∀ j ∈ range n, 0 < (1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaH n x i j :=
    fun j hj => mul_pos (by positivity)
      (Finset.sum_pos (fun i hi => hHpos i (mem_range.mp hi) j (mem_range.mp hj)) hne)
  -- (c) row reciprocal means of `ℋ` recover the prefix harmonic means
  have hrow : ∀ i ∈ range n, ((1 / (n : ℝ)) * ∑ j ∈ range n, (kedlayaH n x i j)⁻¹)⁻¹ =
      ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹ := by
    intro i hi
    have hr := mean_sum_weight_mul_row (mem_range.mp hi) (fun k => (x k)⁻¹)
    simp only [kedlayaH, inv_inv, div_eq_mul_inv]
    simp only [← div_eq_mul_inv] at hr ⊢
    rw [hr, inv_div]
  have hsum_pos : 0 < (1 / (n : ℝ)) *
      ∑ j ∈ range n, ((∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1))⁻¹ :=
    mul_pos (by positivity) (Finset.sum_pos (fun j hj =>
      inv_pos.mpr (lt_of_lt_of_le (hcolpos j hj) (hcol j hj))) hne)
  calc (1 / (n : ℝ)) * ∑ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹
      = (1 / (n : ℝ)) * ∑ i ∈ range n,
          ((1 / (n : ℝ)) * ∑ j ∈ range n, (kedlayaH n x i j)⁻¹)⁻¹ := by
        rw [Finset.sum_congr rfl hrow]
    _ ≤ ((1 / (n : ℝ)) * ∑ j ∈ range n,
          ((1 / (n : ℝ)) * ∑ i ∈ range n, kedlayaH n x i j)⁻¹)⁻¹ :=
        mean_harm_le_harm_mean hn _ hHpos
    _ ≤ ((1 / (n : ℝ)) *
          ∑ j ∈ range n, ((∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1))⁻¹)⁻¹ := by
        refine inv_anti₀ hsum_pos (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j hj => inv_anti₀ (hcolpos j hj) (hcol j hj)) (by positivity))


/-- Symmetry of Kedlaya's geometric means, `𝒢(i,j) = 𝒢(j,i)`, from Lemma 1 (iii). -/
theorem kedlayaG_symm {n i j : ℕ} (hi : i < n) (hj : j < n) (x : ℕ → ℝ) :
    kedlayaG n x i j = kedlayaG n x j i := by
  unfold kedlayaG
  exact Finset.prod_congr rfl fun k _ => by rw [weight_symm hi hj]

/-- **Mixed geometric-mean / harmonic-mean inequality**, Proposition 4 of
arXiv 2401.10234 (Nam): for positive reals `x_1, …, x_n`,
`(∏_{i=1}^n i / (1/x_1 + ⋯ + 1/x_i))^{1/n} ≤ [(1/n) ∑_{j=1}^n ((x_1 ⋯ x_j)^{1/j})⁻¹]⁻¹`.
Stated 0-indexed: `x 0, …, x (n-1)`. -/
theorem mixed_gm_hm {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) :
    (∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)) ≤
      ((1 / (n : ℝ)) *
        ∑ j ∈ range n, ((∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)))⁻¹)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (range n).Nonempty := ⟨0, mem_range.mpr hn⟩
  have hxs : ∀ k ∈ range n, 0 < x k := fun k hk => hx k (mem_range.mp hk)
  have hHG : ∀ i < n, ∀ j < n, 0 < (∑ k ∈ range n, weight n i j k / x k) ∧
      kedlayaH n x i j ≤ kedlayaG n x i j := fun i hi j hj =>
    weighted_harm_le_geom (weight n i j) x (fun k _ => weight_nonneg n i j k)
      (sum_weight_k hi hj) hxs
  have hHpos : ∀ i < n, ∀ j < n, 0 < kedlayaH n x i j := fun i hi j hj =>
    inv_pos.mpr (hHG i hi j hj).1
  -- prefix geometric means are column geometric means of `𝒢`
  have hGM : ∀ j ∈ range n, (∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)) =
      ∏ i ∈ range n, kedlayaG n x i j ^ (1 / (n : ℝ)) := by
    intro j hj
    rw [← prod_kedlayaG_rpow x hx (mem_range.mp hj)]
    exact Finset.prod_congr rfl fun i hi => by
      rw [kedlayaG_symm (mem_range.mp hi) (mem_range.mp hj)]
  -- reciprocal column bound: `GM_j⁻¹ ≤ ∏_i (ℋ(i,j)⁻¹)^{1/n}`
  have hcol : ∀ j ∈ range n, ((∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)))⁻¹ ≤
      ∏ i ∈ range n, ((kedlayaH n x i j)⁻¹) ^ (1 / (n : ℝ)) := by
    intro j hj
    rw [hGM j hj, ← Finset.prod_inv_distrib]
    have hGpos : ∀ i < n, 0 < kedlayaG n x i j := fun i _ =>
      Finset.prod_pos fun k hk => Real.rpow_pos_of_pos (hxs k hk) _
    refine Finset.prod_le_prod
      (fun i hi => (inv_pos.mpr (Real.rpow_pos_of_pos (hGpos i (mem_range.mp hi)) _)).le)
      (fun i hi => ?_)
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    rw [Real.inv_rpow (hHpos i hi' j hj').le]
    exact inv_anti₀ (Real.rpow_pos_of_pos (hHpos i hi' j hj') _)
      (Real.rpow_le_rpow (hHpos i hi' j hj').le (hHG i hi' j hj').2 (by positivity))
  -- Hölder step on the transposed matrix `ℋ(i,j)⁻¹`
  have hHold := mean_prod_rpow_le_prod_mean_rpow hn (fun j i => (kedlayaH n x i j)⁻¹)
    (fun j hj i hi => (inv_pos.mpr (hHpos i hi j hj)).le)
  -- row reciprocal means recover the prefix harmonic means
  have hrow : ∀ i ∈ range n, (1 / (n : ℝ)) * ∑ j ∈ range n, (kedlayaH n x i j)⁻¹ =
      (((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹)⁻¹ := by
    intro i hi
    have hr := mean_sum_weight_mul_row (mem_range.mp hi) (fun k => (x k)⁻¹)
    simp only [kedlayaH, inv_inv, div_eq_mul_inv]
    simp only [← div_eq_mul_inv] at hr ⊢
    rw [hr, inv_div]
  have hHMpos : ∀ i ∈ range n, 0 < ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹ :=
    fun i hi => div_pos (by positivity) (Finset.sum_pos (fun k hk => inv_pos.mpr (hx k (by
      have := mem_range.mp hk; have := mem_range.mp hi; omega))) ⟨0, by simp⟩)
  have hPpos : 0 < (∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos (Finset.prod_pos hHMpos) _
  have hmean : (1 / (n : ℝ)) *
      ∑ j ∈ range n, ((∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)))⁻¹ ≤
      ((∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)))⁻¹ := by
    calc (1 / (n : ℝ)) *
          ∑ j ∈ range n, ((∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)))⁻¹
        ≤ (1 / (n : ℝ)) * ∑ j ∈ range n, ∏ i ∈ range n, ((kedlayaH n x i j)⁻¹) ^ (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcol) (by positivity)
      _ ≤ ∏ i ∈ range n, ((1 / (n : ℝ)) * ∑ j ∈ range n, (kedlayaH n x i j)⁻¹) ^ (1 / (n : ℝ)) :=
          hHold
      _ = ∏ i ∈ range n, ((((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)))⁻¹ := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [hrow i hi, Real.inv_rpow (hHMpos i hi).le]
      _ = ((∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)))⁻¹ := by
          rw [Finset.prod_inv_distrib, Real.finsetProd_rpow _ _ (fun i hi => (hHMpos i hi).le)]
  have hsum_pos : 0 < (1 / (n : ℝ)) *
      ∑ j ∈ range n, ((∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1)))⁻¹ :=
    mul_pos (by positivity) (Finset.sum_pos (fun j hj => inv_pos.mpr (Real.rpow_pos_of_pos
      (Finset.prod_pos fun k hk => hx k (by
        have := mem_range.mp hk; have := mem_range.mp hj; omega)) _)) hne)
  calc (∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ))
      = (((∏ i ∈ range n, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), (x k)⁻¹) ^ (1 / (n : ℝ)))⁻¹)⁻¹ :=
        (inv_inv _).symm
    _ ≤ _ := inv_anti₀ hsum_pos hmean


/-- **Mixed AM-GM-HM chain**, Theorem 5 of arXiv 2401.10234 (Nam), 0-indexed: writing
`A_j = (x_1 + ⋯ + x_j)/j`, `G_j = (x_1 ⋯ x_j)^{1/j}`, `H_j = j / (1/x_1 + ⋯ + 1/x_j)`,
`(1/n) ∑_i (∏_{j≤i} H_j)^{1/i} ≤ (1/n) ∑_i [(1/i) ∑_{j≤i} G_j⁻¹]⁻¹
  ≤ [(1/n) ∑_i ((1/i) ∑_{j≤i} G_j)⁻¹]⁻¹ ≤ [(1/n) ∑_i ((∏_{j≤i} A_j)^{1/i})⁻¹]⁻¹`. -/
theorem mixed_am_gm_hm_chain {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ k < n, 0 < x k) :
    let A : ℕ → ℝ := fun j => (∑ k ∈ range (j + 1), x k) / ((j : ℝ) + 1)
    let G : ℕ → ℝ := fun j => (∏ k ∈ range (j + 1), x k) ^ (1 / ((j : ℝ) + 1))
    let H : ℕ → ℝ := fun j => ((j : ℝ) + 1) / ∑ k ∈ range (j + 1), (x k)⁻¹
    (1 / (n : ℝ)) * ∑ i ∈ range n, (∏ j ∈ range (i + 1), H j) ^ (1 / ((i : ℝ) + 1)) ≤
        (1 / (n : ℝ)) * ∑ i ∈ range n,
          ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), (G j)⁻¹)⁻¹ ∧
      (1 / (n : ℝ)) * ∑ i ∈ range n, ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), (G j)⁻¹)⁻¹ ≤
        ((1 / (n : ℝ)) * ∑ i ∈ range n, ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), G j)⁻¹)⁻¹ ∧
      ((1 / (n : ℝ)) * ∑ i ∈ range n, ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), G j)⁻¹)⁻¹ ≤
        ((1 / (n : ℝ)) * ∑ i ∈ range n, ((∏ j ∈ range (i + 1), A j) ^ (1 / ((i : ℝ) + 1)))⁻¹)⁻¹ := by
  intro A G H
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (range n).Nonempty := ⟨0, mem_range.mpr hn⟩
  have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := fun i => by push_cast; ring
  have hxi : ∀ i < n, ∀ k < i + 1, 0 < x k := fun i hi k hk => hx k (by omega)
  have hGpos : ∀ j < n, 0 < G j := fun j hj =>
    Real.rpow_pos_of_pos (Finset.prod_pos fun k hk => hx k (by
      have := mem_range.mp hk; omega)) _
  refine ⟨?_, ?_, ?_⟩
  · -- Proposition 4 at each prefix length `i + 1`
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    have h4 := mixed_gm_hm (Nat.succ_pos i) x (hxi i (mem_range.mp hi))
    simp only [hcast] at h4
    exact h4
  · -- Proposition 3 applied to the prefix geometric means
    have h3 := mixed_am_hm hn G (fun j hj => hGpos j hj)
    have hl : ∀ i ∈ range n, ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), (G j)⁻¹)⁻¹ =
        ((i : ℝ) + 1) / ∑ j ∈ range (i + 1), (G j)⁻¹ := fun i _ => by
      rw [mul_inv, one_div, inv_inv, div_eq_mul_inv]
    have hr : ∀ i ∈ range n, ((1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), G j)⁻¹ =
        ((∑ j ∈ range (i + 1), G j) / ((i : ℝ) + 1))⁻¹ := fun i _ => by
      rw [one_div_mul_eq_div]
    rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr]
    exact h3
  · -- Proposition 2 at each prefix length `i + 1`, then monotonicity of the harmonic mean
    have hAMpos : ∀ i ∈ range n, 0 < (1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), G j :=
      fun i hi => mul_pos (by positivity) (Finset.sum_pos (fun j hj => hGpos j (by
        have := mem_range.mp hj; have := mem_range.mp hi; omega)) ⟨0, by simp⟩)
    have h2 : ∀ i ∈ range n, (1 / ((i : ℝ) + 1)) * ∑ j ∈ range (i + 1), G j ≤
        (∏ j ∈ range (i + 1), A j) ^ (1 / ((i : ℝ) + 1)) := fun i hi => by
      have h := kedlaya_mixed_am_gm (Nat.succ_pos i) x (hxi i (mem_range.mp hi))
      simp only [hcast] at h
      exact h
    have hsum_pos : 0 < (1 / (n : ℝ)) *
        ∑ i ∈ range n, ((∏ j ∈ range (i + 1), A j) ^ (1 / ((i : ℝ) + 1)))⁻¹ :=
      mul_pos (by positivity) (Finset.sum_pos (fun i hi =>
        inv_pos.mpr (lt_of_lt_of_le (hAMpos i hi) (h2 i hi))) hne)
    exact inv_anti₀ hsum_pos (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => inv_anti₀ (hAMpos i hi) (h2 i hi)) (by positivity))

/-! ## Ground truth and non-vacuity -/

/-- Lemma 1 (v) checked by direct computation (n = 3, j = 2, k = 1):
`a_1(1,2) + a_1(2,2) + a_1(3,2) = 1/2 + 1/2 + 1/2 = 3/2 = n/j`. -/
example : ∑ i ∈ range 3, weight 3 i 1 0 = 3 / 2 := by
  norm_num [weight, Finset.sum_range_succ, Nat.choose]

/-- Lemma 1 (iv) checked by direct computation (n = 4, i = 3, j = 2):
`a_1(3,2) + a_2(3,2) = 1/3 + 2/3 = 1`. -/
example : ∑ k ∈ range 4, weight 4 2 1 k = 1 := by
  norm_num [weight, Finset.sum_range_succ, Nat.choose]

/-- Non-vacuity of Proposition 2: its hypotheses hold jointly at `n = 3`, `x = (1, 2, 3)`. -/
example : (1 / ((3 : ℕ) : ℝ)) *
      ∑ i ∈ range 3, (∏ k ∈ range (i + 1), ((k : ℝ) + 1)) ^ (1 / ((i : ℝ) + 1)) ≤
    (∏ j ∈ range 3, (∑ k ∈ range (j + 1), ((k : ℝ) + 1)) / ((j : ℝ) + 1)) ^
      (1 / ((3 : ℕ) : ℝ)) :=
  kedlaya_mixed_am_gm (by norm_num) (fun k => (k : ℝ) + 1) (fun k _ => by positivity)

/-- Non-vacuity of Proposition 3: its hypotheses hold jointly at `n = 3`, `x = (1, 2, 3)`. -/
example : (1 / ((3 : ℕ) : ℝ)) *
      ∑ i ∈ range 3, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), ((k : ℝ) + 1)⁻¹ ≤
    ((1 / ((3 : ℕ) : ℝ)) *
      ∑ j ∈ range 3, ((∑ k ∈ range (j + 1), ((k : ℝ) + 1)) / ((j : ℝ) + 1))⁻¹)⁻¹ :=
  mixed_am_hm (by norm_num) (fun k => (k : ℝ) + 1) (fun k _ => by positivity)

/-- Non-vacuity of Proposition 4: its hypotheses hold jointly at `n = 3`, `x = (1, 2, 3)`. -/
example : (∏ i ∈ range 3, ((i : ℝ) + 1) / ∑ k ∈ range (i + 1), ((k : ℝ) + 1)⁻¹) ^
      (1 / ((3 : ℕ) : ℝ)) ≤
    ((1 / ((3 : ℕ) : ℝ)) * ∑ j ∈ range 3,
      ((∏ k ∈ range (j + 1), ((k : ℝ) + 1)) ^ (1 / ((j : ℝ) + 1)))⁻¹)⁻¹ :=
  mixed_gm_hm (by norm_num) (fun k => (k : ℝ) + 1) (fun k _ => by positivity)

/-- Proposition 2 is not an equality in general: at `n = 2`, `x = (1, 3)` the left
side is `(1 + √3)/2` and the right side is `√2`, and `(1 + √3)/2 < √2`. -/
example : (1 + Real.sqrt 3) / 2 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by positivity)]
  have h3 : Real.sqrt 3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

end Candidates.KedlayaMixedInequalityHolland
