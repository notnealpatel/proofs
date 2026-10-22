/-
# Gurland's ratio: convergence of the Hurwitz-series expansion

Source: Halina Wiśniewska, *Some inequalities for Gurland's ratio of the
gamma functions*, arXiv:2512.07028, Section 2: Theorem 1 (`tw-zmi`),
Corollary 1 (`wn1`), and Open problems 1–2 after Corollary 3 (`wn3`).
For `G*(x,y) = Γ(1+x)Γ(1+y)/Γ(1+(x+y)/2)²`, those problems ask whether
the expansion of `log G*` converges and its remainder tends to zero for
all `x,y > 0`, beyond the sufficient condition
`Q(x,y) = |x-y|/(2(1+√(xy))) < 1`.

Both conclusions are proved here for positive `x,y`. With `a=(x+y)/2`
and `d=(x-y)/2`, Euler's log-Gamma limit gives
`log G* = ∑_{n≥1} -log(1-d²/(n+a)²)`. Each ratio lies in `[0,1)`;
expanding `-log(1-u)` and interchanging nonnegative sums gives
`∑_{k≥1} d^{2k} ζ(2k,1+a)/k`.

`hurwitzZetaSeries` is the explicit real series with a natural exponent,
not Mathlib's `HurwitzZeta.hurwitzZeta`; no bridge to that function is
claimed. `partialSum m` is the source's `S_m`, and `remainder m` is the
actual difference `log G* - S_m`, whose limit is zero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SomeInequalitiesGurlandRatio

open Real Filter Topology

/-- The modified Gurland ratio of arXiv:2512.07028, eq. (1.2):
`G*(x, y) = Γ(1 + x) Γ(1 + y) / Γ(1 + (x + y)/2)²`. -/
noncomputable def gurlandStar (x y : ℝ) : ℝ :=
  Gamma (1 + x) * Gamma (1 + y) / Gamma (1 + (x + y) / 2) ^ 2

/-- The Hurwitz zeta series `ζ(s, q) = ∑_{n ≥ 0} (n + q)^{-s}` of
arXiv:2512.07028, eq. (1.3), with natural-number exponent `s`. -/
noncomputable def hurwitzZetaSeries (s : ℕ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, (((n : ℝ) + q) ^ s)⁻¹

/-- The `k`-th term `(1/k) ((x - y)/2)^{2k} ζ(2k, 1 + (x + y)/2)` of the expansion
of `ln G*(x, y)` in arXiv:2512.07028, Theorem 1. -/
noncomputable def zetaTerm (k : ℕ) (x y : ℝ) : ℝ :=
  1 / (k : ℝ) * ((x - y) / 2) ^ (2 * k) * hurwitzZetaSeries (2 * k) (1 + (x + y) / 2)

/-- The partial sum `S_m(x, y) = ∑_{k=1}^{m-1} (1/k) ((x - y)/2)^{2k} ζ(2k, 1 + (x + y)/2)`
of arXiv:2512.07028, Corollary 1. -/
noncomputable def partialSum (m : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 m, zetaTerm k x y

/-- The remainder `R^m(x, y) = ln G*(x, y) - S_m(x, y)` of arXiv:2512.07028, Theorem 1. -/
noncomputable def remainder (m : ℕ) (x y : ℝ) : ℝ :=
  log (gurlandStar x y) - partialSum m x y

/-! ## Examples for the definitions -/

example : gurlandStar 1 1 = 1 := by
  have h2 : Gamma 2 = 1 := Gamma_two
  norm_num [gurlandStar, h2]

example : gurlandStar 0 2 = 2 := by
  have h2 : Gamma 2 = 1 := Gamma_two
  have h3 : Gamma 3 = 2 := by
    have h := Gamma_nat_eq_factorial 2
    rw [show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num] at h
    rw [h]
    norm_num [Nat.factorial]
  norm_num [gurlandStar, h2, h3]

example : hurwitzZetaSeries 2 1 = π ^ 2 / 6 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, Nat.cast_add,
    Nat.cast_one] at h
  norm_num at h
  rw [hurwitzZetaSeries]
  exact h.tsum_eq

example (x y : ℝ) : partialSum 1 x y = 0 := by simp [partialSum]

example (x y : ℝ) :
    partialSum 2 x y = ((x - y) / 2) ^ 2 * hurwitzZetaSeries 2 (1 + (x + y) / 2) := by
  simp [partialSum, zetaTerm]

/-! ## The logarithmic series `ln G* = ∑_{n ≥ 1} -log(1 - d²/(n + a)²)` -/

/-- The ratio `u_j = ((x - y)/2)² / (j + 1 + (x + y)/2)²`, i.e. `d²/(n + a)²` with
`n = j + 1`. -/
noncomputable def ratioU (x y : ℝ) (j : ℕ) : ℝ :=
  ((x - y) / 2) ^ 2 / ((j : ℝ) + (1 + (x + y) / 2)) ^ 2

/-- `ln G*(x, y) = ln Γ(1 + x) + ln Γ(1 + y) - 2 ln Γ(1 + (x + y)/2)` for `x, y > 0`. -/
theorem log_gurlandStar {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log (gurlandStar x y) =
      log (Gamma (1 + x)) + log (Gamma (1 + y)) - 2 * log (Gamma (1 + (x + y) / 2)) := by
  have hgx : 0 < Gamma (1 + x) := Gamma_pos_of_pos (by linarith)
  have hgy : 0 < Gamma (1 + y) := Gamma_pos_of_pos (by linarith)
  have hga : 0 < Gamma (1 + (x + y) / 2) := Gamma_pos_of_pos (by linarith)
  rw [gurlandStar, log_div (by positivity) (by positivity), log_mul hgx.ne' hgy.ne', log_pow]
  push_cast
  ring

/-- The factorization `(n + x)(n + y) = (n + a)² - d²`, in the form
`2 log(1 + a + j) - log(1 + x + j) - log(1 + y + j) = -log(1 - u_j)`. -/
theorem log_term_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (j : ℕ) :
    2 * log (1 + (x + y) / 2 + j) - log (1 + x + j) - log (1 + y + j) =
      -log (1 - ratioU x y j) := by
  have hc : 0 < (j : ℝ) + (1 + (x + y) / 2) := by positivity
  have hpx : 0 < 1 + x + (j : ℝ) := by positivity
  have hpy : 0 < 1 + y + (j : ℝ) := by positivity
  have hfac : 1 - ratioU x y j =
      (1 + x + j) * (1 + y + j) / ((j : ℝ) + (1 + (x + y) / 2)) ^ 2 := by
    rw [ratioU]
    field_simp
    ring
  rw [hfac, log_div (by positivity) (by positivity), log_mul hpx.ne' hpy.ne', log_pow,
    show (j : ℝ) + (1 + (x + y) / 2) = 1 + (x + y) / 2 + j by ring]
  push_cast
  ring

/-- `0 ≤ u_j`. -/
theorem ratioU_nonneg (x y : ℝ) (j : ℕ) : 0 ≤ ratioU x y j := by
  rw [ratioU]
  positivity

/-- `u_j < 1` for `x, y > 0`, since `(n + a)² - d² = (n + x)(n + y) > 0`. -/
theorem ratioU_lt_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (j : ℕ) : ratioU x y j < 1 := by
  have hc : 0 < (j : ℝ) + (1 + (x + y) / 2) := by positivity
  have hdiff : ((j : ℝ) + (1 + (x + y) / 2)) ^ 2 - ((x - y) / 2) ^ 2 =
      (1 + x + j) * (1 + y + j) := by ring
  have hpos : 0 < (1 + x + (j : ℝ)) * (1 + y + j) := by positivity
  rw [ratioU, div_lt_one (by positivity)]
  linarith

/-- Euler's limit formula for `log Γ` gives
`ln G*(x, y) = ∑_{n ≥ 1} -log(1 - d²/(n + a)²)` for all `x, y > 0`. -/
theorem hasSum_neg_log_one_sub_ratioU {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun j : ℕ => -log (1 - ratioU x y j)) (log (gurlandStar x y)) := by
  have hA := BohrMollerup.tendsto_log_gamma (show (0 : ℝ) < 1 + x by linarith)
  have hB := BohrMollerup.tendsto_log_gamma (show (0 : ℝ) < 1 + y by linarith)
  have hC := BohrMollerup.tendsto_log_gamma (show (0 : ℝ) < 1 + (x + y) / 2 by linarith)
  have hnonneg : ∀ j : ℕ, 0 ≤ -log (1 - ratioU x y j) := fun j =>
    neg_nonneg.2 (log_nonpos (by linarith [ratioU_lt_one hx hy j])
      (by linarith [ratioU_nonneg x y j]))
  have hlim : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), -log (1 - ratioU x y j))
      atTop (𝓝 (log (gurlandStar x y))) := by
    rw [log_gurlandStar hx hy]
    refine ((hA.add hB).sub (hC.const_mul 2)).congr fun n => ?_
    simp only [BohrMollerup.logGammaSeq, ← log_term_eq hx hy]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2 ((tendsto_add_atTop_iff_nat 1).1 hlim)

/-! ## Interchanging the two nonnegative series -/

/-- The double-series term `u_j^{k+1}/(k+1)` indexed by `(j, k)`. -/
noncomputable def doubleTerm (x y : ℝ) (p : ℕ × ℕ) : ℝ :=
  ratioU x y p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1)

/-- Expanding each `-log(1 - u_j) = ∑_{k ≥ 0} u_j^{k+1}/(k+1)` and summing over `j` first
(all terms are nonnegative): `ln G*(x, y) = ∑_{k ≥ 0} ∑_{j ≥ 0} u_j^{k+1}/(k+1)`. -/
theorem hasSum_tsum_ratioU_pow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun k : ℕ => ∑' j : ℕ, ratioU x y j ^ (k + 1) / ((k : ℝ) + 1))
      (log (gurlandStar x y)) := by
  have hf0 : 0 ≤ doubleTerm x y := fun p => by
    have hu := ratioU_nonneg x y p.1
    simp only [doubleTerm, Pi.zero_apply]
    positivity
  have hrow : ∀ j : ℕ,
      HasSum (fun k : ℕ => doubleTerm x y (j, k)) (-log (1 - ratioU x y j)) := fun j => by
    have hu : |ratioU x y j| < 1 := by
      rw [abs_of_nonneg (ratioU_nonneg x y j)]
      exact ratioU_lt_one hx hy j
    have h := hasSum_pow_div_log_of_abs_lt_one hu
    exact h
  have hcol := hasSum_neg_log_one_sub_ratioU hx hy
  have hrow_tsum : (fun j : ℕ => ∑' k : ℕ, doubleTerm x y (j, k)) =
      fun j => -log (1 - ratioU x y j) :=
    funext fun j => (hrow j).tsum_eq
  have hsumm : Summable (doubleTerm x y) := by
    refine (summable_prod_of_nonneg hf0).2 ⟨fun j => (hrow j).summable, ?_⟩
    rw [hrow_tsum]
    exact hcol.summable
  have hF : HasSum (doubleTerm x y) (log (gurlandStar x y)) := by
    have h := hsumm.hasSum
    rwa [hsumm.tsum_prod' fun j => (hrow j).summable, hrow_tsum, hcol.tsum_eq] at h
  have hswap : HasSum (fun p : ℕ × ℕ => doubleTerm x y p.swap) (log (gurlandStar x y)) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF
  exact hswap.prod_fiberwise fun k => (hsumm.prod_symm.prod_factor k).hasSum

/-- `∑_{j ≥ 0} u_j^{k+1}/(k+1) = (1/(k+1)) d^{2(k+1)} ζ(2(k+1), 1 + a)`. -/
theorem tsum_ratioU_pow_eq_zetaTerm (x y : ℝ) (k : ℕ) :
    ∑' j : ℕ, ratioU x y j ^ (k + 1) / ((k : ℝ) + 1) = zetaTerm (k + 1) x y := by
  rw [zetaTerm, hurwitzZetaSeries, ← tsum_mul_left]
  congr 1
  funext j
  rw [ratioU, div_pow, ← pow_mul, ← pow_mul]
  push_cast
  ring

/-! ## Main results: Open problems 1 and 2 of arXiv:2512.07028 -/

/-- **Expansion of `ln G*` (answer to arXiv:2512.07028, Open problems 1-2).**  For every
`x, y > 0` (no further hypothesis such as `Q(x, y) < 1`),
`ln G*(x, y) = ∑_{k ≥ 1} (1/k) ((x - y)/2)^{2k} ζ(2k, 1 + (x + y)/2)`,
as an unconditionally convergent series (`HasSum`, indexed by `k + 1`). -/
theorem hasSum_log_gurlandStar {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun k : ℕ => zetaTerm (k + 1) x y) (log (gurlandStar x y)) := by
  have h := hasSum_tsum_ratioU_pow hx hy
  simp only [tsum_ratioU_pow_eq_zetaTerm] at h
  exact h

/-- For positive `x, y`, the partial sums `S_m(x,y)` converge to `ln G*(x,y)`
(arXiv:2512.07028, Open problem 2). -/
theorem tendsto_partialSum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun m : ℕ => partialSum m x y) atTop (𝓝 (log (gurlandStar x y))) := by
  have h := (hasSum_log_gurlandStar hx hy).tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, partialSum, Finset.sum_Ico_eq_sum_range, add_comm 1]

/-- **Open problem 2 of arXiv:2512.07028, as an equality.**  For every `x, y > 0`,
`S_∞(x, y) = lim_{m → ∞} S_m(x, y)` equals `ln G*(x, y)`. -/
theorem limUnder_partialSum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    limUnder atTop (fun m : ℕ => partialSum m x y) = log (gurlandStar x y) :=
  (tendsto_partialSum hx hy).limUnder_eq

/-- For positive `x, y`, the remainder `ln G*(x,y) - S_m(x,y)` tends to zero
(arXiv:2512.07028, Open problem 1). -/
theorem tendsto_remainder {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun m : ℕ => remainder m x y) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := log (gurlandStar x y))).sub (tendsto_partialSum hx hy)
  rw [sub_self] at h
  exact h

/-- The lower bound `0 ≤ R^m(x, y)` of arXiv:2512.07028, Theorem 1, for every `x, y > 0`
and every `m`. -/
theorem remainder_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (m : ℕ) :
    0 ≤ remainder m x y := by
  have hterm : ∀ k : ℕ, 0 ≤ zetaTerm (k + 1) x y := fun k => by
    rw [← tsum_ratioU_pow_eq_zetaTerm]
    exact tsum_nonneg fun j => by
      have := ratioU_nonneg x y j
      positivity
  have hle : ∑ k ∈ Finset.range (m - 1), zetaTerm (k + 1) x y ≤ log (gurlandStar x y) :=
    sum_le_hasSum _ (fun k _ => hterm k) (hasSum_log_gurlandStar hx hy)
  rw [remainder, partialSum, Finset.sum_Ico_eq_sum_range, sub_nonneg]
  simpa only [add_comm 1] using hle

/-- Non-vacuity: the hypotheses hold at `(x, y) = (1/100, 100)`, where the paper's
sufficient condition `Q(x, y) = |x - y| / (2(1 + √(xy))) < 1` fails (`Q = 24.975`). -/
example : Tendsto (fun m : ℕ => remainder m (1 / 100) 100) atTop (𝓝 0) :=
  tendsto_remainder (by norm_num) (by norm_num)

end Candidates.SomeInequalitiesGurlandRatio
