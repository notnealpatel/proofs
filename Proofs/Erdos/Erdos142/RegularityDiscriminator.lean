/-
  Erdős Problem #142 — the shared regularity discriminator.

  The Erdős #142 program studies a counting function `a(N)` (the largest size of a
  3-AP-free subset of `range N`) together with its *deficit*

      `F(N) = log (N / a(N))`,   `D(N) = F(N) / sqrt (log N)`.

  The endpoint of the asymptotic argument is always the same: from
  `F(N) = O(sqrt (log N))` (i.e. `D` bounded) together with the approximate
  product relation `a(N M) ≈ a(N) a(M)` (defect `o(sqrt (log N + log M))`), one
  must conclude `D(N) → 0`, i.e. `a(N) = N^{1-o(1)}`.

  This file isolates the **deterministic analytic kernel** of that endpoint, so
  that the number-theoretic/combinatorial lanes can feed it without duplicating
  the asymptotics.  The kernel is the doubling (square-scale) recurrence

      `D(N^2) = sqrt 2 * D(N) + o(1)`,

  which is exactly what the product relation gives at `M = N`, together with
  boundedness of `D`.  The mechanism is that iterating the recurrence along the
  orbit `N ↦ N^2` multiplies `D` by `sqrt 2` while the errors accumulate with
  weights forming a convergent geometric series; boundedness then forces `D` to
  be as small as the tail of `ε`, hence zero in the limit.

  Two kernels are provided:

  * `tendsto_zero_of_sqrt_two_recurrence` — the exact recurrence
    `|D(N^2) - sqrt 2 * D(N)| ≤ ε(N)` with `ε → 0`, plus `0 ≤ D` and `D` bounded
    above, forces `D → 0`.  This is the primary discriminator.
  * `tendsto_zero_of_dyadic_and_slowVariation` — the transfer step: if `D` is
    slowly varying on `[N, N^2]` (in the multiplicative sense) and vanishes along
    the dyadic scales `2^k`, then `D → 0` everywhere.  This is what upgrades a
    sparse (dyadic) recurrence to a global statement.

  Both statements are non-vacuous (`D ≡ 0` satisfies every hypothesis) and carry
  explicit positivity guards (`sqrt`/`log` arguments, the `N ≥ 2` threshold, and
  `sqrt 2 > 1`) so that no denominator or degenerate value is left to junk.
  Axiom status is checked with `#print axioms` at the end of the file.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped Topology BigOperators

namespace Erdos142

/-! ## Elementary facts about `sqrt 2` -/

/-- The doubling eigenvalue `sqrt 2` is strictly greater than `1`. -/
theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- The uniform geometric bound behind the recurrence squeeze: for `r > 1` the
partial sums `∑_{j < k} r^{-(j+1)}` are all bounded by `1 / (r - 1)`, the tail of
the geometric series at ratio `r⁻¹`. -/
theorem geom_sum_inv_le {r : ℝ} (hr : 1 < r) (k : ℕ) :
    ∑ j ∈ Finset.range k, r⁻¹ ^ (j + 1) ≤ (r - 1)⁻¹ := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hs0 : 0 ≤ r⁻¹ := by positivity
  have hfac : ∑ j ∈ Finset.range k, r⁻¹ ^ (j + 1)
      = r⁻¹ * ∑ j ∈ Finset.range k, r⁻¹ ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [pow_succ, mul_comm])
  have hkey : (∑ j ∈ Finset.range k, r⁻¹ ^ j) * (r⁻¹ - 1) = r⁻¹ ^ k - 1 :=
    geom_sum_mul r⁻¹ k
  have hden : (0 : ℝ) < 1 - r⁻¹ := by
    have : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    linarith
  have hsum_eq : ∑ j ∈ Finset.range k, r⁻¹ ^ j = (1 - r⁻¹ ^ k) / (1 - r⁻¹) := by
    rw [eq_div_iff (ne_of_gt hden)]
    nlinarith [hkey]
  have hpowk : (0 : ℝ) ≤ r⁻¹ ^ k := by positivity
  have hle : (1 - r⁻¹ ^ k) / (1 - r⁻¹) ≤ 1 / (1 - r⁻¹) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    linarith
  rw [hfac, hsum_eq]
  calc r⁻¹ * ((1 - r⁻¹ ^ k) / (1 - r⁻¹))
      ≤ r⁻¹ * (1 / (1 - r⁻¹)) := mul_le_mul_of_nonneg_left hle hs0
    _ = (r - 1)⁻¹ := by
        field_simp

/-! ## Kernel 1: the square-scale `sqrt 2` recurrence forces `D → 0` -/

/-- **The deterministic regularity discriminator.**  Let `D` be a nonnegative,
bounded-above function on the tail `n ≥ N₀`, and suppose that at the square scale
`D` satisfies the approximate doubling relation
`|D (n^2) - sqrt 2 * D n| ≤ ε n` with `ε n → 0`.  Then `D n → 0`.

The proof iterates the recurrence along `n ↦ n^2`.  Writing the telescoping
identity `D (n^(2^k)) / (sqrt 2)^k = D n + ∑_{j<k} X (n^(2^j)) / (sqrt 2)^(j+1)`
with `X m = D (m^2) - sqrt 2 * D m`, and using `0 ≤ D (n^(2^k)) ≤ B` together
with `|X| ≤ ε`, gives
`D n ≤ B / (sqrt 2)^k + ∑_{j<k} ε (n^(2^j)) / (sqrt 2)^(j+1)`.
Letting `k → ∞` and using `ε (n^(2^j)) ≤ sup_{m ≥ n} ε m → 0` and the geometric
bound `geom_sum_inv_le` yields `D n → 0`. -/
theorem tendsto_zero_of_sqrt_two_recurrence
    (D ε : ℕ → ℝ) (N₀ : ℕ)
    (hD_nonneg : ∀ n, N₀ ≤ n → 0 ≤ D n)
    (hD_bdd : ∃ B, ∀ n, N₀ ≤ n → D n ≤ B)
    (hε : Tendsto ε atTop (nhds 0))
    (hrec : ∀ n, N₀ ≤ n → |D (n ^ 2) - Real.sqrt 2 * D n| ≤ ε n) :
    Tendsto D atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hD_bdd
  set r : ℝ := Real.sqrt 2 with hr
  have hr1 : 1 < r := by rw [hr]; exact one_lt_sqrt_two
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop N₀] with n hn
    exact lt_of_lt_of_le ha (hD_nonneg n hn)
  · intro b hb
    set η : ℝ := b * (r - 1) / (2 * r) with hη
    have hηpos : 0 < η := by rw [hη]; positivity
    obtain ⟨Nε, hNε⟩ := (Metric.tendsto_atTop.1 hε) η hηpos
    have hεsmall : ∀ n, Nε ≤ n → ε n < η := by
      intro n hn
      have h := hNε n hn
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.1 h).2
    obtain ⟨k, hk⟩ : ∃ k, B ≤ η * r ^ k := by
      have hgeo := (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop (B / η)
      rw [eventually_atTop] at hgeo
      obtain ⟨k, hk⟩ := hgeo
      exact ⟨k, by
        have h := hk k le_rfl
        rwa [div_le_iff₀ hηpos, mul_comm] at h⟩
    refine eventually_atTop.2 ⟨max (max N₀ Nε) 1, ?_⟩
    intro n hn
    have hnN₀ : N₀ ≤ n :=
      le_trans (le_trans (le_max_left N₀ Nε) (le_max_left (max N₀ Nε) 1)) hn
    have hnNε : Nε ≤ n :=
      le_trans (le_trans (le_max_right N₀ Nε) (le_max_left (max N₀ Nε) 1)) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right (max N₀ Nε) 1) hn
    let m : ℕ → ℕ := fun j => n ^ (2 ^ j)
    have hm1 : ∀ j, 1 ≤ m j := fun j => one_le_pow₀ hn1
    have hmn : ∀ j, n ≤ m j := by
      intro j
      have h : n ^ 1 ≤ n ^ (2 ^ j) := pow_le_pow_right₀ hn1 Nat.one_le_two_pow
      simpa using h
    have hmN₀ : ∀ j, N₀ ≤ m j := fun j => le_trans hnN₀ (hmn j)
    have hmNε : ∀ j, Nε ≤ m j := fun j => le_trans hnNε (hmn j)
    have hmsq : ∀ j, m (j + 1) = (m j) ^ 2 := by
      intro j
      show n ^ 2 ^ (j + 1) = (n ^ 2 ^ j) ^ 2
      rw [pow_succ, pow_mul]
    have hmrec : ∀ j, |D ((m j) ^ 2) - r * D (m j)| ≤ ε (m j) := by
      intro j
      have h := hrec (m j) (hmN₀ j)
      rwa [hr] at h
    let X : ℕ → ℝ := fun j => D ((m j) ^ 2) - r * D (m j)
    let g : ℕ → ℝ := fun k => D (m k) / r ^ k
    have hX : ∀ j, |X j| ≤ ε (m j) := fun j => hmrec j
    have hgrec : ∀ k, g (k + 1) = g k + X k / r ^ (k + 1) := by
      intro k
      show D (m (k + 1)) / r ^ (k + 1) = D (m k) / r ^ k + X k / r ^ (k + 1)
      rw [hmsq k]
      simp only [X]
      rw [pow_succ]
      field_simp
      ring
    have hgtel : ∀ k, g k = D n + ∑ j ∈ Finset.range k, X j / r ^ (j + 1) := by
      intro k
      induction k with
      | zero => simp [g, m, div_one]
      | succ k ih =>
        rw [hgrec k, ih, Finset.sum_range_succ]
        ring
    have hsum_le : ∑ j ∈ Finset.range k, ε (m j) / r ^ (j + 1) ≤ η * (r - 1)⁻¹ := by
      have hterm : ∀ j ∈ Finset.range k, ε (m j) / r ^ (j + 1) ≤ η * r⁻¹ ^ (j + 1) := by
        intro j _
        rw [div_eq_mul_inv, inv_pow]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hεsmall (m j) (hmNε j))) (by positivity)
      calc ∑ j ∈ Finset.range k, ε (m j) / r ^ (j + 1)
          ≤ ∑ j ∈ Finset.range k, η * r⁻¹ ^ (j + 1) := Finset.sum_le_sum hterm
        _ = η * ∑ j ∈ Finset.range k, r⁻¹ ^ (j + 1) := by rw [Finset.mul_sum]
        _ ≤ η * (r - 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (geom_sum_inv_le hr1 k) (le_of_lt hηpos)
    have hbound : D n ≤ B / r ^ k + η * (r - 1)⁻¹ := by
      have h1 : D n = g k - ∑ j ∈ Finset.range k, X j / r ^ (j + 1) := by
        rw [hgtel k]; ring
      have h2 : -∑ j ∈ Finset.range k, X j / r ^ (j + 1)
          ≤ ∑ j ∈ Finset.range k, ε (m j) / r ^ (j + 1) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro j _
        have hneg : -X j ≤ ε (m j) := by
          have h := abs_le.1 (hX j)
          linarith [h.1, h.2]
        have hpos : (0 : ℝ) < r ^ (j + 1) := by positivity
        rw [← neg_div]
        exact div_le_div_of_nonneg_right hneg (le_of_lt hpos)
      have hgk : g k ≤ B / r ^ k := by
        simp only [g]
        exact div_le_div_of_nonneg_right (hB (m k) (hmN₀ k)) (by positivity)
      rw [h1]
      linarith [h2, hgk, hsum_le]
    have hBk : B / r ^ k ≤ η := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < r ^ k)]
      linarith [hk]
    calc D n ≤ B / r ^ k + η * (r - 1)⁻¹ := hbound
      _ ≤ η + η * (r - 1)⁻¹ := by linarith [hBk]
      _ < b := by
        have hval : η + η * (r - 1)⁻¹ = b / 2 := by
          rw [hη]
          have hrm1 : r - 1 ≠ 0 := by linarith
          field_simp
          ring
        rw [hval]; linarith [hb]

/-! ## Kernel 2: slow variation transfers a dyadic vanishing to all scales -/

/-- **Slow-variation transfer.**  Suppose `D` is nonnegative on `n ≥ N₀`, slowly
varying on multiplicative windows `[n, n^2]` with modulus `ω n → 0`, i.e.
`|D m - D n| ≤ ω n` whenever `n ≤ m ≤ n^2`, and suppose `D (2^k) → 0` along the
dyadic scales.  Then `D n → 0`.

The proof picks, for each `n ≥ 2`, the exponent `k = log₂ n + 1`, for which
`n ≤ 2^k ≤ n^2`; slow variation compares `D n` with `D (2^k)`, and the latter is
small because `2^k → ∞`. -/
theorem tendsto_zero_of_dyadic_and_slowVariation
    (D : ℕ → ℝ) (ω : ℕ → ℝ) (N₀ : ℕ)
    (hD_nonneg : ∀ n, N₀ ≤ n → 0 ≤ D n)
    (hω : Tendsto ω atTop (nhds 0))
    (hslow : ∀ n m, N₀ ≤ n → n ≤ m → m ≤ n ^ 2 → |D m - D n| ≤ ω n)
    (hdyadic : Tendsto (fun k : ℕ => D (2 ^ k)) atTop (nhds 0)) :
    Tendsto D atTop (nhds 0) := by
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop N₀] with n hn
    exact lt_of_lt_of_le ha (hD_nonneg n hn)
  · intro b hb
    have hb2 : 0 < b / 2 := by linarith
    obtain ⟨Nω, hNω⟩ := (Metric.tendsto_atTop.1 hω) (b / 2) hb2
    have hωsmall : ∀ n, Nω ≤ n → ω n < b / 2 := by
      intro n hn
      have h := hNω n hn
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.1 h).2
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hdyadic) (b / 2) hb2
    have hDsmall : ∀ k, K ≤ k → D (2 ^ k) < b / 2 := by
      intro k hk
      have h := hK k hk
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.1 h).2
    refine eventually_atTop.2 ⟨max (max (max N₀ Nω) (2 ^ K)) 2, ?_⟩
    intro n hn
    have hnN₀ : N₀ ≤ n :=
      le_trans (le_trans (le_trans (le_max_left N₀ Nω) (le_max_left _ _))
        (le_max_left _ _)) hn
    have hnNω : Nω ≤ n :=
      le_trans (le_trans (le_trans (le_max_right N₀ Nω) (le_max_left _ _))
        (le_max_left _ _)) hn
    have hn2K : 2 ^ K ≤ n :=
      le_trans (le_trans (le_max_right (max N₀ Nω) (2 ^ K)) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ 2) hn
    set k : ℕ := Nat.log 2 n + 1 with hkdef
    have hn_le : n ≤ 2 ^ k := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      simpa [hkdef] using le_of_lt h
    have h2k_le : 2 ^ k ≤ n ^ 2 := by
      have hnpos : n ≠ 0 := by omega
      have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hnpos
      calc 2 ^ k = 2 ^ Nat.log 2 n * 2 := by rw [hkdef, pow_succ]
        _ ≤ n * 2 := Nat.mul_le_mul_right 2 h1
        _ ≤ n * n := Nat.mul_le_mul_left n (by omega)
        _ = n ^ 2 := (pow_two n).symm
    have hKle : K ≤ k := by
      have h : 2 ^ K ≤ 2 ^ k := le_trans hn2K hn_le
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
    have hDk : D (2 ^ k) < b / 2 := hDsmall k hKle
    have hslow' := hslow n (2 ^ k) hnN₀ hn_le h2k_le
    have hωn : ω n < b / 2 := hωsmall n hnNω
    have hupper : D n ≤ D (2 ^ k) + ω n := by
      have h := (abs_le.1 hslow').1
      linarith
    linarith

/-! ## The #142 deficit definitions -/

/-- The logarithmic deficit `F(N) = log (N / a(N))` of a counting function `a`
with `a(N) ≤ N`.  The hypothesis `a(N) ≥ 1` for `N ≥ 1` keeps the argument of
`log` positive. -/
noncomputable def logDeficit (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (a N))

/-- The normalized deficit `D(N) = F(N) / sqrt (log N)`, the quantity that the
#142 endpoint drives to zero. -/
noncomputable def normalizedDeficit (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  logDeficit a N / Real.sqrt (Real.log N)

/-- Ground truth: for the identity counting function `a(N) = N` the deficit
vanishes. -/
example : logDeficit (fun N => N) 4 = 0 := by
  simp [logDeficit]

/-- Ground truth: at `a ≡ 1` the deficit is `log N`. -/
example : logDeficit (fun _ => 1) 4 = Real.log 4 := by
  simp [logDeficit]

/-- Ground truth at the degenerate index `N = 1`: `log 1 = 0`, so the denominator
`sqrt (log N)` vanishes and `D 1 = 0 / 0` is the junk value.  The analytic
statements above therefore carry the positive-denominator guard `N ≥ 2`, where
`log N > 0`. -/
example : normalizedDeficit (fun _ => 1) 1 = 0 := by
  simp [normalizedDeficit, logDeficit]

/-- **The square-scale identity.**  For `N ≥ 2`, the difference between the
normalized deficit at `N^2` and `sqrt 2` times its value at `N` is exactly the
logarithmic product defect divided by `sqrt (2 log N)`.  This is the bridge from
the #142 product relation `a(N)^2 ≈ a(N^2)` to the recurrence consumed by
`tendsto_zero_of_sqrt_two_recurrence`. -/
theorem normalizedDeficit_sq_sub {a : ℕ → ℕ} {N : ℕ} (hN : 2 ≤ N)
    (ha_pos : ∀ N, 1 ≤ N → 1 ≤ a N) :
    normalizedDeficit a (N ^ 2) - Real.sqrt 2 * normalizedDeficit a N
      = Real.log ((a N : ℝ) ^ 2 / (a (N ^ 2) : ℝ)) / Real.sqrt (2 * Real.log N) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1'
  have haN : (0 : ℝ) < (a N : ℝ) := by exact_mod_cast (ha_pos N hN1)
  have haN2 : (0 : ℝ) < (a (N ^ 2) : ℝ) := by
    exact_mod_cast (ha_pos (N ^ 2) (by nlinarith [hN]))
  have hcast : ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
  rw [normalizedDeficit, normalizedDeficit, logDeficit, logDeficit, hcast]
  rw [Real.log_div (by positivity : ((N : ℝ) ^ 2) ≠ 0) (ne_of_gt haN2)]
  rw [Real.log_pow]
  rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt haN)]
  rw [Real.log_div (by positivity : ((a N : ℝ) ^ 2) ≠ 0) (ne_of_gt haN2)]
  rw [Real.log_pow]
  simp only [Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (N : ℝ))]
  have hsq : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogN)
  have hsq2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq' : Real.sqrt (Real.log (N : ℝ)) ^ 2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (le_of_lt hlogN)
  field_simp
  rw [hsq2']
  ring

/-- **The #142 consumer (recurrence form).**  A nonnegative, bounded-above
normalized deficit satisfying the square-scale `sqrt 2` recurrence with `o(1)`
defect tends to zero.  This is the shape in which the combinatorial lanes deliver
their product relation. -/
theorem tendsto_normalizedDeficit_zero_of_recurrence
    (a : ℕ → ℕ) (ε : ℕ → ℝ)
    (hD_nonneg : ∀ N, 1 ≤ N → 0 ≤ normalizedDeficit a N)
    (hD_bdd : ∃ B, ∀ N, 1 ≤ N → normalizedDeficit a N ≤ B)
    (hε : Tendsto ε atTop (nhds 0))
    (hrec : ∀ N, 1 ≤ N →
      |normalizedDeficit a (N ^ 2) - Real.sqrt 2 * normalizedDeficit a N| ≤ ε N) :
    Tendsto (normalizedDeficit a) atTop (nhds 0) :=
  tendsto_zero_of_sqrt_two_recurrence _ _ 1 hD_nonneg hD_bdd hε hrec

/-- **The #142 consumer (product-defect form).**  Let `a` be a counting function
with `1 ≤ a(N) ≤ N` for `N ≥ 1`, whose normalized deficit is bounded above and
whose *logarithmic product defect* `|log (a(N)^2 / a(N^2))|` is `≤ η(N)` with
`η(N) / sqrt (log N) → 0`.  Then `D(N) → 0`.

This is the deterministic endpoint requested for Erdős #142: `F(N) = O(sqrt (log N))`
is `hD_bdd`, and the approximate product relation `a(N M) ≈ a(N) a(M)` with
defect `o(sqrt (log N + log M))` specializes at `M = N` to `hprod` with
`η(N) = o(sqrt (log N))`. -/
theorem tendsto_normalizedDeficit_zero_of_product_defect
    (a : ℕ → ℕ) (η : ℕ → ℝ)
    (ha_pos : ∀ N, 1 ≤ N → 1 ≤ a N)
    (ha_le : ∀ N, 1 ≤ N → a N ≤ N)
    (hD_bdd : ∃ B, ∀ N, 2 ≤ N → normalizedDeficit a N ≤ B)
    (hη : Tendsto (fun N => η N / Real.sqrt (Real.log N)) atTop (nhds 0))
    (hprod : ∀ N, 2 ≤ N → |Real.log ((a N : ℝ) ^ 2 / (a (N ^ 2) : ℝ))| ≤ η N) :
    Tendsto (normalizedDeficit a) atTop (nhds 0) := by
  apply tendsto_zero_of_sqrt_two_recurrence (normalizedDeficit a)
    (fun N => η N / Real.sqrt (2 * Real.log N)) 2
  · intro N hN
    have hN1 : 1 ≤ N := by omega
    have haN : (0 : ℝ) < (a N : ℝ) := by exact_mod_cast (ha_pos N hN1)
    have hle : (a N : ℝ) ≤ (N : ℝ) := by exact_mod_cast (ha_le N hN1)
    rw [normalizedDeficit, logDeficit]
    apply div_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ haN]
      simpa using hle
    · exact Real.sqrt_nonneg _
  · exact hD_bdd
  · have h1 : Tendsto (fun N => (Real.sqrt 2)⁻¹ * (η N / Real.sqrt (Real.log N)))
        atTop (nhds 0) := by
      simpa using hη.const_mul (Real.sqrt 2)⁻¹
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (N : ℝ))]
    have hsq : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogN)
    have hsq2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
  · intro N hN
    rw [normalizedDeficit_sq_sub hN ha_pos, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (hprod N hN) (Real.sqrt_nonneg _)

end Erdos142

#print axioms Erdos142.one_lt_sqrt_two
#print axioms Erdos142.geom_sum_inv_le
#print axioms Erdos142.tendsto_zero_of_sqrt_two_recurrence
#print axioms Erdos142.normalizedDeficit_sq_sub
#print axioms Erdos142.tendsto_normalizedDeficit_zero_of_recurrence
#print axioms Erdos142.tendsto_normalizedDeficit_zero_of_product_defect
#print axioms Erdos142.tendsto_zero_of_dyadic_and_slowVariation