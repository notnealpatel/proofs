/-
  Erdős Problem #142 — the eventual EHPS-shaped torus lower bound.

  This module closes the asymptotic chain: it composes the four accepted
  kernels `TorusCensusDecay`, `TorusSaddlePoint`, `TorusErrorAbsorption`, and
  `TorusAsymptoticAssembly` into the *unconditional* eventual lower bound

  `N · exp(-(torusLeadingConstant + δ) · √(log N)) ≤ r₃(N)`

  for every `δ > 0`, where `r₃(N) = rothNumberNat N`.

  The construction is the EHPS torus saddle point at a fixed defect budget
  `δ > 0`.  For the sub-unit regime `0 < δ ≤ 1` we take the parameters

  * `η = torusEta δ` (the quadratic loss of the defect, with `0 < η ≤ 1`);
  * `e = max 6 (18/η)`;
  * `βmax = log(24/7) + η` (the census-log ceiling);
  * `K = βmax + log 1320 + 2·log e` (the additive error budget);

  and, for each sufficiently large `N`, a prime `q > N` (via
  `Nat.exists_infinite_primes`), the census exponent
  `β = log(1/b(e,q)) ∈ [1, βmax]` (`census_log_bounds`), and the integer saddle
  scale `k = saddleK β (log N)` (`saddleK_spec`).  The logarithmic budget

  `k·β + log N/k + log(660·k·e²)`

  is then bounded by `(torusLeadingConstant + δ)·√(log N)`:

  * `k·β + log N/k ≤ 2·√(β·log N) + β ≤ (torusLeadingConstant + δ/2)·√(log N)`
    by the saddle bound, monotonicity of `√`, and the square-completion
    identity `two_mul_sqrt_log_add_torusEta`;
  * `β + log(660·k·e²) ≤ K + log(log N)/2` using `k ≤ 2·√(log N)`;
  * `K + log(log N)/2 ≤ (δ/2)·√(log N)` by `torusErrorAbsorption`.

  `rothNumberNat_lower_bound_of_budget` then turns this budget into the bound.
  The general `δ > 0` case reduces to `δ = 1` by monotonicity of `exp`, since a
  larger defect only weakens the lower bound.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.TorusCensusDecay
import Erdos.Erdos142.TorusSaddlePoint
import Erdos.Erdos142.TorusErrorAbsorption
import Erdos.Erdos142.TorusAsymptoticAssembly

set_option autoImplicit false

namespace Erdos142

/-- **Core eventual lower bound in the sub-unit defect regime.**  For reals
`δ` with `0 < δ ≤ 1`,

`∀ᶠ N, N · exp(-(torusLeadingConstant + δ)·√(log N)) ≤ r₃(N)`.

The parameters `η = torusEta δ`, `e = max 6 (18/η)`, `βmax = log(24/7) + η`,
and `K = βmax + log 1320 + 2·log e` are fixed once and for all.  Eventually the
five scale constraints `64 ≤ N`, `58/η ≤ N`, `4·βmax ≤ log N`,
`4096/δ^4 ≤ log N`, and `16·K²/δ² ≤ log N` hold simultaneously; for such `N` a
prime `q > N` is chosen and the census/saddle/absorption chain supplies the
budget consumed by `rothNumberNat_lower_bound_of_budget`. -/
lemma eventually_lower_bound_of_le_one (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) * Real.exp (-(torusLeadingConstant + δ) * Real.sqrt (Real.log N)) ≤
        (rothNumberNat N : ℝ) := by
  set η : ℝ := torusEta δ with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact torusEta_pos hδ0
  have hη1 : η ≤ 1 := by rw [hηdef]; exact torusEta_le_one hδ0 hδ1
  set e : ℝ := max 6 (18 / η) with hedef
  have he6 : 6 ≤ e := by rw [hedef]; exact le_max_left _ _
  have he18 : 18 / η ≤ e := by rw [hedef]; exact le_max_right _ _
  set βmax : ℝ := Real.log (24 / 7) + η with hβmaxdef
  have hβmax0 : 0 < βmax := by
    have h := Real.log_pos (by norm_num : (1 : ℝ) < 24 / 7)
    rw [hβmaxdef]; linarith
  set K : ℝ := βmax + Real.log 1320 + 2 * Real.log e with hKdef
  have hK0 : 0 ≤ K := by
    have he1 : (1 : ℝ) ≤ e := by linarith
    have hloge : 0 ≤ Real.log e := Real.log_nonneg he1
    have hlog1320 : 0 ≤ Real.log 1320 := Real.log_nonneg (by norm_num)
    rw [hKdef]; linarith [hβmax0.le, hloge, hlog1320]
  have htend : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, (64 : ℕ) ≤ N := Filter.eventually_ge_atTop 64
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, 58 / η ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (Filter.eventually_ge_atTop (58 / η))
  have h3 : ∀ᶠ N : ℕ in Filter.atTop, 4 * βmax ≤ Real.log (N : ℝ) :=
    htend.eventually (Filter.eventually_ge_atTop (4 * βmax))
  have h4 : ∀ᶠ N : ℕ in Filter.atTop, 4096 / δ ^ 4 ≤ Real.log (N : ℝ) :=
    htend.eventually (Filter.eventually_ge_atTop (4096 / δ ^ 4))
  have h5 : ∀ᶠ N : ℕ in Filter.atTop, 16 * K ^ 2 / δ ^ 2 ≤ Real.log (N : ℝ) :=
    htend.eventually (Filter.eventually_ge_atTop (16 * K ^ 2 / δ ^ 2))
  refine (h1.and (h2.and (h3.and (h4.and h5)))).mono (fun N hN => ?_)
  obtain ⟨hN64, hN58, hN4β, hN4096, hN16K⟩ := hN
  obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (N + 1)
  have hNq : N < q := by omega
  have hNleqq : N ≤ q := by omega
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨hbpos, hlog1, hlogβmaxraw⟩ :=
    census_log_bounds (e := e) (η := η) (q := q) (N := N) hη0 hη1 he6 he18 hNq hN58
  set β : ℝ := Real.log (1 / b e q) with hβdef
  have hβ1 : 1 ≤ β := hlog1
  have hβle : β ≤ βmax := by
    have h := hlogβmaxraw
    rw [← hβmaxdef] at h
    exact h
  have hlogNpos : 0 < Real.log (N : ℝ) := by linarith [hN4β, hβmax0]
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := hlogNpos.le
  have h4β : 4 * β ≤ Real.log (N : ℝ) := by linarith [hβle, hN4β]
  have hspec := saddleK_spec (β := β) (L := Real.log (N : ℝ)) hβ1 h4β
  set k : ℕ := saddleK β (Real.log (N : ℝ)) with hkdef
  obtain ⟨hk1, hkle, hsaddle⟩ := hspec
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hepos : 0 < e := by linarith
  have hdiv : Real.log (N : ℝ) / β ≤ Real.log (N : ℝ) := div_le_self hlogN0 hβ1
  have hsqrtdiv : Real.sqrt (Real.log (N : ℝ) / β) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_le_sqrt hdiv
  have hk_le2 : (k : ℝ) ≤ 2 * Real.sqrt (Real.log (N : ℝ)) := by linarith [hkle, hsqrtdiv]
  have h660k : 0 < 660 * (k : ℝ) * e ^ 2 := by positivity
  have hsqrtlogpos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogNpos
  have hstep : 660 * (k : ℝ) * e ^ 2 ≤ 1320 * e ^ 2 * Real.sqrt (Real.log (N : ℝ)) := by
    have h660e2 : (0 : ℝ) ≤ 660 * e ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hk_le2 h660e2
    nlinarith [hmul]
  have hlogmono : Real.log (660 * (k : ℝ) * e ^ 2) ≤
      Real.log (1320 * e ^ 2 * Real.sqrt (Real.log (N : ℝ))) :=
    Real.log_le_log h660k hstep
  have hexpand : Real.log (1320 * e ^ 2 * Real.sqrt (Real.log (N : ℝ))) =
      Real.log 1320 + 2 * Real.log e + Real.log (Real.log (N : ℝ)) / 2 := by
    have h1ne : (1320 : ℝ) * e ^ 2 ≠ 0 := by positivity
    have h2ne : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt hsqrtlogpos
    rw [Real.log_mul h1ne h2ne]
    rw [Real.log_mul (by norm_num : (1320 : ℝ) ≠ 0) (by positivity : e ^ 2 ≠ 0)]
    rw [Real.log_pow, Real.log_sqrt hlogN0]
    norm_num
  have hC : β + Real.log (660 * (k : ℝ) * e ^ 2) ≤
      K + Real.log (Real.log (N : ℝ)) / 2 := by
    have h := hlogmono
    rw [hexpand] at h
    rw [hKdef]
    linarith [h, hβle]
  have hD : K + Real.log (Real.log (N : ℝ)) / 2 ≤
      (δ / 2) * Real.sqrt (Real.log (N : ℝ)) :=
    torusErrorAbsorption (δ := δ) (K := K) (L := Real.log (N : ℝ)) hδ0 hK0 hN4096 hN16K
  have hB : 2 * Real.sqrt (β * Real.log (N : ℝ)) ≤
      (torusLeadingConstant + δ / 2) * Real.sqrt (Real.log (N : ℝ)) := by
    have hβlog : β * Real.log (N : ℝ) ≤ βmax * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hβle hlogN0
    have hsqrt1 : Real.sqrt (β * Real.log (N : ℝ)) ≤
        Real.sqrt (βmax * Real.log (N : ℝ)) := Real.sqrt_le_sqrt hβlog
    have hsplit : Real.sqrt (βmax * Real.log (N : ℝ)) =
        Real.sqrt βmax * Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_mul hβmax0.le _
    have h2sqrt : 2 * Real.sqrt βmax = torusLeadingConstant + δ / 2 := by
      rw [hβmaxdef, hηdef]
      exact two_mul_sqrt_log_add_torusEta hδ0
    calc 2 * Real.sqrt (β * Real.log (N : ℝ))
        ≤ 2 * Real.sqrt (βmax * Real.log (N : ℝ)) := by linarith [hsqrt1]
      _ = 2 * (Real.sqrt βmax * Real.sqrt (Real.log (N : ℝ))) := by rw [hsplit]
      _ = (2 * Real.sqrt βmax) * Real.sqrt (Real.log (N : ℝ)) := by ring
      _ = (torusLeadingConstant + δ / 2) * Real.sqrt (Real.log (N : ℝ)) := by rw [h2sqrt]
  have hbudget : (k : ℝ) * β + Real.log (N : ℝ) / (k : ℝ) +
      Real.log (660 * (k : ℝ) * e ^ 2) ≤
      (torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)) := by
    linarith [hsaddle, hB, hC, hD]
  rw [hβdef] at hbudget
  simpa only [neg_mul] using
    rothNumberNat_lower_bound_of_budget (e := e) (C := torusLeadingConstant + δ)
      (N := N) (q := q) (k := k) hN64 hNleqq hk1 he6 hbpos hbudget

/-- **Eventual EHPS-shaped torus lower bound for the Roth number.**  For every
real `δ > 0`,

`∀ᶠ N, N · exp(-(torusLeadingConstant + δ)·√(log N)) ≤ r₃(N)`.

For `δ ≤ 1` this is `eventually_lower_bound_of_le_one`.  For `δ > 1` the
sub-unit statement at `δ = 1` is stronger, because `torusLeadingConstant + 1 ≤
torusLeadingConstant + δ` makes the exponential factor larger; monotonicity of
`Real.exp` and multiplication by `N ≥ 0` transfer the bound. -/
theorem eventually_rothNumberNat_lower_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) * Real.exp (-(torusLeadingConstant + δ) * Real.sqrt (Real.log N)) ≤
        (rothNumberNat N : ℝ) := by
  by_cases hδ1 : δ ≤ 1
  · exact eventually_lower_bound_of_le_one δ hδ hδ1
  · have hδ1' : 1 < δ := not_le.mp hδ1
    have h1 := eventually_lower_bound_of_le_one 1 (by norm_num) (le_refl 1)
    refine h1.mono (fun N hN => ?_)
    have hle : torusLeadingConstant + 1 ≤ torusLeadingConstant + δ := by linarith [hδ1']
    have hsqrt0 : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
    have harg : -(torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)) ≤
        -(torusLeadingConstant + 1) * Real.sqrt (Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (neg_le_neg hle) hsqrt0
    have hexp := Real.exp_le_exp.mpr harg
    calc (N : ℝ) * Real.exp (-(torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)))
        ≤ (N : ℝ) *
            Real.exp (-(torusLeadingConstant + 1) * Real.sqrt (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg N)
      _ ≤ (rothNumberNat N : ℝ) := hN

-- Ground-truth checks.

/-- Non-vacuity at `δ = 1`: the target theorem applies to the boundary defect
and yields the eventual statement explicitly. -/
example : ∀ᶠ N : ℕ in Filter.atTop,
    (N : ℝ) * Real.exp (-(torusLeadingConstant + 1) * Real.sqrt (Real.log N)) ≤
      (rothNumberNat N : ℝ) :=
  eventually_rothNumberNat_lower_bound 1 (by norm_num)

/-- Non-vacuity of the eventual statement: instantiating the bound at `δ = 1`
and unpacking `Filter.eventually_atTop` produces a concrete `N` for which the
inequality holds, so the statement is not vacuously true. -/
example : ∃ N : ℕ, (N : ℝ) * Real.exp (-(torusLeadingConstant + 1) * Real.sqrt (Real.log N)) ≤
    (rothNumberNat N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (eventually_rothNumberNat_lower_bound 1 (by norm_num))
  exact ⟨N₀, hN₀ N₀ le_rfl⟩

/-- The reduction for `δ > 1` is exercised at `δ = 2`, one full unit above the
sub-unit regime. -/
example : ∀ᶠ N : ℕ in Filter.atTop,
    (N : ℝ) * Real.exp (-(torusLeadingConstant + 2) * Real.sqrt (Real.log N)) ≤
      (rothNumberNat N : ℝ) :=
  eventually_rothNumberNat_lower_bound 2 (by norm_num)

#print axioms eventually_lower_bound_of_le_one
#print axioms eventually_rothNumberNat_lower_bound

end Erdos142