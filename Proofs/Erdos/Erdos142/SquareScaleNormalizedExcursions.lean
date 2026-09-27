/-
  Erdős Problem #142 — normalized square-tower excursions.

  This module records a *strict conditional asymptotic advance* on a fixed
  square tower.  For a base `M` and the iterated-square tower

      `N k = M ^ (2 ^ k)`,

  write `D k = normalizedDeficit r₃ (N k)` for the normalized deficit and

      `Z k = squareScaleDefect (N k) / √(log (N k))`

  for the normalized square-scale defect.  The theorem proved here is

      `(∃ᶠ k, c ≤ D k) → (∃ᶠ k, Z k ≤ -(2 - √2) · c)`

  for every `M ≥ 3` and every `c > 0`.

  **What this says and what it does not say.**  The conclusion is *conditional*
  on the hypothesis that the normalized deficits carry positive mass `c`
  infinitely often along the tower.  It asserts that this frequent positive
  `D`-mass forces normalized square-scale defects to make negative excursions
  bounded away from zero infinitely often.  It does **not** prove `D → 0`, it
  does **not** prove the existence of positive excursions, it is **not** a
  two-sided oscillation statement, and it does **not** provide an asymptotic
  formula for `D` or `Z`.  It is a one-directional implication between two
  frequent-event statements.

  The analytic content is a reusable generic real-sequence growth lemma: a
  shift identity `x k = s · d (k+1) - s² · d k` with `1 < s`, together with an
  eventual upper bound on `d` and infinitely many `d k ≥ c`, forces infinitely
  many `x k ≤ -(s² - s)·c`.  The Erdős endpoint specializes it at `s = √2`,
  where `s² - s = 2 - √2`, using the exact tower recurrence
  `Z k = √2 · D (k+1) - 2 · D k` and the accepted eventual envelope
  `eventually_normalizedDeficit_rothNumberNat_le_add 1`.

  No `sorry`, no `admit`, no `native_decide`, no `unsafe`, and no new axioms;

-/

import Erdos.Erdos142.NormalizedDeficitEnvelope
import Erdos.Erdos142.SquareScaleNegative

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The generic shift-growth lemma -/

/-- **Generic shift-growth lemma.**  Let `1 < s`, let `d` and `x` be real
sequences obeying the shift identity `x k = s · d (k+1) - s² · d k`, and suppose
`d` is eventually bounded above by `B`.  If `d k ≥ c` infinitely often, then
`x k ≤ -(s² - s) · c` infinitely often.

The proof negates the conclusion to get the eventual strict reverse
`s · (d k - c) < d (k+1) - c` for `e = d - c`, intersects the frequent seed
`c ≤ d k` with that eventual region and the eventual upper bound, applies the
growth once to obtain a strictly positive seed, iterates the recurrence
geometrically, and contradicts the eventual upper bound via
`tendsto_pow_atTop_atTop_of_one_lt`.  No positivity of `c` is used; it belongs
to the Erdős endpoint, where `c` is the frequent normalized-deficit level. -/
theorem frequently_shift_sub_le_neg_of_frequently_le
    (d x : ℕ → ℝ) (s B c : ℝ) (hs : 1 < s)
    (hx : ∀ k : ℕ, x k = s * d (k + 1) - s ^ 2 * d k)
    (hupper : ∀ᶠ k : ℕ in atTop, d k ≤ B)
    (hfreq : ∃ᶠ k : ℕ in atTop, c ≤ d k) :
    ∃ᶠ k : ℕ in atTop, x k ≤ -(s ^ 2 - s) * c := by
  rw [Filter.Frequently]
  intro hnever
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hgrowth : ∀ᶠ k : ℕ in atTop, s * (d k - c) < d (k + 1) - c := by
    filter_upwards [hnever] with k hk
    have hk' : -(s ^ 2 - s) * c < x k := lt_of_not_ge hk
    rw [hx k] at hk'
    have h1 : s * d (k + 1) > s ^ 2 * d k - (s ^ 2 - s) * c := by linarith
    have h2 : s * (s * d k - (s - 1) * c) = s ^ 2 * d k - (s ^ 2 - s) * c := by ring
    rw [← h2] at h1
    have h3 : s * d k - (s - 1) * c < d (k + 1) := lt_of_mul_lt_mul_left h1 hs0.le
    linarith [h3]
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hgrowth.and hupper)
  obtain ⟨j, hjc, hjK⟩ := (hfreq.and_eventually (eventually_ge_atTop K)).exists
  have hseed : 0 < d (j + 1) - c := by
    have h1 := (hK j hjK).1
    have h2 : 0 ≤ d j - c := by linarith
    nlinarith [h1, h2, hs0]
  have hgeom : ∀ n : ℕ, s ^ n * (d (j + 1) - c) ≤ d (j + 1 + n) - c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := (hK (j + 1 + n) (by omega)).1
      have hmul := mul_le_mul_of_nonneg_left ih hs0.le
      have hgoal : s ^ (n + 1) * (d (j + 1) - c) ≤ s * (d (j + 1 + n) - c) := by
        rw [pow_succ]
        linarith [hmul]
      have he : j + 1 + (n + 1) = j + 1 + n + 1 := by omega
      rw [he]
      exact le_of_lt (lt_of_le_of_lt hgoal hstep)
  have hbound : ∀ n : ℕ, s ^ n * (d (j + 1) - c) ≤ B - c := by
    intro n
    have hu := (hK (j + 1 + n) (by omega)).2
    linarith [hgeom n, hu]
  have hpow : Tendsto (fun n : ℕ => s ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hs
  have hscale : Tendsto (fun n : ℕ => (d (j + 1) - c) * s ^ n) atTop atTop :=
    hpow.const_mul_atTop hseed
  obtain ⟨n, hn⟩ := (hscale.eventually (eventually_gt_atTop (B - c))).exists
  have hle := hbound n
  nlinarith [hn, hle]

/-- **Non-vacuity of the generic shift-growth lemma.**  The constant sequence
`d ≡ 1/2` with `s = 2`, `B = 1` and `c = 1/2` satisfies every hypothesis (it is
bounded above by `1` and is frequently at least `1/2`), so all hypotheses are
jointly realizable and the conclusion is not vacuous. -/
example :
    ∃ᶠ _ : ℕ in atTop,
      2 * (1 / 2 : ℝ) - 2 ^ 2 * (1 / 2) ≤ -(2 ^ 2 - 2) * (1 / 2) :=
  frequently_shift_sub_le_neg_of_frequently_le
    (fun _ : ℕ => (1 / 2 : ℝ))
    (fun _ : ℕ => 2 * (1 / 2 : ℝ) - 2 ^ 2 * (1 / 2))
    (2 : ℝ) 1 (1 / 2) (by norm_num) (fun _ => rfl)
    (Filter.Eventually.of_forall (fun _ => by norm_num))
    (Filter.Frequently.of_forall (fun _ => by norm_num))

/-- The endpoint's excursion constant is strictly positive: `0 < 2 - √2`.  Hence
the infinity-often bound `-(2 - √2)·c` with `c > 0` is a strictly negative
level, as the informal statement intends. -/
example : (0 : ℝ) < 2 - Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hsq, hnn]

/-! ## The exact tower recurrence for the normalized square-scale defect -/

/-- **Exact tower recurrence.**  Along the square tower `N k = M ^ (2 ^ k)`, the
normalized square-scale defect satisfies the linear recurrence

`Z k = √2 · D (k+1) - 2 · D k`,

where `D k = normalizedDeficit r₃ (N k)` and
`Z k = squareScaleDefect (N k) / √(log (N k))`.

The recurrence combines `squareScaleDefect_eq_rothLogDeficit_sub` with the tower
identity `N (k+1) = (N k)²` and the logarithmic-scale identity
`√(log (N (k+1))) = √2 · √(log (N k))` supplied by `sqrt_log_iterated_square`.
The base hypothesis `M ≥ 2` keeps `√(log M)` and `√(log (M ^ (2 ^ k)))` nonzero,
off their junk values at `M = 1`. -/
theorem squareScaleDefect_div_sqrt_log_iterated_square_eq
    (M k : ℕ) (hM : 2 ≤ M) :
    squareScaleDefect (M ^ (2 ^ k)) /
        Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) =
      Real.sqrt 2 *
          normalizedDeficit rothNumberNat (M ^ (2 ^ (k + 1))) -
        2 * normalizedDeficit rothNumberNat (M ^ (2 ^ k)) := by
  have hM1 : 1 ≤ M := by omega
  have hNk : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ hM1
  have hsq : (M ^ (2 ^ k)) ^ 2 = M ^ (2 ^ (k + 1)) := by
    rw [pow_succ 2 k]
    exact (pow_mul M (2 ^ k) 2).symm
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hA : Real.sqrt (Real.log (M : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogM)
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hnorm : ∀ N : ℕ, normalizedDeficit rothNumberNat N =
      rothLogDeficit N / Real.sqrt (Real.log ((N : ℕ) : ℝ)) := fun N => rfl
  have hsk := sqrt_log_iterated_square M k hM1
  have hsk1 := sqrt_log_iterated_square M (k + 1) hM1
  have hsk_ne : Real.sqrt (Real.log (M : ℝ)) * (Real.sqrt 2) ^ k ≠ 0 :=
    mul_ne_zero hA (pow_ne_zero k hs2)
  have hS0 : Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) ≠ 0 := by
    rw [hsk]
    exact hsk_ne
  have hS : Real.sqrt (Real.log ((M ^ (2 ^ (k + 1)) : ℕ) : ℝ)) =
      Real.sqrt 2 * Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) := by
    rw [hsk, hsk1, pow_succ]
    ring
  rw [squareScaleDefect_eq_rothLogDeficit_sub _ hNk, hsq, hnorm, hnorm, hS]
  field_simp [hS0, hs2, mul_ne_zero hs2 hS0]

/-! ## The Erdős endpoint -/

set_option linter.unusedVariables false in
/-- **Normalized square-tower excursion theorem.**  For every base `M ≥ 3` and
every `c > 0`, if the normalized deficits of the iterated-square tower
`N k = M ^ (2 ^ k)` are at least `c` infinitely often, then the normalized
square-scale defects `Z k = squareScaleDefect (N k) / √(log (N k))` are at most
`-(2 - √2)·c` infinitely often:

`(∃ᶠ k, c ≤ normalizedDeficit r₃ (N k)) →`
`(∃ᶠ k, squareScaleDefect (N k) / √(log (N k)) ≤ -(2 - √2)·c)`.

This is a *conditional* statement: the conclusion is derived from the frequent
positive `D`-mass hypothesis.  It does **not** claim `D → 0`, it does **not**
produce positive excursions, it is **not** a two-sided oscillation result, and
it gives **no** asymptotic formula for `D` or `Z`.

The proof instantiates the generic shift-growth lemma at `s = √2` with the exact
recurrence `squareScaleDefect_div_sqrt_log_iterated_square_eq`, the eventual
upper bound `eventually_normalizedDeficit_rothNumberNat_le_add 1` composed with
the tower tending to infinity, and the identity `(√2)² = 2` to normalize the
constant `s² - s = 2 - √2`. -/
theorem frequently_normalizedSquareScaleDefect_le_of_frequently_normalizedDeficit_le
    (M : ℕ) (hM : 3 ≤ M) (c : ℝ) (hc : 0 < c)
    (hD : ∃ᶠ k : ℕ in atTop, c ≤ normalizedDeficit rothNumberNat (M ^ (2 ^ k))) :
    ∃ᶠ k : ℕ in atTop,
      squareScaleDefect (M ^ (2 ^ k)) /
          Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) ≤
        -(2 - Real.sqrt 2) * c := by
  have hsqrt2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have htower : Tendsto (fun k : ℕ => M ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < M)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  have hupper : ∀ᶠ k : ℕ in atTop,
      normalizedDeficit rothNumberNat (M ^ (2 ^ k)) ≤ torusLeadingConstant + 1 :=
    htower.eventually (eventually_normalizedDeficit_rothNumberNat_le_add 1 (by norm_num))
  have hx : ∀ k : ℕ,
      squareScaleDefect (M ^ (2 ^ k)) /
          Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) =
        Real.sqrt 2 * normalizedDeficit rothNumberNat (M ^ (2 ^ (k + 1))) -
          (Real.sqrt 2) ^ 2 * normalizedDeficit rothNumberNat (M ^ (2 ^ k)) := by
    intro k
    rw [squareScaleDefect_div_sqrt_log_iterated_square_eq M k (by omega),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmain := frequently_shift_sub_le_neg_of_frequently_le
    (fun k : ℕ => normalizedDeficit rothNumberNat (M ^ (2 ^ k)))
    (fun k : ℕ => squareScaleDefect (M ^ (2 ^ k)) /
      Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)))
    (Real.sqrt 2) (torusLeadingConstant + 1) c hsqrt2 hx hupper hD
  apply hmain.mono
  intro k hk
  rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hk



end

end Erdos142