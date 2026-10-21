/-
# Lonely runner conjecture for three runners (two nonzero integer speeds)

## Source

* MathOverflow, lonely runner discussions:
  <https://mathoverflow.net/a/100381> and <https://mathoverflow.net/a/219880>.
* Classical result: J. M. Wills (1967); U. Betke and J. M. Wills (1972).
  The general conjecture (stated by Wills 1967 and Cusick 1973) is proved up to
  seven runners (Barajas–Serra, 2008); eight runners was claimed in 2025
  (arXiv:2509.14111).  The general case is open.
* `formal-conjectures` (`Wikipedia/LonelyRunnerConjecture.lean`) states the
  general conjecture only, with `sorry`.

## Informal claim (verbatim from the triage spec)

"For all nonzero integers a, b there is a real t with dist(t*a, Z) >= 1/3 and
dist(t*b, Z) >= 1/3. Distinctness is not even needed."

This is the `k = 2` case of the lonely runner conjecture ("for k nonzero speeds
there is a time t with ||t v_i|| >= 1/(k+1) for all i"), i.e. three runners
with speeds `0, a, b` after passing to the frame of the slowest runner.

Recorded 2026-10-21.  Status: proved in the literature (Wills 1967); the
argument below is the standard Bezout construction.

## Proof sketch

Reduce to `0 < a, 0 < b`.  Put `S = a + b`, `g = gcd(a, S)` (so also `g ∣ b`),
`s = S / g ≥ 2`, `r = ⌈s / 3⌉`, so `s ≤ 3r ≤ 2s`.  Bezout gives
`g = a u + S v`.  With `t = r u / S` we get `t a = r g / S - r v` and
`t b = r u + r v - r g / S`, while `q = r g / S = r / s ∈ [1/3, 2/3]`.
Hence both `t a` and `t b` are at distance `≥ 1/3` from every integer.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.LonelyRunnerThree

/-- A real `q ∈ [1/3, 2/3]` is at distance at least `1/3` from every integer. -/
theorem one_third_le_abs_sub_intCast {q : ℝ} (hq1 : 1 / 3 ≤ q) (hq2 : q ≤ 2 / 3) (k : ℤ) :
    1 / 3 ≤ |q - k| := by
  rcases le_or_gt k 0 with hk | hk
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Positive-speed case, in the strong form: for positive integers `a, b` there is
a time `t` such that `t * a` and `t * b` are at distance at least `1/3` from every
integer. -/
theorem exists_forall_one_third_le_of_pos (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ∃ t : ℝ, ∀ k : ℤ, 1 / 3 ≤ |t * a - k| ∧ 1 / 3 ≤ |t * b - k| := by
  set S : ℤ := a + b with hS
  set g : ℤ := (Int.gcd a S : ℤ) with hg
  have hga : g ∣ a := Int.gcd_dvd_left a S
  have hgS : g ∣ S := Int.gcd_dvd_right a S
  have hgb : g ∣ b := by
    have : g ∣ S - a := dvd_sub hgS hga
    simpa [hS] using this
  have hgpos : 0 < g := by
    have : 0 < Int.gcd a S := Int.gcd_pos_of_ne_zero_left S ha.ne'
    positivity
  have hga_le : g ≤ a := Int.le_of_dvd ha hga
  have hgb_le : g ≤ b := Int.le_of_dvd hb hgb
  obtain ⟨s, hs⟩ := hgS
  have hs2 : 2 ≤ s := by
    by_contra h
    push Not at h
    have : g * s ≤ g * 1 := mul_le_mul_of_nonneg_left (by omega) hgpos.le
    omega
  set r : ℤ := (s + 2) / 3 with hr
  have hr1 : s ≤ 3 * r := by omega
  have hr2 : 3 * r ≤ 2 * s := by omega
  -- Bezout: g = a u + S v
  set u : ℤ := Int.gcdA a S
  set v : ℤ := Int.gcdB a S
  have hbez : g = a * u + S * v := Int.gcd_eq_gcd_ab a S
  have hSpos : (0 : ℝ) < S := by
    have : (0 : ℤ) < S := by omega
    exact_mod_cast this
  set q : ℝ := (r : ℝ) * g / S with hq
  have hSR : (S : ℝ) = g * s := by exact_mod_cast hs
  have hq1 : 1 / 3 ≤ q := by
    rw [hq, le_div_iff₀ hSpos, hSR]
    have : (s : ℝ) ≤ 3 * r := by exact_mod_cast hr1
    have hg0 : (0 : ℝ) < g := by exact_mod_cast hgpos
    nlinarith
  have hq2 : q ≤ 2 / 3 := by
    rw [hq, div_le_iff₀ hSpos, hSR]
    have : (3 : ℝ) * r ≤ 2 * s := by exact_mod_cast hr2
    have hg0 : (0 : ℝ) < g := by exact_mod_cast hgpos
    nlinarith
  refine ⟨(r : ℝ) * u / S, fun k => ⟨?_, ?_⟩⟩
  · have hbezR : (g : ℝ) = a * u + S * v := by exact_mod_cast hbez
    have heq : (r : ℝ) * u / S * a - k = q - ((r * v + k : ℤ) : ℝ) := by
      rw [hq]
      push_cast
      field_simp
      rw [hbezR]
      ring
    rw [heq]
    exact one_third_le_abs_sub_intCast hq1 hq2 _
  · have hbezR : (g : ℝ) = a * u + S * v := by exact_mod_cast hbez
    have hSab : (S : ℝ) = a + b := by rw [hS]; push_cast; ring
    have heq : (r : ℝ) * u / S * b - k = -(q - ((r * u + r * v - k : ℤ) : ℝ)) := by
      rw [hq]
      push_cast
      field_simp
      rw [hbezR, hSab]
      ring
    rw [heq, abs_neg]
    exact one_third_le_abs_sub_intCast hq1 hq2 _

/-- Distance to the integers is invariant under negating the speed: if `t * |a|` is at
distance at least `1/3` from every integer then so is `t * a`. -/
theorem forall_one_third_le_of_abs {t : ℝ} {a : ℤ}
    (h : ∀ k : ℤ, 1 / 3 ≤ |t * ((|a| : ℤ) : ℝ) - k|) (k : ℤ) : 1 / 3 ≤ |t * a - k| := by
  rcases abs_choice a with ha | ha
  · simpa [ha] using h k
  · have hk := h (-k)
    have heq : t * ((|a| : ℤ) : ℝ) - ((-k : ℤ) : ℝ) = -(t * a - k) := by
      rw [ha]; push_cast; ring
    rwa [heq, abs_neg] at hk

/-- Strong form of the three-runner lonely runner theorem: for nonzero integers `a, b`
there is a time `t` such that `t * a` and `t * b` are at distance at least `1/3` from
every integer. -/
theorem exists_forall_one_third_le (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : ℝ, ∀ k : ℤ, 1 / 3 ≤ |t * a - k| ∧ 1 / 3 ≤ |t * b - k| := by
  obtain ⟨t, ht⟩ := exists_forall_one_third_le_of_pos |a| |b| (abs_pos.mpr ha) (abs_pos.mpr hb)
  exact ⟨t, fun k => ⟨forall_one_third_le_of_abs (fun k => (ht k).1) k,
    forall_one_third_le_of_abs (fun k => (ht k).2) k⟩⟩

/-- **Lonely runner conjecture for three runners** (Wills 1967; MathOverflow answers
100381 and 219880): for all nonzero integers `a, b` there is a real time `t` with
`dist(t a, ℤ) ≥ 1/3` and `dist(t b, ℤ) ≥ 1/3`, where `dist(x, ℤ) = |x - round x|`.
Distinctness of `a` and `b` is not needed. -/
theorem lonely_runner_two_speeds (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : ℝ, 1 / 3 ≤ |t * a - round (t * a)| ∧ 1 / 3 ≤ |t * b - round (t * b)| := by
  obtain ⟨t, ht⟩ := exists_forall_one_third_le a b ha hb
  exact ⟨t, (ht _).1, (ht _).2⟩

/-- **Lonely runner theorem, three runners with distinct integer speeds**: if
`v : Fin 3 → ℤ` is injective, then every runner `i` is lonely at some time, i.e.
there is `t` with `dist(t (v j - v i), ℤ) ≥ 1/3` for every other runner `j`. -/
theorem lonely_runner_three (v : Fin 3 → ℤ) (hv : Function.Injective v) (i : Fin 3) :
    ∃ t : ℝ, ∀ j : Fin 3, j ≠ i →
      1 / 3 ≤ |t * ((v j - v i : ℤ) : ℝ) - round (t * ((v j - v i : ℤ) : ℝ))| := by
  have hne : ∀ j : Fin 3, j ≠ i → v j - v i ≠ 0 := fun j hj h =>
    hj (hv (sub_eq_zero.mp h))
  have key : ∀ j₁ j₂ : Fin 3, j₁ ≠ i → j₂ ≠ i → (∀ j : Fin 3, j ≠ i → j = j₁ ∨ j = j₂) →
      ∃ t : ℝ, ∀ j : Fin 3, j ≠ i →
        1 / 3 ≤ |t * ((v j - v i : ℤ) : ℝ) - round (t * ((v j - v i : ℤ) : ℝ))| := by
    intro j₁ j₂ h₁ h₂ hcov
    obtain ⟨t, ht⟩ := exists_forall_one_third_le _ _ (hne j₁ h₁) (hne j₂ h₂)
    refine ⟨t, fun j hj => ?_⟩
    rcases hcov j hj with rfl | rfl
    · exact (ht _).1
    · exact (ht _).2
  fin_cases i
  · exact key 1 2 (by decide) (by decide) (by decide)
  · exact key 0 2 (by decide) (by decide) (by decide)
  · exact key 0 1 (by decide) (by decide) (by decide)

/-- Ground truth: the time `t = 1/3` works for the speeds `a = 1, b = 2`
(`t a = 1/3`, `t b = 2/3`). -/
example : 1 / 3 ≤ |(1 / 3 : ℝ) * (1 : ℤ) - round ((1 / 3 : ℝ) * (1 : ℤ))| ∧
    1 / 3 ≤ |(1 / 3 : ℝ) * (2 : ℤ) - round ((1 / 3 : ℝ) * (2 : ℤ))| := by
  have h1 : round ((1 / 3 : ℝ) * (1 : ℤ)) = 0 := by
    rw [round_eq_zero_iff]; norm_num
  have h2 : round ((1 / 3 : ℝ) * (2 : ℤ)) = 1 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [h1, h2]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Sanity check of `round`-distance: at `t = 1/2` the runner of speed `2` is back at
the origin (distance `0` from `ℤ`), so not every time is a lonely time. -/
example : round ((1 / 2 : ℝ) * (2 : ℤ)) = 1 ∧ |(1 / 2 : ℝ) * (2 : ℤ) - round ((1 / 2 : ℝ) * (2 : ℤ))| = 0 := by
  have h : round ((1 / 2 : ℝ) * (2 : ℤ)) = 1 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [h]; norm_num

/-- The hypotheses of `lonely_runner_three` are satisfiable: speeds `0, 1, 2` are
distinct. -/
example : Function.Injective (![0, 1, 2] : Fin 3 → ℤ) := by decide

end Candidates.LonelyRunnerThree
