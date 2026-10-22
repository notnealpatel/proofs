/-
# A145996 — Jasinski: the quintic `F_k` has a rational root only for `k ∈ {0, 1, 2, 4, 243}`

Artur Jasinski's conjecture in OEIS A145996 says that the nonnegative
parameters for which the quintic `F_k` has a rational root are exactly
`0,1,2,4,243`; at `k = 1` it degenerates to degree one.
The proof below gives the characterization for all integer parameters.

Write `F = a(x) k^2 + b(x) k + c(x)` with `a = (x-1)(4x^2+2x-1)^2`,
`b = -32x^5+20x^3+4`, `c = 16x^5`.  The discriminant in `k` is
`16 (x^2-x-1)^2 (5x^2-2x+1)`, so a rational point gives a rational point
`s^2 = 5x^2-2x+1` on a conic.  Projecting from `(0, 1)` with slope `u` gives
`k (u+3) (u^2-4u-1)^2 = 128`.  Writing `u = P/Q` in lowest terms, the factors
`P+3Q` and `P^2-4PQ-Q^2` are coprime to `Q`, so `(P+3Q)(P^2-4PQ-Q^2)^2 ∣ 128`,
which leaves a finite search.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A145996JasinskiQuinticRational

/-- Jasinski's quintic `F_k(x) = 4k - k^2 + 5k^2 x + (20k - 20k^2) x^3
+ (16 - 32k + 16k^2) x^5`, for an integer parameter `k`, evaluated at a
rational `x`. -/
def F (k : ℤ) (x : ℚ) : ℚ :=
  4 * k - k ^ 2 + 5 * k ^ 2 * x + (20 * k - 20 * k ^ 2) * x ^ 3 +
    (16 - 32 * k + 16 * k ^ 2) * x ^ 5

/-! ## explicit rational roots for the listed terms -/

example : F 0 0 = 0 := by norm_num [F]
example : F 1 (-3 / 5) = 0 := by norm_num [F]
example : F 2 1 = 0 := by norm_num [F]
example : F 4 0 = 0 := by norm_num [F]
example : F 243 (3 / 11) = 0 := by norm_num [F]
/-- `F_3` has no root at `x = 0` (sanity check that `F` is not identically zero). -/
example : F 3 0 = 3 := by norm_num [F]

/-! ## Auxiliary lemmas -/

/-- No rational number squares to `5`. -/
theorem sq_ne_five (y : ℚ) : y ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨y, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at hsq
  obtain ⟨r, hr⟩ : IsSquare (5 : ℤ) := by simpa using hsq.1
  have hr2 : r ≤ 3 := by nlinarith
  have hr3 : -3 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- Finite search: for `m ∣ 128` (written `m = ±n`) and `1 ≤ Q ≤ 47`, the
divisibility `m (m^2 - 10 m Q + 20 Q^2)^2 ∣ 128` holds only for
`(m, Q) ∈ {(2,1), (4,1), (8,1), (8,3)}`. Here `Q = j + 1`. -/
theorem finite_check : ∀ n ∈ ([1, 2, 4, 8, 16, 32, 64, 128] : List ℤ), ∀ j : ℕ, j < 47 →
    (n * (n ^ 2 - 10 * n * ((j : ℤ) + 1) + 20 * ((j : ℤ) + 1) ^ 2) ^ 2 ∣ 128 →
      (n = 2 ∧ j = 0) ∨ (n = 4 ∧ j = 0) ∨ (n = 8 ∧ j = 0) ∨ (n = 8 ∧ j = 2)) ∧
    (-n * ((-n) ^ 2 - 10 * (-n) * ((j : ℤ) + 1) + 20 * ((j : ℤ) + 1) ^ 2) ^ 2 ∣ 128 →
      False) := by
  decide

/-- Integrality step: if `k (u+3) (u^2-4u-1)^2 = 128` for an integer `k` and a
rational `u`, then `k ∈ {1, 2, 4, 243}`. -/
theorem mem_of_mul_eq_128 (k : ℤ) (u : ℚ)
    (h : (k : ℚ) * (u + 3) * (u ^ 2 - 4 * u - 1) ^ 2 = 128) :
    k ∈ ({1, 2, 4, 243} : Finset ℤ) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, u.den = j + 1 := ⟨u.den - 1, by have := u.den_pos; omega⟩
  set P : ℤ := u.num with hP
  set Q : ℤ := (u.den : ℤ) with hQ
  have hQj : Q = (j : ℤ) + 1 := by rw [hQ, hj]; push_cast; ring
  have hQpos : (0 : ℚ) < Q := by rw [hQ]; exact_mod_cast u.den_pos
  have hu : u = P / Q := (Rat.num_div_den u).symm
  have hcop : IsCoprime P Q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact u.reduced
  -- the integral equation
  have hZ : k * (P + 3 * Q) * (P ^ 2 - 4 * P * Q - Q ^ 2) ^ 2 = 128 * Q ^ 5 := by
    have hQ0 : (Q : ℚ) ≠ 0 := hQpos.ne'
    have hq : (k : ℚ) * (P + 3 * Q) * (P ^ 2 - 4 * P * Q - Q ^ 2) ^ 2 = 128 * Q ^ 5 := by
      rw [hu] at h
      field_simp at h
      linear_combination h
    exact_mod_cast hq
  set m : ℤ := P + 3 * Q with hm
  set d : ℤ := P ^ 2 - 4 * P * Q - Q ^ 2 with hd
  have hmc : IsCoprime m Q := by
    rw [hm, mul_comm 3 Q]; exact hcop.add_mul_left_left 3
  have hdc : IsCoprime d Q := by
    have h1 : d = P ^ 2 + Q * (-4 * P - Q) := by rw [hd]; ring
    rw [h1]; exact hcop.pow_left.add_mul_left_left _
  have hDc : IsCoprime (m * d ^ 2) (Q ^ 5) := (hmc.mul_left hdc.pow_left).pow_right
  have hdvd : m * d ^ 2 ∣ 128 := by
    apply hDc.dvd_of_dvd_mul_right
    exact ⟨k, by linear_combination -hZ⟩
  -- bounds
  have hmabs : m.natAbs ∣ 128 := by
    have := Int.natAbs_dvd_natAbs.mpr (dvd_trans (dvd_mul_right m _) hdvd)
    simpa using this
  have hmle : m ≤ 128 := by
    have := Nat.le_of_dvd (by norm_num) hmabs
    omega
  have hd2 : d ^ 2 ≤ 128 := Int.le_of_dvd (by norm_num) (dvd_trans (dvd_mul_left _ m) hdvd)
  have hdm : d = m ^ 2 - 10 * m * Q + 20 * Q ^ 2 := by rw [hd, hm]; ring
  have hQ1 : 1 ≤ Q := by rw [hQj]; omega
  have hQle : Q ≤ 47 := by
    by_contra hQ48
    rw [not_le] at hQ48
    have hdl : 1024 ≤ d := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmle) (by linarith : (0 : ℤ) ≤ 10 * Q - m - 128)]
    nlinarith
  have hjlt : j < 47 := by omega
  -- the divisor list
  have hmem : m.natAbs ∈ Nat.divisors 128 := Nat.mem_divisors.mpr ⟨hmabs, by norm_num⟩
  have hdivs : Nat.divisors 128 = {1, 2, 4, 8, 16, 32, 64, 128} := by decide
  rw [hdivs] at hmem
  rw [hdm, hQj] at hdvd
  have hZ' : k * m * (m ^ 2 - 10 * m * ((j : ℤ) + 1) + 20 * ((j : ℤ) + 1) ^ 2) ^ 2 =
      128 * ((j : ℤ) + 1) ^ 5 := by rw [← hQj, ← hdm]; exact hZ
  have hnl : (m.natAbs : ℤ) ∈ ([1, 2, 4, 8, 16, 32, 64, 128] : List ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨hpos, hneg⟩ := finite_check _ hnl j hjlt
  rcases Int.natAbs_eq m with hms | hms
  · rw [← hms] at hpos
    rcases hpos hdvd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      · subst h2
        rw [h1] at hZ'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
  · rw [← hms] at hneg
    exact (hneg hdvd).elim

/-- Elimination step (genus-0 parametrization). If `x (5 - u^2) = 2 (1 + u)`,
`s = 1 + u x` and `2 a(x) k + b(x) = 4 (x^2 - x - 1) s` with
`a(x) = (x-1)(4x^2+2x-1)^2 ≠ 0` and `b(x) = -32x^5 + 20x^3 + 4`, then
`k (u+3) (u^2-4u-1)^2 = 128`. -/
theorem key_identity (k x u s : ℚ) (h1 : x * (5 - u ^ 2) = 2 * (1 + u))
    (h2 : s = 1 + u * x)
    (h3 : 2 * ((x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2) * k + (-32 * x ^ 5 + 20 * x ^ 3 + 4) =
      4 * (x ^ 2 - x - 1) * s)
    (ha : (x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2 ≠ 0) :
    k * (u + 3) * (u ^ 2 - 4 * u - 1) ^ 2 = 128 := by
  subst h2
  have h : (x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2 *
      (k * (u + 3) * (u ^ 2 - 4 * u - 1) ^ 2 - 128) = 0 := by
    linear_combination ((u + 3) * (u ^ 2 - 4 * u - 1) ^ 2 / 2) * h3 +
      (-16*x^4*u^3 + 80*x^4*u^2 - 2*x^2*u^4 + 80*x^4*u + 32*x^3*u^2 + 20*x^2*u^3
        + 2*x*u^4 - 400*x^4 - 128*x^3*u - 40*x^2*u^2 - 8*x*u^3 + 2*u^4 - 160*x^3
        - 164*x^2*u - 36*x*u^2 - 12*u^3 + 442*x^2 + 120*x*u - 8*u^2 + 178*x + 108*u
        - 58) * h1
  have h' := (mul_eq_zero.mp h).resolve_left ha
  linear_combination h'

/-- Forward direction: if `F_k` has a rational root then
`k ∈ {0, 1, 2, 4, 243}`. -/
theorem mem_of_F_eq_zero (k : ℤ) (x : ℚ) (h : F k x = 0) :
    k ∈ ({0, 1, 2, 4, 243} : Finset ℤ) := by
  simp only [F] at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hx0 : x = 0
  · subst hx0
    have hk : (k : ℚ) * (4 - k) = 0 := by linear_combination h
    have hk' : k * (4 - k) = 0 := by exact_mod_cast hk
    rcases mul_eq_zero.mp hk' with hk0 | hk4
    · left; exact hk0
    · right; right; right; left; linarith
  by_cases hx1 : x = 1
  · subst hx1
    have hk : (k : ℚ) = 2 := by linear_combination -h / 8
    right; right; left; exact_mod_cast hk
  -- the leading coefficient `a(x)` and `x^2 - x - 1` do not vanish
  have hfac : 4 * x ^ 2 + 2 * x - 1 ≠ 0 := by
    intro h0
    exact sq_ne_five (4 * x + 1) (by linear_combination 4 * h0)
  have ha : (x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hx1) (pow_ne_zero 2 hfac)
  have hq : x ^ 2 - x - 1 ≠ 0 := by
    intro h0
    exact sq_ne_five (2 * x - 1) (by linear_combination 4 * h0)
  -- a rational point on the conic `s^2 = 5x^2 - 2x + 1`
  obtain ⟨s, hs3⟩ : ∃ s : ℚ,
      2 * ((x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2) * k + (-32 * x ^ 5 + 20 * x ^ 3 + 4) =
        4 * (x ^ 2 - x - 1) * s :=
    ⟨_, (mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hq)).symm⟩
  have hs2 : s ^ 2 = 5 * x ^ 2 - 2 * x + 1 := by
    have h0 : (4 * (x ^ 2 - x - 1)) ^ 2 * (s ^ 2 - (5 * x ^ 2 - 2 * x + 1)) = 0 := by
      linear_combination (-(4 * (x ^ 2 - x - 1) * s +
        2 * ((x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2) * k + (-32 * x ^ 5 + 20 * x ^ 3 + 4))) * hs3
        + 4 * ((x - 1) * (4 * x ^ 2 + 2 * x - 1) ^ 2) * h
    have h0' := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 (mul_ne_zero (by norm_num) hq))
    linear_combination h0'
  -- the slope `u` of the line through `(0, 1)` and `(x, s)`
  set u : ℚ := (s - 1) / x with hu
  have hux : u * x = s - 1 := div_mul_cancel₀ _ hx0
  have h1 : x * (5 - u ^ 2) = 2 * (1 + u) := by
    have h0 : x * (x * (5 - u ^ 2) - 2 * (1 + u)) = 0 := by
      linear_combination (-(u * x + s - 1) - 2) * hux - hs2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hx0)
  have hkey := key_identity k x u s h1 (by linear_combination -hux) hs3 ha
  have hmem := mem_of_mul_eq_128 k u hkey
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hk | hk | hk | hk
  · right; left; exact hk
  · right; right; left; exact hk
  · right; right; right; left; exact hk
  · right; right; right; right; exact hk

/-- Backward direction: each `k ∈ {0, 1, 2, 4, 243}` has an explicit rational
root of `F_k` (`x = 0, -3/5, 1, 0, 3/11` respectively). -/
theorem exists_F_eq_zero_of_mem (k : ℤ) (hk : k ∈ ({0, 1, 2, 4, 243} : Finset ℤ)) :
    ∃ x : ℚ, F k x = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num [F]⟩
  · exact ⟨-3 / 5, by norm_num [F]⟩
  · exact ⟨1, by norm_num [F]⟩
  · exact ⟨0, by norm_num [F]⟩
  · exact ⟨3 / 11, by norm_num [F]⟩

/-! ## The conjecture -/

/-- **Jasinski's conjecture (A145996), integer form.** For an integer `k`, the
quintic `4k - k^2 + 5k^2 x + (20k - 20k^2) x^3 + (16 - 32k + 16k^2) x^5` has a
rational root if and only if `k ∈ {0, 1, 2, 4, 243}`.

Source: OEIS A145996, comment "Conjecture: This sequence is finite and
complete." (Artur Jasinski, 2008). This integer statement is stronger than the
entry's (the entry is `nonn`, i.e. ranges over `k ≥ 0`). -/
theorem A145996_complete (k : ℤ) :
    (∃ x : ℚ, F k x = 0) ↔ k ∈ ({0, 1, 2, 4, 243} : Finset ℤ) :=
  ⟨fun ⟨x, hx⟩ => mem_of_F_eq_zero k x hx, exists_F_eq_zero_of_mem k⟩

/-- **Jasinski's conjecture (A145996), as stated in the entry.** The set of
nonnegative integers `k` for which the quintic `F_k` has a rational root is
exactly `{0, 1, 2, 4, 243}`, so the sequence `0, 1, 2, 4, 243` is finite and
complete. -/
theorem A145996_finite_complete :
    {k : ℕ | ∃ x : ℚ, F k x = 0} = ({0, 1, 2, 4, 243} : Set ℕ) := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [A145996_complete]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end Candidates.A145996JasinskiQuinticRational
