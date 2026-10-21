/-
# Abedelfatah: `p_r, p_{r+1}, p_{3r+ε}` have only the trivial common zero iff `r ≢ 1 (mod 3)`

## Source

* arXiv 2609.07932, Abed Abedelfatah, "Two Infinite Families of Regular
  Sequences of Power Sums in Three Variables" (2026 preprint, unrefereed).
  Retrieved 2026-10-21 (`fetch 2609.07932`, LaTeX source).
  Theorem 1.1 (verbatim): "Let `r ≥ 1` and `ε ∈ {1,2}`. Then
  `p_r, p_{r+1}, p_{3r+ε}` form a regular sequence in `ℂ[x,y,z]` if and only
  if `r ≢ 1 (mod 3)`."  Corollary 1.2: "Let `r ≥ 1` and `j ∈ {0,1,2,3}`. Then
  `p_r, p_{r+1}, p_{3r+j}` form a regular sequence if and only if
  `6 ∣ r(r+1)(3r+j)`."  Here `p_m = x^m + y^m + z^m`.
* arXiv 0801.2662, A. Conca, C. Krattenthaler, J. Watanabe, "Regular sequences
  of symmetric polynomials", Rend. Sem. Mat. Univ. Padova 121 (2009) 179-199.
  Conjecture 2.10 (label `con3`, verbatim): "Let `A = {a,b,c}`, where `a,b,c`
  are positive integers with `a < b < c` and `GCD(A) = 1`. Then `p_A(3)` is a
  regular sequence in `R_3` if and only if `abc ≡ 0 (mod 6)`."  The 'only if'
  part is their Lemma 2.8; the 'if' part is open in general.  The two families
  above are the cases settled by Abedelfatah.

## Formalized form

By Lemma 2.1 of arXiv:2609.07932 (homogeneous forms of positive degree in
`ℂ[x,y,z]` form a regular sequence iff they have no common zero in `ℙ²`),
regularity is equivalent to: the only common zero in `ℂ³` is `(0,0,0)`.  This
module states and proves the **zero-set form** (`TrivialCommonZero`); the
commutative-algebra bridge (Lemma 2.1, Cohen-Macaulayness of `ℂ[x,y,z]`) is
not formalized here.

* `trivialCommonZero_iff` — Theorem 1.1, zero-set form, `ε ∈ {1,2}`.
* `trivialCommonZero_of_shift_zero_or_three` — the `j ∈ {0,3}` cases of
  Corollary 1.2 (Proposition 2.13 of CKW), zero-set form.
* `trivialCommonZero_iff_six_dvd` — Corollary 1.2, zero-set form.

## Status

Proved in the source paper (arXiv:2609.07932, an unrefereed preprint); here
the zero-set form is kernel-checked, with no `sorry`.  The proof follows the
paper: torus lemma (Lemma 2.2), the four reductions modulo `(p_r, p_{r+1})`
(Proposition 2.3), and the cases `e₁ = 0`, `e₂ = 0` (Proposition 3.1).  In the
`e₂ = 0` case the backward sign-alternation argument is replaced by an
equivalent closed-cone argument (`seqA_no_two_consecutive_zeros`).
Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.AbedelfatahPowerSumsTrivialZero

open ComplexConjugate

/-- The power sum `p_m(x,y,z) = x^m + y^m + z^m` in three complex variables. -/
def p (m : ℕ) (x y z : ℂ) : ℂ := x ^ m + y ^ m + z ^ m

/-- `TrivialCommonZero a b c`: the power sums `p_a, p_b, p_c` have only the
trivial common zero `(0,0,0)` in `ℂ³`.  By the projective criterion (Lemma 2.1
of arXiv:2609.07932) this is equivalent to `p_a, p_b, p_c` being a regular
sequence in `ℂ[x,y,z]` when `a, b, c ≥ 1`; that bridge is not formalized here. -/
def TrivialCommonZero (a b c : ℕ) : Prop :=
  ∀ x y z : ℂ, p a x y z = 0 → p b x y z = 0 → p c x y z = 0 → x = 0 ∧ y = 0 ∧ z = 0

example : p 2 1 1 1 = 3 := by norm_num [p]

example : p 3 1 2 (-3) = -18 := by norm_num [p]

example : p 0 0 0 0 = 3 := by norm_num [p]

/-! ## Torus lemma (Lemma 2.2) -/

/-- Two-variable core of the torus lemma: if `x^r + y^r = 0` and
`x^{r+1} + y^{r+1} = 0` with `r ≥ 1`, then `x = y = 0`. -/
theorem eq_zero_of_two (r : ℕ) (hr : 1 ≤ r) (x y : ℂ) (h0 : x ^ r + y ^ r = 0)
    (h1 : x ^ (r + 1) + y ^ (r + 1) = 0) : x = 0 ∧ y = 0 := by
  have hr0 : r ≠ 0 := by omega
  have hprod : (x - y) * y ^ r = 0 := by linear_combination x * h0 - h1
  have hy : y = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · have hxy : x = y := sub_eq_zero.mp h
      subst hxy
      have h2 : 2 * x ^ r = 0 := by linear_combination h0
      exact pow_eq_zero_iff hr0 |>.mp ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
    · exact pow_eq_zero_iff hr0 |>.mp h
  subst hy
  refine ⟨?_, rfl⟩
  rw [zero_pow hr0, add_zero] at h0
  exact pow_eq_zero_iff hr0 |>.mp h0

/-- **Torus lemma** (Lemma 2.2 of arXiv:2609.07932).  A common zero of `p_r` and
`p_{r+1}` (`r ≥ 1`) is either `(0,0,0)` or has `xyz ≠ 0`. -/
theorem torus (r : ℕ) (hr : 1 ≤ r) (x y z : ℂ) (h0 : p r x y z = 0)
    (h1 : p (r + 1) x y z = 0) : (x = 0 ∧ y = 0 ∧ z = 0) ∨ x * y * z ≠ 0 := by
  by_cases hxyz : x * y * z = 0
  · left
    have hr0 : r ≠ 0 := by omega
    unfold p at h0 h1
    rcases mul_eq_zero.mp hxyz with hxy | hz
    · rcases mul_eq_zero.mp hxy with hx | hy
      · subst hx
        obtain ⟨hy, hz⟩ := eq_zero_of_two r hr y z (by simpa [zero_pow hr0] using h0)
          (by simpa using h1)
        exact ⟨rfl, hy, hz⟩
      · subst hy
        obtain ⟨hx, hz⟩ := eq_zero_of_two r hr x z (by simpa [zero_pow hr0] using h0)
          (by simpa using h1)
        exact ⟨hx, rfl, hz⟩
    · subst hz
      obtain ⟨hx, hy⟩ := eq_zero_of_two r hr x y (by simpa [zero_pow hr0] using h0)
        (by simpa using h1)
      exact ⟨hx, hy, rfl⟩
  · exact Or.inr hxyz

/-! ## The four reductions (Proposition 2.3) -/

/-- Reduction (2.1): on `V(p_r, p_{r+1})`, `p_{3r} = 3 e₃^r`. -/
theorem p_three_mul (r : ℕ) (x y z : ℂ) (h0 : p r x y z = 0) :
    p (3 * r) x y z = 3 * (x * y * z) ^ r := by
  unfold p at *
  linear_combination ((x ^ r) ^ 2 + (y ^ r) ^ 2 + (z ^ r) ^ 2 - x ^ r * y ^ r - y ^ r * z ^ r
    - z ^ r * x ^ r) * h0

/-- Reduction (2.2): on `V(p_r, p_{r+1})`, `p_{3r+1} = e₁ e₃^r`. -/
theorem p_three_mul_add_one (r : ℕ) (x y z : ℂ) (h0 : p r x y z = 0)
    (h1 : p (r + 1) x y z = 0) :
    p (3 * r + 1) x y z = (x + y + z) * (x * y * z) ^ r := by
  unfold p at *
  linear_combination ((x ^ r) ^ 2 + x ^ r * y ^ r + (y ^ r) ^ 2) * h1
    + (-x * x ^ r * y ^ r - y * y ^ r * x ^ r + z * z ^ r * (z ^ r - x ^ r - y ^ r)) * h0

/-- Reduction (2.3): on `V(p_r, p_{r+1})`, `p_{3r+2} = e₂ e₃^r`. -/
theorem p_three_mul_add_two (r : ℕ) (x y z : ℂ) (h0 : p r x y z = 0)
    (h1 : p (r + 1) x y z = 0) :
    p (3 * r + 2) x y z = (x * y + y * z + z * x) * (x * y * z) ^ r := by
  unfold p at *
  linear_combination (x * (x ^ r) ^ 2 + y * (y ^ r) ^ 2 + z * (z ^ r) ^ 2) * h1
    - (x * y * x ^ r * y ^ r + x * z * x ^ r * z ^ r + y * z * y ^ r * z ^ r) * h0

/-- Reduction (2.4): on `V(p_r, p_{r+1})`, `p_{3r+3} = 3 e₃^{r+1}`. -/
theorem p_three_mul_add_three (r : ℕ) (x y z : ℂ) (h0 : p r x y z = 0)
    (h1 : p (r + 1) x y z = 0) :
    p (3 * r + 3) x y z = 3 * (x * y * z) ^ (r + 1) := by
  have e1 := p_three_mul_add_one r x y z h0 h1
  have e2 := p_three_mul_add_two r x y z h0 h1
  have e0 := p_three_mul r x y z h0
  unfold p at *
  linear_combination (x + y + z) * e2 - (x * y + y * z + z * x) * e1 + x * y * z * e0

/-! ## The case `e₁ = 0` (Proposition 3.1, first case) -/

/-- Norm comparison in the case `e₁ = 0`: if `a + b + c = 0` and `(a,b,c)` is a
common zero of `p_r, p_{r+1}`, then `|b| < |a|` is impossible.  (From
`a^r (a - c) = b^r (c - b)` and `|a-c|² - |c-b|² = 3(|a|² - |b|²)`.) -/
theorem not_normSq_lt (r : ℕ) (hr : 1 ≤ r) (a b c : ℂ) (habc : a + b + c = 0)
    (h0 : a ^ r + b ^ r + c ^ r = 0) (h1 : a ^ (r + 1) + b ^ (r + 1) + c ^ (r + 1) = 0) :
    ¬ Complex.normSq b < Complex.normSq a := by
  intro hlt
  have hc : c = -a - b := by linear_combination habc
  have hkey : a ^ r * (2 * a + b) = b ^ r * (-a - 2 * b) := by
    rw [hc] at h0 h1
    linear_combination h1 - (-a - b) * h0
  have hn := congrArg Complex.normSq hkey
  simp only [map_mul, map_pow] at hn
  have hid : Complex.normSq (2 * a + b) - Complex.normSq (-a - 2 * b)
      = 3 * (Complex.normSq a - Complex.normSq b) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hb0 : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hpow : Complex.normSq b ^ r < Complex.normSq a ^ r :=
    pow_lt_pow_left₀ hlt hb0 (by omega)
  have hq0 : 0 ≤ Complex.normSq (-a - 2 * b) := Complex.normSq_nonneg _
  have hqlt : Complex.normSq (-a - 2 * b) < Complex.normSq (2 * a + b) := by linarith
  have hbr : 0 ≤ Complex.normSq b ^ r := pow_nonneg hb0 r
  nlinarith

/-- **Case `e₁ = 0`** (Proposition 3.1 of arXiv:2609.07932, first case).  A
common zero of `p_r, p_{r+1}, e₁` with `xyz ≠ 0` forces `|x| = |y| = |z|`, hence
`e₂ = 0`, hence `x³ = y³ = z³ = xyz`, and then `r ≡ 1 (mod 3)`. -/
theorem e1_case (r : ℕ) (hr : 1 ≤ r) (x y z : ℂ) (hxyz : x * y * z ≠ 0)
    (he1 : x + y + z = 0) (h0 : p r x y z = 0) (h1 : p (r + 1) x y z = 0) : r % 3 = 1 := by
  unfold p at h0 h1
  have hxy := not_normSq_lt r hr x y z he1 h0 h1
  have hyx := not_normSq_lt r hr y x z (by linear_combination he1) (by linear_combination h0)
    (by linear_combination h1)
  have hzy := not_normSq_lt r hr y z x (by linear_combination he1) (by linear_combination h0)
    (by linear_combination h1)
  have hyz := not_normSq_lt r hr z y x (by linear_combination he1) (by linear_combination h0)
    (by linear_combination h1)
  have hNxy : Complex.normSq x = Complex.normSq y :=
    le_antisymm (not_lt.mp hxy) (not_lt.mp hyx)
  have hNyz : Complex.normSq z = Complex.normSq y :=
    le_antisymm (not_lt.mp hyz) (not_lt.mp hzy)
  have hx0 : x ≠ 0 := by intro h; apply hxyz; rw [h]; ring
  have hN : (Complex.normSq x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr hx0).ne'
  have hcx := Complex.mul_conj x
  have hcy := Complex.mul_conj y
  have hcz := Complex.mul_conj z
  rw [← hNxy] at hcy
  rw [hNyz, ← hNxy] at hcz
  have hconj : conj x + conj y + conj z = 0 := by
    rw [← map_add, ← map_add, he1, map_zero]
  have he2' : (Complex.normSq x : ℂ) * (x * y + y * z + z * x) = 0 := by
    linear_combination (x * y * z) * hconj - y * z * hcx - x * z * hcy - x * y * hcz
  have he2 : x * y + y * z + z * x = 0 := (mul_eq_zero.mp he2').resolve_left hN
  set c := x * y * z with hcdef
  have hx3 : x ^ 3 = c := by linear_combination x ^ 2 * he1 - x * he2
  have hy3 : y ^ 3 = c := by linear_combination y ^ 2 * he1 - y * he2
  have hz3 : z ^ 3 = c := by linear_combination z ^ 2 * he1 - z * he2
  have hpow3 : ∀ (a : ℂ), a ^ 3 = c → ∀ q s : ℕ, a ^ (3 * q + s) = c ^ q * a ^ s := by
    intro a ha q s
    rw [pow_add, pow_mul, ha]
  have hrdecomp : r = 3 * (r / 3) + r % 3 := (Nat.div_add_mod r 3).symm
  have hlt : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  have hc0 : c ≠ 0 := hxyz
  interval_cases h : r % 3
  · exfalso
    rw [hrdecomp, hpow3 x hx3, hpow3 y hy3, hpow3 z hz3] at h0
    have h3 : 3 * c ^ (r / 3) = 0 := by linear_combination h0
    exact pow_ne_zero _ hc0 ((mul_eq_zero.mp h3).resolve_left three_ne_zero)
  · rfl
  · exfalso
    have hr1 : r + 1 = 3 * (r / 3 + 1) + 0 := by omega
    rw [hr1, hpow3 x hx3, hpow3 y hy3, hpow3 z hz3] at h1
    have h3 : 3 * c ^ (r / 3 + 1) = 0 := by linear_combination h1
    exact pow_ne_zero _ hc0 ((mul_eq_zero.mp h3).resolve_left three_ne_zero)

/-! ## The case `e₂ = 0` (Proposition 3.1, second case) -/

/-- Closed-cone invariant for the backward recurrence `T g(n) = g(n+2) + g(n+3)`
with `T > 0`: if `g` is nonnegative at `m, m+1, m+2`, it is nonnegative at every
`n, n+1, n+2` with `n ≤ m`. -/
theorem cone (T : ℝ) (hT : 0 < T) (g : ℕ → ℝ)
    (hg : ∀ n, T * g n = g (n + 2) + g (n + 3)) (m : ℕ)
    (h0 : 0 ≤ g m) (h1 : 0 ≤ g (m + 1)) (h2 : 0 ≤ g (m + 2)) :
    ∀ n, n ≤ m → 0 ≤ g n ∧ 0 ≤ g (n + 1) ∧ 0 ≤ g (n + 2) := by
  suffices key : ∀ d n, n + d = m → 0 ≤ g n ∧ 0 ≤ g (n + 1) ∧ 0 ≤ g (n + 2) by
    intro n hn
    exact key (m - n) n (by omega)
  intro d
  induction d with
  | zero => intro n hn; subst hn; exact ⟨h0, h1, h2⟩
  | succ d ih =>
    intro n hn
    obtain ⟨i1, i2, i3⟩ := ih (n + 1) (by omega)
    refine ⟨?_, i1, i2⟩
    have hsum : 0 ≤ T * g n := by rw [hg n]; linarith
    exact (mul_nonneg_iff_of_pos_left hT).mp hsum

/-- Sign argument of Proposition 3.1 (second case): a real sequence with
`b 1 = b 2 = 1` and `b (n+3) = b (n+2) - T b n`, `T > 0`, never vanishes at two
consecutive indices `r, r+1` with `r ≥ 1`.  (The paper's alternating signs of
`W_j = a_{r-j}/A` are the closed cone of `cone` applied to `(-1)^n b n`.) -/
theorem seqA_no_two_consecutive_zeros (T : ℝ) (hT : 0 < T) (b : ℕ → ℝ) (hb1 : b 1 = 1)
    (hb2 : b 2 = 1) (hb : ∀ n, b (n + 3) = b (n + 2) - T * b n) (r : ℕ) (hr : 1 ≤ r)
    (hr0 : b r = 0) (hr1 : b (r + 1) = 0) : False := by
  rcases Nat.lt_or_ge r 2 with hlt | hge
  · obtain rfl : r = 1 := by omega
    rw [hb1] at hr0; exact one_ne_zero hr0
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hm : b m = 0 := by
    have hrec := hb m
    rw [show m + 3 = m + 2 + 1 by ring, hr1, hr0] at hrec
    have hTm : T * b m = 0 := by linarith
    rcases mul_eq_zero.mp hTm with h | h
    · linarith
    · exact h
  set g : ℕ → ℝ := fun n => (-1) ^ n * b n with hgdef
  have hg : ∀ n, T * g n = g (n + 2) + g (n + 3) := by
    intro n
    simp only [hgdef, hb n, pow_succ]
    ring
  have hg' : ∀ n, T * (-g n) = (-g (n + 2)) + (-g (n + 3)) := by
    intro n; rw [mul_neg, hg n]; ring
  have hgm : g m = 0 := by simp [hgdef, hm]
  have hgm2 : g (m + 2) = 0 := by simp [hgdef, hr0]
  have hg1 : g 1 = -1 := by simp [hgdef, hb1]
  have hg2 : g 2 = 1 := by simp [hgdef, hb2]
  rcases le_total 0 (g (m + 1)) with hc | hc
  · have h01 := (cone T hT g hg m (by rw [hgm]) hc (by rw [hgm2]) 0 (Nat.zero_le _)).2.1
    rw [zero_add, hg1] at h01
    linarith
  · have h02 := (cone T hT (fun n => -g n) hg' m (by simp [hgm]) (by simpa using hc)
      (by simp [hgm2]) 0 (Nat.zero_le _)).2.2
    rw [zero_add, hg2] at h02
    linarith

/-- The real sequence `a_n = p_n / e₁ⁿ` of the paper (case `e₂ = 0`):
`a₀ = 3`, `a₁ = a₂ = 1`, `a_{n+3} = a_{n+2} - T a_n`. -/
def seqA (T : ℝ) : ℕ → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | n + 3 => seqA T (n + 2) - T * seqA T n

example : seqA 1 3 = -2 := by norm_num [seqA]

example : seqA 2 4 = -7 := by norm_num [seqA]

/-- The paper's values `a₃ = 1 - 3T`, `a₄ = 1 - 4T`. -/
example (T : ℝ) : seqA T 3 = 1 - 3 * T ∧ seqA T 4 = 1 - 4 * T := by
  constructor <;> simp only [seqA] <;> ring

/-- **Case `e₂ = 0`, normalized** (proof of Proposition 3.1, second case, of
arXiv:2609.07932, with `x = 1`, `y = t`, `|z| ≤ |t| ≤ 1`).  If `t + z + t z = 0`
(that is, `e₂(1,t,z) = 0`), `e₁(1,t,z) = 1 + t + z ≠ 0`, and the power sums
`p_r`, `p_{r+1}` of `(1,t,z)` vanish, we reach a contradiction: first `|t| = 1`,
then `T = -e₃/e₁³ = s/(s-1)³ > 0` with `s = |1+t|²`, and `p_n / e₁ⁿ` is the real
sequence `seqA T`, which cannot vanish at two consecutive indices. -/
theorem e2_normalized (t z : ℂ) (r : ℕ) (hr : 1 ≤ r) (ht0 : t ≠ 0)
    (hzt : Complex.normSq z ≤ Complex.normSq t) (ht1 : Complex.normSq t ≤ 1)
    (he2 : t + z + t * z = 0) (he1 : 1 + t + z ≠ 0)
    (hp : 1 + t ^ r + z ^ r = 0) (hp1 : 1 + t ^ (r + 1) + z ^ (r + 1) = 0) : False := by
  have h1t : 1 + t ≠ 0 := by
    intro h; apply ht0; linear_combination he2 - z * h
  have hz1 : z * (1 + t) = -t := by linear_combination he2
  have hNt : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht0
  set s : ℝ := Complex.normSq (1 + t) with hsdef
  have hs1 : 1 ≤ s := by
    have hm : Complex.normSq z * s = Complex.normSq t := by
      rw [hsdef, ← map_mul, hz1, Complex.normSq_neg]
    have hs0 : 0 ≤ s := Complex.normSq_nonneg _
    nlinarith
  have hkey : t ^ r * (t * (t + 2)) = -(2 * t + 1) := by
    linear_combination (1 + t) * (hp1 - z * hp) + (1 + t ^ r) * he2
  -- norm comparison forces |t| = 1
  have hnormkey : Complex.normSq t ^ r * (Complex.normSq t * Complex.normSq (t + 2))
      = Complex.normSq (2 * t + 1) := by
    have h := congrArg Complex.normSq hkey
    simpa only [map_mul, map_pow, Complex.normSq_neg] using h
  have hid1 : Complex.normSq (2 * t + 1) - Complex.normSq t * Complex.normSq (t + 2)
      = (1 - Complex.normSq t) * (1 + Complex.normSq t + 4 * t.re) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
    ring
  have hid2 : s = 1 + 2 * t.re + Complex.normSq t := by
    simp only [hsdef, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have hQ : 0 < Complex.normSq (t + 2) := by
    apply Complex.normSq_pos.mpr
    intro h
    have ht2 : t = -2 := by linear_combination h
    rw [ht2] at ht1
    norm_num [Complex.normSq_apply] at ht1
  have hN1 : Complex.normSq t = 1 := by
    by_contra hne
    have hlt : Complex.normSq t < 1 := lt_of_le_of_ne ht1 hne
    have hge : Complex.normSq t * Complex.normSq (t + 2) ≤ Complex.normSq (2 * t + 1) := by
      nlinarith
    have hpow : Complex.normSq t ^ r < 1 := pow_lt_one₀ hNt.le hlt (by omega)
    have hprod : 0 < Complex.normSq t * Complex.normSq (t + 2) := mul_pos hNt hQ
    nlinarith
  -- with |t| = 1: (1+t)^2 = s t
  have htc : t * conj t = 1 := by
    rw [Complex.mul_conj, hN1, Complex.ofReal_one]
  have hsc : (1 + t) * (1 + conj t) = (s : ℂ) := by
    rw [hsdef, ← Complex.mul_conj, map_add, map_one]
  have hst : (s : ℂ) * t = (1 + t) ^ 2 := by
    linear_combination -t * hsc + (1 + t) * htc
  set E : ℂ := 1 + t + z with hEdef
  have hE1t : E * (1 + t) = t * ((s : ℂ) - 1) := by
    linear_combination hz1 - hst
  have hs_ne : s ≠ 1 := by
    intro h
    apply he1
    have h' : E * (1 + t) = 0 := by rw [hE1t, h]; push_cast; ring
    exact (mul_eq_zero.mp h').resolve_right h1t
  have hs_gt : 1 < s := lt_of_le_of_ne hs1 (Ne.symm hs_ne)
  set T : ℝ := s / (s - 1) ^ 3 with hTdef
  have hT : 0 < T := div_pos (by linarith) (pow_pos (by linarith) 3)
  have hTc : (T : ℂ) * ((s : ℂ) - 1) ^ 3 = s := by
    have hs1' : ((s : ℂ) - 1) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    rw [hTdef, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp
  have htz : t * z = -(T : ℂ) * E ^ 3 := by
    have hc : (1 + t) ^ 3 ≠ 0 := pow_ne_zero 3 h1t
    apply mul_right_cancel₀ hc
    have hL : t * z * (1 + t) ^ 3 = -(s : ℂ) * t ^ 3 := by
      linear_combination t * (1 + t) ^ 2 * hz1 + t ^ 2 * hst
    have hR : -(T : ℂ) * E ^ 3 * (1 + t) ^ 3 = -(s : ℂ) * t ^ 3 := by
      linear_combination -(T : ℂ) * ((E * (1 + t)) ^ 2 + E * (1 + t) * (t * ((s : ℂ) - 1))
        + (t * ((s : ℂ) - 1)) ^ 2) * hE1t - t ^ 3 * hTc
    rw [hL, hR]
  -- Newton recurrence and the real sequence
  have hnewton : ∀ n : ℕ, 1 + t ^ (n + 3) + z ^ (n + 3)
      = E * (1 + t ^ (n + 2) + z ^ (n + 2)) + t * z * (1 + t ^ n + z ^ n) := by
    intro n
    linear_combination (-(1 + t ^ (n + 1) + z ^ (n + 1))) * he2
  have hbridge : ∀ n : ℕ, (seqA T n : ℂ) * E ^ n = 1 + t ^ n + z ^ n ∧
      (seqA T (n + 1) : ℂ) * E ^ (n + 1) = 1 + t ^ (n + 1) + z ^ (n + 1) ∧
      (seqA T (n + 2) : ℂ) * E ^ (n + 2) = 1 + t ^ (n + 2) + z ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [seqA, pow_zero]; push_cast; ring
      · simp only [seqA, zero_add, pow_one, Complex.ofReal_one, one_mul, hEdef]
      · simp only [seqA, zero_add, Complex.ofReal_one, one_mul, hEdef]
        linear_combination 2 * he2
    | succ n ih =>
      obtain ⟨i0, i1, i2⟩ := ih
      refine ⟨i1, i2, ?_⟩
      rw [show n + 1 + 2 = n + 3 by ring, hnewton n, seqA, Complex.ofReal_sub,
        Complex.ofReal_mul, htz, ← i2, ← i0]
      ring
  have hb0 : seqA T r = 0 := by
    have h := (hbridge r).1
    rw [hp] at h
    exact_mod_cast (mul_eq_zero.mp h).resolve_right (pow_ne_zero r he1)
  have hb1 : seqA T (r + 1) = 0 := by
    have h := (hbridge r).2.1
    rw [hp1] at h
    exact_mod_cast (mul_eq_zero.mp h).resolve_right (pow_ne_zero (r + 1) he1)
  exact seqA_no_two_consecutive_zeros T hT (seqA T) rfl rfl (fun n => rfl) r hr hb0 hb1

/-- **Case `e₂ = 0`, ordered** (`|z| ≤ |y| ≤ |x|`): reduces to `e2_normalized`
by scaling `x` to `1`. -/
theorem e2_case_ordered (r : ℕ) (hr : 1 ≤ r) (x y z : ℂ) (hxyz : x * y * z ≠ 0)
    (hzy : Complex.normSq z ≤ Complex.normSq y) (hyx : Complex.normSq y ≤ Complex.normSq x)
    (he2 : x * y + y * z + z * x = 0) (he1 : x + y + z ≠ 0)
    (h0 : p r x y z = 0) (h1 : p (r + 1) x y z = 0) : False := by
  have hx : x ≠ 0 := by intro h; apply hxyz; rw [h]; ring
  have hy : y ≠ 0 := by intro h; apply hxyz; rw [h]; ring
  have hNx : 0 ≤ Complex.normSq x := Complex.normSq_nonneg x
  unfold p at h0 h1
  apply e2_normalized (y / x) (z / x) r hr (div_ne_zero hy hx)
  · rw [map_div₀, map_div₀]; exact div_le_div_of_nonneg_right hzy hNx
  · rw [map_div₀]; exact div_le_one_of_le₀ hyx hNx
  · field_simp; linear_combination he2
  · intro h; apply he1; field_simp at h; linear_combination h
  · rw [div_pow, div_pow]; field_simp; linear_combination h0
  · rw [div_pow, div_pow]; field_simp; linear_combination h1

/-- **Case `e₂ = 0`** (Proposition 3.1 of arXiv:2609.07932, second case).  For
`r ≥ 1` there is no common zero of `p_r, p_{r+1}, e₂` with `xyz ≠ 0` and
`e₁ ≠ 0`. -/
theorem e2_case (r : ℕ) (hr : 1 ≤ r) (x y z : ℂ) (hxyz : x * y * z ≠ 0)
    (he2 : x * y + y * z + z * x = 0) (he1 : x + y + z ≠ 0)
    (h0 : p r x y z = 0) (h1 : p (r + 1) x y z = 0) : False := by
  unfold p at h0 h1
  have key := e2_case_ordered r hr
  simp only [p] at key
  rcases le_total (Complex.normSq y) (Complex.normSq x) with hyx | hxy <;>
  rcases le_total (Complex.normSq z) (Complex.normSq y) with hzy | hyz <;>
  rcases le_total (Complex.normSq z) (Complex.normSq x) with hzx | hxz
  all_goals first
    | exact key x y z hxyz hzy hyx he2 he1 h0 h1
    | exact key x z y (fun h => hxyz (by linear_combination h)) hyz hzx
        (by linear_combination he2) (fun h => he1 (by linear_combination h))
        (by linear_combination h0) (by linear_combination h1)
    | exact key z x y (fun h => hxyz (by linear_combination h)) hyx hxz
        (by linear_combination he2) (fun h => he1 (by linear_combination h))
        (by linear_combination h0) (by linear_combination h1)
    | exact key y x z (fun h => hxyz (by linear_combination h)) hzx hxy
        (by linear_combination he2) (fun h => he1 (by linear_combination h))
        (by linear_combination h0) (by linear_combination h1)
    | exact key y z x (fun h => hxyz (by linear_combination h)) hxz hzy
        (by linear_combination he2) (fun h => he1 (by linear_combination h))
        (by linear_combination h0) (by linear_combination h1)
    | exact key z y x (fun h => hxyz (by linear_combination h)) hxy hyz
        (by linear_combination he2) (fun h => he1 (by linear_combination h))
        (by linear_combination h0) (by linear_combination h1)

/-! ## The witness `[1 : ω : ω²]` -/

/-- A primitive cube root of unity `ω` satisfies `ω³ = 1` and `1 + ω + ω² = 0`. -/
theorem exists_cube_root : ∃ ω : ℂ, ω ^ 3 = 1 ∧ 1 + ω + ω ^ 2 = 0 := by
  have hω := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  refine ⟨_, hω.pow_eq_one, ?_⟩
  have h := hω.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- If `ω³ = 1` and `1 + ω + ω² = 0`, then `p_m(1, ω, ω²) = 0` whenever `3 ∤ m`. -/
theorem p_one_omega (ω : ℂ) (h3 : ω ^ 3 = 1) (h1 : 1 + ω + ω ^ 2 = 0) (m : ℕ)
    (hm : m % 3 ≠ 0) : p m 1 ω (ω ^ 2) = 0 := by
  unfold p
  have hdec : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod m 3).symm
  have hlt : m % 3 < 3 := Nat.mod_lt m (by norm_num)
  have hω : ω ^ m = ω ^ (m % 3) := by
    conv_lhs => rw [hdec, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [one_pow, ← pow_mul, mul_comm 2 m, pow_mul, hω]
  interval_cases h : m % 3
  · exact absurd rfl hm
  · linear_combination h1
  · linear_combination h1 + ω * h3

/-! ## Main results -/

/-- **Abedelfatah, Theorem 1.1 of arXiv:2609.07932, zero-set form.**  Let
`r ≥ 1` and `ε ∈ {1,2}`.  The power sums `p_r, p_{r+1}, p_{3r+ε}` in
`ℂ[x,y,z]` have only the trivial common zero `(0,0,0)` in `ℂ³` if and only if
`r ≢ 1 (mod 3)`.  (By Lemma 2.1 there, this is equivalent to their forming a
regular sequence; this proves the families `{r, r+1, 3r+1}` and
`{r, r+1, 3r+2}` of Conjecture 2.10 of Conca-Krattenthaler-Watanabe,
arXiv:0801.2662, in zero-set form.) -/
theorem trivialCommonZero_iff (r : ℕ) (hr : 1 ≤ r) (ε : ℕ) (hε : ε = 1 ∨ ε = 2) :
    TrivialCommonZero r (r + 1) (3 * r + ε) ↔ r % 3 ≠ 1 := by
  constructor
  · intro htriv hr1
    obtain ⟨ω, h3, h1⟩ := exists_cube_root
    have hz : ∀ m, m % 3 ≠ 0 → p m 1 ω (ω ^ 2) = 0 := p_one_omega ω h3 h1
    have hnz := htriv 1 ω (ω ^ 2) (hz r (by omega)) (hz (r + 1) (by omega))
      (hz (3 * r + ε) (by omega))
    exact one_ne_zero hnz.1
  · intro hr1 x y z h0 h1 h2
    rcases torus r hr x y z h0 h1 with hzero | hxyz
    · exact hzero
    · exfalso
      have he3 : (x * y * z) ^ r ≠ 0 := pow_ne_zero r hxyz
      rcases hε with rfl | rfl
      · rw [p_three_mul_add_one r x y z h0 h1] at h2
        have he1 : x + y + z = 0 := (mul_eq_zero.mp h2).resolve_right he3
        exact hr1 (e1_case r hr x y z hxyz he1 h0 h1)
      · rw [p_three_mul_add_two r x y z h0 h1] at h2
        have he2 : x * y + y * z + z * x = 0 := (mul_eq_zero.mp h2).resolve_right he3
        by_cases he1 : x + y + z = 0
        · exact hr1 (e1_case r hr x y z hxyz he1 h0 h1)
        · exact e2_case r hr x y z hxyz he2 he1 h0 h1

/-- **Shifts `j ∈ {0,3}`** (Corollary 1.2 of arXiv:2609.07932, the cases
covered by Proposition 2.13 of Conca-Krattenthaler-Watanabe), zero-set form: for
every `r ≥ 1`, `p_r, p_{r+1}, p_{3r+j}` have only the trivial common zero in
`ℂ³`. -/
theorem trivialCommonZero_of_shift_zero_or_three (r : ℕ) (hr : 1 ≤ r) (j : ℕ)
    (hj : j = 0 ∨ j = 3) : TrivialCommonZero r (r + 1) (3 * r + j) := by
  intro x y z h0 h1 h2
  rcases torus r hr x y z h0 h1 with hzero | hxyz
  · exact hzero
  · exfalso
    rcases hj with rfl | rfl
    · rw [add_zero, p_three_mul r x y z h0] at h2
      exact pow_ne_zero r hxyz ((mul_eq_zero.mp h2).resolve_left three_ne_zero)
    · rw [p_three_mul_add_three r x y z h0 h1] at h2
      exact pow_ne_zero (r + 1) hxyz ((mul_eq_zero.mp h2).resolve_left three_ne_zero)

/-- Arithmetic of Corollary 1.2: for `j ≤ 3`, `6 ∣ r(r+1)(3r+j)` iff
`j ∈ {0,3}` or `r ≢ 1 (mod 3)`. -/
theorem six_dvd_iff (r j : ℕ) (hj : j ≤ 3) :
    6 ∣ r * (r + 1) * (3 * r + j) ↔ (j = 0 ∨ j = 3 ∨ r % 3 ≠ 1) := by
  have key : ∀ a : Fin 6, ∀ i : Fin 4,
      ((a : ℕ) * ((a : ℕ) + 1) * (3 * (a : ℕ) + (i : ℕ)) % 6 = 0 ↔
        ((i : ℕ) = 0 ∨ (i : ℕ) = 3 ∨ (a : ℕ) % 3 ≠ 1)) := by decide
  have h := key ⟨r % 6, Nat.mod_lt r (by norm_num)⟩ ⟨j, by omega⟩
  simp only at h
  have hmod : r * (r + 1) * (3 * r + j) % 6 = r % 6 * (r % 6 + 1) * (3 * (r % 6) + j) % 6 := by
    simp [Nat.mul_mod, Nat.add_mod]
  have hr3 : r % 6 % 3 = r % 3 := Nat.mod_mod_of_dvd r (by norm_num)
  rw [Nat.dvd_iff_mod_eq_zero, hmod, h, hr3]

/-- **Abedelfatah, Corollary 1.2 of arXiv:2609.07932, zero-set form.**  Let
`r ≥ 1` and `j ∈ {0,1,2,3}`.  The power sums `p_r, p_{r+1}, p_{3r+j}` have only
the trivial common zero in `ℂ³` if and only if `6 ∣ r(r+1)(3r+j)`. -/
theorem trivialCommonZero_iff_six_dvd (r : ℕ) (hr : 1 ≤ r) (j : ℕ) (hj : j ≤ 3) :
    TrivialCommonZero r (r + 1) (3 * r + j) ↔ 6 ∣ r * (r + 1) * (3 * r + j) := by
  rw [six_dvd_iff r j hj]
  rcases (by omega : j = 0 ∨ j = 3 ∨ j = 1 ∨ j = 2) with h | h | h
  · exact ⟨fun _ => Or.inl h, fun _ => trivialCommonZero_of_shift_zero_or_three r hr j (Or.inl h)⟩
  · exact ⟨fun _ => Or.inr (Or.inl h),
      fun _ => trivialCommonZero_of_shift_zero_or_three r hr j (Or.inr h)⟩
  · rw [trivialCommonZero_iff r hr j h]
    constructor
    · intro hr1; exact Or.inr (Or.inr hr1)
    · rintro (h0 | h3 | hr1)
      · omega
      · omega
      · exact hr1

/-! ## Non-vacuity checks -/

/-- `r = 2`, `ε = 1`: `p₂, p₃, p₇` have only the trivial common zero. -/
example : TrivialCommonZero 2 3 7 := (trivialCommonZero_iff 2 (by norm_num) 1 (Or.inl rfl)).mpr
  (by norm_num)

/-- `r = 1`, `ε = 2`: `p₁, p₂, p₅` have the nontrivial common zero `(1, ω, ω²)`. -/
example : ¬ TrivialCommonZero 1 2 5 := fun h =>
  (trivialCommonZero_iff 1 le_rfl 2 (Or.inr rfl)).mp h rfl

/-- The witness `(1, ω, ω²)` is a genuine nontrivial common zero of
`p₄, p₅, p₁₃` (`r = 4`, `ε = 1`). -/
example : ∃ x y z : ℂ, p 4 x y z = 0 ∧ p 5 x y z = 0 ∧ p 13 x y z = 0 ∧ x ≠ 0 := by
  obtain ⟨ω, h3, h1⟩ := exists_cube_root
  exact ⟨1, ω, ω ^ 2, p_one_omega ω h3 h1 4 (by norm_num), p_one_omega ω h3 h1 5 (by norm_num),
    p_one_omega ω h3 h1 13 (by norm_num), one_ne_zero⟩

end Candidates.AbedelfatahPowerSumsTrivialZero
