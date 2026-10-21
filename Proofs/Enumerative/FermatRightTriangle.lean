/-
# Fermat's right triangle theorem

## Source

P. de Fermat, marginal note to Bachet's Diophantus (Arithmetica, Book VI,
problem 26), proof by infinite descent; see L. J. Mordell, *Diophantine
Equations* (1969), Ch. 4; N. Koblitz, *Introduction to Elliptic Curves and
Modular Forms*, Ch. I §1; K. Conrad, "The congruent number problem",
Harvard College Math. Review 2 (2008).

## Informal statement (verbatim from the target spec, 2026-10-21)

> There are no integers x, y, z with xyz ≠ 0 and x^4 - y^4 = z^2.
> Equivalently, no right triangle with rational sides has square area. In
> particular, 1 is not a congruent number: there are no positive rationals
> a, b, c with a^2 + b^2 = c^2 and ab = 2.

## Mathlib check (2026-10-21)

`Mathlib/NumberTheory/FLT/Four.lean` proves only `not_fermat_42`
(`a ^ 4 + b ^ 4 ≠ c ^ 2`) and `fermatLastTheoremFour`.  `leandoc` probes
"fourth power difference square", "congruent number", "Fermat right
triangle area square" and a grep for `x ^ 4 - y ^ 4` find nothing.  The repo
module `Enumerative.CongruentBSD` defines `A273929.IsCongruentArea` and
`A273929.IsCongruentNumber` and proves only `¬ IsCongruentArea 0` and
`¬ IsCongruentArea (-1)`.

## Proof outline

Infinite descent on `|x|` for `Solution x y z := y ≠ 0 ∧ z ≠ 0 ∧ x⁴ - y⁴ = z²`:

* if `d = gcd x y > 1`, then `d² ∣ z` and `(x/d, y/d, z/d²)` is smaller;
* if `x, y` are coprime then `x` is odd (mod 4);
* `y` odd: classify the primitive triple `(y², z, x²)`:
  `y² = m² - n²`, `x² = m² + n²`, so `(m, n, xy)` is a solution, `|m| < |x|`;
* `y` even: classify `(z, y², x²)`: `y² = 2mn`, `x² = m² + n²`; with `p` the
  odd and `q` the even one of `m, n`, `p = a²`, `q = 2b²`; classify
  `(a², 2b², |x|)`: `a² = r² - s²`, `b² = rs`, so `r = c²`, `s = d²` and
  `(c, d, a)` is a solution with `|c| < |x|`.

The congruent-number corollary clears denominators: from `a² + b² = c²`,
`ab = 2` one gets `C⁴ - (2D)⁴ = (A² - B²)²` with `A ≠ B` because `√2` is
irrational.
-/
import Mathlib
import Enumerative.CongruentBSD

set_option autoImplicit false

namespace Candidates.FermatRightTriangle

open A273929

/-- `Solution x y z`: the triple `(x, y, z)` solves `x ^ 4 - y ^ 4 = z ^ 2` with `y ≠ 0`
and `z ≠ 0` (then `x ≠ 0` is automatic, see `Solution.x_ne_zero`). -/
def Solution (x y z : ℤ) : Prop := y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 - y ^ 4 = z ^ 2

/-- Ground truth: the equation has the trivial solution `(1, 0, 1)`, which `Solution`
excludes through `y ≠ 0`. -/
example : (1 : ℤ) ^ 4 - 0 ^ 4 = 1 ^ 2 ∧ ¬ Solution 1 0 1 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨hy, -, -⟩
  exact hy rfl

/-- Ground truth: `(1, 1, 0)` solves the equation but is excluded through `z ≠ 0`. -/
example : (1 : ℤ) ^ 4 - 1 ^ 4 = 0 ^ 2 ∧ ¬ Solution 1 1 0 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨-, hz, -⟩
  exact hz rfl

/-- Ground truth: `Solution` unfolds to the equation; e.g. `(2, 1, 1)` fails it
(`16 - 1 = 15 ≠ 1`). -/
example : ¬ Solution 2 1 1 := by
  rintro ⟨-, -, h⟩
  norm_num at h

/-- Ground truth: the exponent matters — `x ^ 2 - y ^ 2 = z ^ 2` has the nontrivial
solution `(5, 4, 3)`. -/
example : (5 : ℤ) ^ 2 - 4 ^ 2 = 3 ^ 2 := by norm_num

/-- Non-vacuity of the congruent-area corollaries: `6` is a congruent area
(the `(3, 4, 5)` triangle). -/
example : IsCongruentArea 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- In a primitive-style triple: if `a` is coprime to `c` and `a² + b² = c²`, then `a`
is coprime to `b`. -/
lemma isCoprime_leg {a b c : ℤ} (h : IsCoprime a c) (habc : a ^ 2 + b ^ 2 = c ^ 2) :
    IsCoprime a b := by
  have h2 : IsCoprime a (c ^ 2) := h.pow_right
  rw [← habc, show a ^ 2 + b ^ 2 = b ^ 2 + a * a by ring] at h2
  have h3 : IsCoprime a (b ^ 2) := IsCoprime.of_add_mul_left_right h2
  exact (IsCoprime.pow_right_iff two_pos).mp h3

/-- A positive factor of a square, coprime to its cofactor, is a square. -/
lemma eq_sq_of_isCoprime_of_pos {a b c : ℤ} (h : IsCoprime a b) (ha : 0 < a)
    (heq : a * b = c ^ 2) : ∃ a0 : ℤ, a = a0 ^ 2 := by
  obtain ⟨a0, h0 | h0⟩ := Int.sq_of_isCoprime h heq
  · exact ⟨a0, h0⟩
  · nlinarith [sq_nonneg a0]

/-- A solution has `x ≠ 0`. -/
lemma Solution.x_ne_zero {x y z : ℤ} (h : Solution x y z) : x ≠ 0 := by
  rintro rfl
  obtain ⟨hy, -, h⟩ := h
  have : 0 < y ^ 4 := by positivity
  nlinarith [sq_nonneg z]

/-- Descent when `gcd x y ≠ 1`: dividing by `d = gcd x y` gives a solution with smaller
`|x|`. -/
lemma exists_smaller_of_gcd_ne_one {x y z : ℤ} (h : Solution x y z) (hg : Int.gcd x y ≠ 1) :
    ∃ x' y' z', Solution x' y' z' ∧ x'.natAbs < x.natAbs := by
  obtain ⟨hy, hz, heq⟩ := h
  have hx : x ≠ 0 := Solution.x_ne_zero ⟨hy, hz, heq⟩
  have hd0 : Int.gcd x y ≠ 0 := Int.gcd_ne_zero_right hy
  obtain ⟨x', hxe⟩ : (Int.gcd x y : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hye⟩ : (Int.gcd x y : ℤ) ∣ y := Int.gcd_dvd_right x y
  generalize Int.gcd x y = d at hd0 hg hxe hye
  subst hxe hye
  have hdz : ((d : ℤ) ^ 2) ^ 2 ∣ z ^ 2 := ⟨x' ^ 4 - y' ^ 4, by rw [← heq]; ring⟩
  obtain ⟨z', rfl⟩ : (d : ℤ) ^ 2 ∣ z := (Int.pow_dvd_pow_iff two_ne_zero).mp hdz
  have hd4 : ((d : ℤ)) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd0)
  refine ⟨x', y', z', ⟨right_ne_zero_of_mul hy, right_ne_zero_of_mul hz, ?_⟩, ?_⟩
  · apply mul_left_cancel₀ hd4
    linear_combination heq
  · have hd1 : 1 < d := by omega
    have hx' : x' ≠ 0 := right_ne_zero_of_mul hx
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have : 0 < x'.natAbs := Int.natAbs_pos.mpr hx'
    nlinarith

/-- Second descent step (the `y` even case): if `p` odd, `p, q > 0` coprime,
`p² + q² = x²` and `pq = 2w²`, there is a solution with smaller `|x|`. -/
lemma exists_smaller_of_sum_sq {p q x w : ℤ} (hco : IsCoprime p q) (hp2 : p % 2 = 1)
    (hp : 0 < p) (hq : 0 < q) (hx : p ^ 2 + q ^ 2 = x ^ 2) (hpq : p * q = 2 * w ^ 2) :
    ∃ x' y' z', Solution x' y' z' ∧ x'.natAbs < x.natAbs := by
  -- `q` is even
  have h2q : (2 : ℤ) ∣ q := by
    rcases Int.prime_two.dvd_or_dvd (show (2 : ℤ) ∣ p * q from ⟨w ^ 2, hpq⟩) with h | h
    · omega
    · exact h
  obtain ⟨q', rfl⟩ := h2q
  have hpq' : p * q' = w ^ 2 := by linarith
  have hco' : IsCoprime p q' := hco.of_mul_right_right
  have hq' : 0 < q' := by omega
  obtain ⟨a, rfl⟩ := eq_sq_of_isCoprime_of_pos hco' hp hpq'
  obtain ⟨b, rfl⟩ := eq_sq_of_isCoprime_of_pos hco'.symm hq' (by rw [mul_comm]; exact hpq')
  have hxpos : 0 < |x| := abs_pos.mpr (by rintro rfl; nlinarith)
  have htriple : PythagoreanTriple (a ^ 2) (2 * b ^ 2) |x| := by
    unfold PythagoreanTriple
    rw [abs_mul_abs_self]; linear_combination hx
  obtain ⟨r, s, hr, hs, hxr, hgcd, -, hr0⟩ :=
    htriple.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hco) hp2 hxpos
  have hrs : r * s = b ^ 2 := by linarith
  have hb : b ≠ 0 := by rintro rfl; simp at hq'
  have hrs0 : 0 < r * s := by rw [hrs]; positivity
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hrs0; simp at hrs0
  have hspos : 0 < s := pos_of_mul_pos_right hrs0 hr0
  have hcors : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  obtain ⟨c, rfl⟩ := eq_sq_of_isCoprime_of_pos hcors hrpos hrs
  obtain ⟨d, rfl⟩ := eq_sq_of_isCoprime_of_pos hcors.symm hspos (by rw [mul_comm]; exact hrs)
  refine ⟨c, d, a, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro rfl; simp at hspos
  · rintro rfl; simp at hp
  · linear_combination -hr
  · rw [Int.natAbs_lt_iff_sq_lt, ← sq_abs x, hxr]
    nlinarith

/-- In a solution with `x, y` coprime, `x` is odd (an even `x` gives `z² ≡ 3 mod 4`). -/
lemma odd_x {x y z : ℤ} (heq : x ^ 4 - y ^ 4 = z ^ 2) (hco : IsCoprime x y) : x % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · exfalso
    obtain ⟨k, rfl⟩ : (2 : ℤ) ∣ x := Int.dvd_of_emod_eq_zero hx
    have hy : y % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one y with hy | hy
      · have hu : IsUnit (2 : ℤ) :=
          hco.isUnit_of_dvd' (dvd_mul_right 2 k) (Int.dvd_of_emod_eq_zero hy)
        rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
      · exact hy
    obtain ⟨j, rfl⟩ : Odd y := Int.odd_iff.mpr hy
    have h4 := congrArg (Int.cast : ℤ → ZMod 4) heq
    push_cast at h4
    generalize (k : ZMod 4) = a at h4
    generalize (j : ZMod 4) = b at h4
    generalize (z : ZMod 4) = c at h4
    revert a b c
    decide
  · exact hx

/-- Descent step for coprime `x, y`: there is a solution with smaller `|x|`. -/
lemma exists_smaller_of_isCoprime {x y z : ℤ} (h : Solution x y z) (hco : IsCoprime x y) :
    ∃ x' y' z', Solution x' y' z' ∧ x'.natAbs < x.natAbs := by
  obtain ⟨hy, hz, heq⟩ := h
  have hx : x ≠ 0 := Solution.x_ne_zero ⟨hy, hz, heq⟩
  have hx2 : x % 2 = 1 := odd_x heq hco
  have hco2 : IsCoprime (y ^ 2) (x ^ 2) := hco.symm.pow
  have hleg : (y ^ 2) ^ 2 + z ^ 2 = (x ^ 2) ^ 2 := by linear_combination -heq
  have hcoyz : IsCoprime (y ^ 2) z := isCoprime_leg hco2 hleg
  have hx2pos : 0 < x ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
  · -- `y` even, `z` odd
    have hz2 : z % 2 = 1 := by
      have hxo : Odd (x ^ 4) := (Int.odd_iff.mpr hx2).pow
      have hye : Even (y ^ 4) := (Int.even_iff.mpr hy2).pow_of_ne_zero (by norm_num)
      have hzo : Odd (z ^ 2) := heq ▸ hxo.sub_even hye
      exact Int.odd_iff.mp (Int.odd_pow.mp hzo |>.resolve_right (by norm_num))
    have htriple : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
      unfold PythagoreanTriple; linear_combination -heq
    obtain ⟨m, n, -, hmn, hxmn, hgcd, hpar, hm0⟩ :=
      htriple.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcoyz.symm) hz2 hx2pos
    obtain ⟨w, rfl⟩ : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hy2
    have hmnw : m * n = 2 * w ^ 2 := by linarith
    have hw : w ≠ 0 := right_ne_zero_of_mul hy
    have hmn0 : 0 < m * n := by rw [hmnw]; positivity
    have hmpos : 0 < m := by
      rcases hm0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hmn0; simp at hmn0
    have hnpos : 0 < n := pos_of_mul_pos_right hmn0 hm0
    have hcomn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    have hxsq : m ^ 2 + n ^ 2 = x ^ 2 := hxmn.symm
    rcases hpar with ⟨-, hn1⟩ | ⟨hm1, -⟩
    · exact exists_smaller_of_sum_sq hcomn.symm hn1 hnpos hmpos (by linarith)
        (by rw [mul_comm]; exact hmnw)
    · exact exists_smaller_of_sum_sq hcomn hm1 hmpos hnpos hxsq hmnw
  · -- `y` odd
    have hy2' : y ^ 2 % 2 = 1 := Int.odd_iff.mp (Int.odd_iff.mpr hy2).pow
    have htriple : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
      unfold PythagoreanTriple; linear_combination -heq
    obtain ⟨m, n, hymn, hzmn, hxmn, -, -, -⟩ :=
      htriple.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcoyz) hy2' hx2pos
    have hn : n ≠ 0 := by rintro rfl; exact hz (by rw [hzmn]; ring)
    refine ⟨m, n, x * y, ⟨hn, mul_ne_zero hx hy, ?_⟩, ?_⟩
    · have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
      rw [this, hymn, hxmn]; ring
    · rw [Int.natAbs_lt_iff_sq_lt]
      have : 0 < n ^ 2 := by positivity
      nlinarith


/-- The descent step: every solution has a solution with strictly smaller `|x|`. -/
lemma Solution.exists_smaller {x y z : ℤ} (h : Solution x y z) :
    ∃ x' y' z', Solution x' y' z' ∧ x'.natAbs < x.natAbs := by
  by_cases hg : Int.gcd x y = 1
  · exact exists_smaller_of_isCoprime h (Int.isCoprime_iff_gcd_eq_one.mpr hg)
  · exact exists_smaller_of_gcd_ne_one h hg

/-- No solutions exist (infinite descent on `|x|`). -/
lemma not_solution (x y z : ℤ) : ¬ Solution x y z := by
  suffices key : ∀ N : ℕ, ∀ x y z : ℤ, x.natAbs = N → ¬ Solution x y z from
    key _ x y z rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x y z rfl h
    obtain ⟨x', y', z', h', hlt⟩ := h.exists_smaller
    exact ih _ hlt x' y' z' rfl h'

/-- **Fermat's right triangle theorem.** There are no integers `x, y, z` with `y ≠ 0`,
`z ≠ 0` and `x ^ 4 - y ^ 4 = z ^ 2`.  (The source's hypothesis `x ≠ 0` is not needed:
`x = 0` forces `-y ^ 4 = z ^ 2`, impossible for `y ≠ 0`.) -/
theorem not_fourth_sub_fourth_eq_sq {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 :=
  fun h => not_solution x y z ⟨hy, hz, h⟩

/-- **`1` is not a congruent number**: there are no positive rationals `a, b, c` with
`a ^ 2 + b ^ 2 = c ^ 2` and `a * b = 2`. -/
theorem not_isCongruentArea_one : ¬ IsCongruentArea 1 := by
  rintro ⟨a, b, c, ha, hb, -, hpy, harea⟩
  -- the legs differ, since `a = b` would give `a ^ 2 = 2`
  have hab : a ≠ b := by
    rintro rfl
    have ha2 : ((a : ℝ)) ^ 2 = 2 := by exact_mod_cast (by linear_combination harea : a ^ 2 = 2)
    have hsqrt : Real.sqrt 2 = ((|a| : ℚ) : ℝ) := by
      rw [Rat.cast_abs, ← ha2, Real.sqrt_sq_eq_abs]
    exact irrational_sqrt_two.ne_rat _ hsqrt
  -- clear denominators
  set D : ℤ := a.den * b.den * c.den with hD
  set A : ℤ := a.num * b.den * c.den with hA
  set B : ℤ := a.den * b.num * c.den with hB
  set C : ℤ := a.den * b.den * c.num with hC
  have hD0 : D ≠ 0 := by positivity
  have hAq : (A : ℚ) = a * D := by
    simp only [hA, hD]; push_cast; rw [← Rat.mul_den_eq_num a]; ring
  have hBq : (B : ℚ) = b * D := by
    simp only [hB, hD]; push_cast; rw [← Rat.mul_den_eq_num b]; ring
  have hCq : (C : ℚ) = c * D := by
    simp only [hC, hD]; push_cast; rw [← Rat.mul_den_eq_num c]; ring
  have hpyZ : A ^ 2 + B ^ 2 = C ^ 2 := by
    have : (A : ℚ) ^ 2 + B ^ 2 = C ^ 2 := by
      rw [hAq, hBq, hCq]; linear_combination (D : ℚ) ^ 2 * hpy
    exact_mod_cast this
  have hAB : A * B = 2 * D ^ 2 := by
    have : (A : ℚ) * B = 2 * D ^ 2 := by
      rw [hAq, hBq]; linear_combination (D : ℚ) ^ 2 * harea
    exact_mod_cast this
  have hz : A ^ 2 - B ^ 2 ≠ 0 := by
    intro h0
    have h0q : ((a ^ 2 - b ^ 2) * D ^ 2 : ℚ) = 0 := by
      have : ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = 0 := by exact_mod_cast h0
      push_cast at this
      rw [hAq, hBq] at this
      linear_combination this
    have hDq : (D : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD0)
    have hsq : a ^ 2 = b ^ 2 := by
      have := (mul_eq_zero.mp h0q).resolve_right hDq
      linear_combination this
    exact hab ((sq_eq_sq₀ ha.le hb.le).mp hsq)
  refine not_fourth_sub_fourth_eq_sq (x := C) (y := 2 * D) (z := A ^ 2 - B ^ 2)
    (mul_ne_zero two_ne_zero hD0) hz ?_
  linear_combination -(A ^ 2 + B ^ 2 + C ^ 2) * hpyZ + 4 * (A * B + 2 * D ^ 2) * hAB

/-- **No right triangle with rational sides has square area**: for every rational `q`,
`q ^ 2` is not a congruent area. -/
theorem not_isCongruentArea_sq (q : ℚ) : ¬ IsCongruentArea (q ^ 2) := by
  rintro ⟨a, b, c, ha, hb, hc, hpy, harea⟩
  have hq : q ≠ 0 := by
    rintro rfl
    have : 0 < a * b := mul_pos ha hb
    rw [harea] at this
    norm_num at this
  have hqa : 0 < |q| := abs_pos.mpr hq
  refine not_isCongruentArea_one
    ⟨a / |q|, b / |q|, c / |q|, by positivity, by positivity, by positivity, ?_, ?_⟩
  · rw [div_pow, div_pow, div_pow, ← hpy, add_div]
  · field_simp
    rw [sq_abs, harea]
    ring

/-- **Fermat (A003273): no positive square is a congruent number**, i.e. for every `k : ℕ`,
`k ^ 2` is not in OEIS A003273; in particular `1` is not a congruent number. -/
theorem not_isCongruentNumber_sq (k : ℕ) : ¬ IsCongruentNumber (k ^ 2) := by
  unfold IsCongruentNumber
  push_cast
  exact not_isCongruentArea_sq (k : ℚ)

/-- **`1` is not a congruent number** (OEIS A003273 form). -/
theorem not_isCongruentNumber_one : ¬ IsCongruentNumber 1 := by
  simpa using not_isCongruentNumber_sq 1

end Candidates.FermatRightTriangle
