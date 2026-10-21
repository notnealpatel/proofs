/-
# Liouville's bound `g(4) ≤ 53`

## Classical source

* J. Liouville (1859): every natural number is a sum of at most `53`
  biquadrates (attribution as given by the target spec and Hardy–Wright;
  the original publication was not re-read for this module).
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*,
  §21.3 ("Biquadrates"), which proves `g(4) ≤ 53` from Liouville's identity
  and Lagrange's four-square theorem.

## Informal statement (as recorded by the target spec, 2026-10-21)

> Every natural number is a sum of at most 53 fourth powers of natural
> numbers. It follows from Liouville's identity
> 6(a^2+b^2+c^2+d^2)^2 = sum_{i<j} [(x_i+x_j)^4 + (x_i-x_j)^4]
> and Lagrange's four-square theorem.

Date: 2026-10-21.

## Mathlib absence

`leandoc` searches for "waring fourth powers", "sum of fourth powers",
"biquadrate", and `grep -i "waring\|fourth power"` over Mathlib found no
fourth-power representation theorem; Mathlib has `Nat.sum_four_squares`
(Lagrange) only.  The repo module `Enumerative.IdealWaring` defines
`A002804.IsSumOfNthPowers`, `A002804.WaringAdmissible`, `A002804.waringG`, and
the lower witness `79` for `n = 4`, but has no upper bound at `n = 4`.

## Proof (Hardy–Wright §21.3)

Write `N = 6 q + r` with `r ≤ 5`.  By Lagrange `q = a₁² + a₂² + a₃² + a₄²`,
and each `aᵢ` is again a sum of four squares, so Liouville's identity makes
each `6 aᵢ²` a sum of `12` fourth powers.  Hence `6 q` is a sum of `48`
fourth powers and `N` a sum of `48 + 5 = 53`.
-/
import Mathlib
import Enumerative.IdealWaring

set_option autoImplicit false

namespace LiouvilleWaringFour

open A002804

/-! ## Liouville's identity -/

/-- **Liouville's identity** over `ℤ`:
`6 (a² + b² + c² + d²)² = ∑_{x < y} ((x + y)⁴ + (x - y)⁴)`, the sum running
over the six pairs drawn from `a, b, c, d`. -/
theorem liouville_identity (a b c d : ℤ) :
    6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 =
      (a + b) ^ 4 + (a - b) ^ 4 + (a + c) ^ 4 + (a - c) ^ 4 + (a + d) ^ 4 + (a - d) ^ 4
      + (b + c) ^ 4 + (b - c) ^ 4 + (b + d) ^ 4 + (b - d) ^ 4
      + (c + d) ^ 4 + (c - d) ^ 4 := by
  ring

/-- A fourth power of an integer is the fourth power of its absolute value,
read back as a natural number: `(|z| : ℤ)⁴ = z⁴`. -/
theorem natAbs_cast_pow_four (z : ℤ) : ((z.natAbs : ℕ) : ℤ) ^ 4 = z ^ 4 := by
  rw [Int.natCast_natAbs]
  exact Even.pow_abs (by decide) z

/-! ## Closure properties of `IsSumOfNthPowers` -/

/-- Representations add: if `a` is a sum of at most `s` and `b` of at most `t`
`n`-th powers, then `a + b` is a sum of at most `s + t` `n`-th powers. -/
theorem isSumOfNthPowers_add {n s t a b : ℕ} (ha : IsSumOfNthPowers n s a)
    (hb : IsSumOfNthPowers n t b) : IsSumOfNthPowers n (s + t) (a + b) := by
  obtain ⟨m, hm, rfl⟩ := ha
  obtain ⟨m', hm', rfl⟩ := hb
  refine ⟨m + m', ?_, ?_⟩
  · rw [Multiset.card_add]
    omega
  · rw [Multiset.map_add, Multiset.sum_add]

/-- Any `r` is a sum of `r` copies of `1 ^ n`. -/
theorem isSumOfNthPowers_self (n r : ℕ) : IsSumOfNthPowers n r r :=
  ⟨Multiset.replicate r 1, by rw [Multiset.card_replicate],
    by simp [Multiset.map_replicate, Multiset.sum_replicate]⟩

/-- **Liouville's identity, natural-number form.**  For natural `a, b, c, d`,
`6 (a² + b² + c² + d²)²` is a sum of at most `12` fourth powers of natural
numbers, namely the `|x ± y|⁴` over the six pairs. -/
theorem isSumOfNthPowers_six_mul_sq (a b c d : ℕ) :
    IsSumOfNthPowers 4 12 (6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2) := by
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  let D : ℤ := d
  refine ⟨{(A + B).natAbs, (A - B).natAbs, (A + C).natAbs, (A - C).natAbs,
    (A + D).natAbs, (A - D).natAbs, (B + C).natAbs, (B - C).natAbs,
    (B + D).natAbs, (B - D).natAbs, (C + D).natAbs, (C - D).natAbs}, by simp, ?_⟩
  apply (Nat.cast_inj (R := ℤ)).mp
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, natAbs_cast_pow_four]
  rw [liouville_identity A B C D]
  ring

/-- `6 m²` is a sum of at most `12` fourth powers, for every natural `m`
(Lagrange's four-square theorem fed into `isSumOfNthPowers_six_mul_sq`). -/
theorem isSumOfNthPowers_six_mul_sq' (m : ℕ) : IsSumOfNthPowers 4 12 (6 * m ^ 2) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  rw [← h]
  exact isSumOfNthPowers_six_mul_sq a b c d

/-- `6 q` is a sum of at most `48` fourth powers, for every natural `q`. -/
theorem isSumOfNthPowers_six_mul (q : ℕ) : IsSumOfNthPowers 4 48 (6 * q) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares q
  have hsplit : 6 * q = 6 * a ^ 2 + 6 * b ^ 2 + 6 * c ^ 2 + 6 * d ^ 2 := by
    rw [← h]
    ring
  rw [hsplit]
  exact isSumOfNthPowers_add (isSumOfNthPowers_add (isSumOfNthPowers_add
    (isSumOfNthPowers_six_mul_sq' a) (isSumOfNthPowers_six_mul_sq' b))
    (isSumOfNthPowers_six_mul_sq' c)) (isSumOfNthPowers_six_mul_sq' d)

/-! ## The theorem -/

/-- **Liouville (1859): `g(4) ≤ 53`.**  Every natural number is a sum of at
most `53` fourth powers of natural numbers. -/
theorem waringAdmissible_four_fiftyThree : WaringAdmissible 4 53 := by
  intro N
  have hdiv : N = 6 * (N / 6) + N % 6 := (Nat.div_add_mod N 6).symm
  have hr : N % 6 ≤ 5 := Nat.lt_succ_iff.mp (Nat.mod_lt N (by norm_num))
  rw [hdiv]
  exact isSumOfNthPowers_add (isSumOfNthPowers_six_mul (N / 6))
    ((isSumOfNthPowers_self 4 (N % 6)).mono hr)

/-- Padding a list of bases to an exact-length tuple: a list `l` with `l.length = k`
gives `f : Fin k → ℕ` with `∑ i, f i ^ n = ∑_{x ∈ l} x ^ n`. -/
theorem exists_fin_of_list (n k : ℕ) (l : List ℕ) (hl : l.length = k) :
    ∃ f : Fin k → ℕ, ∑ i, f i ^ n = (l.map (· ^ n)).sum := by
  subst hl
  exact ⟨fun i => l[i.1], Fin.sum_univ_fun_getElem l (· ^ n)⟩

/-- **Liouville (1859), Mathlib-only form.**  Every natural number `N` is
`∑_{i < 53} f(i)⁴` for some `f : Fin 53 → ℕ` (zero summands allowed, so this
is "at most 53 fourth powers"). -/
theorem exists_sum_fiftyThree_fourth_powers (N : ℕ) :
    ∃ f : Fin 53 → ℕ, ∑ i, f i ^ 4 = N := by
  obtain ⟨m, hcard, hsum⟩ := waringAdmissible_four_fiftyThree N
  let l : List ℕ := m.toList ++ List.replicate (53 - Multiset.card m) 0
  have hlen : l.length = 53 := by
    simp only [l, List.length_append, Multiset.length_toList, List.length_replicate]
    omega
  have hlsum : (l.map (· ^ 4)).sum = N := by
    rw [← hsum]
    simp [l, List.sum_replicate]
  obtain ⟨f, hf⟩ := exists_fin_of_list 4 53 l hlen
  exact ⟨f, hf.trans hlsum⟩

/-- **Bounds on `g(4)`**: `19 ≤ g(4) ≤ 53`.  The upper bound is Liouville's;
the lower bound is the repo's Euler witness `79` (`A002804.idealWaring 4 = 19`).
The admissibility witness `waringAdmissible_four_fiftyThree` makes the `sInf`
defining `waringG 4` nonjunk. -/
theorem nineteen_le_waringG_four_le_fiftyThree : 19 ≤ waringG 4 ∧ waringG 4 ≤ 53 := by
  refine ⟨?_, waringG_le waringAdmissible_four_fiftyThree⟩
  have hlb := idealWaring_le_waringG (n := 4) (by norm_num)
    ⟨53, waringAdmissible_four_fiftyThree⟩
  rwa [show idealWaring 4 = 19 by decide] at hlb

/-! ## Ground truth -/

-- Liouville's identity at `(1, 2, 0, 0)`: `6 · 5² = 150`
example : (6 : ℤ) * (1 ^ 2 + 2 ^ 2 + 0 ^ 2 + 0 ^ 2) ^ 2 = 150 := by norm_num

-- the twelve bases it produces at `(1, 2, 0, 0)`: `150 = 3⁴ + 5 · 1⁴ + 4 · 2⁴ + 2 · 0⁴`
example : IsSumOfNthPowers 4 12 150 :=
  ⟨{3, 1, 1, 1, 1, 1, 2, 2, 2, 2, 0, 0}, by decide, by decide⟩

-- the definition is not vacuous at `n = 4`: `79` needs `19` fourth powers, not `18`
example : IsSumOfNthPowers 4 19 79 ∧ ¬ IsSumOfNthPowers 4 18 79 :=
  ⟨isSumOfNthPowers_seventyNine, not_isSumOfNthPowers_seventyNine⟩

-- the main theorem specialised at `79`
example : IsSumOfNthPowers 4 53 79 := waringAdmissible_four_fiftyThree 79

end LiouvilleWaringFour
