/-
# A102091 — Lu: primes `≡ 5, 7 (mod 12)` avoid centered `n`-gonal numbers

Steven Lu's conjecture in OEIS A102091 says that, for `n > 6`, primes
congruent to `5` or `7` modulo `12` divide no centered `n`-gonal number iff
`n` is a term of A102091. The third term `108` refutes the implication from sequence membership to prime avoidance:
`1 + 108·(2·3/2) = 325` is divisible by `5`.

A restricted implication is proved as
`dvd_sub_eight_of_dvd_centeredPolygonal`: for a term `n`, every such prime
dividing a centered `n`-gonal number divides `n - 8`. The Pell identity
`a(i)(a(i)-8) = 3(4y_i)²` follows from `a(i) = 4+4x_i`, with
`x_i + y_i√3 = (2+√3)^i`; quadratic reciprocity supplies the character of `3`.
The converse of this restricted statement is not treated.

## Formal conventions

* `a i` is the OEIS term `a(i)` for `1 ≤ i` (offset 1), defined by the entry's
  recurrence; `a 0 = 8` is the value of Barker's closed form at `0`, chosen so
  the recurrence holds uniformly, and is excluded from membership by `1 ≤ i`.
  The sequence is computed in `ℤ` so the recurrence needs no truncated
  subtraction.
* `centeredPolygonal n k = 1 + n · (k (k+1) / 2)`; the division is exact since
  `k (k+1)` is even, so no junk value arises.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A102091Refutation

/-! ## Definitions -/

/-- A102091 by the entry's recurrence `a(n) = 5 a(n-1) - 5 a(n-2) + a(n-3)`,
`a(1) = 12`, `a(2) = 32`, `a(3) = 108` (offset 1).  The value `a 0 = 8` lies
outside the offset; it is Barker's closed form `2 (2 + (2-√3)^0 + (2+√3)^0)`
and makes `a 3 = 5 · 32 - 5 · 12 + 8 = 108`. -/
def a : ℕ → ℤ
  | 0 => 8
  | 1 => 12
  | 2 => 32
  | n + 3 => 5 * a (n + 2) - 5 * a (n + 1) + a n

/-- Membership in the OEIS sequence A102091: `m = a(i)` for some index
`i ≥ 1` (the entry's offset). -/
def InA102091 (m : ℕ) : Prop := ∃ i : ℕ, 1 ≤ i ∧ a i = m

/-- The `k`-th centered `n`-gonal number `1 + n k (k+1) / 2` (`k ≥ 0`). -/
def centeredPolygonal (n k : ℕ) : ℕ := 1 + n * (k * (k + 1) / 2)

/-! ## Examples -/

-- The first twelve listed terms of A102091.
example : (List.range 12).map (fun i => a (i + 1)) =
    [12, 32, 108, 392, 1452, 5408, 20172, 75272, 280908, 1048352, 3912492,
      14601608] := by
  decide

-- Centered hexagonal numbers (A003215): `1, 7, 19, 37, 61, 91`.
example : (List.range 6).map (centeredPolygonal 6) = [1, 7, 19, 37, 61, 91] := by
  decide

-- Centered 12-gonal (star) numbers (A003154): `1, 13, 37, 73, 121, 181`.
example : (List.range 6).map (centeredPolygonal 12) = [1, 13, 37, 73, 121, 181] := by
  decide

/-! ## The conjecture -/

/-- **Lu's conjecture (A102091, Steven Lu).**

Formalized: for every `n > 6`, no prime `q` with `q % 12 = 5` or `q % 12 = 7`
divides any centered `n`-gonal number `1 + n k (k+1) / 2` (`k ≥ 0`) if and only
if `n` is a term of A102091. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 6 < n →
    ((∀ q k : ℕ, q.Prime → (q % 12 = 5 ∨ q % 12 = 7) → ¬ q ∣ centeredPolygonal n k) ↔
      InA102091 n)

/-! ## Refutation -/

/-- `108 = a(3)` is a term of A102091. -/
theorem inA102091_108 : InA102091 108 := ⟨3, by norm_num, by decide⟩

/-- The centered `108`-gonal number with `k = 2` is `325 = 5² · 13`. -/
theorem centeredPolygonal_108_two : centeredPolygonal 108 2 = 325 := by decide

/-- **Lu's conjecture is false.**

Counterexample to the "if" direction: `n = 108 = a(3)` is a term of A102091
and `108 > 6`, yet the prime `q = 5 ≡ 5 (mod 12)` divides the centered
`108`-gonal number `1 + 108 · (2 · 3 / 2) = 325` (`k = 2`). See below for the restriction excluding primes dividing `n - 8`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hiff := hconj 108 (by norm_num)
  have hnone := hiff.2 inA102091_108
  have hdvd : 5 ∣ centeredPolygonal 108 2 := by
    rw [centeredPolygonal_108_two]
    norm_num
  exact hnone 5 2 Nat.prime_five (Or.inl (by norm_num)) hdvd

/-! ## The repaired "if" direction -/

/-- `(x_i, y_i)` with `x_i + y_i √3 = (2 + √3)^i`, by the recursion
`(x, y) ↦ (2x + 3y, x + 2y)` from `(1, 0)`. -/
def pell : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (2 * (pell n).1 + 3 * (pell n).2, (pell n).1 + 2 * (pell n).2)

-- `(2 + √3)^i` for `i = 0, 1, 2, 3`: `1`, `2 + √3`, `7 + 4√3`, `26 + 15√3`.
example : (List.range 4).map pell = [(1, 0), (2, 1), (7, 4), (26, 15)] := by
  decide

/-- The Pell equation `x_i² - 3 y_i² = 1`. -/
theorem pell_norm (n : ℕ) : (pell n).1 ^ 2 - 3 * (pell n).2 ^ 2 = 1 := by
  induction n with
  | zero => simp [pell]
  | succ n ih =>
    simp only [pell]
    linear_combination ih

/-- The first coordinate satisfies `x_{n+2} = 4 x_{n+1} - x_n`. -/
theorem pell_fst_rec (n : ℕ) :
    (pell (n + 2)).1 = 4 * (pell (n + 1)).1 - (pell n).1 := by
  simp only [pell]
  ring

/-- Closed form `a(n) = 4 + 4 x_n` (Barker's formula, since
`2 x_n = (2+√3)^n + (2-√3)^n`). -/
theorem a_eq_pell : ∀ n : ℕ, a n = 4 + 4 * (pell n).1
  | 0 => by simp [a, pell]
  | 1 => by simp [a, pell]
  | 2 => by simp [a, pell]
  | n + 3 => by
    rw [a, a_eq_pell n, a_eq_pell (n + 1), a_eq_pell (n + 2), pell_fst_rec (n + 1),
      pell_fst_rec n]
    ring

/-- The Pell identity behind the conjecture: `a(n) (a(n) - 8) = 3 (4 y_n)²`. -/
theorem a_mul_sub_eight (n : ℕ) : a n * (a n - 8) = 3 * (4 * (pell n).2) ^ 2 := by
  rw [a_eq_pell]
  linear_combination 16 * pell_norm n

/-- `2` is not a square modulo `3`. -/
theorem not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by decide

/-- For a prime `q ≡ 5` or `7 (mod 12)`, `3` is a quadratic nonresidue mod `q`
(quadratic reciprocity). -/
theorem not_isSquare_three {q : ℕ} (hq : q.Prime) (hq12 : q % 12 = 5 ∨ q % 12 = 7) :
    ¬ IsSquare (3 : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcast : ((3 : ℕ) : ZMod q) = 3 := by norm_num
  rw [← hcast]
  rcases hq12 with h5 | h7
  · have h4 : q % 4 = 1 := by omega
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h4 (by norm_num)]
    have hq3 : ((q : ℕ) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod q 3, show q % 3 = 2 by omega]
      rfl
    rw [hq3]
    exact not_isSquare_two_zmod_three
  · have h4 : q % 4 = 3 := by omega
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 (by norm_num) (by omega)]
    have hq3 : ((q : ℕ) : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod q 3, show q % 3 = 1 by omega]
      rfl
    rw [hq3]
    exact not_not.mpr ⟨1, by norm_num⟩

/-- **The repaired "if" direction.**  If `n` is a term of A102091 and a prime
`q ≡ 5` or `7 (mod 12)` divides a centered `n`-gonal number, then `q ∣ n - 8`.
So Lu's claim holds for all such primes not dividing `n - 8`; the counterexample
`n = 108`, `q = 5` has `5 ∣ 100`. -/
theorem dvd_sub_eight_of_dvd_centeredPolygonal {n q k : ℕ} (hn : InA102091 n)
    (hq : q.Prime) (hq12 : q % 12 = 5 ∨ q % 12 = 7) (hdvd : q ∣ centeredPolygonal n k) :
    (q : ℤ) ∣ (n : ℤ) - 8 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨i, -, hi⟩ := hn
  set T := k * (k + 1) / 2 with hT
  have hTtwo : 2 * T = k * (k + 1) := by
    rw [hT]
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
  have hzero : (1 : ZMod q) + (n : ZMod q) * (T : ZMod q) = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff _ q).2 hdvd
    simpa [centeredPolygonal, hT] using h0
  have hTz : 2 * (T : ZMod q) = (k : ZMod q) * ((k : ZMod q) + 1) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ZMod q)) hTtwo
  have hpellz : (n : ZMod q) * ((n : ZMod q) - 8) = 3 * (4 * ((pell i).2 : ZMod q)) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) (a_mul_sub_eight i)
    simp only [hi] at h
    push_cast at h
    exact h
  have hsq : ((n : ZMod q) * (2 * k + 1)) ^ 2 = (n : ZMod q) * ((n : ZMod q) - 8) := by
    linear_combination (8 * (n : ZMod q)) * hzero - (4 * (n : ZMod q) ^ 2) * hTz
  have hy : (4 * ((pell i).2 : ZMod q)) = 0 := by
    by_contra hne
    apply not_isSquare_three hq hq12
    refine ⟨(n : ZMod q) * (2 * k + 1) / (4 * ((pell i).2 : ZMod q)), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hne hne)]
    linear_combination -(hsq.trans hpellz)
  rw [hy] at hpellz
  have hprod : (n : ZMod q) * ((n : ZMod q) - 8) = 0 := by
    rw [hpellz]
    ring
  rcases mul_eq_zero.1 hprod with hn0 | hn8
  · rw [hn0] at hzero
    simp at hzero
  · have hcast : (((n : ℤ) - 8 : ℤ) : ZMod q) = 0 := by
      push_cast
      exact hn8
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 hcast

-- Non-vacuity: the hypotheses of `dvd_sub_eight_of_dvd_centeredPolygonal` hold
-- jointly at the counterexample `n = 108`, `q = 5`, `k = 2`, where `5 ∣ 100`.
example : InA102091 108 ∧ Nat.Prime 5 ∧ (5 % 12 = 5 ∨ 5 % 12 = 7) ∧
    5 ∣ centeredPolygonal 108 2 ∧ (5 : ℤ) ∣ (108 : ℤ) - 8 :=
  ⟨inA102091_108, Nat.prime_five, Or.inl rfl, by decide, by norm_num⟩

end Candidates.A102091Refutation
