/-
# Coprime-coefficient Frobenius number: `g(a,b) ≥ 4 f(a,b)`

## Source

arXiv:2610.17267, Grace Natalie Jaffe, "Denominators in the Farey Sequence,
the Stern Sequence, and the Frobenius Problem with Relatively Prime
Multipliers".  Retrieved 2026-10-21.

* Section "The Frobenius Connection": for positive coprime `a, b`,
  `g(a,b)` is "the largest integer that cannot be expressed as `ax+by` for
  *relatively prime*, non-negative integers `x,y`; if no such integer
  exists, we will say `g(a,b)=∞`", and `f(a,b) = ab-a-b` is the classical
  Frobenius number.
* Section "Future Directions" (`\label{conj:frob}`), verbatim:

  > For all $a,b \geq 2$ relatively prime, we have $g(a,b) \geq 4 f(a,b)$.

## Status

Open in the paper: stated as a conjecture supported by the computed values
`g(a,b)` for `a, b ≤ 200`.  This module proves it.  The same quantity was
introduced independently as `G_{a_1,a_2}` by Ding, Wang and Zhang, "The
Diophantine Frobenius Problem revisited", arXiv:2509.08599 (September
2025, not cited by Jaffe), who prove `a_1 a_2 ≤ G ≪ a_1 a_2 (log a_1 a_2)^2`
and `G_{2,a} = 4a - 2`; neither source proves `g ≥ 4f`, and no other source
for it was found (search coverage: arXiv and web, no MathSciNet).

## Formal reading

`g(a,b) ≥ 4 f(a,b)` (with the paper's convention `g = ∞` allowed) is
equivalent to the existence of an integer `n ≥ 4 f(a,b)` with no
representation `n = ax+by`, `x,y ≥ 0`, `gcd(x,y) = 1`.  The main theorem
`exists_not_coprimeRep_ge_four_frobenius` states exactly that, with
`f(a,b)` computed in `ℤ`.  The corollary
`four_frobenius_le_coprimeFrobenius` restates it for `g` defined as a
supremum, under the explicit hypothesis that the non-representable set is
bounded above (the paper's existence theorem, not reproved here).

## Proof outline

*Covering lemma.*  If `gcd(a,b) = 1` and `x₀ < b`, every non-negative
solution of `ax+by = ax₀+by₀` is `(x₀+bk, y₀-ak)` with `ak ≤ y₀`; if none
of these pairs is coprime then `ax₀+by₀` has no coprime representation.

*Modular witnesses.*  Take `x₀ = λb mod P` and `P ∣ y₀ + λa`.  Then
`gcd(P, λ+k)` divides both `x₀+bk` and `y₀-ak`, so it suffices that
`gcd(P, λ+k) ≠ 1` for every `k ≤ y₀/a` (a Jacobsthal-type covering).
With `y₀ ≥ 4a-4` the witness is at least `b y₀ ≥ 4f(a,b)`.

* `a = 2`: the paper's witness `4b-2` (its Proposition "twosies").
* `a ≥ 30` (the smaller of the two): `P = 30`, `λ = 2`,
  `y₀ = 4a + (24a mod 30)`; the moduli `2, 3, 5` cover `λ + k ∈ {2,…,6}`.
* `3 ≤ a ≤ 29`: a per-`a` triple `(P, λ, y₀)` with `P ≤ 110`, checked by
  `decide`; it applies whenever `λb mod P < b`.  The remaining 95 pairs
  (all with `b < 110`) carry explicit certificates `(x₀, y₀)`, also checked
  by `decide`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FrobeniusCoprimeCoefficient

/-! ## Definitions -/

/-- `CoprimeRep a b n`: the paper's "`n` can be expressed as `ax+by` for relatively
prime, non-negative integers `x, y`". -/
def CoprimeRep (a b n : ℕ) : Prop :=
  ∃ x y : ℕ, a * x + b * y = n ∧ Nat.Coprime x y

/-- The coprime-coefficient Frobenius number `g(a,b)`: the supremum of the integers with no
coprime representation.  It is the paper's `g(a,b)` whenever that set is bounded above,
which is the paper's existence theorem; otherwise `sSup` takes its junk value `0`, so every
statement about it below carries the boundedness hypothesis explicitly. -/
noncomputable def coprimeFrobenius (a b : ℕ) : ℕ :=
  sSup {n : ℕ | ¬ CoprimeRep a b n}

/-- Boolean covering check: `x₀ < b` and, for every `k ≤ y₀ / a`, the pair
`(x₀ + b k, y₀ - a k)` is not coprime. -/
def coverCheck (a b x0 y0 : ℕ) : Bool :=
  decide (x0 < b) &&
    (List.range (y0 / a + 1)).all fun k => Nat.gcd (x0 + b * k) (y0 - a * k) != 1

/-! ## Ground truth from the paper (the running example `a = 5`, `b = 7`) -/

example : CoprimeRep 5 7 12 := ⟨1, 1, by norm_num, by decide⟩

example : CoprimeRep 5 7 157 := ⟨2, 21, by norm_num, by decide⟩

example : coverCheck 5 7 6 18 = true := by decide

example : coverCheck 5 7 6 19 = false := by decide

/-! ## Symmetry and the covering lemma -/

/-- Coprime representability is symmetric in the two multipliers. -/
theorem coprimeRep_comm {a b n : ℕ} : CoprimeRep a b n ↔ CoprimeRep b a n := by
  constructor
  · rintro ⟨x, y, hxy, hco⟩
    exact ⟨y, x, by rw [← hxy]; ring, hco.symm⟩
  · rintro ⟨x, y, hxy, hco⟩
    exact ⟨y, x, by rw [← hxy]; ring, hco.symm⟩

/-- For coprime `a, b` and `x₀ < b`, every non-negative solution of
`a x + b y = a x₀ + b y₀` is `x = x₀ + b k`, `y = y₀ - a k` for some `k` with `a k ≤ y₀`. -/
theorem eq_of_mul_add_mul_eq {a b x0 y0 x y : ℕ} (hab : Nat.Coprime a b) (hx0 : x0 < b)
    (h : a * x + b * y = a * x0 + b * y0) :
    ∃ k : ℕ, x = x0 + b * k ∧ a * k + y = y0 := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le x0) hx0
  have hmod : a * x ≡ a * x0 [MOD b] := by
    have h' := congrArg (· % b) h
    simpa [Nat.ModEq, Nat.add_mul_mod_self_left] using h'
  have hx : x ≡ x0 [MOD b] := Nat.ModEq.cancel_left_of_coprime hab.symm hmod
  have hxmod : x % b = x0 := by
    rw [hx]
    exact Nat.mod_eq_of_lt hx0
  have hxk : x = x0 + b * (x / b) := by
    have hdiv := Nat.mod_add_div x b
    omega
  refine ⟨x / b, hxk, ?_⟩
  rw [hxk] at h
  have hbb : b * (a * (x / b) + y) = b * y0 := by
    rw [← Nat.add_left_cancel_iff (n := a * x0), ← h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hb hbb

/-- Covering lemma: if `gcd(a,b) = 1`, `x₀ < b`, and no pair `(x₀ + b k, y₀ - a k)` with
`a k ≤ y₀` is coprime, then `a x₀ + b y₀` has no coprime representation. -/
theorem not_coprimeRep_of_cover {a b x0 y0 : ℕ} (hab : Nat.Coprime a b) (hx0 : x0 < b)
    (hcov : ∀ k : ℕ, a * k ≤ y0 → ¬ Nat.Coprime (x0 + b * k) (y0 - a * k)) :
    ¬ CoprimeRep a b (a * x0 + b * y0) := by
  rintro ⟨x, y, hxy, hco⟩
  obtain ⟨k, hxk, hyk⟩ := eq_of_mul_add_mul_eq hab hx0 hxy
  have hle : a * k ≤ y0 := by omega
  have hy : y = y0 - a * k := by omega
  subst hxk hy
  exact hcov k hle hco

/-- Soundness of `coverCheck`. -/
theorem not_coprimeRep_of_coverCheck {a b x0 y0 : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (h : coverCheck a b x0 y0 = true) : ¬ CoprimeRep a b (a * x0 + b * y0) := by
  simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨hx0, hall⟩ := h
  refine not_coprimeRep_of_cover hab hx0 fun k hk hco => hall k ?_ hco
  have hkle : k ≤ y0 / a := (Nat.le_div_iff_mul_le ha).mpr (by rw [mul_comm]; exact hk)
  omega

/-- Modular witnesses: with `x₀ = λ b mod P` and `P ∣ y₀ + λ a`, the number `gcd(P, λ+k)`
divides both `x₀ + b k` and `y₀ - a k`; so if it differs from `1` whenever `a k ≤ y₀`,
then `a x₀ + b y₀` has no coprime representation. -/
theorem not_coprimeRep_of_modular {a b P lam y0 : ℕ} (hab : Nat.Coprime a b)
    (hx0 : lam * b % P < b) (hP : P ∣ y0 + lam * a)
    (hcov : ∀ k : ℕ, a * k ≤ y0 → Nat.gcd P (lam + k) ≠ 1) :
    ¬ CoprimeRep a b (a * (lam * b % P) + b * y0) := by
  refine not_coprimeRep_of_cover hab hx0 fun k hk hco => hcov k hk ?_
  set d := Nat.gcd P (lam + k) with hd
  have hdP : d ∣ P := Nat.gcd_dvd_left P (lam + k)
  have hdl : d ∣ lam + k := Nat.gcd_dvd_right P (lam + k)
  have hdx : d ∣ lam * b % P + b * k := by
    have hsplit : lam * b % P + b * k + P * (lam * b / P) = b * (lam + k) := by
      have hdiv := Nat.mod_add_div (lam * b) P
      have hc : b * lam = lam * b := mul_comm b lam
      rw [mul_add]
      omega
    have h2 : d ∣ lam * b % P + b * k + P * (lam * b / P) := by
      rw [hsplit]
      exact Dvd.dvd.mul_left hdl b
    exact (Nat.dvd_add_left (Dvd.dvd.mul_right hdP _)).mp h2
  have hdy : d ∣ y0 - a * k := by
    have hsplit : y0 - a * k + a * (lam + k) = y0 + lam * a := by
      have hc : a * lam = lam * a := mul_comm a lam
      rw [mul_add]
      omega
    have h2 : d ∣ y0 - a * k + a * (lam + k) := by
      rw [hsplit]
      exact hdP.trans hP
    exact (Nat.dvd_add_left (Dvd.dvd.mul_left hdl a)).mp h2
  have hdd : Nat.Coprime d d :=
    Nat.Coprime.coprime_dvd_left hdx (Nat.Coprime.coprime_dvd_right hdy hco)
  exact Nat.Coprime.eq_one_of_dvd hdd (dvd_refl d)

/-- Size bound: if `4 a ≤ y₀ + 4` then `a x₀ + b y₀ ≥ 4 (ab - a - b)`. -/
theorem four_frobenius_le_of_le {a b x0 y0 : ℕ} (h : 4 * a ≤ y0 + 4) :
    4 * ((a : ℤ) * b - a - b) ≤ ((a * x0 + b * y0 : ℕ) : ℤ) := by
  have h' : (4 : ℤ) * a ≤ y0 + 4 := by exact_mod_cast h
  have hb : (0 : ℤ) ≤ b := Int.natCast_nonneg b
  have ha : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hx : (0 : ℤ) ≤ x0 := Int.natCast_nonneg x0
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h' hb, mul_nonneg ha hx]

/-! ## The three regimes for the smaller multiplier -/

/-- The case `a = 2` (paper, Proposition "twosies"): `4b - 2` has no coprime
representation by `2` and odd `b ≥ 3`. -/
theorem not_coprimeRep_two {b : ℕ} (hb : 2 ≤ b) (hab : Nat.Coprime 2 b) :
    ¬ CoprimeRep 2 b (2 * (b - 1) + b * 2) := by
  have hodd : Odd b := Nat.coprime_two_left.mp hab
  obtain ⟨m, hm⟩ := hodd
  refine not_coprimeRep_of_cover hab (by omega) fun k hk hco => ?_
  have hk1 : k ≤ 1 := by omega
  interval_cases k
  · have hco0 : Nat.Coprime (b - 1) 2 := by simpa using hco
    have hdvd : 2 ∣ b - 1 := ⟨m, by omega⟩
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hdvd (dvd_refl 2) hco0
  · have h1 : b - 1 + b * 1 = 1 := by simpa using hco
    omega

/-- The case `a ≥ 30`: `x₀ = 2b mod 30`, `y₀ = 4a + (24a mod 30)`, covered by the moduli
`2, 3, 5`. -/
theorem not_coprimeRep_of_thirty_le {a b : ℕ} (ha : 30 ≤ a) (hb : 30 ≤ b)
    (hab : Nat.Coprime a b) :
    ¬ CoprimeRep a b (a * (2 * b % 30) + b * (4 * a + 24 * a % 30)) := by
  refine not_coprimeRep_of_modular hab ?_ (by omega) fun k hk => ?_
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) hb
  · have hlt : a * k < a * 5 := by
      have : 24 * a % 30 < 30 := Nat.mod_lt _ (by norm_num)
      omega
    have hk5 : k < 5 := Nat.lt_of_mul_lt_mul_left hlt
    interval_cases k <;> decide

/-- Per-`a` modular parameters `(P, λ, y₀)` for `3 ≤ a ≤ 29`. -/
def smallParams : ℕ → ℕ × ℕ × ℕ
  | 3 => (10, 4, 8)
  | 4 => (42, 7, 14)
  | 5 => (30, 2, 20)
  | 6 => (110, 33, 22)
  | 7 => (42, 32, 28)
  | 8 => (42, 7, 28)
  | 9 => (30, 3, 33)
  | 10 => (30, 2, 40)
  | 11 => (66, 8, 44)
  | 12 => (42, 6, 54)
  | 13 => (30, 24, 48)
  | 14 => (30, 24, 54)
  | 15 => (30, 24, 60)
  | 16 => (30, 24, 66)
  | 17 => (30, 24, 72)
  | 18 => (30, 24, 78)
  | 19 => (30, 2, 82)
  | 20 => (30, 2, 80)
  | 21 => (30, 24, 96)
  | 22 => (30, 3, 84)
  | 23 => (30, 2, 104)
  | 24 => (30, 2, 102)
  | 25 => (30, 2, 100)
  | 26 => (30, 25, 100)
  | 27 => (30, 25, 105)
  | 28 => (30, 24, 108)
  | 29 => (30, 24, 114)
  | _ => (1, 0, 0)

/-- Boolean check of the hypotheses of `not_coprimeRep_of_modular` and of the size bound for
the parameters `smallParams a`. -/
def smallParamsOK (a : ℕ) : Bool :=
  let P := (smallParams a).1
  let lam := (smallParams a).2.1
  let y0 := (smallParams a).2.2
  decide (0 < P) && decide (P ≤ 110) && (y0 + lam * a) % P == 0 && decide (4 * a ≤ y0 + 4) &&
    (List.range (y0 / a + 1)).all fun k => Nat.gcd P (lam + k) != 1

/-- The per-`a` parameters pass the check for every `3 ≤ a ≤ 29`. -/
theorem smallParamsOK_all : ∀ a < 30, 3 ≤ a → smallParamsOK a = true := by
  decide

/-- Explicit certificates `(a, b, x₀, y₀)` for the pairs `3 ≤ a < b` where the per-`a`
parameters do not apply. -/
def certTable : List (ℕ × ℕ × ℕ × ℕ) := [
  (3, 4, 2, 6), (3, 7, 4, 14), (4, 5, 4, 10), (4, 7, 0, 18),
  (4, 9, 6, 10), (4, 11, 10, 10), (4, 15, 3, 30), (4, 17, 11, 11),
  (4, 21, 0, 18), (4, 23, 12, 18), (4, 29, 6, 18), (4, 35, 0, 18),
  (5, 6, 0, 19), (5, 7, 6, 18), (5, 8, 4, 14), (5, 9, 8, 22),
  (5, 11, 3, 15), (5, 12, 0, 19), (5, 13, 6, 24), (5, 14, 12, 18),
  (6, 7, 4, 28), (6, 11, 10, 18), (6, 13, 8, 18), (6, 19, 14, 18),
  (6, 23, 22, 18), (6, 25, 20, 18), (6, 29, 28, 18), (6, 31, 2, 28),
  (6, 35, 20, 28), (6, 43, 38, 18), (6, 49, 28, 28), (6, 53, 46, 28),
  (6, 55, 0, 28), (6, 59, 18, 28), (6, 73, 26, 28), (6, 83, 70, 40),
  (7, 9, 6, 32), (7, 10, 6, 27), (7, 11, 5, 35), (7, 13, 12, 42),
  (7, 15, 10, 32), (7, 17, 6, 30), (7, 18, 12, 32), (7, 19, 8, 34),
  (7, 22, 10, 35), (7, 26, 24, 42), (7, 30, 20, 32), (7, 34, 2, 34),
  (7, 38, 24, 39), (8, 9, 3, 30), (8, 11, 2, 34), (8, 15, 3, 60),
  (8, 17, 6, 54), (8, 21, 15, 54), (8, 23, 22, 38), (8, 29, 19, 38),
  (8, 35, 28, 38), (9, 16, 6, 42), (9, 17, 0, 60), (9, 19, 17, 51),
  (10, 11, 4, 30), (10, 13, 6, 48), (11, 12, 0, 43), (11, 13, 12, 66),
  (11, 14, 0, 60), (11, 15, 6, 50), (11, 16, 4, 46), (11, 19, 9, 69),
  (11, 20, 18, 51), (11, 21, 12, 68), (11, 23, 3, 99), (11, 24, 6, 46),
  (11, 29, 27, 57), (11, 30, 12, 50), (11, 31, 12, 54), (11, 32, 8, 46),
  (11, 38, 18, 69), (11, 39, 36, 66), (11, 40, 30, 60), (11, 41, 3, 39),
  (11, 48, 38, 54), (11, 49, 0, 60), (11, 57, 21, 77), (12, 13, 9, 45),
  (12, 17, 11, 44), (12, 19, 11, 66), (13, 16, 2, 64), (13, 17, 10, 100),
  (13, 21, 0, 90), (14, 17, 4, 62), (15, 16, 8, 108), (15, 17, 0, 66),
  (16, 17, 6, 108), (16, 21, 15, 108), (17, 21, 6, 74)]

/-- Coverage check: every coprime pair `3 ≤ a < b` with `a < 30`, `b ≤ 110`, for which
`λ b mod P ≥ b`, has a certificate in `certTable` passing `coverCheck` and the size bound. -/
def finiteCovered : Bool :=
  (List.range 30).all fun a => (List.range 111).all fun b =>
    !(decide (3 ≤ a) && decide (a < b) && Nat.gcd a b == 1 &&
        decide (b ≤ (smallParams a).2.1 * b % (smallParams a).1)) ||
      certTable.any fun e =>
        e.1 == a && e.2.1 == b && coverCheck a b e.2.2.1 e.2.2.2 &&
          decide (4 * a ≤ e.2.2.2 + 4 ∨ 4 * (a * b) ≤ a * e.2.2.1 + b * e.2.2.2 + 4 * a + 4 * b)

/-- The finite certificate table covers all exceptional pairs. -/
theorem finiteCovered_eq_true : finiteCovered = true := by
  decide

/-- Size bound from the second disjunct of the certificate check. -/
theorem four_frobenius_le_of_le' {a b x0 y0 : ℕ}
    (h : 4 * (a * b) ≤ a * x0 + b * y0 + 4 * a + 4 * b) :
    4 * ((a : ℤ) * b - a - b) ≤ ((a * x0 + b * y0 : ℕ) : ℤ) := by
  have h' : ((4 * (a * b) : ℕ) : ℤ) ≤ ((a * x0 + b * y0 + 4 * a + 4 * b : ℕ) : ℤ) :=
    by exact_mod_cast h
  push_cast at h' ⊢
  linarith

/-- The regime `3 ≤ a ≤ 29`, `a < b`: either the per-`a` modular witness applies, or the pair
is one of the finitely many with an explicit certificate. -/
theorem exists_not_coprimeRep_of_small {a b : ℕ} (ha3 : 3 ≤ a) (ha : a < 30) (hlt : a < b)
    (hab : Nat.Coprime a b) :
    ∃ n : ℕ, 4 * ((a : ℤ) * b - a - b) ≤ n ∧ ¬ CoprimeRep a b n := by
  have hok := smallParamsOK_all a ha ha3
  simp only [smallParamsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hP0, hP110⟩, hdiv⟩, hy0⟩, hcov⟩ := hok
  by_cases hx : (smallParams a).2.1 * b % (smallParams a).1 < b
  · refine ⟨_, four_frobenius_le_of_le hy0,
      not_coprimeRep_of_modular hab hx (Nat.dvd_of_mod_eq_zero hdiv) fun k hk => hcov k ?_⟩
    have hkle : k ≤ (smallParams a).2.2 / a :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hk)
    omega
  · have hb : b < 111 := by
      have hmod := Nat.mod_lt ((smallParams a).2.1 * b) hP0
      omega
    have hfin := finiteCovered_eq_true
    simp only [finiteCovered, List.all_eq_true, List.mem_range] at hfin
    have hab' : Nat.gcd a b = 1 := hab
    have hpair := hfin a ha b hb
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hpair
    rcases hpair with (((hbad | hbad) | hbad) | hbad) | ⟨e, -, ⟨⟨he1, he2⟩, hcheck⟩, hsize⟩
    · exact absurd ha3 hbad
    · exact absurd hlt hbad
    · exact absurd hab' hbad
    · exact absurd (not_lt.mp hx) hbad
    · subst he1 he2
      refine ⟨_, ?_, not_coprimeRep_of_coverCheck hab (by omega) hcheck⟩
      rcases hsize with hsize | hsize
      · exact four_frobenius_le_of_le hsize
      · exact four_frobenius_le_of_le' hsize

/-! ## Ground truth: the paper's exact values -/

/-- The paper's value `g(5,7) = 156` is non-representable (its Figure "example": the four
solutions `(6,18), (13,13), (20,8), (27,3)` of `5x + 7y = 156` all have `gcd > 1`). -/
theorem not_coprimeRep_five_seven : ¬ CoprimeRep 5 7 156 :=
  not_coprimeRep_of_coverCheck (x0 := 6) (y0 := 18) (by decide) (by norm_num) (by decide)

/-- Every `n ≥ 11` has a coprime representation by `2` and `3`. -/
theorem coprimeRep_two_three {n : ℕ} (hn : 11 ≤ n) : CoprimeRep 2 3 n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  interval_cases r
  · refine ⟨2 * q - 3, 2, by omega, ?_⟩
    exact Nat.coprime_two_right.mpr ⟨q - 2, by omega⟩
  · exact ⟨2 * q - 1, 1, by omega, Nat.coprime_one_right _⟩
  · refine ⟨2 * q - 5, 4, by omega, ?_⟩
    have h2 : Nat.Coprime (2 * q - 5) 2 := Nat.coprime_two_right.mpr ⟨q - 3, by omega⟩
    simpa using Nat.Coprime.pow_right 2 h2
  · exact ⟨2 * q, 1, by omega, Nat.coprime_one_right _⟩

/-- Ground truth for `coprimeFrobenius`: the paper's `g(2,3) = 4·3 - 2 = 10`
(Proposition "twosies" at `b = 3`). -/
theorem coprimeFrobenius_two_three : coprimeFrobenius 2 3 = 10 := by
  have hgreat : IsGreatest {n : ℕ | ¬ CoprimeRep 2 3 n} 10 := by
    refine ⟨not_coprimeRep_two (b := 3) (by norm_num) (by norm_num), fun n hn => ?_⟩
    by_contra hlt
    exact hn (coprimeRep_two_three (by omega))
  exact hgreat.csSup_eq

/-- Non-vacuity: the hypotheses of the main theorem hold at `a = 5`, `b = 7`, and the
theorem's bound `4 f(5,7) = 92` is below the paper's `g(5,7) = 156`. -/
example : 2 ≤ 5 ∧ 2 ≤ 7 ∧ Nat.Coprime 5 7 ∧ 4 * ((5 : ℤ) * 7 - 5 - 7) ≤ (156 : ℕ) := by
  decide

/-! ## Main theorem -/

/-- **Conjecture `conj:frob` of arXiv:2610.17267 (Jaffe), proved.**  For all relatively prime
`a, b ≥ 2` there is an integer `n ≥ 4 f(a,b) = 4(ab - a - b)` that cannot be written as
`a x + b y` with `x, y ≥ 0` and `gcd(x, y) = 1`; that is, `g(a,b) ≥ 4 f(a,b)`. -/
theorem exists_not_coprimeRep_ge_four_frobenius {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : Nat.Coprime a b) :
    ∃ n : ℕ, 4 * ((a : ℤ) * b - a - b) ≤ n ∧ ¬ CoprimeRep a b n := by
  wlog hlt : a < b generalizing a b
  · have hne : a ≠ b := by
      rintro rfl
      have h1 : a = 1 := by simpa using hab
      omega
    obtain ⟨n, hn, hrep⟩ := this hb ha hab.symm (by omega)
    refine ⟨n, by linarith, fun h => hrep (coprimeRep_comm.mp h)⟩
  rcases (show a = 2 ∨ (3 ≤ a ∧ a < 30) ∨ 30 ≤ a by omega) with h2 | ⟨ha3, ha30⟩ | ha30
  · subst h2
    exact ⟨_, four_frobenius_le_of_le' (by omega), not_coprimeRep_two hb hab⟩
  · exact exists_not_coprimeRep_of_small ha3 ha30 hlt hab
  · refine ⟨_, four_frobenius_le_of_le ?_, not_coprimeRep_of_thirty_le ha30 (by omega) hab⟩
    omega

/-- **`g(a,b) ≥ 4 f(a,b)` for the supremum form of `g`.**  For relatively prime `a, b ≥ 2`,
if the set of integers with no coprime representation is bounded above (the paper's
existence theorem for `g`, kept as an explicit hypothesis), then
`4 (ab - a - b) ≤ g(a,b)`. -/
theorem four_frobenius_le_coprimeFrobenius {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : Nat.Coprime a b) (hbdd : BddAbove {n : ℕ | ¬ CoprimeRep a b n}) :
    4 * ((a : ℤ) * b - a - b) ≤ coprimeFrobenius a b := by
  obtain ⟨n, hn, hrep⟩ := exists_not_coprimeRep_ge_four_frobenius ha hb hab
  have hle : n ≤ coprimeFrobenius a b := le_csSup hbdd hrep
  have hle' : (n : ℤ) ≤ coprimeFrobenius a b := by exact_mod_cast hle
  linarith

end Candidates.FrobeniusCoprimeCoefficient
