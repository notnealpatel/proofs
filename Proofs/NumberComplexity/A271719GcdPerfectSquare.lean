/-
# A271719 — Sun: primitive `x + y + z = n` with `x² + (2y+z)²` a square

## OEIS source (retrieved with `oeis show A271719`, 2026-10-21)

```
NAME:     Number of ordered ways to write n as x + y + z with x >= y > 0, z > 0
          and gcd(x,y,z) = 1 such that x^2 + (2*y+z)^2 is a square.
TERMS:    0,0,0,0,0,2,0,0,0,0,1,1,3,1,2,4,3,1,3,4,3,2,2,1,4,2,5,4,5,2,6,4,7,4,
          6,4,8,5,7,7,10,3,9,7,10,9,10,4,8,5,6,4,9,1,8,5,7,6,12,4,17,11,15,10,
          15,8,21,12,15,9
OFFSET:   1
COMMENT (the conjecture):
  Conjecture: a(n) > 0 for all n > 10, and a(n) = 1 only for
  n = 11, 12, 14, 18, 24, 54.
AUTHOR:   Zhi-Wei Sun, Apr 12 2016 (the conjecture line carries no separate
          signature; it is part of Sun's original entry; live entry checked)
```

## Literature status (triage)

Open as far as the triage could tell: the entry contains no proof, Sun's
arXiv:1604.06723 does not state or prove it, and a web search found only the
OEIS page.  The triage recomputed the data up to `n = 20000`; this attempt
recomputed it (independent brute force for `n ≤ 200` cross-checked against a
Pythagorean-pair enumeration) up to `n = 30000`.

This module proves the conjecture completely (no `sorry`; axioms
`propext`, `Classical.choice`, `Quot.sound`).

## Proof outline (formalized below)

Put `u = x` and `v = 2y + z`.  Then `y = u + v - n`, `z = 2n - 2u - v`, and the
side conditions become `n < u + v`, `2u + v < 2n`, `v ≤ n`, and
`gcd(x, y, z) = gcd(u, v, n)`.  For a Pythagorean pair `(a, b)` and a scale `t`
with `gcd(a, b) = 1`, the pair `(u, v) = (a t, b t)` is admissible iff
`b t ≤ n`, `(2a + b) t < 2n`, `n < (a + b) t` and `gcd(t, n) = 1`.  Seven
triples cover every ratio `n / t ∈ [51, 408)` and three cover `[24, 48)`.
Bertrand's postulate gives primes `p₁, …, p₄` with `n / p₁ ∈ [24, 48)`,
`n / p₂ ∈ [51, 102)`, `n / p₃ ∈ [102, 204)`, `n / p₄ ∈ [204, 408)`.  For
`n ≥ 2914` no three of them divide `n` (their product would exceed `n`), so
two of them are coprime to `n` and give two distinct representations.  The
range `11 ≤ n < 2914` is a kernel-checked finite search for two explicit
representations, and the six exceptional values are counted exactly.
-/
import Mathlib

set_option autoImplicit false
/- The kernel-evaluated finite checks below are elaborated sequentially: run in
parallel they exhaust the 14 GB address-space cap used on this machine. -/
set_option Elab.async false

namespace Candidates.A271719GcdPerfectSquare

/-! ## Definition layer -/

/-- The representations counted by A271719, encoded by the pair `(x, y)`; the
third coordinate is `z = n - x - y`, which the guard `x + y < n` keeps positive
(so the truncated subtraction never hits its junk value).  The conditions are
`1 ≤ y ≤ x`, `z > 0`, `gcd(x, y, z) = 1` and `x² + (2y + z)²` a perfect
square. -/
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p =>
    p.2 ≤ p.1 ∧ p.1 + p.2 < n ∧ Nat.gcd (Nat.gcd p.1 p.2) (n - p.1 - p.2) = 1 ∧
      IsSquare (p.1 ^ 2 + (2 * p.2 + (n - p.1 - p.2)) ^ 2)

/-- A271719: the number of ordered ways to write `n = x + y + z` with
`x ≥ y > 0`, `z > 0`, `gcd(x, y, z) = 1` and `x² + (2y+z)²` a square. -/
def a (n : ℕ) : ℕ := (reps n).card

/-- The first 30 terms agree with the OEIS DATA line (offset 1). -/
example : (List.range' 1 30).map a =
    [0,0,0,0,0,2,0,0,0,0,1,1,3,1,2,4,3,1,3,4,3,2,2,1,4,2,5,4,5,2] := by
  decide +kernel

/-- Membership in `reps` unfolded. -/
theorem mem_reps {n x y : ℕ} : (x, y) ∈ reps n ↔
    (1 ≤ x ∧ x ≤ n) ∧ (1 ≤ y ∧ y ≤ n) ∧ y ≤ x ∧ x + y < n ∧
      Nat.gcd (Nat.gcd x y) (n - x - y) = 1 ∧ IsSquare (x ^ 2 + (2 * y + (n - x - y)) ^ 2) := by
  simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- **Change of variables.**  If `u² + v² = w²`, `n < u + v`, `2u + v < 2n`,
`v ≤ n` and `gcd(u, v, n) = 1`, then `(x, y) = (u, u + v - n)` is a
representation of `n` (with `z = 2n - 2u - v` and `2y + z = v`). -/
theorem mem_reps_of_pyth {n u v w : ℕ} (h1 : n < u + v) (h2 : 2 * u + v < 2 * n)
    (h3 : v ≤ n) (hg : Nat.gcd (Nat.gcd u v) n = 1) (hw : u ^ 2 + v ^ 2 = w ^ 2) :
    (u, u + v - n) ∈ reps n := by
  rw [mem_reps]
  have hz : 2 * (u + v - n) + (n - u - (u + v - n)) = v := by omega
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
  · set d := Nat.gcd (Nat.gcd u (u + v - n)) (n - u - (u + v - n)) with hd
    have hdu : d ∣ u := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hdy : d ∣ u + v - n := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hdz : d ∣ n - u - (u + v - n) := Nat.gcd_dvd_right _ _
    have hdv : d ∣ v := by
      rw [← hz]
      exact Nat.dvd_add (Nat.dvd_mul_left_of_dvd hdy 2) hdz
    have hdn : d ∣ n := by
      have hn : u + (u + v - n) + (n - u - (u + v - n)) = n := by omega
      rw [← hn]
      exact Nat.dvd_add (Nat.dvd_add hdu hdy) hdz
    have hd1 : d ∣ Nat.gcd (Nat.gcd u v) n :=
      Nat.dvd_gcd (Nat.dvd_gcd hdu hdv) hdn
    rw [hg] at hd1
    exact Nat.dvd_one.mp hd1
  · rw [hz, hw]
    exact ⟨w, by ring⟩


/-! ## Representations from scaled Pythagorean triples -/

/-- `n` has a representation coming from a pair `(u, v)` (with `x = u`,
`y = u + v - n`) whose greatest common divisor is `t`.  Representations with
different `t` are different elements of `reps n`. -/
def HasRepWithGcd (n t : ℕ) : Prop :=
  ∃ u v : ℕ, n < u + v ∧ (u, u + v - n) ∈ reps n ∧ Nat.gcd u v = t

/-- **Scaled-triple witness.**  If `a² + b² = c²` with `gcd(a, b) = 1`, and the
scale `t` satisfies `b t ≤ n`, `(2a + b) t < 2n`, `n < (a + b) t` and
`gcd(t, n) = 1`, then `(u, v) = (a t, b t)` is a representation of `n`. -/
theorem hasRepWithGcd_of_triple {n a b c t : ℕ} (habc : a ^ 2 + b ^ 2 = c ^ 2)
    (hab : Nat.gcd a b = 1) (h1 : b * t ≤ n) (h2 : (2 * a + b) * t < 2 * n)
    (h3 : n < (a + b) * t) (ht : Nat.Coprime t n) : HasRepWithGcd n t := by
  have hg : Nat.gcd (a * t) (b * t) = t := by
    rw [Nat.gcd_mul_right, hab, one_mul]
  have e1 : (a + b) * t = a * t + b * t := by ring
  have e2 : (2 * a + b) * t = 2 * (a * t) + b * t := by ring
  refine ⟨a * t, b * t, by omega, ?_, hg⟩
  refine mem_reps_of_pyth (w := c * t) (by omega) (by omega) h1 ?_ ?_
  · rw [hg]
    exact ht
  · rw [mul_pow, mul_pow, mul_pow, ← add_mul, habc]

/-- Two representations with different gcd parameters give `2 ≤ a n`. -/
theorem two_le_a_of_hasRepWithGcd {n t t' : ℕ} (h : HasRepWithGcd n t)
    (h' : HasRepWithGcd n t') (htt : t ≠ t') : 2 ≤ a n := by
  obtain ⟨u, v, huv, hmem, hg⟩ := h
  obtain ⟨u', v', huv', hmem', hg'⟩ := h'
  have hne : (u, u + v - n) ≠ (u', u' + v' - n) := by
    intro heq
    have hu : u = u' := congrArg Prod.fst heq
    have hy : u + v - n = u' + v' - n := congrArg Prod.snd heq
    have hv : v = v' := by omega
    exact htt (by rw [← hg, ← hg', hu, hv])
  exact Finset.one_lt_card.mpr ⟨_, hmem, _, hmem', hne⟩

/-- A representation gives `0 < a n`. -/
theorem a_pos_of_hasRepWithGcd {n t : ℕ} (h : HasRepWithGcd n t) : 0 < a n := by
  obtain ⟨u, v, -, hmem, -⟩ := h
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- **Low window.**  The triples `(7,24,25)`, `(20,21,29)`, `(9,40,41)` cover
every ratio `n / t ∈ [24, 48)`. -/
theorem hasRepWithGcd_of_low {n t : ℕ} (ht : Nat.Coprime t n) (h1 : 24 * t ≤ n)
    (h2 : n < 48 * t) : HasRepWithGcd n t := by
  rcases lt_or_ge n (31 * t) with hA | hA
  · exact hasRepWithGcd_of_triple (a := 7) (b := 24) (c := 25) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (41 * t) with hB | hB
  · exact hasRepWithGcd_of_triple (a := 20) (b := 21) (c := 29) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  · exact hasRepWithGcd_of_triple (a := 9) (b := 40) (c := 41) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht

/-- **High window.**  The triples `(28,45,53)`, `(33,56,65)`, `(39,80,89)`,
`(44,117,125)`, `(85,132,157)`, `(105,208,233)`, `(136,273,305)` cover every
ratio `n / t ∈ [51, 408)`. -/
theorem hasRepWithGcd_of_high {n t : ℕ} (ht : Nat.Coprime t n) (h1 : 51 * t ≤ n)
    (h2 : n < 408 * t) : HasRepWithGcd n t := by
  rcases lt_or_ge n (73 * t) with hA | hA
  · exact hasRepWithGcd_of_triple (a := 28) (b := 45) (c := 53) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (89 * t) with hB | hB
  · exact hasRepWithGcd_of_triple (a := 33) (b := 56) (c := 65) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (119 * t) with hC | hC
  · exact hasRepWithGcd_of_triple (a := 39) (b := 80) (c := 89) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (161 * t) with hD | hD
  · exact hasRepWithGcd_of_triple (a := 44) (b := 117) (c := 125) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (217 * t) with hE | hE
  · exact hasRepWithGcd_of_triple (a := 85) (b := 132) (c := 157) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  rcases lt_or_ge n (313 * t) with hF | hF
  · exact hasRepWithGcd_of_triple (a := 105) (b := 208) (c := 233) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht
  · exact hasRepWithGcd_of_triple (a := 136) (b := 273) (c := 305) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) ht


/-! ## Large `n`: four Bertrand primes -/

/-- Three distinct primes dividing `n`, with `n < 102 q₁`, `n < 204 q₂` and
`n < 408 q₃`, force `n < 2914`: their product divides `n`, while
`n³ < 102 · 204 · 408 · q₁ q₂ q₃`. -/
theorem lt_of_three_prime_dvd {n q₁ q₂ q₃ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hq₃ : q₃.Prime) (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃) (h23 : q₂ ≠ q₃) (hn : 0 < n)
    (d₁ : q₁ ∣ n) (d₂ : q₂ ∣ n) (d₃ : q₃ ∣ n) (b₁ : n < 102 * q₁) (b₂ : n < 204 * q₂)
    (b₃ : n < 408 * q₃) : n < 2914 := by
  have c12 : Nat.Coprime q₁ q₂ := (Nat.coprime_primes hq₁ hq₂).mpr h12
  have c13 : Nat.Coprime q₁ q₃ := (Nat.coprime_primes hq₁ hq₃).mpr h13
  have c23 : Nat.Coprime q₂ q₃ := (Nat.coprime_primes hq₂ hq₃).mpr h23
  have hdvd : q₁ * q₂ * q₃ ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left c13 c23)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd c12 d₁ d₂) d₃
  have hle : q₁ * q₂ * q₃ ≤ n := Nat.le_of_dvd hn hdvd
  have hcube : n * n * n < (102 * q₁) * (204 * q₂) * (408 * q₃) :=
    Nat.mul_lt_mul'' (Nat.mul_lt_mul'' b₁ b₂) b₃
  have hsq : n * n * n < 8489664 * n := by
    calc n * n * n < (102 * q₁) * (204 * q₂) * (408 * q₃) := hcube
      _ = 8489664 * (q₁ * q₂ * q₃) := by ring
      _ ≤ 8489664 * n := Nat.mul_le_mul_left _ hle
  have hsq' : n * n < 8489664 := Nat.lt_of_mul_lt_mul_right hsq
  nlinarith

/-- **Large `n`.**  For `n ≥ 2914` there are two representations with different
gcd parameters, so `2 ≤ a n`. -/
theorem two_le_a_of_large {n : ℕ} (hn : 2914 ≤ n) : 2 ≤ a n := by
  obtain ⟨p₁, hp₁, hp₁l, hp₁u⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 48) (by omega)
  obtain ⟨p₂, hp₂, hp₂l, hp₂u⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 102) (by omega)
  obtain ⟨p₃, hp₃, hp₃l, hp₃u⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 204) (by omega)
  obtain ⟨p₄, hp₄, hp₄l, hp₄u⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 408) (by omega)
  -- the four ratio windows
  have w₁ : 24 * p₁ ≤ n ∧ n < 48 * p₁ := by omega
  have w₂ : 51 * p₂ ≤ n ∧ n < 102 * p₂ := by omega
  have w₃ : 102 * p₃ ≤ n ∧ n < 204 * p₃ := by omega
  have w₄ : 204 * p₄ ≤ n ∧ n < 408 * p₄ := by omega
  -- a prime not dividing `n` yields a representation
  have r₁ : ¬ p₁ ∣ n → HasRepWithGcd n p₁ := fun h =>
    hasRepWithGcd_of_low ((Nat.Prime.coprime_iff_not_dvd hp₁).mpr h) w₁.1 w₁.2
  have r₂ : ¬ p₂ ∣ n → HasRepWithGcd n p₂ := fun h =>
    hasRepWithGcd_of_high ((Nat.Prime.coprime_iff_not_dvd hp₂).mpr h) w₂.1 (by omega)
  have r₃ : ¬ p₃ ∣ n → HasRepWithGcd n p₃ := fun h =>
    hasRepWithGcd_of_high ((Nat.Prime.coprime_iff_not_dvd hp₃).mpr h) (by omega) (by omega)
  have r₄ : ¬ p₄ ∣ n → HasRepWithGcd n p₄ := fun h =>
    hasRepWithGcd_of_high ((Nat.Prime.coprime_iff_not_dvd hp₄).mpr h) (by omega) w₄.2
  have n12 : p₁ ≠ p₂ := by omega
  have n13 : p₁ ≠ p₃ := by omega
  have n14 : p₁ ≠ p₄ := by omega
  have n23 : p₂ ≠ p₃ := by omega
  have n24 : p₂ ≠ p₄ := by omega
  have n34 : p₃ ≠ p₄ := by omega
  have hn0 : 0 < n := by omega
  by_cases d₁ : p₁ ∣ n
  · by_cases d₂ : p₂ ∣ n
    · by_cases d₃ : p₃ ∣ n
      · exact absurd (lt_of_three_prime_dvd hp₁ hp₂ hp₃ n12 n13 n23 hn0 d₁ d₂ d₃
          (by omega) (by omega) (by omega)) (by omega)
      · by_cases d₄ : p₄ ∣ n
        · exact absurd (lt_of_three_prime_dvd hp₁ hp₂ hp₄ n12 n14 n24 hn0 d₁ d₂ d₄
            (by omega) (by omega) (by omega)) (by omega)
        · exact two_le_a_of_hasRepWithGcd (r₃ d₃) (r₄ d₄) n34
    · by_cases d₃ : p₃ ∣ n
      · by_cases d₄ : p₄ ∣ n
        · exact absurd (lt_of_three_prime_dvd hp₁ hp₃ hp₄ n13 n14 n34 hn0 d₁ d₃ d₄
            (by omega) (by omega) (by omega)) (by omega)
        · exact two_le_a_of_hasRepWithGcd (r₂ d₂) (r₄ d₄) n24
      · exact two_le_a_of_hasRepWithGcd (r₂ d₂) (r₃ d₃) n23
  · by_cases d₂ : p₂ ∣ n
    · by_cases d₃ : p₃ ∣ n
      · by_cases d₄ : p₄ ∣ n
        · exact absurd (lt_of_three_prime_dvd hp₂ hp₃ hp₄ n23 n24 n34 hn0 d₂ d₃ d₄
            (by omega) (by omega) (by omega)) (by omega)
        · exact two_le_a_of_hasRepWithGcd (r₁ d₁) (r₄ d₄) n14
      · exact two_le_a_of_hasRepWithGcd (r₁ d₁) (r₃ d₃) n13
    · exact two_le_a_of_hasRepWithGcd (r₁ d₁) (r₂ d₂) n12


/-! ## Small `n`: a kernel-checked witness search

The search below only proposes candidates; soundness rests on
`mem_reps_of_pyth`, so the candidate generator needs no correctness proof. -/

/-- Pythagorean triples `(a, b, c)` used to propose candidates `(a t, b t, c t)`. -/
def famList : List (ℕ × ℕ × ℕ) :=
  [(3, 4, 5), (4, 3, 5), (5, 12, 13), (12, 5, 13), (15, 8, 17), (8, 15, 17), (7, 24, 25),
    (24, 7, 25), (21, 20, 29), (20, 21, 29), (35, 12, 37), (12, 35, 37), (45, 28, 53)]

/-- Boolean test that `(u, v, w)` satisfies the hypotheses of `mem_reps_of_pyth`. -/
def goodB (n u v w : ℕ) : Bool :=
  decide (n < u + v) && decide (2 * u + v < 2 * n) && decide (v ≤ n) &&
    (Nat.gcd (Nat.gcd u v) n == 1) && (u * u + v * v == w * w)

/-- Candidate triples `(a t, b t, c t)` for the scales `t` in the range allowed by
`n < (a + b) t` and `b t ≤ n`. -/
def cands (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  famList.flatMap fun f =>
    (List.range' (n / (f.1 + f.2.1) + 1) (n / f.2.1 - n / (f.1 + f.2.1))).map fun t =>
      (f.1 * t, f.2.1 * t, f.2.2 * t)

/-- `true` when the first two candidates passing `goodB` have different pairs
`(u, v)`. -/
def twoReps (n : ℕ) : Bool :=
  match (cands n).filter (fun c => goodB n c.1 c.2.1 c.2.2) with
  | c :: d :: _ => c.1 != d.1 || c.2.1 != d.2.1
  | _ => false

/-- A candidate passing `goodB` is a representation. -/
theorem mem_reps_of_goodB {n u v w : ℕ} (h : goodB n u v w = true) :
    n < u + v ∧ (u, u + v - n) ∈ reps n := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, hg⟩, hw⟩ := h
  refine ⟨h1, mem_reps_of_pyth h1 h2 h3 hg (w := w) ?_⟩
  simpa [sq] using hw

/-- Soundness of the search: `twoReps n = true` gives `2 ≤ a n`. -/
theorem two_le_a_of_twoReps {n : ℕ} (h : twoReps n = true) : 2 ≤ a n := by
  unfold twoReps at h
  split at h
  next c d rest hl =>
    have hc : c ∈ (cands n).filter (fun c => goodB n c.1 c.2.1 c.2.2) := by
      rw [hl]; exact List.mem_cons_self
    have hd : d ∈ (cands n).filter (fun c => goodB n c.1 c.2.1 c.2.2) := by
      rw [hl]; exact List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨hc1, hcm⟩ := mem_reps_of_goodB (List.mem_filter.mp hc).2
    obtain ⟨hd1, hdm⟩ := mem_reps_of_goodB (List.mem_filter.mp hd).2
    have hne : (c.1, c.1 + c.2.1 - n) ≠ (d.1, d.1 + d.2.1 - n) := by
      intro heq
      have hu : c.1 = d.1 := (Prod.mk.inj heq).1
      have hy : c.1 + c.2.1 - n = d.1 + d.2.1 - n := (Prod.mk.inj heq).2
      have hv : c.2.1 = d.2.1 := by omega
      simp [hu, hv] at h
    exact Finset.one_lt_card.mpr ⟨_, hcm, _, hdm, hne⟩
  next => exact absurd h (by simp)

/-- The six exceptional values of the conjecture, as a Boolean test. -/
def exceptionalB (n : ℕ) : Bool :=
  n == 11 || n == 12 || n == 14 || n == 18 || n == 24 || n == 54

/-- Check `twoReps k` for every non-exceptional `k ∈ [s, s + L)`. -/
def checkRange : ℕ → ℕ → Bool
  | _, 0 => true
  | s, L + 1 => (exceptionalB s || twoReps s) && checkRange (s + 1) L

/-- Soundness of `checkRange`. -/
theorem twoReps_of_checkRange {s L : ℕ} (h : checkRange s L = true) {k : ℕ}
    (hs : s ≤ k) (hk : k < s + L) : exceptionalB k = true ∨ twoReps k = true := by
  induction L generalizing s with
  | zero => omega
  | succ L ih =>
    simp only [checkRange, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases Nat.eq_or_lt_of_le hs with hks | hks
    · subst hks; exact h.1
    · exact ih h.2 (by omega) (by omega)

/-- The finite search: every non-exceptional `n ∈ [11, 2914)` passes `twoReps`. -/
theorem checkRange_small : checkRange 11 2903 = true := by
  decide +kernel


/-! ## The conjecture -/

/-- The six exceptional values: `a n = 1` for `n ∈ {11, 12, 14, 18, 24, 54}`
(exhaustive kernel evaluation of `reps n`). -/
theorem a_eq_one_of_exceptional :
    a 11 = 1 ∧ a 12 = 1 ∧ a 14 = 1 ∧ a 18 = 1 ∧ a 24 = 1 ∧ a 54 = 1 := by
  decide +kernel

/-- For every `n > 10` outside `{11, 12, 14, 18, 24, 54}`, `a n ≥ 2`. -/
theorem two_le_a {n : ℕ} (hn : 10 < n) (hE : n ∉ ({11, 12, 14, 18, 24, 54} : Finset ℕ)) :
    2 ≤ a n := by
  rcases le_or_gt 2914 n with hbig | hsmall
  · exact two_le_a_of_large hbig
  · rcases twoReps_of_checkRange checkRange_small (k := n) (by omega) (by omega) with h | h
    · exfalso
      apply hE
      simp only [exceptionalB, Bool.or_eq_true, beq_iff_eq] at h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact two_le_a_of_twoReps h

/-- **Sun's conjecture, part (i)** (A271719, Zhi-Wei Sun, Apr 12 2016): `a(n) > 0`
for every `n > 10`. -/
theorem a_pos {n : ℕ} (hn : 10 < n) : 0 < a n := by
  by_cases hE : n ∈ ({11, 12, 14, 18, 24, 54} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    obtain ⟨h11, h12, h14, h18, h24, h54⟩ := a_eq_one_of_exceptional
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have h2 := two_le_a hn hE
    omega

/-- **Sun's conjecture** (A271719, Zhi-Wei Sun, Apr 12 2016).

Verbatim: "Conjecture: a(n) > 0 for all n > 10, and a(n) = 1 only for
n = 11, 12, 14, 18, 24, 54."

Here `a n` counts the ordered ways to write `n = x + y + z` with `x ≥ y > 0`,
`z > 0`, `gcd(x, y, z) = 1` and `x² + (2y + z)²` a perfect square.  The
statement is: for every `n > 10`, `a n > 0`, and `a n = 1` holds exactly for
`n ∈ {11, 12, 14, 18, 24, 54}` (the "only for" of the source, together with
the fact that these six values do have `a n = 1`, as the DATA line shows). -/
theorem a271719_conjecture (n : ℕ) (hn : 10 < n) :
    0 < a n ∧ (a n = 1 ↔ n ∈ ({11, 12, 14, 18, 24, 54} : Finset ℕ)) := by
  refine ⟨a_pos hn, ⟨fun h1 => ?_, fun hE => ?_⟩⟩
  · by_contra hE
    have h2 := two_le_a hn hE
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    obtain ⟨h11, h12, h14, h18, h24, h54⟩ := a_eq_one_of_exceptional
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h11, h12, h14, h18, h24, h54]

/-- The hypothesis `10 < n` is load-bearing: `a 10 = 0`. -/
example : a 10 = 0 := by decide +kernel

end Candidates.A271719GcdPerfectSquare
