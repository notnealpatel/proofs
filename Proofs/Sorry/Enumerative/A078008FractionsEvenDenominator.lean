/-
# A078008 — Adamson: even denominators in the Farey (Stern–Brocot) mediant rows

## OEIS source (retrieved with `oeis show A078008`, 2026-10-21)

```
NAME:     Expansion of (1 - x)/((1 + x)*(1 - 2*x)).
TERMS:    1,0,2,2,6,10,22,42,86,170,342,682,1366,2730,5462,10922,21846,43690,
          87382,174762,349526,699050,1398102,2796202,5592406,11184810,...
FORMULA:  a(n) = (2^n + 2*(-1)^n)/3. - Mario Catalani, Aug 29 2003
FORMULA:  a(n) = a(n-1) + 2a(n-2) with a(0) = 1 and a(1) = 0. (Euler, via Rickey)
COMMENT (the conjecture):
  Conjecture: a(n) = the number of fractions in the infinite Farey row of 2^n
  terms with even denominators. Compare the Salamin & Gosper item in the Beeler
  et al. link. - _Gary W. Adamson_, Oct 27 2003
```

## Interpretation

The "infinite Farey row of `2^n` terms" is read as the Stern–Brocot / Farey
mediant row: start from `0/1, 1/1`; at each step insert the mediant
`(a+c)/(b+d)` between every pair of neighbours `a/b, c/d`.  The `n`-th row
consists of the `2^n` mediants inserted at step `n+1` (row 0 is `1/2`, row 1
is `1/3, 2/3`, row 2 is `1/4, 2/5, 3/5, 3/4`, ...).  This is the convention
under which the triage matched the data (even-denominator counts
`1,0,2,2,6,10,22,42,86,170,342` for `n = 0..10`); this module extends the
check to `n = 19` by computation and then proves it for all `n`.

Fractions are counted as rationals (`ℚ`, lowest terms): the mediant pairs are
shown to be coprime, so the pair denominator equals `Rat.den`.

## Status

Triage: open (no proof in the entry or literature found by triage; the
underlying fact — Stern's diatomic `s(k)` is even iff `3 ∣ k` — is classical).
This module proves the conjecture in full.

## Proof outline

Only the parities of denominators of neighbours matter.  Let `x(L)` be the
number of neighbouring pairs in the list `L` with both denominators odd and
`y(L)` the number of pairs with denominators of different parity.  No two
neighbours ever both have even denominators.  Inserting mediants gives
`x' = y`, `y' = 2x + y`, and the even-denominator mediants of `L` are exactly
those coming from odd/odd pairs, so the count is `x`.  From `x₀ = 1, y₀ = 0`
we get `x(n+2) = x(n+1) + 2 x(n)`, Euler's recursion for A078008.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A078008FractionsEvenDenominator

/-! ## Definition layer -/

/-- A078008 by Euler's recursion `a(n) = a(n-1) + 2 a(n-2)`, `a(0) = 1`,
`a(1) = 0`, i.e. the coefficients of `(1 - x)/((1 + x)(1 - 2x))
= (1 - x)/(1 - x - 2x^2)`. -/
def a078008 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => a078008 (n + 1) + 2 * a078008 n

example : (List.range 12).map a078008 = [1, 0, 2, 2, 6, 10, 22, 42, 86, 170, 342, 682] := by
  decide

/-- The list of mediants of neighbouring fractions of `L`, with fractions
represented as (numerator, denominator) pairs: `a/b, c/d ↦ (a+c)/(b+d)`. -/
def mediants : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: t => (a.1 + b.1, a.2 + b.2) :: mediants (b :: t)
  | _ => []

/-- One Farey/Stern–Brocot refinement step: insert the mediant between every
pair of neighbours. -/
def insertMediants : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: t => a :: (a.1 + b.1, a.2 + b.2) :: insertMediants (b :: t)
  | l => l

/-- The Farey/Stern–Brocot list after `n` refinement steps starting from
`0/1, 1/1` (it has `2^n + 1` entries). -/
def fareyList : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 1), (1, 1)]
  | n + 1 => insertMediants (fareyList n)

/-- The `n`-th mediant row, as (numerator, denominator) pairs: the `2^n`
mediants inserted at refinement step `n + 1`. -/
def mediantRow (n : ℕ) : List (ℕ × ℕ) :=
  mediants (fareyList n)

/-- The `n`-th mediant row as a list of rational numbers. -/
def mediantRowRat (n : ℕ) : List ℚ :=
  (mediantRow n).map fun p => (p.1 : ℚ) / p.2

example : mediantRow 0 = [(1, 2)] := by decide
example : mediantRow 1 = [(1, 3), (2, 3)] := by decide
example : mediantRow 2 = [(1, 4), (2, 5), (3, 5), (3, 4)] := by decide
example : mediantRow 3 = [(1, 5), (2, 7), (3, 8), (3, 7), (4, 7), (5, 8), (5, 7), (4, 5)] := by
  decide
example : (List.range 7).map (fun n => ((mediantRow n).filter fun p => Even p.2).length) =
    [1, 0, 2, 2, 6, 10, 22] := by
  decide

/-! ## Parity bookkeeping -/

/-- Number of neighbouring pairs in `L` whose denominators are both odd. -/
def oddOddCount : List (ℕ × ℕ) → ℕ
  | a :: b :: t => (if a.2 % 2 = 1 ∧ b.2 % 2 = 1 then 1 else 0) + oddOddCount (b :: t)
  | _ => 0

/-- Number of neighbouring pairs in `L` whose denominators have different parity. -/
def mixedCount : List (ℕ × ℕ) → ℕ
  | a :: b :: t => (if a.2 % 2 ≠ b.2 % 2 then 1 else 0) + mixedCount (b :: t)
  | _ => 0

/-- No two neighbours of `L` both have even denominators. -/
def NoEvenEven : List (ℕ × ℕ) → Prop
  | a :: b :: t => ¬(a.2 % 2 = 0 ∧ b.2 % 2 = 0) ∧ NoEvenEven (b :: t)
  | _ => True

/-- Refining a list starting with `b` yields a list starting with `b`. -/
theorem insertMediants_cons (b : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    ∃ r, insertMediants (b :: t) = b :: r := by
  cases t with
  | nil => exact ⟨[], rfl⟩
  | cons c t => exact ⟨_, rfl⟩

/-- If no neighbours are both even, the even-denominator mediants of `L` are
exactly those of odd/odd neighbour pairs. -/
theorem countEven_mediants (a b : ℕ × ℕ) (t : List (ℕ × ℕ))
    (h : NoEvenEven (a :: b :: t)) :
    ((mediants (a :: b :: t)).filter fun p => Even p.2).length =
      oddOddCount (a :: b :: t) := by
  induction t generalizing a b with
  | nil =>
    simp only [NoEvenEven] at h
    simp only [mediants, oddOddCount, List.filter]
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.even_iff, Nat.add_mod]
  | cons c t ih =>
    simp only [NoEvenEven] at h
    have ih' := ih b c h.2
    simp only [mediants, oddOddCount, List.filter] at ih' ⊢
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.even_iff, Nat.add_mod, Nat.add_comm]

/-- After refinement, odd/odd neighbour pairs are exactly one per former mixed pair. -/
theorem oddOddCount_insertMediants (a b : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    oddOddCount (insertMediants (a :: b :: t)) = mixedCount (a :: b :: t) := by
  induction t generalizing a b with
  | nil =>
    simp only [insertMediants, oddOddCount, mixedCount]
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.add_mod]
  | cons c t ih =>
    have ih' := ih b c
    obtain ⟨r, hr⟩ := insertMediants_cons c t
    simp only [insertMediants, hr, oddOddCount, mixedCount] at ih' ⊢
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.add_mod]

/-- After refinement, mixed neighbour pairs are two per former odd/odd pair
plus one per former mixed pair. -/
theorem mixedCount_insertMediants (a b : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    mixedCount (insertMediants (a :: b :: t)) =
      2 * oddOddCount (a :: b :: t) + mixedCount (a :: b :: t) := by
  induction t generalizing a b with
  | nil =>
    simp only [insertMediants, oddOddCount, mixedCount]
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.add_mod]
  | cons c t ih =>
    have ih' := ih b c
    obtain ⟨r, hr⟩ := insertMediants_cons c t
    simp only [insertMediants, hr, oddOddCount, mixedCount] at ih' ⊢
    rcases Nat.mod_two_eq_zero_or_one a.2 with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.2 with hb | hb <;>
      simp_all [Nat.add_mod] <;> omega

/-- Refinement preserves the absence of even/even neighbours. -/
theorem noEvenEven_insertMediants (a b : ℕ × ℕ) (t : List (ℕ × ℕ))
    (h : NoEvenEven (a :: b :: t)) : NoEvenEven (insertMediants (a :: b :: t)) := by
  induction t generalizing a b with
  | nil =>
    simp only [NoEvenEven] at h
    simp only [insertMediants, NoEvenEven, and_true, not_and]
    constructor <;> (intro h1 h2; omega)
  | cons c t ih =>
    simp only [NoEvenEven] at h
    have ih' := ih b c h.2
    have hstep : insertMediants (a :: b :: c :: t) =
        a :: (a.1 + b.1, a.2 + b.2) :: insertMediants (b :: c :: t) := rfl
    obtain ⟨r, hr⟩ := insertMediants_cons b (c :: t)
    rw [hstep, hr]
    rw [hr] at ih'
    refine ⟨?_, ?_, ih'⟩
    · intro h12
      exact h.1 ⟨h12.1, by omega⟩
    · intro h12
      exact h.1 ⟨by omega, h12.2⟩

/-! ## The Farey lists -/

/-- Every Farey list has at least two entries. -/
theorem fareyList_eq_cons (n : ℕ) : ∃ a b t, fareyList n = a :: b :: t := by
  induction n with
  | zero => exact ⟨_, _, _, rfl⟩
  | succ n ih =>
    obtain ⟨a, b, t, h⟩ := ih
    obtain ⟨r, hr⟩ := insertMediants_cons b t
    exact ⟨a, _, _, by rw [fareyList, h, insertMediants]⟩

/-- No two neighbours in a Farey list both have even denominators. -/
theorem noEvenEven_fareyList (n : ℕ) : NoEvenEven (fareyList n) := by
  induction n with
  | zero => simp [fareyList, NoEvenEven]
  | succ n ih =>
    obtain ⟨a, b, t, h⟩ := fareyList_eq_cons n
    rw [fareyList, h]
    rw [h] at ih
    exact noEvenEven_insertMediants a b t ih

/-- The odd/odd and mixed neighbour counts of the Farey lists satisfy
`x(n+1) = y(n)` and `y(n+1) = 2 x(n) + y(n)`. -/
theorem counts_fareyList_succ (n : ℕ) :
    oddOddCount (fareyList (n + 1)) = mixedCount (fareyList n) ∧
      mixedCount (fareyList (n + 1)) =
        2 * oddOddCount (fareyList n) + mixedCount (fareyList n) := by
  obtain ⟨a, b, t, h⟩ := fareyList_eq_cons n
  rw [fareyList, h]
  exact ⟨oddOddCount_insertMediants a b t, mixedCount_insertMediants a b t⟩

/-- The odd/odd neighbour count of the `n`-th Farey list is A078008(n), and
the mixed count is A078008(n+1). -/
theorem counts_fareyList (n : ℕ) :
    oddOddCount (fareyList n) = a078008 n ∧ mixedCount (fareyList n) = a078008 (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hx, hy⟩ := counts_fareyList_succ n
    refine ⟨hx.trans ih.2, ?_⟩
    rw [hy, ih.1, ih.2, a078008]
    ring

/-- **Pair form.** The number of even-denominator (numerator, denominator)
pairs in the `n`-th mediant row is A078008(n). -/
theorem countEven_mediantRow (n : ℕ) :
    ((mediantRow n).filter fun p => Even p.2).length = a078008 n := by
  obtain ⟨a, b, t, h⟩ := fareyList_eq_cons n
  have hne := noEvenEven_fareyList n
  rw [h] at hne
  rw [mediantRow, h, countEven_mediants a b t hne, ← h]
  exact (counts_fareyList n).1

/-! ## Closed form and row length -/

/-- Catalani's closed form, multiplied out: `3 a(n) = 2^n + 2 (-1)^n`. -/
theorem three_mul_a078008 (n : ℕ) : 3 * (a078008 n : ℤ) = 2 ^ n + 2 * (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [a078008]
    | 1, _ => norm_num [a078008]
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      rw [a078008]
      push_cast
      rw [pow_succ, pow_succ, pow_succ, pow_succ]
      rw [pow_succ] at h1
      rw [pow_succ] at h1
      linear_combination h1 + 2 * h0

/-- Catalani's closed form `a(n) = (2^n + 2 (-1)^n)/3` (the division is exact). -/
theorem a078008_eq (n : ℕ) : (a078008 n : ℤ) = (2 ^ n + 2 * (-1) ^ n) / 3 := by
  rw [← three_mul_a078008, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- Refining a list `a :: t` of length `k + 1` gives a list of length `2k + 1`. -/
theorem length_insertMediants (a : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    (insertMediants (a :: t)).length = 2 * t.length + 1 := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih =>
    rw [insertMediants, List.length_cons, List.length_cons, ih b, List.length_cons]
    ring

/-- A list `a :: t` has `t.length` neighbour mediants. -/
theorem length_mediants (a : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    (mediants (a :: t)).length = t.length := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih => rw [mediants, List.length_cons, ih b, List.length_cons]

/-- The `n`-th Farey list is `a :: t` with `t` of length `2^n`. -/
theorem fareyList_eq_cons_length (n : ℕ) : ∃ a t, fareyList n = a :: t ∧ t.length = 2 ^ n := by
  induction n with
  | zero => exact ⟨_, _, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, t, h, hl⟩ := ih
    have hlen := length_insertMediants a t
    cases hr : insertMediants (a :: t) with
    | nil => rw [hr] at hlen; simp at hlen
    | cons a' t' =>
      refine ⟨a', t', by rw [fareyList, h, hr], ?_⟩
      rw [hr, List.length_cons, hl] at hlen
      rw [pow_succ]
      omega

/-- The `n`-th mediant row has `2^n` terms. -/
theorem length_mediantRow (n : ℕ) : (mediantRow n).length = 2 ^ n := by
  obtain ⟨a, t, h, hl⟩ := fareyList_eq_cons_length n
  rw [mediantRow, h, length_mediants, hl]

/-! ## Mediants are in lowest terms -/

/-- Neighbours `a/b, c/d` of `L` satisfy the unimodularity relation `c b = a d + 1`. -/
def AllAdjacent : List (ℕ × ℕ) → Prop
  | a :: b :: t => b.1 * a.2 = a.1 * b.2 + 1 ∧ AllAdjacent (b :: t)
  | _ => True

/-- A mediant of unimodular neighbours is unimodular with each of them. -/
theorem adjacent_mediant (a b : ℕ × ℕ) (h : b.1 * a.2 = a.1 * b.2 + 1) :
    (a.1 + b.1) * a.2 = a.1 * (a.2 + b.2) + 1 ∧ b.1 * (a.2 + b.2) = (a.1 + b.1) * b.2 + 1 := by
  constructor
  · calc (a.1 + b.1) * a.2 = a.1 * a.2 + b.1 * a.2 := by ring
      _ = a.1 * a.2 + (a.1 * b.2 + 1) := by rw [h]
      _ = a.1 * (a.2 + b.2) + 1 := by ring
  · calc b.1 * (a.2 + b.2) = b.1 * a.2 + b.1 * b.2 := by ring
      _ = (a.1 * b.2 + 1) + b.1 * b.2 := by rw [h]
      _ = (a.1 + b.1) * b.2 + 1 := by ring

/-- Refinement preserves unimodularity of neighbours. -/
theorem allAdjacent_insertMediants (a b : ℕ × ℕ) (t : List (ℕ × ℕ))
    (h : AllAdjacent (a :: b :: t)) : AllAdjacent (insertMediants (a :: b :: t)) := by
  induction t generalizing a b with
  | nil =>
    obtain ⟨h1, h2⟩ := adjacent_mediant a b h.1
    exact ⟨h1, h2, trivial⟩
  | cons c t ih =>
    have ih' := ih b c h.2
    have hstep : insertMediants (a :: b :: c :: t) =
        a :: (a.1 + b.1, a.2 + b.2) :: insertMediants (b :: c :: t) := rfl
    obtain ⟨r, hr⟩ := insertMediants_cons b (c :: t)
    rw [hstep, hr]
    rw [hr] at ih'
    obtain ⟨h1, h2⟩ := adjacent_mediant a b h.1
    exact ⟨h1, h2, ih'⟩

/-- Neighbours in every Farey list are unimodular. -/
theorem allAdjacent_fareyList (n : ℕ) : AllAdjacent (fareyList n) := by
  induction n with
  | zero => exact ⟨by norm_num, trivial⟩
  | succ n ih =>
    obtain ⟨a, b, t, h⟩ := fareyList_eq_cons n
    rw [fareyList, h]
    rw [h] at ih
    exact allAdjacent_insertMediants a b t ih

/-- If `p.1 * q = r * p.2 + 1` for some `q, r`, then `p.1` and `p.2` are coprime:
a pair unimodular with some neighbour is in lowest terms. -/
theorem coprime_of_unimodular (p : ℕ × ℕ) (q r : ℕ) (h : p.1 * q = r * p.2 + 1) :
    Nat.Coprime p.1 p.2 := by
  have h1 : Nat.gcd p.1 p.2 ∣ p.1 * q := Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) q
  have h2 : Nat.gcd p.1 p.2 ∣ r * p.2 := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) r
  rw [h] at h1
  exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h2).mp h1)

/-- Every mediant of a unimodular list is in lowest terms with positive denominator. -/
theorem coprime_of_mem_mediants (l : List (ℕ × ℕ)) (hl : AllAdjacent l) (p : ℕ × ℕ)
    (hp : p ∈ mediants l) : Nat.Coprime p.1 p.2 ∧ 0 < p.2 := by
  induction l with
  | nil => simp [mediants] at hp
  | cons a t ih =>
    cases t with
    | nil => simp [mediants] at hp
    | cons b t =>
      rw [mediants, List.mem_cons] at hp
      rcases hp with rfl | hp
      · obtain ⟨h1, -⟩ := adjacent_mediant a b hl.1
        refine ⟨coprime_of_unimodular _ a.2 a.1 h1, ?_⟩
        rcases Nat.eq_zero_or_pos (a.2 + b.2) with h0 | h0
        · have ha : a.2 = 0 := by omega
          have hb : b.2 = 0 := by omega
          have hcontra := hl.1
          rw [ha, hb] at hcontra
          simp at hcontra
        · exact h0
      · exact ih hl.2 hp

/-- For a pair in lowest terms with positive denominator, the denominator of the
corresponding rational number is the pair's denominator. -/
theorem den_div_of_coprime (p : ℕ × ℕ) (hc : Nat.Coprime p.1 p.2) (hpos : 0 < p.2) :
    ((p.1 : ℚ) / p.2).den = p.2 := by
  have h := Rat.den_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by exact_mod_cast hpos)
    (by simpa using hc)
  have hcast : ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ) = (p.1 : ℚ) / p.2 := by push_cast; rfl
  rw [hcast] at h
  exact_mod_cast h

/-! ## The conjecture -/

/-- **Adamson's conjecture (A078008, Gary W. Adamson, Oct 27 2003), proved.**

Verbatim: "Conjecture: a(n) = the number of fractions in the infinite Farey row
of 2^n terms with even denominators."

Here the `n`-th Farey row is `mediantRowRat n`, the `2^n` mediants inserted at
step `n + 1` of the Farey/Stern–Brocot refinement of `0/1, 1/1`
(`length_mediantRow`), counted as rational numbers by their reduced
denominators, and `a(n) = (2^n + 2(-1)^n)/3` is Catalani's closed form of
A078008 (exact division, see `three_mul_a078008`). -/
theorem a078008_fractions_even_denominator (n : ℕ) :
    (((mediantRowRat n).filter fun q => Even q.den).length : ℤ) = (2 ^ n + 2 * (-1) ^ n) / 3 := by
  rw [← a078008_eq, ← countEven_mediantRow, mediantRowRat, List.filter_map, List.length_map]
  congr 2
  apply List.filter_congr
  intro p hp
  obtain ⟨hc, hpos⟩ := coprime_of_mem_mediants _ (allAdjacent_fareyList n) p hp
  simp only [Function.comp_apply, den_div_of_coprime p hc hpos]

end Candidates.A078008FractionsEvenDenominator
