/-
# A008590 — Ratajczak: parity of the `gcd_2` / `lcd_2` sums characterizes multiples of 8

## OEIS source (retrieved with `oeis show A008590`, 2026-10-21)

```
NAME:     Multiples of 8.
TERMS:    0,8,16,24,32,40,48,56,64,72,80,88,96,104,112,120,128,136,144,152,...
COMMENT (the conjecture, From _Lechoslaw Ratajczak_, Sep 03 2017):
  Conjecture: let gcd_2(b,c) be the second greatest common divisor and
  lcd_2(b,c) be the second least common divisor of not coprime integers b and
  c. Consecutive elements of this sequence (for a(n) > 0) are consecutive
  integers m for which both Sum_{k=1..m, gcd(k,m)<>1} gcd_2(k,m) and
  Sum_{k=1..m, gcd(k,m) <>1} lcd_2(k,m) are even numbers.
  a(1) = 8 because 1+2+1+4 = 8 (8 is even) and 2+2+2+2 = 8 (8 is even).
  a(2) = 16 because 1+2+1+4+1+2+1+8 = 20 (20 is even) and
    2+2+2+2+2+2+2+2 = 16 (16 is even).
  a(3) = 24 because 1+1+2+3+4+1+1+6+1+1+4+3+2+1+1+12 = 44 (44 is even) and
    2+3+2+2+2+3+2+2+2+3+2+2+2+3+2+2 = 36 (36 is even).
  The conjecture was checked for 5*10^4 consecutive integers.
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell; the entry reports a check to `5*10^4`).  Re-validated here by a
bounded Python sweep for `2 ≤ m ≤ 20000` (no exceptions).  This module proves
it outright (`ratajczak_conjecture`).

## Reading of the conjecture

"Consecutive elements ... (for a(n) > 0) are consecutive integers m for which
both sums are even" says: the positive integers `m` with both sums even are
exactly the positive multiples of `8`.  At `m = 1` both sums are empty (`0`,
even) while `8 ∤ 1`, so the claim is stated for `2 ≤ m`; the sanity layer
records the `m = 1` exception, which shows the guard is load-bearing.

## Proof idea

With `g = gcd(k,m) > 1`, `lcd_2(k,m) = minFac g` and `gcd_2(k,m) = g / minFac g`.
`minFac g` is odd iff `g` is odd, and `g / minFac g` is odd iff `4 ∤ g`.  Hence,
mod 2, the `lcd_2` sum is `(m - φ m) - #{k : 2 ∣ gcd k m}` and the `gcd_2` sum
is `(m - φ m) - #{k : 4 ∣ gcd k m}`, where `#{k ≤ m : d ∣ gcd k m}` is `m / d`
if `d ∣ m` and `0` otherwise.  Since `φ m` is even for `m > 2`, both are even
iff `8 ∣ m` (the case `m = 2` has `φ 2 = 1` and is handled by the same counts).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A008590GcdSecondLargest

/-! ## Definition layer -/

/-- The common positive divisors of `k` and `m` (for `m ≠ 0`): the divisors of
`m` that also divide `k`. -/
def commonDivisors (k m : ℕ) : Finset ℕ := m.divisors.filter (· ∣ k)

/-- `gcd_2(k, m)`, the second greatest common divisor of `k` and `m`: the
largest common divisor after the greatest one is removed.  (Junk value `0` when
`k` and `m` are coprime; the conjecture only sums over non-coprime `k`.) -/
def gcd₂ (k m : ℕ) : ℕ :=
  ((commonDivisors k m).erase ((commonDivisors k m).sup id)).sup id

/-- `lcd_2(k, m)`, the second least common divisor of `k` and `m`: the least
common divisor is always `1`, so this is the smallest common divisor exceeding
`1`.  (Junk value `0` when there is none, i.e. `k` and `m` coprime.) -/
def lcd₂ (k m : ℕ) : ℕ :=
  let T := (commonDivisors k m).filter (1 < ·)
  if h : T.Nonempty then T.min' h else 0

/-- `Sum_{k=1..m, gcd(k,m) <> 1} gcd_2(k,m)`. -/
def gcd₂Sum (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), gcd₂ k m

/-- `Sum_{k=1..m, gcd(k,m) <> 1} lcd_2(k,m)`. -/
def lcd₂Sum (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), lcd₂ k m

-- Ground truth: the worked examples of the entry (`a(1)`, `a(2)`, `a(3)`).
example : gcd₂Sum 8 = 8 := by decide
example : lcd₂Sum 8 = 8 := by decide
example : gcd₂Sum 16 = 20 := by decide
example : lcd₂Sum 16 = 16 := by decide
example : gcd₂Sum 24 = 44 := by decide
example : lcd₂Sum 24 = 36 := by decide
-- Individual values: `gcd_2(6, 24) = 3`, `lcd_2(6, 24) = 2`, `lcd_2(9, 24) = 3`.
example : gcd₂ 6 24 = 3 ∧ lcd₂ 6 24 = 2 ∧ lcd₂ 9 24 = 3 := by decide
-- Ground truth against the DATA line: in `[1, 24]` the `m` with both sums even
-- are `1` (empty sums) and the first positive terms `8, 16, 24`.
example : (Finset.Icc 1 24).filter (fun m => Even (gcd₂Sum m) ∧ Even (lcd₂Sum m)) =
    {1, 8, 16, 24} := by decide

/-! ## Bridge to `Nat.minFac` -/

/-- For `m ≠ 0`, the common divisors of `k` and `m` are the divisors of `gcd k m`. -/
theorem mem_commonDivisors {k m d : ℕ} (hm : m ≠ 0) :
    d ∈ commonDivisors k m ↔ d ∣ Nat.gcd k m := by
  simp only [commonDivisors, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  tauto

/-- For `m ≠ 0`, the greatest common divisor in the `commonDivisors` sense is `gcd k m`. -/
theorem sup_commonDivisors {k m : ℕ} (hm : m ≠ 0) :
    (commonDivisors k m).sup id = Nat.gcd k m := by
  have hg : 0 < Nat.gcd k m := Nat.gcd_pos_of_pos_right k (Nat.pos_of_ne_zero hm)
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact Nat.le_of_dvd hg ((mem_commonDivisors hm).1 hd)
  · exact Finset.le_sup (f := id) ((mem_commonDivisors hm).2 dvd_rfl)

/-- For `m ≠ 0` and `gcd k m ≠ 1`, `gcd_2(k, m) = g / minFac g` with `g = gcd k m`. -/
theorem gcd₂_eq {k m : ℕ} (hm : m ≠ 0) (hk : Nat.gcd k m ≠ 1) :
    gcd₂ k m = Nat.gcd k m / (Nat.gcd k m).minFac := by
  set g := Nat.gcd k m with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_right k (Nat.pos_of_ne_zero hm)
  have hp : g.minFac.Prime := Nat.minFac_prime hk
  have hp1 : 1 < g.minFac := hp.one_lt
  have hlt : g / g.minFac < g := Nat.div_lt_self hg hp1
  unfold gcd₂
  rw [sup_commonDivisors hm]
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    rw [Finset.mem_erase, mem_commonDivisors hm, ← hgdef] at hd
    obtain ⟨hne, e, he⟩ := hd
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [mul_zero] at he
      omega
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hne (by rw [he, mul_one])
    have he2 : 2 ≤ e := by omega
    have hpe : g.minFac ≤ e := Nat.minFac_le_of_dvd he2 ⟨d, by rw [he, mul_comm]⟩
    rw [Nat.le_div_iff_mul_le hp.pos]
    calc d * g.minFac ≤ d * e := Nat.mul_le_mul_left d hpe
      _ = g := he.symm
  · apply Finset.le_sup (f := id)
    rw [Finset.mem_erase, mem_commonDivisors hm]
    exact ⟨hlt.ne, Nat.div_dvd_of_dvd (Nat.minFac_dvd g)⟩

/-- For `m ≠ 0` and `gcd k m ≠ 1`, `lcd_2(k, m) = minFac (gcd k m)`. -/
theorem lcd₂_eq {k m : ℕ} (hm : m ≠ 0) (hk : Nat.gcd k m ≠ 1) :
    lcd₂ k m = (Nat.gcd k m).minFac := by
  set g := Nat.gcd k m
  have hp : g.minFac.Prime := Nat.minFac_prime hk
  have hmem : g.minFac ∈ (commonDivisors k m).filter (1 < ·) := by
    rw [Finset.mem_filter, mem_commonDivisors hm]
    exact ⟨Nat.minFac_dvd g, hp.one_lt⟩
  have hne : ((commonDivisors k m).filter (1 < ·)).Nonempty := ⟨_, hmem⟩
  unfold lcd₂
  simp only [dif_pos hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · apply Finset.le_min'
    intro d hd
    rw [Finset.mem_filter, mem_commonDivisors hm] at hd
    exact Nat.minFac_le_of_dvd hd.2 hd.1

/-- `minFac g` is odd iff `g` is odd (including `g = 0, 1`). -/
theorem odd_minFac_iff (g : ℕ) : Odd g.minFac ↔ Odd g := by
  by_cases h2 : 2 ∣ g
  · rw [(Nat.minFac_eq_two_iff g).2 h2]
    simp only [Nat.odd_iff]
    omega
  · have hodd : Odd g := Nat.odd_iff.2 (by omega)
    simp only [hodd, iff_true]
    by_cases h1 : g = 1
    · subst h1
      simp
    · have hdvd : g.minFac ∣ g := Nat.minFac_dvd g
      exact Nat.odd_iff.2 (by
        rcases Nat.even_or_odd g.minFac with he | ho
        · exact absurd ((even_iff_two_dvd.1 he).trans hdvd) h2
        · exact Nat.odd_iff.1 ho)

/-- `g / minFac g` is odd iff `4 ∤ g` (including `g = 0, 1`). -/
theorem odd_div_minFac_iff (g : ℕ) : Odd (g / g.minFac) ↔ ¬ 4 ∣ g := by
  by_cases h2 : 2 ∣ g
  · rw [(Nat.minFac_eq_two_iff g).2 h2, Nat.odd_iff]
    omega
  · have hdvd : g / g.minFac ∣ g := Nat.div_dvd_of_dvd (Nat.minFac_dvd g)
    have hodd : Odd (g / g.minFac) := by
      rcases Nat.even_or_odd (g / g.minFac) with he | ho
      · exact absurd ((even_iff_two_dvd.1 he).trans hdvd) h2
      · exact ho
    simp only [hodd, true_iff]
    omega

/-! ## Counting -/

/-- The index set `{k ∈ [1, m] : gcd(k, m) ≠ 1}` of both sums. -/
def support (m : ℕ) : Finset ℕ := (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1)

/-- `#{k ∈ [1, m] : gcd(k, m) ≠ 1} + φ(m) = m`. -/
theorem card_support_add_totient (m : ℕ) : (support m).card + m.totient = m := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 m) (p := fun k => Nat.gcd k m ≠ 1)
  have ht : ((Finset.Icc 1 m).filter (fun k => ¬ Nat.gcd k m ≠ 1)).card = m.totient := by
    rw [← Nat.filter_coprime_Ico_eq_totient m 1]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, not_not, Nat.Coprime,
      Nat.gcd_comm m k]
    omega
  rw [support, ← ht, h]
  simp

/-- For `d ≥ 2`, the number of `k ∈ [1, m]` with `gcd(k, m) ≠ 1` and `d ∣ gcd(k, m)`
is `m / d` if `d ∣ m` and `0` otherwise. -/
theorem card_support_filter_dvd (m d : ℕ) (hd : 2 ≤ d) :
    ((support m).filter (fun k => d ∣ Nat.gcd k m)).card = if d ∣ m then m / d else 0 := by
  split_ifs with hdm
  · rw [← Nat.Ioc_filter_dvd_card_eq_div m d]
    congr 1
    ext k
    simp only [support, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hk, -⟩, hdk, -⟩
      exact ⟨by omega, hdk⟩
    · rintro ⟨hk, hdk⟩
      refine ⟨⟨by omega, ?_⟩, hdk, hdm⟩
      intro h1
      have hd1 : d ∣ 1 := h1 ▸ Nat.dvd_gcd hdk hdm
      have hdle : d ≤ 1 := Nat.le_of_dvd one_pos hd1
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hdk
    exact hdm (hdk.trans (Nat.gcd_dvd_right k m))

/-! ## The conjecture -/

/-- **Ratajczak's conjecture (A008590, Lechoslaw Ratajczak, Sep 03 2017).**

For `m ≥ 2`, both `Sum_{k=1..m, gcd(k,m) <> 1} gcd_2(k,m)` and
`Sum_{k=1..m, gcd(k,m) <> 1} lcd_2(k,m)` are even if and only if `8 ∣ m`,
where `gcd_2` is the second greatest and `lcd_2` the second least common
divisor.  The guard `2 ≤ m` excludes `m = 1`, where both sums are empty. -/
theorem ratajczak_conjecture (m : ℕ) (hm : 2 ≤ m) :
    (Even (gcd₂Sum m) ∧ Even (lcd₂Sum m)) ↔ 8 ∣ m := by
  have hm0 : m ≠ 0 := by omega
  have hgcd : ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), gcd₂ k m =
      ∑ k ∈ support m, Nat.gcd k m / (Nat.gcd k m).minFac := by
    apply Finset.sum_congr rfl
    intro k hk
    exact gcd₂_eq hm0 (Finset.mem_filter.1 hk).2
  have hlcd : ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), lcd₂ k m =
      ∑ k ∈ support m, (Nat.gcd k m).minFac := by
    apply Finset.sum_congr rfl
    intro k hk
    exact lcd₂_eq hm0 (Finset.mem_filter.1 hk).2
  rw [gcd₂Sum, lcd₂Sum, hgcd, hlcd, Finset.even_sum_iff_even_card_odd,
    Finset.even_sum_iff_even_card_odd]
  simp only [odd_div_minFac_iff, odd_minFac_iff]
  -- parity counts
  have hA := card_support_add_totient m
  have hx := Finset.card_filter_add_card_filter_not
    (s := support m) (p := fun k => Odd (Nat.gcd k m))
  have hz := Finset.card_filter_add_card_filter_not
    (s := support m) (p := fun k => ¬ 4 ∣ Nat.gcd k m)
  have hy2 : ((support m).filter (fun k => ¬ Odd (Nat.gcd k m))).card =
      if 2 ∣ m then m / 2 else 0 := by
    rw [← card_support_filter_dvd m 2 le_rfl]
    congr 1
    apply Finset.filter_congr
    intro k _
    rw [Nat.not_odd_iff_even, even_iff_two_dvd]
  have hw : ((support m).filter (fun k => ¬ ¬ 4 ∣ Nat.gcd k m)).card =
      if 4 ∣ m then m / 4 else 0 := by
    rw [← card_support_filter_dvd m 4 (by norm_num)]
    congr 1
    apply Finset.filter_congr
    intro k _
    rw [not_not]
  have hφ : 2 < m → m.totient % 2 = 0 := fun h => Nat.even_iff.1 (Nat.totient_even h)
  have hφ2 : m = 2 → m.totient = 1 := by
    rintro rfl
    rfl
  simp only [Nat.even_iff]
  split_ifs at hy2 hw <;> omega

/-! ## Sanity layer -/

-- Satisfiability: the hypothesis `2 ≤ m` and the conclusion are jointly met
-- at `m = 8`, and the theorem is not vacuous at a non-multiple (`m = 12`).
example : Even (gcd₂Sum 8) ∧ Even (lcd₂Sum 8) :=
  (ratajczak_conjecture 8 (by norm_num)).2 ⟨1, rfl⟩
example : ¬ (Even (gcd₂Sum 12) ∧ Even (lcd₂Sum 12)) := by
  rw [ratajczak_conjecture 12 (by norm_num)]
  decide

-- The guard `2 ≤ m` is load-bearing: at `m = 1` both sums are `0` but `8 ∤ 1`.
example : (Even (gcd₂Sum 1) ∧ Even (lcd₂Sum 1)) ∧ ¬ 8 ∣ 1 := by decide

end Candidates.A008590GcdSecondLargest
