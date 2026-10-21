/-
# A274010 — Oudra: the Stechkin function is `tau(n) + tau(n-1) - 2`

## OEIS source (retrieved with `oeis show A274010`, 2026-10-21)

```
NAME:     Boris Stechkin function: a(n) is the number of m with 2 <= m <= n
          and floor(n(m-1)/m) divisible by m-1.
TERMS:    0,0,1,2,3,3,4,4,4,5,5,4,6,6,4,6,7,5,6,6,6,8,6,4,8,9,5,6,8,6,8,8,6,
          8,6,6,11,9,4,6,10,8,8,8,6,10,8,4,10,11,7,8,8,6,8,10,10,10,6,4,12,12,
          4,8,11,9,10,8,6,8,10,8,12,12,4,8,10,8,10,8,10   (offset 0)
FORMULA (the conjecture):
  Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2. - _Ridouane Oudra_, Feb 28 2020
COMMENT:
  Stechkin proves: n-1 is prime iff a(n) = A000005(n). ...
```

## Status

Triage: "open" in the sense that the entry labels the formula a conjecture
and gives no proof; no proof was located in the literature.  The entry's
Maple program already counts `m` with `n = k*m + j`, `j ∈ {0, 1}`, which is
the content of the key lemma below.  Computationally checked for
`2 ≤ n ≤ 3000` (python, against the listed terms for `0 ≤ n ≤ 80`).
This module proves the conjecture without `sorry`
(`stechkin_eq_tau_add_tau_sub_two`).

## Proof

Write `n = q*m + r`, `0 ≤ r < m`.  Then `floor(n(m-1)/m) = q(m-1) + (r - 1)`
(truncated subtraction), and `0 ≤ r - 1 < m - 1`, so `(m-1)` divides the floor
iff `r ≤ 1`, i.e. iff `m ∣ n` or `m ∣ n - 1`.  For `m ≥ 2` these are disjoint,
so `a(n) = (tau(n) - 1) + (tau(n-1) - 1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A274010FloorStechkinFunction

/-- The Stechkin function (OEIS A274010): `a(n)` is the number of `m` with
`2 ≤ m ≤ n` such that `m - 1` divides `floor(n(m-1)/m)`.  Natural division is
the floor; `m - 1` is never truncated since `2 ≤ m`. -/
def stechkin (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter (fun m => (m - 1) ∣ n * (m - 1) / m)).card

example : stechkin 0 = 0 := by decide
example : stechkin 1 = 0 := by decide
example : stechkin 2 = 1 := by decide
example : stechkin 3 = 2 := by decide
example : stechkin 4 = 3 := by decide
example : stechkin 5 = 3 := by decide
example : stechkin 12 = 6 := by decide
example : stechkin 36 = 11 := by decide

/-- Floor formula: for `1 ≤ k`, `floor(n*k/(k+1)) = q*k + (r - 1)` where
`q = n / (k+1)`, `r = n % (k+1)`, and `r - 1` is truncated subtraction. -/
theorem mul_div_succ_eq (n k : ℕ) (hk : 1 ≤ k) :
    n * k / (k + 1) = n / (k + 1) * k + (n % (k + 1) - 1) := by
  have hdm := Nat.div_add_mod n (k + 1)
  have hr := Nat.mod_lt n (show 0 < k + 1 by omega)
  set q := n / (k + 1)
  set r := n % (k + 1)
  clear_value q r
  apply Nat.div_eq_of_lt_le
  · rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0] at hdm ⊢
      rw [← hdm]; simp only [Nat.zero_sub, add_zero]; nlinarith
    · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [← hdm]; simp only [Nat.add_sub_cancel]; nlinarith
  · rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0] at hdm ⊢
      rw [← hdm]; simp only [Nat.zero_sub, add_zero]; nlinarith
    · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [← hdm]; simp only [Nat.add_sub_cancel]; nlinarith

/-- Key lemma: for `2 ≤ m`, `(m-1) ∣ floor(n(m-1)/m)` iff `n mod m ∈ {0, 1}`. -/
theorem dvd_floor_iff (n m : ℕ) (hm : 2 ≤ m) :
    (m - 1) ∣ n * (m - 1) / m ↔ n % m = 0 ∨ n % m = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  rw [Nat.add_sub_cancel, mul_div_succ_eq n k hk, Nat.dvd_add_right (dvd_mul_left k _)]
  have hr := Nat.mod_lt n (show 0 < k + 1 by omega)
  constructor
  · intro hd
    have hlt : n % (k + 1) - 1 < k := by omega
    have hz : n % (k + 1) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · intro h
    have hz : n % (k + 1) - 1 = 0 := by omega
    rw [hz]
    exact dvd_zero k

/-- For `2 ≤ m` and `1 ≤ n`, `n mod m = 1` iff `m ∣ n - 1`. -/
theorem mod_eq_one_iff_dvd_sub_one (n m : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    n % m = 1 ↔ m ∣ n - 1 := by
  rw [← Nat.modEq_iff_dvd' hn, Nat.ModEq, Nat.mod_eq_of_lt (show 1 < m by omega)]
  exact eq_comm

/-- The counted set is the disjoint union of the divisors `≥ 2` of `n` and
of `n - 1`. -/
theorem filter_eq_union (n : ℕ) (hn : 2 ≤ n) :
    (Finset.Icc 2 n).filter (fun m => (m - 1) ∣ n * (m - 1) / m) =
      n.divisors.erase 1 ∪ (n - 1).divisors.erase 1 := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hm2, hmn⟩, hd⟩
    rcases (dvd_floor_iff n m hm2).1 hd with h0 | h1
    · exact Or.inl ⟨by omega, Nat.dvd_of_mod_eq_zero h0, by omega⟩
    · exact Or.inr ⟨by omega, (mod_eq_one_iff_dvd_sub_one n m hm2 (by omega)).1 h1, by omega⟩
  · rintro (⟨hm1, hdvd, hn0⟩ | ⟨hm1, hdvd, hn0⟩)
    · have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hdvd; omega
      have hm2 : 2 ≤ m := by omega
      exact ⟨⟨hm2, Nat.le_of_dvd (by omega) hdvd⟩,
        (dvd_floor_iff n m hm2).2 (Or.inl (Nat.mod_eq_zero_of_dvd hdvd))⟩
    · have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hdvd; omega
      have hm2 : 2 ≤ m := by omega
      exact ⟨⟨hm2, (Nat.le_of_dvd (by omega) hdvd).trans (Nat.sub_le n 1)⟩,
        (dvd_floor_iff n m hm2).2
          (Or.inr ((mod_eq_one_iff_dvd_sub_one n m hm2 (by omega)).2 hdvd))⟩

/-- No `m ≥ 2` divides both `n` and `n - 1` (for `1 ≤ n`). -/
theorem disjoint_divisors_erase (n : ℕ) (hn : 1 ≤ n) :
    Disjoint (n.divisors.erase 1) ((n - 1).divisors.erase 1) := by
  rw [Finset.disjoint_left]
  intro m hA hB
  simp only [Finset.mem_erase, Nat.mem_divisors] at hA hB
  have hsub : m ∣ n - (n - 1) := Nat.dvd_sub hA.2.1 hB.2.1
  rw [show n - (n - 1) = 1 by omega, Nat.dvd_one] at hsub
  exact hA.1 hsub

/-- Cancellation-free form of Oudra's formula: for `2 ≤ n`,
`a(n) + 2 = tau(n) + tau(n-1)`. -/
theorem stechkin_add_two (n : ℕ) (hn : 2 ≤ n) :
    stechkin n + 2 = n.divisors.card + (n - 1).divisors.card := by
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.2 (by omega)
  have h2 : 1 ∈ (n - 1).divisors := Nat.one_mem_divisors.2 (by omega)
  have hA := Finset.card_erase_add_one h1
  have hB := Finset.card_erase_add_one h2
  rw [stechkin, filter_eq_union n hn,
    Finset.card_union_of_disjoint (disjoint_divisors_erase n (by omega))]
  omega

/-- **Oudra's conjecture (A274010, Ridouane Oudra, Feb 28 2020).**

Verbatim: "Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2."  Here `a` is
the Stechkin function `stechkin` and `tau = Nat.divisors · |>.card`.  The
difference is taken in `ℤ`; the `n - 1` inside `tau` is guarded by `2 ≤ n`. -/
theorem stechkin_eq_tau_add_tau_sub_two (n : ℕ) (hn : 2 ≤ n) :
    (stechkin n : ℤ) = (n.divisors.card : ℤ) + ((n - 1).divisors.card : ℤ) - 2 := by
  have h := stechkin_add_two n hn
  omega

/-- A natural number is prime iff it has exactly two divisors. -/
theorem prime_iff_card_divisors_eq_two (p : ℕ) : p.Prime ↔ p.divisors.card = 2 := by
  constructor
  · intro pp
    rw [pp.divisors, Finset.card_pair pp.one_lt.ne]
  · intro hcard
    have hp0 : p ≠ 0 := by rintro rfl; simp at hcard
    have hp1 : p ≠ 1 := by rintro rfl; simp at hcard
    have hsub : ({1, p} : Finset ℕ) ⊆ p.divisors := by
      intro d hd
      rcases Finset.mem_insert.1 hd with rfl | hd'
      · exact Nat.one_mem_divisors.2 hp0
      · rw [Finset.mem_singleton.1 hd']
        exact Nat.mem_divisors_self p hp0
    have hpair : ({1, p} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hp1)
    have heq : ({1, p} : Finset ℕ) = p.divisors :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    refine Nat.prime_def.2 ⟨by omega, fun m hm => ?_⟩
    have hmem : m ∈ ({1, p} : Finset ℕ) := heq ▸ Nat.mem_divisors.2 ⟨hm, hp0⟩
    simpa using hmem

/-- **Stechkin's criterion (A274010 comment).** For `2 ≤ n`, `n - 1` is prime
iff `a(n) = tau(n)`.  Derived here from Oudra's formula. -/
theorem prime_sub_one_iff_stechkin_eq (n : ℕ) (hn : 2 ≤ n) :
    (n - 1).Prime ↔ stechkin n = n.divisors.card := by
  rw [prime_iff_card_divisors_eq_two]
  have h := stechkin_add_two n hn
  omega

end Candidates.A274010FloorStechkinFunction
