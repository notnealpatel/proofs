/-
# A238977 — Bala: `a(n+3) ≡ 1 (mod n)` iff `gcd(n, 6) = 1`

## OEIS source (retrieved with `oeis show A238977`, 2026-10-21)

```
NAME:     Number of ballot sequences of length n with exactly 2 fixed points.
TERMS:    0,0,1,1,3,8,24,74,246,848,3088,11644,45844,186336,784928,3403128,
          15212744,69802944,328988096,1587831568,7848954928,39651793024,
          204691645824,1078028406176,5790745961568,31687186373888,
          176575788105984,1001061518465984,5771865641210176   (offset 0)
KEYWORDS: nonn,easy
FORMULA (Peter Bala, Oct 05 2021):
  a(n) = (1/3)*( A000085(n) - A000085(n-3) ) for n >= 3.
  Conjecture: a(n+3) ==  1 (mod n) iff n is coprime to 2 and 3, that is,
  iff n is a term of A007310. (End)
```

## Status

Triage: open (no proof found in the entry or the literature; one web search).
The forward direction also follows from the known congruence
`t(n+m) ≡ t(n) (mod m)` for odd `m` (cited via J. S. Kim, arXiv:0902.4311).
This file proves the full equivalence.

## Fidelity

`a` is defined by Bala's formula (stated in the entry for `n ≥ 3`) together
with the listed initial terms `a(0) = a(1) = 0`, `a(2) = 1`; the ballot-sequence
interpretation of the NAME is not formalized.  The definition is checked
against all 29 listed terms, and `three_mul_a_add` shows that the truncated
`ℕ` subtraction and division in the formula are exact.

## Proof outline

1. `t(m) = ∑_k C(m, 2k) (2k-1)!!` (`invol_eq_S`).
2. For odd `n` and `k ≥ 1`, `n ∣ C(n, 2k) (2k-1)!!`, because
   `n ∣ C(n, 2k) gcd(n, 2k)` and the odd number `gcd(n, 2k) ≤ k` divides
   `(2k-1)!!`; hence `t(n) ≡ 1 (mod n)` for odd `n` (`invol_modEq_one`).
3. `t(n+3) = (2n+4) t(n) + n(n+3) t(n-1)`, so for odd `n`,
   `3 (a(n+3) - 1) = n Q` with `Q = 2 + (2n+3) u + (n+3) t(n-1)`.
4. If `gcd(n, 6) = 1` then `n ∣ a(n+3) - 1`.  If `n` is even, `a(n+3)` is even.
   If `3 ∣ n` (and `n` odd) then `Q ≡ 2 (mod 3)`, so `n ∤ a(n+3) - 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A238977InvolutionBalaFormula

open Finset

/-- The involution numbers `t(n)` (OEIS A000085):
`t(0) = t(1) = 1`, `t(n+2) = t(n+1) + (n+1) * t(n)`. -/
def invol : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => invol (n + 1) + (n + 1) * invol n

/-- A238977 through Bala's formula: `a(n) = (t(n) - t(n-3)) / 3` for `n ≥ 3`,
with the listed initial terms `a(0) = a(1) = 0`, `a(2) = 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => (invol (n + 3) - invol n) / 3

example : (List.range 10).map invol = [1, 1, 2, 4, 10, 26, 76, 232, 764, 2620] := by decide

example : (List.range 29).map a =
    [0, 0, 1, 1, 3, 8, 24, 74, 246, 848, 3088, 11644, 45844, 186336, 784928, 3403128,
      15212744, 69802944, 328988096, 1587831568, 7848954928, 39651793024, 204691645824,
      1078028406176, 5790745961568, 31687186373888, 176575788105984, 1001061518465984,
      5771865641210176] := by decide

/-- The odd double factorial `(2k-1)!! = ∏_{i<k} (2i+1)`, written as a product to
avoid truncated subtraction. -/
def oddProd (k : ℕ) : ℕ := ∏ i ∈ range k, (2 * i + 1)

/-- Truncated closed form `S(m, N) = ∑_{k<N} C(m, 2k) (2k-1)!!`. -/
def S (m N : ℕ) : ℕ := ∑ k ∈ range N, m.choose (2 * k) * oddProd k

/-- `S(m, ·)` is stable once `2N > m`. -/
lemma S_succ_of_lt {m N : ℕ} (h : m < 2 * N) : S m (N + 1) = S m N := by
  rw [S, sum_range_succ, Nat.choose_eq_zero_of_lt h, zero_mul, add_zero, S]

/-- The involution recurrence for the truncated sums. -/
lemma S_rec (m N : ℕ) : S (m + 2) (N + 1) = S (m + 1) (N + 1) + (m + 1) * S m N := by
  have hterm : ∀ k, (m + 2).choose (2 * (k + 1)) * oddProd (k + 1) =
      (m + 1).choose (2 * (k + 1)) * oddProd (k + 1) + (m + 1) * (m.choose (2 * k) * oddProd k) := by
    intro k
    have h1 : (m + 2).choose (2 * (k + 1)) = (m + 1).choose (2 * k + 1) + (m + 1).choose (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ']
    have h2 : (m + 1) * m.choose (2 * k) = (m + 1).choose (2 * k + 1) * (2 * k + 1) :=
      Nat.add_one_mul_choose_eq m (2 * k)
    have h3 : oddProd (k + 1) = oddProd k * (2 * k + 1) := by
      rw [oddProd, prod_range_succ, oddProd]
    rw [h1, h3, ← mul_assoc (m + 1), h2]
    ring
  rw [S, S, S, sum_range_succ', sum_range_succ', mul_sum]
  simp only [hterm, sum_add_distrib]
  simp only [mul_zero, Nat.choose_zero_right]
  ring

/-- Closed form: `t(m) = ∑_{k ≤ m} C(m, 2k) (2k-1)!!`. -/
lemma invol_eq_S (m : ℕ) : invol m = S m (m + 1) := by
  suffices h : ∀ m, invol m = S m (m + 1) ∧ invol (m + 1) = S (m + 1) (m + 2) from (h m).1
  intro m
  induction m with
  | zero => refine ⟨by decide, by decide⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have e1 : S (m + 1) (m + 3) = S (m + 1) (m + 2) := S_succ_of_lt (by omega)
    have e2 : S m (m + 2) = S m (m + 1) := S_succ_of_lt (by omega)
    rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring, invol, S_rec, e1, e2, ← ih.1, ← ih.2]

/-- Every odd `d ≤ 2k - 1` (written `d < 2k`) divides `(2k-1)!!`. -/
lemma dvd_oddProd {d k : ℕ} (hd : Odd d) (hdk : d < 2 * k) : d ∣ oddProd k := by
  obtain ⟨i, rfl⟩ := hd
  exact dvd_prod_of_mem (fun i => 2 * i + 1) (mem_range.2 (by omega))

/-- `n ∣ C(n, j) * gcd(n, j)`. -/
lemma dvd_choose_mul_gcd (n j : ℕ) : n ∣ n.choose j * Nat.gcd n j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.choose_eq_zero_of_lt hj]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj : n' + 1 ∣ (n' + 1).choose (j' + 1) * (j' + 1) :=
    ⟨n'.choose j', (Nat.add_one_mul_choose_eq n' j').symm⟩
  have hn : n' + 1 ∣ (n' + 1).choose (j' + 1) * (n' + 1) := dvd_mul_left _ _
  have hg := Nat.dvd_gcd hn hj
  rwa [Nat.gcd_mul_left] at hg

/-- For odd `n` and `k ≥ 1`, `n ∣ C(n, 2k) (2k-1)!!`. -/
lemma dvd_choose_mul_oddProd {n k : ℕ} (hn : Odd n) (hk : 0 < k) :
    n ∣ n.choose (2 * k) * oddProd k := by
  set g := Nat.gcd n (2 * k)
  have hgn : g ∣ n := Nat.gcd_dvd_left n (2 * k)
  have hg2k : g ∣ 2 * k := Nat.gcd_dvd_right n (2 * k)
  have hgodd : Odd g := hn.of_dvd_nat hgn
  have hgk : g ∣ k := Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.coprime_two_right.2 hgodd) hg2k
  have hgle : g ≤ k := Nat.le_of_dvd hk hgk
  have hgP : g ∣ oddProd k := dvd_oddProd hgodd (by omega)
  exact (dvd_choose_mul_gcd n (2 * k)).trans (Nat.mul_dvd_mul_left _ hgP)

/-- **Key lemma.** For odd `n`, `t(n) ≡ 1 (mod n)`. -/
lemma invol_modEq_one {n : ℕ} (hn : Odd n) : invol n ≡ 1 [MOD n] := by
  rw [invol_eq_S, S, sum_range_succ']
  simp only [mul_zero, Nat.choose_zero_right, one_mul]
  have hz : ∑ k ∈ range n, n.choose (2 * (k + 1)) * oddProd (k + 1) ≡ 0 [MOD n] :=
    Nat.modEq_zero_iff_dvd.2 (dvd_sum fun k _ => dvd_choose_mul_oddProd hn (Nat.succ_pos k))
  simpa [oddProd] using hz.add_right 1

/-- `t` is monotone in steps of one. -/
lemma invol_le_succ (n : ℕ) : invol n ≤ invol (n + 1) := by
  rcases n with _ | n
  · decide
  · rw [invol]; omega

/-- `t(n+3) ≡ t(n) (mod 3)`. -/
lemma invol_add_three_modEq (n : ℕ) : invol (n + 3) ≡ invol n [MOD 3] := by
  suffices h : ∀ n, invol (n + 3) ≡ invol n [MOD 3] ∧ invol (n + 4) ≡ invol (n + 1) [MOD 3]
    from (h n).1
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hc : n + 4 ≡ n + 1 [MOD 3] := by
      simp only [Nat.ModEq]; omega
    have h := ih.2.add (hc.mul ih.1)
    have e5 : invol (n + 1 + 4) = invol (n + 4) + (n + 4) * invol (n + 3) := rfl
    have e2 : invol (n + 1 + 1) = invol (n + 1) + (n + 1) * invol n := rfl
    rw [e5, e2]
    exact h

/-- Bala's formula is exact: `3 a(n+3) + t(n) = t(n+3)`. -/
lemma three_mul_a_add (n : ℕ) : 3 * a (n + 3) + invol n = invol (n + 3) := by
  have hle : invol n ≤ invol (n + 3) :=
    (invol_le_succ n).trans ((invol_le_succ _).trans (invol_le_succ _))
  have hdvd : 3 ∣ invol (n + 3) - invol n :=
    (Nat.modEq_iff_dvd' hle).1 (invol_add_three_modEq n).symm
  rw [a, Nat.mul_div_cancel' hdvd]
  omega

/-- `t(m)` is even for `m ≥ 2`. -/
lemma even_invol (m : ℕ) : 2 ∣ invol (m + 2) := by
  suffices h : ∀ m, 2 ∣ invol (m + 2) ∧ 2 ∣ invol (m + 3) from (h m).1
  intro m
  induction m with
  | zero => exact ⟨by decide, by decide⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [show m + 1 + 3 = (m + 2) + 2 by ring, invol]
    exact dvd_add ih.2 (dvd_mul_of_dvd_right ih.1 _)

/-- Three-step identity: `t(m+4) = (2m+6) t(m+1) + (m+1)(m+4) t(m)`. -/
lemma invol_add_four (m : ℕ) :
    invol (m + 4) = (2 * m + 6) * invol (m + 1) + (m + 1) * (m + 4) * invol m := by
  have h4 : invol (m + 4) = invol (m + 3) + (m + 3) * invol (m + 2) := rfl
  have h3 : invol (m + 3) = invol (m + 2) + (m + 2) * invol (m + 1) := rfl
  have h2 : invol (m + 2) = invol (m + 1) + (m + 1) * invol m := rfl
  rw [h4, h3, h2]
  ring

/-- For odd `n`, `3 (a(n+3) - 1) = n (2 + (2n+3) u + (n+3) w)` for some integers
`u, w` (here `t(n) = 1 + n u` and `w = t(n-1)`). -/
lemma three_mul_sub_one_eq {n : ℕ} (hn : Odd n) :
    ∃ u w : ℤ, 3 * ((a (n + 3) : ℤ) - 1) = n * (2 + (2 * n + 3) * u + (n + 3) * w) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have hpos := hn.pos; omega⟩
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd).1 (invol_modEq_one hn)
  refine ⟨-v, invol m, ?_⟩
  have hA : (3 * a (m + 1 + 3) + invol (m + 1) : ℤ) = invol (m + 1 + 3) := by
    exact_mod_cast three_mul_a_add (m + 1)
  have h4 : (invol (m + 4) : ℤ) = (2 * m + 6) * invol (m + 1) + (m + 1) * (m + 4) * invol m := by
    exact_mod_cast invol_add_four m
  rw [show m + 1 + 3 = m + 4 by ring] at hA
  push_cast at hv ⊢
  have hT : (invol (m + 1) : ℤ) = 1 - (m + 1) * v := by linarith
  rw [hT] at h4 hA
  linear_combination hA + h4

/-- Forward direction: `gcd(n, 6) = 1` implies `a(n+3) ≡ 1 (mod n)`. -/
theorem a_add_three_modEq_one_of_coprime {n : ℕ} (h : Nat.Coprime n 6) :
    a (n + 3) ≡ 1 [MOD n] := by
  have h2 : Nat.Coprime n 2 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h3 : Nat.Coprime n 3 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have hodd : Odd n := Nat.coprime_two_right.1 h2
  obtain ⟨u, w, huw⟩ := three_mul_sub_one_eq hodd
  have hdvd : (n : ℤ) ∣ 3 * ((a (n + 3) : ℤ) - 1) := ⟨_, huw⟩
  have hdvd' : (n : ℤ) ∣ (a (n + 3) : ℤ) - 1 :=
    (Nat.isCoprime_iff_coprime.2 h3).dvd_of_dvd_mul_left (by exact_mod_cast hdvd)
  rw [Nat.modEq_iff_dvd]
  push_cast
  rw [show (1 : ℤ) - a (n + 3) = -((a (n + 3) : ℤ) - 1) by ring]
  exact hdvd'.neg_right

/-- Converse direction: for `0 < n`, `a(n+3) ≡ 1 (mod n)` implies `gcd(n, 6) = 1`. -/
theorem coprime_of_a_add_three_modEq_one {n : ℕ} (hn : 0 < n) (h : a (n + 3) ≡ 1 [MOD n]) :
    Nat.Coprime n 6 := by
  have hodd : Odd n := by
    by_contra hne
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
      have hn1 : n ≠ 1 := by rintro rfl; exact hne odd_one
      exact ⟨n - 2, by omega⟩
    have h2n : 2 ∣ k + 2 := by
      rcases Nat.even_or_odd (k + 2) with he | ho
      · exact even_iff_two_dvd.1 he
      · exact absurd ho hne
    have hmod2 : a (k + 2 + 3) ≡ 1 [MOD 2] := Nat.ModEq.of_dvd h2n h
    have he1 := even_invol k
    have he2 := even_invol (k + 3)
    have hA := three_mul_a_add (k + 2)
    rw [show k + 3 + 2 = k + 2 + 3 by ring] at he2
    simp only [Nat.ModEq] at hmod2
    omega
  have h3 : Nat.Coprime n 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨r, rfl⟩
    obtain ⟨u, w, huw⟩ := three_mul_sub_one_eq hodd
    have hr : (r : ℤ) ≠ 0 := by
      have hr0 : r ≠ 0 := by rintro rfl; omega
      exact_mod_cast hr0
    have hAr : (a (3 * r + 3) : ℤ) - 1 =
        r * (2 + (2 * ((3 * r : ℕ) : ℤ) + 3) * u + (((3 * r : ℕ) : ℤ) + 3) * w) := by
      push_cast at huw ⊢
      linarith
    have hdvd : ((3 * r : ℕ) : ℤ) ∣ (a (3 * r + 3) : ℤ) - 1 := by
      have hd := (Nat.modEq_iff_dvd).1 h
      rw [show ((1 : ℕ) : ℤ) - a (3 * r + 3) = -((a (3 * r + 3) : ℤ) - 1) by push_cast; ring] at hd
      exact (dvd_neg).1 hd
    rw [hAr, show ((3 * r : ℕ) : ℤ) = r * 3 by push_cast; ring,
      mul_dvd_mul_iff_left hr] at hdvd
    have hQ : (2 + (2 * ((r : ℤ) * 3) + 3) * u + ((r : ℤ) * 3 + 3) * w) =
        2 + 3 * ((2 * r + 1) * u + (r + 1) * w) := by ring
    rw [hQ] at hdvd
    have h32 : (3 : ℤ) ∣ 2 := (Int.dvd_add_left (dvd_mul_right 3 _)).1 hdvd
    norm_num at h32
  exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hodd) h3

/-- **Bala's conjecture (A238977, Peter Bala, Oct 05 2021).** For every `n ≥ 1`,
`a(n+3) ≡ 1 (mod n)` if and only if `n` is coprime to `6` (i.e. `n ∈ A007310`),
where `a(n) = (t(n) - t(n-3)) / 3` and `t` are the involution numbers A000085. -/
theorem a_add_three_modEq_one_iff {n : ℕ} (hn : 0 < n) :
    a (n + 3) ≡ 1 [MOD n] ↔ Nat.Coprime n 6 :=
  ⟨coprime_of_a_add_three_modEq_one hn, a_add_three_modEq_one_of_coprime⟩

/-- Non-vacuity: both sides of the equivalence occur (`n = 5` coprime to `6`,
`n = 3` and `n = 4` not). -/
example : a (5 + 3) ≡ 1 [MOD 5] ∧ ¬ a (3 + 3) ≡ 1 [MOD 3] ∧ ¬ a (4 + 3) ≡ 1 [MOD 4] := by
  decide

end Candidates.A238977InvolutionBalaFormula
