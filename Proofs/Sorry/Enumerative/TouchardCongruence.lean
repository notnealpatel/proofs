/-
# Touchard's congruence and the mod-78 restriction on zeros of complementary Bell numbers

## Source

arXiv:2608.00575, John M. Campbell, "The finitude of the fibers of the complementary Bell
numbers", Section 1 (Introduction and background), the discussion of Wilf's conjecture after
eq. `(displaymain)`; background problems: Subbarao–Verma (2001), Problems 5.5–5.7.
Recorded 2026-10-21.

Verbatim context from the paper (Section 1):

```
we may express Bell polynomials in terms of Stirling numbers of the second kind so that
  B_{n}(x) = \sum_{k=0}^{n} {n \brace k} x^k,
... since f(k) = B_k(-1).
The c=0 case of (displaymain) has been studied extensively in connection with Wilf's
conjecture, which asserts that f(k) \neq 0 for every k > 2 (noting that f(2)=0).
```

## Status of the formalized claim

Known result, proved elsewhere (not in this paper).  Wilf's conjecture itself is open; the
paper's own theorem is the finiteness of every fiber `f⁻¹(c)`, which is *not* formalized
here.  This module formalizes the classical Touchard-type package:

1. Touchard's congruence `S(n+p,k) ≡ S(n,k-p) + S(n+1,k) (mod p)` for prime `p`, and its
   consequences `B_{n+p}(x) = x^p B_n(x) + B_{n+1}(x)` in characteristic `p`,
   `Bell(n+p) ≡ Bell(n) + Bell(n+1)`, `f(n+p) ≡ (-1)^p f(n) + f(n+1) (mod p)`.
2. `f(n)` is odd iff `n ≢ 2 (mod 3)`; `f mod 3` has period `26` with zero classes
   `{2,6,7,9,15,19,20,22}`.
3. Hence `f(n) = 0` forces `n mod 78 ∈ {2,20,32,35,41,59,71,74}`: a special case of Wilf's
   conjecture, not the full conjecture.

Computational evidence (Python, 2026-10-21): the coefficient congruence for
`p ∈ {2,3,5,7,11}`, `n < 60`; the mod-2/mod-3 periodicities for `n ≤ 500`; the only zero of
`f` with `n ≤ 500` is `n = 2`.

## Repo adjacency

`Nat.stirlingSecond` and `Nat.bell` are Mathlib's.  The bridge
`Σ_k S(n,k) = Nat.bell n` is `StirlingBellCombinatorial.sum_stirlingSecond_eq_bell`, and the
expansion `x^n = Σ_l S(n,l) x^{\underline l}` is
`Candidates.A055203AllenRelationsMod.pow_eq_sum_stirlingSecond` (both production modules).
-/
import Mathlib
import Enumerative.StirlingBellCombinatorial
import Enumerative.A055203AllenRelationsMod

set_option autoImplicit false

open Finset

namespace Candidates.TouchardCongruence

/-- Fermat step for Stirling numbers: for a prime `p` and `2 ≤ k < p`,
`S(p, k) ≡ 0 (mod p)`.  Proof: evaluate `x^p = Σ_l S(p,l) x^{\underline l}` at `x = k`,
use `k^p ≡ k (mod p)` and strong induction on `k`, and cancel the unit `k!`. -/
theorem stirlingSecond_prime_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ∀ k, 2 ≤ k → k < p → (p.stirlingSecond k : ZMod p) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk2 hkp
    have hpow := Candidates.A055203AllenRelationsMod.pow_eq_sum_stirlingSecond k p
    have hcast : ((k ^ p : ℕ) : ZMod p) = (k : ZMod p) := by
      rw [Nat.cast_pow, ZMod.pow_card]
    rw [hpow] at hcast
    push_cast at hcast
    have hp1 : p.stirlingSecond 1 = 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
      exact Nat.stirlingSecond_one_right q
    rw [Finset.sum_eq_add 1 k (by omega)] at hcast
    · rw [hp1, Nat.descFactorial_one, Nat.descFactorial_self] at hcast
      have hfac : (k.factorial : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff, hp.out.dvd_factorial]
        omega
      have hmul : (p.stirlingSecond k : ZMod p) * (k.factorial : ZMod p) = 0 := by
        push_cast at hcast ⊢
        linear_combination hcast
      exact (mul_eq_zero.mp hmul).resolve_right hfac
    · intro l _ hl
      rcases Nat.lt_or_ge l 2 with hl2 | hl2
      · have hl0 : l = 0 := by omega
        subst hl0
        have : p.stirlingSecond 0 = 0 := by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
          rfl
        simp [this]
      rcases Nat.lt_or_ge l k with hlk | hlk
      · rw [ih l hlk hl2 (by omega), zero_mul]
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
        simp
    · intro h; simp at h; omega
    · intro h; simp at h; omega


/-- Base case `n = 0` of Touchard's congruence: for a prime `p` and every `k`,
`S(p, k) ≡ S(0, k - p)·[p ≤ k] + S(1, k) (mod p)`, i.e. `S(p,k) ≡ [k = p] + [k = 1]`. -/
theorem stirlingSecond_prime (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (p.stirlingSecond k : ZMod p) =
      (if p ≤ k then ((0 : ℕ).stirlingSecond (k - p) : ZMod p) else 0) +
        ((1 : ℕ).stirlingSecond k : ZMod p) := by
  have h2 := hp.out.two_le
  rcases Nat.lt_or_ge k p with hkp | hkp
  · rw [if_neg (by omega), zero_add]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rfl
      · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [Nat.stirlingSecond_one_right]
        rfl
    · rw [stirlingSecond_prime_eq_zero p k hk2 hkp, Nat.stirlingSecond_eq_zero_of_lt (by omega)]
      simp
  · rw [if_pos hkp, Nat.stirlingSecond_eq_zero_of_lt (n := 1) (by omega)]
    rcases Nat.eq_or_lt_of_le hkp with hk | hk
    · subst hk
      simp [Nat.stirlingSecond_self]
    · rw [Nat.stirlingSecond_eq_zero_of_lt hk]
      obtain ⟨q, hq⟩ : ∃ q, k - p = q + 1 := ⟨k - p - 1, by omega⟩
      rw [hq]
      simp

/-- **Touchard's congruence, coefficientwise.**  For a prime `p` and all `n, k`,
`S(n + p, k) ≡ S(n, k - p) + S(n + 1, k) (mod p)`, where the first term is read as `0`
when `k < p` (guarding the truncated subtraction `k - p`). -/
theorem touchard_coeff (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) :
    ((n + p).stirlingSecond k : ZMod p) =
      (if p ≤ k then (n.stirlingSecond (k - p) : ZMod p) else 0) +
        ((n + 1).stirlingSecond k : ZMod p) := by
  induction n generalizing k with
  | zero => simpa using stirlingSecond_prime p k
  | succ n ih =>
    have hnp : n + 1 + p = (n + p) + 1 := by omega
    rw [hnp]
    rcases k with _ | j
    · have hp0 : ¬ p ≤ 0 := by have := hp.out.two_le; omega
      simp [hp0]
    · rw [Nat.stirlingSecond_succ_succ (n + p) j, Nat.stirlingSecond_succ_succ (n + 1) j]
      push_cast
      rw [ih (j + 1), ih j]
      rcases Nat.lt_or_ge (j + 1) p with hjp | hjp
      · simp only [if_neg (show ¬ p ≤ j + 1 by omega), if_neg (show ¬ p ≤ j by omega)]
        ring
      rcases Nat.eq_or_lt_of_le hjp with hj | hj
      · have hsub : j + 1 - p = 0 := by omega
        simp only [if_pos hjp, if_neg (show ¬ p ≤ j by omega), hsub,
          Nat.stirlingSecond_succ_zero]
        have hpz : ((j : ZMod p) + 1) = 0 := by
          have hc : ((j + 1 : ℕ) : ZMod p) = 0 := by
            rw [← hj]
            exact ZMod.natCast_self p
          push_cast at hc
          exact hc
        rw [hpz]
        ring
      · obtain ⟨m, hm⟩ : ∃ m, j = m + p := ⟨j - p, by omega⟩
        subst hm
        have e1 : m + p + 1 - p = m + 1 := by omega
        have e2 : m + p - p = m := by omega
        simp only [if_pos hjp, if_pos (show p ≤ m + p by omega), e1, e2]
        rw [Nat.stirlingSecond_succ_succ n m]
        push_cast
        rw [ZMod.natCast_self]
        ring


/-- The Bell (Touchard) polynomial `B_n(x) = Σ_{k=0}^{n} S(n,k) x^k`, evaluated at `x` in a
commutative semiring (the paper's eq. `defineBnx`). -/
def bellEval {R : Type*} [CommSemiring R] (n : ℕ) (x : R) : R :=
  ∑ k ∈ range (n + 1), (n.stirlingSecond k : R) * x ^ k

/-- `B_n(x)` may be summed over any range `range N` with `n + 1 ≤ N`, since `S(n,k) = 0`
for `k > n`. -/
theorem bellEval_eq_sum_range {R : Type*} [CommSemiring R] (n N : ℕ) (hN : n + 1 ≤ N)
    (x : R) : bellEval n x = ∑ k ∈ range N, (n.stirlingSecond k : R) * x ^ k := by
  unfold bellEval
  apply Finset.sum_subset (range_subset_range.2 hN)
  intro k _ hk
  rw [Nat.stirlingSecond_eq_zero_of_lt (by simpa using hk)]
  simp

/-- Touchard's coefficientwise congruence transported to any commutative ring of
characteristic `p`. -/
theorem touchard_coeff_cast {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n k : ℕ) :
    ((n + p).stirlingSecond k : R) =
      (if p ≤ k then (n.stirlingSecond (k - p) : R) else 0) +
        ((n + 1).stirlingSecond k : R) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) R) (touchard_coeff p n k)
  split_ifs at h ⊢ <;> simpa using h

/-- **Touchard's congruence for Bell polynomials.**  In any commutative ring `R` of prime
characteristic `p`, `B_{n+p}(x) = x^p B_n(x) + B_{n+1}(x)` for every `x : R` (applied to
`R = (ZMod p)[X]` this is the polynomial congruence). -/
theorem bellEval_add_prime {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n : ℕ) (x : R) :
    bellEval (n + p) x = x ^ p * bellEval n x + bellEval (n + 1) x := by
  rw [bellEval_eq_sum_range (n + p) (p + (n + 2)) (by omega),
    bellEval_eq_sum_range n (n + 2) (by omega),
    bellEval_eq_sum_range (n + 1) (p + (n + 2)) (by omega)]
  simp only [touchard_coeff_cast p n, add_mul, sum_add_distrib, add_left_inj]
  rw [sum_range_add, Finset.mul_sum]
  have hlow : ∑ k ∈ range p,
      (if p ≤ k then (n.stirlingSecond (k - p) : R) else 0) * x ^ k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by simpa using hk)]
    simp
  rw [hlow, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos (by omega), Nat.add_sub_cancel_left, pow_add]
  ring


/-- The complementary Bell number `f(n) = B_n(-1) = Σ_{k=0}^{n} (-1)^k S(n,k)`
(OEIS A000587; arXiv:2608.00575, Section 1). -/
def compBell (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ k * (n.stirlingSecond k : ℤ)

/-- Ground truth: `f(0..11) = 1, -1, 0, 1, 1, -2, -9, -9, 50, 267, 413, -2180`
(OEIS A000587); in particular `f(2) = 0`, the known zero. -/
example : (List.range 12).map compBell = [1, -1, 0, 1, 1, -2, -9, -9, 50, 267, 413, -2180] := by
  decide

/-- The image of `f(n)` in any commutative ring is `B_n(-1)` computed there. -/
theorem cast_compBell {R : Type*} [CommRing R] (n : ℕ) :
    ((compBell n : ℤ) : R) = bellEval n (-1 : R) := by
  unfold compBell bellEval
  push_cast
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Touchard's congruence for complementary Bell numbers: for a prime `p`,
`f(n + p) ≡ (-1)^p f(n) + f(n + 1) (mod p)`. -/
theorem compBell_add_prime (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((compBell (n + p) : ℤ) : ZMod p) =
      (-1) ^ p * (compBell n : ZMod p) + (compBell (n + 1) : ZMod p) := by
  rw [cast_compBell, cast_compBell, cast_compBell, bellEval_add_prime]

/-- `B_n(1)` is the Bell number `Nat.bell n`. -/
theorem bellEval_one {R : Type*} [CommSemiring R] (n : ℕ) : bellEval n (1 : R) = n.bell := by
  rw [bellEval, ← StirlingBellCombinatorial.sum_stirlingSecond_eq_bell]
  push_cast
  simp

/-- **Touchard's congruence** for Bell numbers: `B(n + p) ≡ B(n) + B(n + 1) (mod p)` for
every prime `p`. -/
theorem bell_add_prime (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((n + p).bell : ZMod p) = (n.bell : ZMod p) + ((n + 1).bell : ZMod p) := by
  rw [← bellEval_one, ← bellEval_one, ← bellEval_one, bellEval_add_prime, one_pow, one_mul]

/-- Modulo `2`, `f(n) ≡ 0` if `n ≡ 2 (mod 3)` and `f(n) ≡ 1` otherwise (period `3`). -/
theorem compBell_zmod_two (n : ℕ) :
    ((compBell n : ℤ) : ZMod 2) = if n % 3 = 2 then 0 else 1 := by
  suffices h : ∀ n, ((compBell n : ℤ) : ZMod 2) = (if n % 3 = 2 then 0 else 1) ∧
      ((compBell (n + 1) : ℤ) : ZMod 2) = (if (n + 1) % 3 = 2 then 0 else 1) from (h n).1
  intro n
  induction n with
  | zero =>
    have h0 : compBell 0 = 1 := by decide
    have h1 : compBell 1 = -1 := by decide
    rw [h0, h1]
    decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 by omega, compBell_add_prime 2 n, ih.1, ih.2]
    have h1 : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
    have h2 : (n + 2) % 3 = (n % 3 + 2) % 3 := by omega
    rw [h1, h2]
    have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize n % 3 = r at hr ⊢
    interval_cases r <;> decide


/-- The residues `f(0), …, f(25) mod 3` (one full period). -/
def compBellModThreeTable : List (ZMod 3) :=
  [1, 2, 0, 1, 1, 1, 0, 0, 2, 0, 2, 1, 2, 2, 1, 0, 2, 2, 2, 0, 0, 1, 0, 1, 2, 1]

/-- Modulo `3`, `f(n)` is periodic with period `26`, with residues given by
`compBellModThreeTable`. -/
theorem compBell_zmod_three (n : ℕ) :
    ((compBell n : ℤ) : ZMod 3) = compBellModThreeTable.getD (n % 26) 0 := by
  let P : ℕ → Prop := fun m =>
    ((compBell m : ℤ) : ZMod 3) = compBellModThreeTable.getD (m % 26) 0
  suffices h : ∀ n, P n ∧ P (n + 1) ∧ P (n + 2) from (h n).1
  intro n
  induction n with
  | zero =>
    have h0 : compBell 0 = 1 := by decide
    have h1 : compBell 1 = -1 := by decide
    have h2 : compBell 2 = 0 := by decide
    simp only [P, h0, h1, h2]
    decide
  | succ n ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    refine ⟨ih1, ih2, ?_⟩
    simp only [P] at ih0 ih1 ⊢
    rw [show n + 1 + 2 = n + 3 by omega, compBell_add_prime 3 n, ih0, ih1]
    have h1 : (n + 1) % 26 = (n % 26 + 1) % 26 := by omega
    have h3 : (n + 3) % 26 = (n % 26 + 3) % 26 := by omega
    rw [h1, h3]
    have hr : n % 26 < 26 := Nat.mod_lt _ (by norm_num)
    generalize n % 26 = r at hr ⊢
    revert r
    decide

/-- `f(n)` is odd if and only if `n ≢ 2 (mod 3)`. -/
theorem compBell_odd_iff (n : ℕ) : Odd (compBell n) ↔ n % 3 ≠ 2 := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd, compBell_zmod_two]
  split_ifs with h <;> simp [h]

/-- `3 ∣ f(n)` if and only if `n mod 26 ∈ {2, 6, 7, 9, 15, 19, 20, 22}`. -/
theorem three_dvd_compBell_iff (n : ℕ) :
    (3 : ℤ) ∣ compBell n ↔ n % 26 ∈ ({2, 6, 7, 9, 15, 19, 20, 22} : Finset ℕ) := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    compBell_zmod_three]
  have hr : n % 26 < 26 := Nat.mod_lt _ (by norm_num)
  generalize n % 26 = r at hr ⊢
  revert r
  decide

/-- **Mod-78 restriction on zeros (partial Wilf).**  If `f(n) = 0` then
`n mod 78 ∈ {2, 20, 32, 35, 41, 59, 71, 74}`. -/
theorem mod_78_of_compBell_eq_zero (n : ℕ) (h : compBell n = 0) :
    n % 78 ∈ ({2, 20, 32, 35, 41, 59, 71, 74} : Finset ℕ) := by
  have h2 : n % 3 = 2 := by
    by_contra hne
    have hodd := (compBell_odd_iff n).2 hne
    rw [h] at hodd
    exact absurd hodd (by decide)
  have h3 : n % 26 ∈ ({2, 6, 7, 9, 15, 19, 20, 22} : Finset ℕ) := by
    rw [← three_dvd_compBell_iff, h]
    exact dvd_zero 3
  have e3 : n % 3 = n % 78 % 3 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
  have e26 : n % 26 = n % 78 % 26 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
  rw [e3] at h2
  rw [e26] at h3
  have hr : n % 78 < 78 := Nat.mod_lt _ (by norm_num)
  generalize n % 78 = r at hr h2 h3 ⊢
  revert r
  decide

/-- Wilf's conjecture `f(n) ≠ 0` holds for every `n` outside the eight residue classes
`{2, 20, 32, 35, 41, 59, 71, 74}` modulo `78`. -/
theorem compBell_ne_zero_of_mod_78 (n : ℕ)
    (h : n % 78 ∉ ({2, 20, 32, 35, 41, 59, 71, 74} : Finset ℕ)) : compBell n ≠ 0 :=
  fun h0 => h (mod_78_of_compBell_eq_zero n h0)

/-- Mod-2 period: `f(n + 3) ≡ f(n) (mod 2)`. -/
theorem compBell_add_three_modEq_two (n : ℕ) : compBell (n + 3) ≡ compBell n [ZMOD 2] := by
  change compBell (n + 3) ≡ compBell n [ZMOD ((2 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, compBell_zmod_two, compBell_zmod_two,
    show (n + 3) % 3 = n % 3 by omega]

/-- Mod-3 period: `f(n + 26) ≡ f(n) (mod 3)`. -/
theorem compBell_add_26_modEq_three (n : ℕ) : compBell (n + 26) ≡ compBell n [ZMOD 3] := by
  change compBell (n + 26) ≡ compBell n [ZMOD ((3 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, compBell_zmod_three, compBell_zmod_three,
    show (n + 26) % 26 = n % 26 by omega]

/-- Ground truth: `B_3(2) = 2 + 3·4 + 8 = 22` and `B_4(1) = Bell(4) = 15`. -/
example : bellEval 3 (2 : ℤ) = 22 ∧ bellEval 4 (1 : ℤ) = 15 := by decide

/-- Non-vacuity: the hypothesis of `mod_78_of_compBell_eq_zero` is met at `n = 2`. -/
example : compBell 2 = 0 ∧ 2 % 78 ∈ ({2, 20, 32, 35, 41, 59, 71, 74} : Finset ℕ) := by decide

/-- Non-vacuity: the hypothesis of `compBell_ne_zero_of_mod_78` is met at `n = 3`. -/
example : 3 % 78 ∉ ({2, 20, 32, 35, 41, 59, 71, 74} : Finset ℕ) := by decide

/-- Instance check: Touchard at `p = 3`, `n = 2`, `k = 3`: `S(5,3) = 25 ≡ S(2,0) + S(3,3) = 1`. -/
example : ((Nat.stirlingSecond 5 3 : ℕ) : ZMod 3) = (Nat.stirlingSecond 2 0 : ZMod 3) +
    (Nat.stirlingSecond 3 3 : ZMod 3) := by decide

end Candidates.TouchardCongruence
