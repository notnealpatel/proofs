/-
# A060264 — Greathouse: least prime separating 1², …, n² is the first prime after 2n

## OEIS source (retrieved with `oeis show A060264`, 2026-10-21)

```
NAME:     First prime after 2n.
TERMS:    2,3,5,7,11,11,13,17,17,19,23,23,29,29,29,31,37,37,37,41,41,43,47,47,
          53,53,53,59,59,59,61,67,67,67,71,71,73,79,79,79,83,83,89,89,89,97,...
OFFSET:   0 (a(0) = 2, a(1) = 3, a(2) = 5, a(3) = 7, a(4) = 11, a(5) = 11)
FORMULA:  a(n) = A151800(2*n). - _Reinhard Zumkeller_, Nov 15 2013
PROGRAM:  (PARI) a(n) = nextprime(2*n + 1)  \\ _Harry J. Smith_, Jul 03 2009
COMMENT (the conjecture):
  Conjecture: for n > 2, this is the least prime p such that 1^2, 2^2, 3^2,
  ..., n^2 are distinct mod p. Checked to 10^4. - _Charles R Greathouse IV_,
  Dec 03 2022
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell (the entry records only a check to `10^4`).

## Result of this module

The conjecture is proved for every `n > 2` (`greathouse_conjecture`), with no
remaining `sorry`. The key step is `squaresDistinctMod_iff`: for a prime `p`
and `n ≥ 3`, the squares `1², …, n²` are pairwise distinct mod `p` iff
`2n < p`.

* If `2n < p` and `i² ≡ j² (mod p)` with `1 ≤ j ≤ i ≤ n`, then
  `p ∣ (i + j)(i - j)`; `0 < i + j ≤ 2n < p` and `i - j < n < p` force `i = j`.
* If `p ≤ 2n` and `p = 2`, then `1² ≡ 3² (mod 2)` with `3 ≤ n`.
* If `p ≤ 2n` and `p = 2k + 1` is odd, then `k² ≡ (k + 1)² (mod p)` with
  `1 ≤ k < k + 1 ≤ n`.

The guard `n > 2` is load-bearing: for `n = 2` the prime `2` already
separates `1² = 1` and `2² = 4`, while `a(2) = 5` (see the sanity layer).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A060264DistinctSquaresMod

/-! ## Definition layer -/

/-- `a060264 n` is the first prime after `2n` (OEIS A060264, PARI
`nextprime(2*n + 1)`): the least prime `p` with `2n + 1 ≤ p`. -/
def a060264 (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 * n + 1))

/-- `SquaresDistinctMod n p`: the squares `1², 2², …, n²` are pairwise distinct
modulo `p`, i.e. for `1 ≤ i, j ≤ n`, `i² % p = j² % p` implies `i = j`. -/
def SquaresDistinctMod (n p : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ^ 2 % p = j ^ 2 % p → i = j

instance (n p : ℕ) : Decidable (SquaresDistinctMod n p) := by
  unfold SquaresDistinctMod
  infer_instance

/-- Characterisation of `a060264 n` as the least prime strictly above `2n`. -/
theorem a060264_spec (n : ℕ) :
    (a060264 n).Prime ∧ 2 * n < a060264 n ∧
      ∀ q : ℕ, q.Prime → 2 * n < q → a060264 n ≤ q := by
  have hspec := Nat.find_spec (Nat.exists_infinite_primes (2 * n + 1))
  refine ⟨hspec.2, hspec.1, fun q hq hlt => ?_⟩
  exact Nat.find_min' (Nat.exists_infinite_primes (2 * n + 1)) ⟨hlt, hq⟩

/-- Evaluation rule for `a060264`: `a060264 n = m` iff `m` is a prime with
`2n + 1 ≤ m` and no prime lies in `[2n + 1, m)`. Used for the ground-truth
checks against the DATA line. -/
theorem a060264_eq_iff (n m : ℕ) :
    a060264 n = m ↔
      (2 * n + 1 ≤ m ∧ m.Prime) ∧ ∀ k < m, ¬ (2 * n + 1 ≤ k ∧ k.Prime) := by
  rw [a060264, Nat.find_eq_iff]

/-! ## The key lemma -/

/-- If `2n < p` then `1², …, n²` are pairwise distinct modulo `p`
(primality of `p` is used to split `p ∣ (i + j)(i - j)`). -/
theorem squaresDistinctMod_of_lt {n p : ℕ} (hp : p.Prime) (hlt : 2 * n < p) :
    SquaresDistinctMod n p := by
  have key : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, j ≤ i →
      i ^ 2 % p = j ^ 2 % p → i = j := by
    intro i hi j hj hji hmod
    rw [Finset.mem_Icc] at hi hj
    have hdvd : p ∣ i ^ 2 - j ^ 2 :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hji 2)).mp hmod.symm
    rw [Nat.sq_sub_sq] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with hsum | hdiff
    · have hle : p ≤ i + j := Nat.le_of_dvd (by omega) hsum
      omega
    · by_contra hne
      have hle : p ≤ i - j := Nat.le_of_dvd (by omega) hdiff
      omega
  intro i hi j hj hmod
  rcases le_total j i with hji | hij
  · exact key i hi j hj hji hmod
  · exact (key j hj i hi hij hmod.symm).symm

/-- If `p ≤ 2n` is prime and `3 ≤ n`, then two of `1², …, n²` coincide
modulo `p`. -/
theorem not_squaresDistinctMod_of_le {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime)
    (hle : p ≤ 2 * n) : ¬ SquaresDistinctMod n p := by
  intro hdist
  rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩
  · subst h2
    have h3 : 3 ∈ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
    have h1 : 1 ∈ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
    have h31 := hdist 3 h3 1 h1 (by norm_num)
    omega
  · have hk1 : 1 ≤ k := by
      have htwo := hp.two_le
      omega
    have hmod : (k + 1) ^ 2 % p = k ^ 2 % p := by
      have hexp : (k + 1) ^ 2 = k ^ 2 + p := by rw [hk]; ring
      rw [hexp, Nat.add_mod_right]
    have hk1mem : k + 1 ∈ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
    have hkmem : k ∈ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
    have heq := hdist (k + 1) hk1mem k hkmem hmod
    omega

/-- **Key lemma.** For `n ≥ 3` and `p` prime, the squares `1², …, n²` are
pairwise distinct modulo `p` iff `2n < p`. -/
theorem squaresDistinctMod_iff {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime) :
    SquaresDistinctMod n p ↔ 2 * n < p := by
  constructor
  · intro hdist
    by_contra hle
    exact not_squaresDistinctMod_of_le hn hp (by omega) hdist
  · exact squaresDistinctMod_of_lt hp

/-! ## The conjecture -/

/-- **Greathouse's conjecture (A060264, Charles R Greathouse IV, Dec 03 2022).**

Verbatim: "Conjecture: for n > 2, this is the least prime p such that 1^2, 2^2,
3^2, ..., n^2 are distinct mod p."

Formally: for `2 < n`, the first prime after `2n` is the least element of the
set of primes `p` modulo which `1², …, n²` are pairwise distinct. -/
theorem greathouse_conjecture (n : ℕ) (hn : 2 < n) :
    IsLeast {p : ℕ | p.Prime ∧ SquaresDistinctMod n p} (a060264 n) := by
  obtain ⟨hprime, hlt, hmin⟩ := a060264_spec n
  refine ⟨⟨hprime, squaresDistinctMod_of_lt hprime hlt⟩, ?_⟩
  rintro q ⟨hq, hdist⟩
  exact hmin q hq ((squaresDistinctMod_iff (by omega) hq).mp hdist)

/-! ## Sanity layer -/

-- Ground truth: the first terms `2, 3, 5, 7, 11, 11` of the DATA line.
example : a060264 0 = 2 ∧ a060264 1 = 3 ∧ a060264 2 = 5 ∧ a060264 3 = 7 ∧
    a060264 4 = 11 ∧ a060264 5 = 11 := by
  simp only [a060264_eq_iff]
  decide

-- Ground truth for the predicate: mod 7, the squares `1, 4, 9` are distinct
-- (`1, 4, 2`), and mod 5 they are not (`1, 4, 4`).
example : SquaresDistinctMod 3 7 ∧ ¬ SquaresDistinctMod 3 5 := by decide

-- The guard `2 < n` is load-bearing: for `n = 2` the prime `2` separates
-- `1² = 1` and `2² = 4`, while `a(2) = 5`.
example : SquaresDistinctMod 2 2 ∧ a060264 2 = 5 := by
  rw [a060264_eq_iff]
  decide

-- Satisfiability: the hypothesis `2 < n` is met at `n = 3`.
example : IsLeast {p : ℕ | p.Prime ∧ SquaresDistinctMod 3 p} 7 := by
  have h := greathouse_conjecture 3 (by norm_num)
  have h7 : a060264 3 = 7 := by
    rw [a060264_eq_iff]
    decide
  rwa [h7] at h

end Candidates.A060264DistinctSquaresMod
