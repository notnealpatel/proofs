/-
# A025583 — Irwin: composite non-Goldbach numbers via the last composite triple

## OEIS source (retrieved with `oeis show A025583`, 2026-10-21)

```
NAME:     Composite numbers that are not the sum of 2 primes.
TERMS:    27,35,51,57,65,77,87,93,95,117,119,121,123,125,135,143,145,147,155,
          161,171,177,185,187,189,203,205,207,209,215,217,219,221,237,245,247,
          249,255,261,267,275,287,289,291,297,299,301,303,305,321,323,325,327,
          329,335,341
COMMENT (the conjecture):
  Conjecture: This is the sequence of odd numbers k such that
  (k mod x) mod 2 != 1, where x is the greatest m <= k such that m, m-1 and
  m-2 are all composite. Verified for first 10000 terms.
  - _Benedict W. J. Irwin_, May 06 2016
COMMENT (Peter Munn, May 15 2017, on the even part):
  (If the Goldbach conjecture for even numbers is false this comment should be
  restricted to the odd terms of this sequence ...)
```

## Status

Triage: open (no proof in the entry or the literature found).  As stated, the
conjecture asserts that the sequence contains no even number, i.e. that every
even composite is a sum of two primes: the binary Goldbach conjecture.

## What this file proves

* `inSeq_iff_of_odd` — the odd part of Irwin's conjecture, unconditionally:
  for odd `k`, `k ∈ A025583 ↔ x exists ∧ (k mod x) mod 2 ≠ 1`.
* `irwinConjecture_iff_goldbach` — the full conjecture is equivalent to the
  binary Goldbach conjecture (`∀ n, Even n → 4 ≤ n → n = p + q`).
* `irwinConjecture` — the full conjecture, reduced to Goldbach; its single
  `sorry` is exactly the Goldbach statement `Goldbach`.

Computation (Python, 2026-10-21): the set equality holds for all `k < 20000`
and for all odd `k ≤ 200000`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A025583CompositeSumTwo

/-! ## Definition layer -/

/-- `n` is composite: `1 < n` and `n` is not prime. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

instance : DecidablePred IsComposite := fun n =>
  inferInstanceAs (Decidable (1 < n ∧ ¬ n.Prime))

/-- `n` is the sum of two primes `p + q`. -/
def IsSumTwoPrimes (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Bounded reformulation of `IsSumTwoPrimes` (used for decidability):
`n` is a sum of two primes iff some prime `p ≤ n` has `n - p` prime. -/
theorem isSumTwoPrimes_iff (n : ℕ) :
    IsSumTwoPrimes n ↔ ∃ p ∈ Finset.range (n + 1), p.Prime ∧ (n - p).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact ⟨p, Finset.mem_range.2 (by omega), hp, by rwa [Nat.add_sub_cancel_left]⟩
  · rintro ⟨p, hp, hpp, hq⟩
    have hpn : p < n + 1 := Finset.mem_range.1 hp
    exact ⟨p, n - p, hpp, hq, by omega⟩

instance : DecidablePred IsSumTwoPrimes := fun n =>
  decidable_of_iff _ (isSumTwoPrimes_iff n).symm

/-- Membership in A025583: `k` is composite and not the sum of two primes. -/
def InSeq (k : ℕ) : Prop := IsComposite k ∧ ¬ IsSumTwoPrimes k

instance : DecidablePred InSeq := fun k =>
  inferInstanceAs (Decidable (IsComposite k ∧ ¬ IsSumTwoPrimes k))

/-- `m`, `m - 1` and `m - 2` are all composite.  The guard `2 ≤ m` keeps the
natural subtractions off their truncated values (in fact `IsComposite (m - 2)`
already forces `6 ≤ m`). -/
def TripleComposite (m : ℕ) : Prop :=
  2 ≤ m ∧ IsComposite m ∧ IsComposite (m - 1) ∧ IsComposite (m - 2)

instance : DecidablePred TripleComposite := fun m =>
  inferInstanceAs
    (Decidable (2 ≤ m ∧ IsComposite m ∧ IsComposite (m - 1) ∧ IsComposite (m - 2)))

/-- Irwin's `x`: the greatest `m ≤ k` with `m, m - 1, m - 2` all composite.
`Nat.findGreatest` returns `0` when no such `m` exists (i.e. for `k < 10`);
the conjecture below carries the existence of `m` explicitly. -/
def X (k : ℕ) : ℕ := Nat.findGreatest TripleComposite k

/-! ## Ground truth -/

example : X 27 = 27 := by decide
example : X 13 = 10 := by decide
example : InSeq 27 := by decide
example : ¬ InSeq 25 := by decide
example : IsSumTwoPrimes 4 := by decide

/-- The first nine listed terms of A025583 are exactly the members below 100. -/
example : ∀ k < 100, InSeq k ↔ k ∈ [27, 35, 51, 57, 65, 77, 87, 93, 95] := by
  decide +kernel

/-- Irwin's criterion reproduces the first nine listed terms below 100. -/
example : ∀ k < 100, (Odd k ∧ 10 ≤ k ∧ k % X k % 2 ≠ 1) ↔
    k ∈ [27, 35, 51, 57, 65, 77, 87, 93, 95] := by
  decide +kernel

/-! ## Helper lemmas -/

/-- An even number `n ≥ 4` is composite. -/
theorem isComposite_of_even {n : ℕ} (he : Even n) (h4 : 4 ≤ n) : IsComposite n := by
  refine ⟨by omega, fun hp => ?_⟩
  have h2 : n = 2 := (Nat.Prime.even_iff hp).1 he
  omega

/-- `n ≥ 4` with `n % 2 = 0` is composite. -/
theorem isComposite_of_mod_two {n : ℕ} (he : n % 2 = 0) (h4 : 4 ≤ n) : IsComposite n :=
  isComposite_of_even (Nat.even_iff.2 he) h4

/-- An odd number is a sum of two primes iff `k - 2` is prime (one summand must be `2`). -/
theorem isSumTwoPrimes_iff_of_odd {k : ℕ} (hk : Odd k) :
    IsSumTwoPrimes k ↔ (k - 2).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    rcases Nat.even_or_odd p with hpe | hpo
    · have hp2 : p = 2 := (Nat.Prime.even_iff hp).1 hpe
      subst hp2
      simpa using hq
    · have hqe : Even q := by
        rcases Nat.even_or_odd q with h | h
        · exact h
        · exact absurd hk (Nat.not_odd_iff_even.2 (hpo.add_odd h))
      have hq2 : q = 2 := (Nat.Prime.even_iff hq).1 hqe
      subst hq2
      simpa using hp
  · intro hp
    have h2 : 2 ≤ k - 2 := hp.two_le
    exact ⟨2, k - 2, Nat.prime_two, hp, by omega⟩

/-- The least `m` with `m, m - 1, m - 2` all composite is `10`. -/
theorem ten_le_of_tripleComposite {m : ℕ} (h : TripleComposite m) : 10 ≤ m := by
  by_contra hlt
  interval_cases m <;> revert h <;> decide

/-- `8, 9, 10` are all composite. -/
theorem tripleComposite_ten : TripleComposite 10 := by decide

/-- Irwin's `x` exists below `k` exactly when `10 ≤ k`. -/
theorem exists_tripleComposite_iff (k : ℕ) :
    (∃ m ≤ k, TripleComposite m) ↔ 10 ≤ k := by
  constructor
  · rintro ⟨m, hm, ht⟩
    have h10 : 10 ≤ m := ten_le_of_tripleComposite ht
    omega
  · intro hk
    exact ⟨10, hk, tripleComposite_ten⟩

/-- Characterization of `X k = m`: `m ≤ k` is a composite triple top and no
larger `n ≤ k` is. -/
theorem X_eq_of {k m : ℕ} (hm : m ≤ k) (ht : TripleComposite m)
    (hgt : ∀ n, m < n → n ≤ k → ¬ TripleComposite n) : X k = m := by
  unfold X
  rw [Nat.findGreatest_eq_iff]
  exact ⟨hm, fun _ => ht, fun n h1 h2 => hgt n h1 h2⟩

/-- If one of `n, n - 1, n - 2` is prime then `n` is not a composite triple top. -/
theorem not_tripleComposite_of_prime {n : ℕ} (h : n.Prime ∨ (n - 1).Prime ∨ (n - 2).Prime) :
    ¬ TripleComposite n := by
  rintro ⟨_, h0, h1, h2⟩
  rcases h with h | h | h
  · exact h0.2 h
  · exact h1.2 h
  · exact h2.2 h

/-- For `2 * d < k`, `k mod (k - d) = d`. -/
theorem mod_sub_self {k d : ℕ} (h : 2 * d < k) : k % (k - d) = d := by
  rw [Nat.mod_eq_sub_mod (by omega)]
  have e : k - (k - d) = d := by omega
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

/-- Odd `k ≥ 11` with `k` and `k - 2` composite: `X k = k`. -/
theorem X_eq_self {k : ℕ} (hk : k % 2 = 1) (h11 : 11 ≤ k) (hc : IsComposite k)
    (h2 : ¬ (k - 2).Prime) : X k = k := by
  apply X_eq_of le_rfl
  · exact ⟨by omega, hc, isComposite_of_mod_two (by omega) (by omega), ⟨by omega, h2⟩⟩
  · intro n h1 h2
    omega

/-- Odd `k ≥ 11` prime with `k - 2` composite: `X k = k - 1`. -/
theorem X_eq_sub_one {k : ℕ} (hk : k % 2 = 1) (h11 : 11 ≤ k) (hp : k.Prime)
    (h2 : ¬ (k - 2).Prime) : X k = k - 1 := by
  apply X_eq_of (by omega)
  · have e1 : k - 1 - 1 = k - 2 := by omega
    have e2 : k - 1 - 2 = k - 3 := by omega
    refine ⟨by omega, isComposite_of_mod_two (by omega) (by omega), ?_, ?_⟩
    · rw [e1]
      exact ⟨by omega, h2⟩
    · rw [e2]
      exact isComposite_of_mod_two (by omega) (by omega)
  · intro n h1 h2
    have hn : n = k := by omega
    subst hn
    exact not_tripleComposite_of_prime (Or.inl hp)

/-- Odd `k ≥ 11` with `k - 2` prime and `k - 4` composite: `X k = k - 3`. -/
theorem X_eq_sub_three {k : ℕ} (hk : k % 2 = 1) (h11 : 11 ≤ k) (h2 : (k - 2).Prime)
    (h4 : IsComposite (k - 4)) : X k = k - 3 := by
  apply X_eq_of (by omega)
  · have e1 : k - 3 - 1 = k - 4 := by omega
    have e2 : k - 3 - 2 = k - 5 := by omega
    refine ⟨by omega, isComposite_of_mod_two (by omega) (by omega), ?_, ?_⟩
    · rw [e1]
      exact h4
    · rw [e2]
      exact isComposite_of_mod_two (by omega) (by omega)
  · intro n hlt hle
    apply not_tripleComposite_of_prime
    rcases (show n = k ∨ n = k - 1 ∨ n = k - 2 by omega) with rfl | rfl | rfl
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl (by rwa [show k - 1 - 1 = k - 2 by omega]))
    · exact Or.inl h2

/-- Mod-3 step: for odd `k ≥ 11` with `k - 2` and `k - 4` prime, `3 ∣ k - 6`, so
`k - 6` is composite. -/
theorem isComposite_sub_six {k : ℕ} (hk : k % 2 = 1) (h11 : 11 ≤ k) (h2 : (k - 2).Prime)
    (h4 : (k - 4).Prime) : IsComposite (k - 6) := by
  have n2 : ¬ 3 ∣ k - 2 := fun hd => by
    have h3 : 3 = k - 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).1 hd
    omega
  have n4 : ¬ 3 ∣ k - 4 := fun hd => by
    have h3 : 3 = k - 4 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h4).1 hd
    omega
  have e2 : k - 2 = (k - 6) + 4 := by omega
  have e4 : k - 4 = (k - 6) + 2 := by omega
  rw [e2] at n2
  rw [e4] at n4
  have d6 : 3 ∣ k - 6 := by omega
  refine ⟨by omega, fun h6 => ?_⟩
  have h3 : 3 = k - 6 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h6).1 d6
  omega

/-- Odd `k ≥ 11` with `k - 2` and `k - 4` prime: `X k = k - 5`. -/
theorem X_eq_sub_five {k : ℕ} (hk : k % 2 = 1) (h11 : 11 ≤ k) (h2 : (k - 2).Prime)
    (h4 : (k - 4).Prime) : X k = k - 5 := by
  apply X_eq_of (by omega)
  · have e1 : k - 5 - 1 = k - 6 := by omega
    have e2 : k - 5 - 2 = k - 7 := by omega
    refine ⟨by omega, isComposite_of_mod_two (by omega) (by omega), ?_, ?_⟩
    · rw [e1]
      exact isComposite_sub_six hk h11 h2 h4
    · rw [e2]
      exact isComposite_of_mod_two (by omega) (by omega)
  · intro n hlt hle
    apply not_tripleComposite_of_prime
    rcases (show n = k ∨ n = k - 1 ∨ n = k - 2 ∨ n = k - 3 ∨ n = k - 4 by omega) with
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl (by rwa [show k - 1 - 1 = k - 2 by omega]))
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by rwa [show k - 3 - 1 = k - 4 by omega]))
    · exact Or.inl h4

/-! ## The odd part of Irwin's conjecture (proved) -/

/-- **Odd part of Irwin's conjecture (A025583), proved.**  For odd `k`, `k` is a
composite number that is not a sum of two primes iff Irwin's `x` (the greatest
`m ≤ k` with `m, m - 1, m - 2` composite) exists and `(k mod x) mod 2 ≠ 1`.

Proof: an odd `k` is a sum of two primes iff `k - 2` is prime.  If `k, k - 2`
are composite then `x = k` and the remainder is `0`; if `k` is prime and
`k - 2` composite then `x = k - 1` and the remainder is `1`; if `k - 2` is prime
then a mod-3 argument on `k - 2, k - 4, k - 6` gives `x = k - 3` or `x = k - 5`
and the remainder is `3` or `5`. -/
theorem inSeq_iff_of_odd {k : ℕ} (hk : Odd k) :
    InSeq k ↔ (∃ m ≤ k, TripleComposite m) ∧ k % X k % 2 ≠ 1 := by
  rw [exists_tripleComposite_iff]
  have hk2 : k % 2 = 1 := Nat.odd_iff.1 hk
  by_cases h11 : k < 11
  · interval_cases k <;> first | omega | decide
  push Not at h11
  have hseq : InSeq k ↔ IsComposite k ∧ ¬ (k - 2).Prime := by
    unfold InSeq
    rw [isSumTwoPrimes_iff_of_odd hk]
  rw [hseq]
  by_cases h2 : (k - 2).Prime
  · simp only [h2, not_true_eq_false, and_false, false_iff, not_and, not_not]
    intro _
    by_cases h4 : IsComposite (k - 4)
    · rw [X_eq_sub_three hk2 h11 h2 h4, mod_sub_self (by omega)]
    · have h4p : (k - 4).Prime := by
        by_contra hn
        exact h4 ⟨by omega, hn⟩
      rw [X_eq_sub_five hk2 h11 h2 h4p, mod_sub_self (by omega)]
  · by_cases hc : IsComposite k
    · rw [X_eq_self hk2 h11 hc h2, Nat.mod_self]
      simp only [hc, h2, not_false_eq_true, and_self, true_iff]
      omega
    · have hp : k.Prime := by
        by_contra hn
        exact hc ⟨by omega, hn⟩
      rw [X_eq_sub_one hk2 h11 hp h2, mod_sub_self (by omega)]
      simp [hc]

/-! ## The full conjecture -/

/-- **Irwin's conjecture (A025583, Benedict W. J. Irwin, May 06 2016)**, as a
proposition.  Verbatim: "Conjecture: This is the sequence of odd numbers k such
that (k mod x) mod 2 != 1, where x is the greatest m <= k such that m, m-1 and
m-2 are all composite."  The existence of `x` is part of the right-hand side. -/
def IrwinConjecture : Prop :=
  ∀ k : ℕ, InSeq k ↔ Odd k ∧ (∃ m ≤ k, TripleComposite m) ∧ k % X k % 2 ≠ 1

/-- The binary (strong) Goldbach conjecture: every even `n ≥ 4` is a sum of two
primes.  Open. -/
def Goldbach : Prop := ∀ n : ℕ, Even n → 4 ≤ n → IsSumTwoPrimes n

/-- **Irwin's conjecture is equivalent to the binary Goldbach conjecture.**
The odd part holds unconditionally (`inSeq_iff_of_odd`); the even part says
exactly that no even composite fails to be a sum of two primes. -/
theorem irwinConjecture_iff_goldbach : IrwinConjecture ↔ Goldbach := by
  constructor
  · intro hI n he h4
    by_contra hn
    have hin : InSeq n := ⟨isComposite_of_even he h4, hn⟩
    exact Nat.not_odd_iff_even.2 he ((hI n).1 hin).1
  · intro hG k
    rcases Nat.even_or_odd k with he | ho
    · have hnot : ¬ InSeq k := by
        rintro ⟨hc, hns⟩
        have h4 : 4 ≤ k := by
          have hk0 : k % 2 = 0 := Nat.even_iff.1 he
          by_contra hlt
          have h1 : 1 < k := hc.1
          interval_cases k
          · exact hc.2 Nat.prime_two
          · omega
        exact hns (hG k he h4)
      have hno : ¬ Odd k := Nat.not_odd_iff_even.2 he
      simp only [hnot, hno, false_and]
    · rw [inSeq_iff_of_odd ho]
      simp only [ho, true_and]

/-- **Irwin's conjecture (A025583, Benedict W. J. Irwin, May 06 2016).**
The composite numbers that are not a sum of two primes are exactly the odd `k`
for which Irwin's `x` (the greatest `m ≤ k` with `m, m - 1, m - 2` composite)
exists and `(k mod x) mod 2 ≠ 1`.

Reduced to the binary Goldbach conjecture by `irwinConjecture_iff_goldbach`;
the single remaining `sorry` is exactly `Goldbach`, which is open. -/
theorem irwinConjecture (k : ℕ) :
    InSeq k ↔ Odd k ∧ (∃ m ≤ k, TripleComposite m) ∧ k % X k % 2 ≠ 1 := by
  have hG : Goldbach := by
    -- Remaining goal: `∀ n : ℕ, Even n → 4 ≤ n → IsSumTwoPrimes n`
    -- (binary Goldbach conjecture; open).
    sorry
  exact irwinConjecture_iff_goldbach.2 hG k

end Candidates.A025583CompositeSumTwo
