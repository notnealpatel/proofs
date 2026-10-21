/-
# A187716 — a Sierpiński number divisible by `3` below `21484572547591559649`

## OEIS source (retrieved with `oeis show A187716`, 2026-10-21)

```
NAME:     Odd numbers m divisible by 3 such that for every k >= 1, m*2^k + 1
          has a divisor in the set {5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73,
          109, 151, 241, 331}.
TERMS:    21484572547591559649,50166404682516122859,51814002736113272553,
          53246606581410442023,58992081042572747991,65634687179877002283,
          80269357428943941837,92027572854849003627,103083799330841020677
XREFS:    Cf. A076336, A187714.
COMMENT:  Wilfrid Keller (2004, published) gave the first known example.
COMMENT:  21484572547591559649 computed in 2017 by the author.
COMMENT (the conjecture):
  Conjecture: 21484572547591559649 is the smallest Sierpiński number that is
  divisible by 3. - _Arkadiusz Wesolowski_, May 12 2017
COMMENT (later retraction by the same author):
  The above conjecture is false, because the Sierpiński number
  7592506760633776533 is a counterexample. - _Arkadiusz Wesolowski_, Jul 27 2023
```

## Status

The conjecture is already retracted in the entry (Jul 27 2023); this module
kernel-checks that retraction.  The counterexample `m = 7592506760633776533`
is odd, divisible by `3`, smaller than `21484572547591559649`, and is a
Sierpiński number: every `m * 2 ^ k + 1` (`k ≥ 1`) is divisible by a prime of
`{5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97, 109, 151, 331, 673}`, the
residue of `k` modulo `720` selecting the prime.  It escapes the entry's
fifteen-prime covering set (at `k = 29`, for instance), which is why the 2017
search over that set missed it.

Definitions: a Sierpiński number (A076336) is an odd `n` such that `n * 2 ^ k + 1`
is composite for every `k ≥ 1`.  For odd `n ≥ 1` and `k ≥ 1` the number
`n * 2 ^ k + 1 ≥ 3`, so "composite" is "not prime".
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A187716Refutation

/-! ## Covering certificates -/

/-- **Covering lemma.** If every prime-candidate `p ∈ S` satisfies
`2 ^ P ≡ 1 [MOD p]` and every residue `r < P` has some `p ∈ S` dividing
`n * 2 ^ r + 1`, then for every `k` some `p ∈ S` divides `n * 2 ^ k + 1`. -/
theorem exists_dvd_of_cover (n P : ℕ) (S : List ℕ) (hP : 0 < P)
    (hS : ∀ p ∈ S, 2 ^ P ≡ 1 [MOD p])
    (hcov : ∀ r < P, ∃ p ∈ S, p ∣ n * 2 ^ r + 1) (k : ℕ) :
    ∃ p ∈ S, p ∣ n * 2 ^ k + 1 := by
  obtain ⟨p, hpS, hpdvd⟩ := hcov (k % P) (Nat.mod_lt k hP)
  refine ⟨p, hpS, ?_⟩
  have hpow : 2 ^ k ≡ 2 ^ (k % P) [MOD p] := by
    have hsplit : 2 ^ k = (2 ^ P) ^ (k / P) * 2 ^ (k % P) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hone : (2 ^ P) ^ (k / P) ≡ 1 [MOD p] := by
      simpa only [one_pow] using (hS p hpS).pow (k / P)
    rw [hsplit]
    simpa only [one_mul] using hone.mul_right (2 ^ (k % P))
  have hmod : n * 2 ^ k + 1 ≡ n * 2 ^ (k % P) + 1 [MOD p] :=
    (hpow.mul_left n).add_right 1
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hpdvd))


/-- **Covering lemma, primality form.** Under the hypotheses of
`exists_dvd_of_cover`, if moreover every `p ∈ S` satisfies `1 < p ≤ n`, then
`n * 2 ^ k + 1` is not prime (for every `k`, including `k = 0`). -/
theorem not_prime_of_cover (n P : ℕ) (S : List ℕ) (hP : 0 < P)
    (hS : ∀ p ∈ S, 2 ^ P ≡ 1 [MOD p])
    (hsize : ∀ p ∈ S, 1 < p ∧ p ≤ n)
    (hcov : ∀ r < P, ∃ p ∈ S, p ∣ n * 2 ^ r + 1) (k : ℕ) :
    ¬ (n * 2 ^ k + 1).Prime := by
  intro hprime
  obtain ⟨p, hpS, hpdvd⟩ := exists_dvd_of_cover n P S hP hS hcov k
  obtain ⟨hp1, hpn⟩ := hsize p hpS
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlt : p < n * 2 ^ k + 1 := by
    calc p ≤ n := hpn
      _ ≤ n * 2 ^ k := Nat.le_mul_of_pos_right n hpow
      _ < n * 2 ^ k + 1 := Nat.lt_succ_self _
  rcases hprime.eq_one_or_self_of_dvd p hpdvd with h | h
  · omega
  · omega

/-! ## Definitions -/

/-- **Sierpiński number (A076336).** An odd `n` such that `n * 2 ^ k + 1` is
composite for every `k ≥ 1`.  Since `n` odd forces `n ≥ 1`, the number
`n * 2 ^ k + 1 ≥ 3` for `k ≥ 1`, so "composite" is "not prime". -/
def IsSierpinski (n : ℕ) : Prop := Odd n ∧ ∀ k : ℕ, 1 ≤ k → ¬ (n * 2 ^ k + 1).Prime

/-- The fifteen primes named in the A187716 definition. -/
def entryPrimes : Finset ℕ := {5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 109, 151, 241, 331}

/-- **A187716 membership.** `m` is odd, divisible by `3`, and for every
`k ≥ 1`, `m * 2 ^ k + 1` has a divisor in `entryPrimes`. -/
def InA187716 (m : ℕ) : Prop :=
  Odd m ∧ 3 ∣ m ∧ ∀ k : ℕ, 1 ≤ k → ∃ p ∈ entryPrimes, p ∣ m * 2 ^ k + 1

/-! ## Ground truth -/

/-- `3` is not a Sierpiński number: `3 * 2 + 1 = 7` is prime. -/
example : ¬ IsSierpinski 3 := fun h => h.2 1 le_rfl (by norm_num)

/-- `78557`, the first term of A076336, is a Sierpiński number (Selfridge's
covering set `{3, 5, 7, 13, 19, 37, 73}` with period `36`). -/
example : IsSierpinski 78557 :=
  ⟨by decide, fun k _ => not_prime_of_cover 78557 36 [3, 5, 7, 13, 19, 37, 73] (by norm_num)
    (by decide) (by decide) (by decide) k⟩

/-- The entry's fifteen primes, as a list. -/
def entryPrimeList : List ℕ := [5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 109, 151, 241, 331]

/-- Every entry of `entryPrimeList` lies in `entryPrimes`. -/
theorem mem_entryPrimes_of_mem_list : ∀ p ∈ entryPrimeList, p ∈ entryPrimes := by
  decide

/-- The first listed term `21484572547591559649` belongs to A187716 (the entry's
fifteen primes cover every residue of `k` modulo `360`). -/
example : InA187716 21484572547591559649 := by
  refine ⟨by decide, by norm_num, fun k _ => ?_⟩
  obtain ⟨p, hp, hdvd⟩ := exists_dvd_of_cover 21484572547591559649 360 entryPrimeList
    (by norm_num) (by decide +kernel) (by decide +kernel) k
  exact ⟨p, mem_entryPrimes_of_mem_list p hp, hdvd⟩


/-! ## The conjecture -/

/-- **Conjecture in A187716 (Arkadiusz Wesolowski, May 12 2017).**
Verbatim: "Conjecture: 21484572547591559649 is the smallest Sierpiński number
that is divisible by 3." -/
def Conjecture : Prop :=
  IsLeast {n : ℕ | IsSierpinski n ∧ 3 ∣ n} 21484572547591559649

/-! ## The counterexample -/

/-- Wesolowski's 2023 counterexample. -/
def counterexample : ℕ := 7592506760633776533

/-- A covering set for `counterexample` with period `720`. -/
def coverList : List ℕ := [5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97, 109, 151, 331, 673]

/-- `7592506760633776533` is a Sierpiński number: every residue of `k` modulo
`720` is covered by a prime of `coverList`, each of which divides `2 ^ 720 - 1`. -/
theorem isSierpinski_counterexample : IsSierpinski counterexample :=
  ⟨by decide, fun k _ => not_prime_of_cover counterexample 720 coverList (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) k⟩

/-- `7592506760633776533` escapes the entry's fifteen-prime covering set: no
prime of `entryPrimes` divides `7592506760633776533 * 2 ^ 29 + 1`. -/
theorem not_inA187716_counterexample : ¬ InA187716 counterexample := by
  intro h
  obtain ⟨p, hp, hdvd⟩ := h.2.2 29 (by norm_num)
  revert hdvd
  revert p
  decide +kernel

/-- **Refutation of the A187716 conjecture.**  Counterexample
`7592506760633776533` (Wesolowski, Jul 27 2023): it is a Sierpiński number,
divisible by `3`, and smaller than `21484572547591559649`.  The conjecture as
the author presumably intended it ("smallest member of A187716", i.e. among
Sierpiński numbers divisible by `3` *covered by the fifteen listed primes*) is
not refuted here; `not_inA187716_counterexample` shows the counterexample lies
outside that restricted class. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hmem : counterexample ∈ {n : ℕ | IsSierpinski n ∧ 3 ∣ n} :=
    ⟨isSierpinski_counterexample, by decide⟩
  have hle : 21484572547591559649 ≤ counterexample := h.2 hmem
  have hlt : counterexample < 21484572547591559649 := by decide
  exact absurd hle (Nat.not_le_of_lt hlt)

end Candidates.A187716Refutation
