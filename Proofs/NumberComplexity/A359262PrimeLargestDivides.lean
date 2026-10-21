/-
# A359262 — Eldar: `a(n) ≥ prime(k) - 2` iff `prime(n) ≡ 1 (mod A002110(k-1))`

## OEIS source (retrieved with `oeis show A359262` and https://oeis.org/A359262/internal,
## 2026-10-21)

```
NAME:     a(n) is the largest number m such that prime(n)^m is in A359260.
TERMS:    0,1,1,3,1,3,1,3,1,1,5,3,1,3,1,1,1,5,3,1,3,3,1,1,3,1,3,1,3,1,3,1,1,3,1,5,
          3,3,1,1,1,5,1,3,1,3,9,3,1,3,1,1,5,1,1,1,1,5,3,1,3,1,3,1,3,1,5,3,1,3,...
KEYWORDS: nonn,easy
AUTHOR:   Amiram Eldar, Dec 23 2022
COMMENT:  a(n) is the largest number m such that the arithmetic mean of
          {1, p, p^2, ..., p^k} is an integer for all k in 1..m.
COMMENT:  Apparently, all the terms are of the form prime(k)-2 (A040976).
          Conjecture: The asymptotic density of the occurrences of prime(k)-2 is
          (1/s(k-1)-1/s(k)), where s(k) = A005867(k) = phi(prime(k)#), and
          prime(k)# is the k-th primorial number (A002110).
FORMULA:  a(n) >= 1 for n >= 2.
          a(n) >= 3 iff prime(n) == 1 (mod 6) (prime(n) is in A002476).
          Conjectures:
          a(n) >= 5 iff prime(n) == 1 (mod 30) (prime(n) is in A132230).
          a(n) >= 9 iff prime(n) == 1 (mod 210) (prime(n) is in A073102).
          a(n) >= prime(k) - 2 iff prime(n) == 1 (mod A002110(k-1)).
```

The conjecture lines carry no separate attribution; they are part of the entry by
Amiram Eldar, Dec 23 2022.

## Definition fidelity

The entry's first comment is used as the definition (`MeanIntegralUpTo`, `largestM`).
It agrees with the NAME: the divisors of `p^m` (`p` prime) in increasing order are
`1, p, …, p^m`, so `p^m ∈ A359260` iff `(k + 1) ∣ 1 + p + ⋯ + p^k` for all `k ∈ 1..m`.
`prime n = Nat.nth Nat.Prime (n - 1)` carries the OEIS offset 1.

## Status

Triage literature status: open (no proof in the entry or found in the literature).
This file proves the general formula line (`conjecture`), the mod 30 and mod 210
conjecture lines, the mod 6 and `a(n) ≥ 1` formula lines, and the comment "all the terms
are of the form prime(k)-2". Key fact: `a(p) + 2` is the least prime `q` with
`p ≢ 1 (mod q)` (`meanIntegralUpTo_iff`, `prime_largestM_add_two`).

Not formalized: the asymptotic-density conjecture in the second comment. It follows from
`conjecture` together with the prime number theorem in arithmetic progressions (natural
density `1/φ(M)` of primes `≡ 1 (mod M)`), which is not available in Mathlib.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A359262PrimeLargestDivides

/-- `geomSum p k = 1 + p + p^2 + ⋯ + p^k`. -/
def geomSum (p k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), p ^ i

/-- Fermat step: if the prime `q` divides `1 + x + ⋯ + x^(q-1)` then `x ≡ 1 (mod q)`. -/
theorem modEq_one_of_dvd_geom_sum {q x : ℕ} (hq : q.Prime)
    (hdvd : q ∣ ∑ i ∈ Finset.range q, x ^ i) : x ≡ 1 [MOD q] := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hsum : ((∑ i ∈ Finset.range q, x ^ i : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hgeom := geom_sum_mul (x : ZMod q) q
  push_cast at hsum
  rw [hsum, zero_mul, ZMod.pow_card] at hgeom
  have hx : (x : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [Nat.cast_one]; exact (sub_eq_zero.1 hgeom.symm)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hx

/-- If `x ≡ 1 (mod q)` then `q ∣ 1 + x + ⋯ + x^(q-1)`. -/
theorem dvd_geom_sum_of_modEq_one {q x : ℕ} (hx : x ≡ 1 [MOD q]) :
    q ∣ ∑ i ∈ Finset.range q, x ^ i := by
  have h : ((∑ i ∈ Finset.range q, x ^ i : ℕ) : ZMod q) = 0 := by
    have hx' : (x : ZMod q) = 1 := by
      rw [← Nat.cast_one]; exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hx
    push_cast
    simp [hx']
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- Multiplicativity of geometric sums: `S_{a b}(x) = S_a(x) · S_b(x^a)`. -/
theorem geom_sum_mul_range (x a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), x ^ i =
      (∑ i ∈ Finset.range a, x ^ i) * ∑ j ∈ Finset.range b, (x ^ a) ^ j := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ (fun j => (x ^ a) ^ j),
      mul_add, Finset.mul_sum]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, ← pow_mul, mul_comm]

/-- If every prime factor `q` of `N` satisfies `x ≡ 1 (mod q)`, then `N ∣ 1 + x + ⋯ + x^(N-1)`. -/
theorem dvd_geom_sum_of_forall_prime (N : ℕ) :
    ∀ x : ℕ, (∀ q : ℕ, q.Prime → q ∣ N → x ≡ 1 [MOD q]) →
      N ∣ ∑ i ∈ Finset.range N, x ^ i := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hx
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N <;> simp
    obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
    obtain ⟨M, rfl⟩ := hqN
    have hM : M < q * M := by
      have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
      exact lt_mul_left hMpos hq.one_lt
    rw [geom_sum_mul_range]
    refine mul_dvd_mul (dvd_geom_sum_of_modEq_one (hx q hq (dvd_mul_right q M))) ?_
    refine ih M hM (x ^ q) fun r hr hrM => ?_
    have h1 := (hx r hr (dvd_mul_of_dvd_right hrM q)).pow q
    rwa [one_pow] at h1

/-- The entry's condition on `m` (first comment of A359262): the arithmetic mean of
`{1, p, p^2, …, p^k}` is an integer, i.e. `(k + 1) ∣ 1 + p + ⋯ + p^k`, for every `k` in `1..m`. -/
def MeanIntegralUpTo (p m : ℕ) : Prop := ∀ k ∈ Finset.Icc 1 m, (k + 1) ∣ geomSum p k

/-- `MeanIntegralUpTo p m` is decidable (a bounded check over `k ∈ 1..m`). -/
instance (p m : ℕ) : Decidable (MeanIntegralUpTo p m) := by
  unfold MeanIntegralUpTo; infer_instance

/-- `largestM p` is the largest `m` with `MeanIntegralUpTo p m`
(an `sSup` over `ℕ`; `largestM_eq` and `le_largestM_iff` show it is attained). -/
noncomputable def largestM (p : ℕ) : ℕ := sSup {m | MeanIntegralUpTo p m}

/-- `prime n` is the `n`-th prime with the OEIS offset 1: `prime 1 = 2`, `prime 2 = 3`, …
(only used at `1 ≤ n`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A002110: the primorial `A002110 j = prime(1) * prime(2) * ⋯ * prime(j)`, `A002110 0 = 1`. -/
noncomputable def A002110 (j : ℕ) : ℕ := ∏ i ∈ Finset.range j, Nat.nth Nat.Prime i

/-- A359262: `a n` is the largest `m` such that the arithmetic mean of `{1, p, …, p^k}` is an
integer for all `k` in `1..m`, where `p = prime n` (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := largestM (prime n)

/-! ## Characterization -/

/-- **Characterization.** For every natural `p` and `m`:
`(k + 1) ∣ 1 + p + ⋯ + p^k` for all `k ∈ 1..m` iff `p ≡ 1 (mod q)` for every prime `q ≤ m + 1`. -/
theorem meanIntegralUpTo_iff (p m : ℕ) :
    MeanIntegralUpTo p m ↔ ∀ q : ℕ, q.Prime → q ≤ m + 1 → p ≡ 1 [MOD q] := by
  constructor
  · intro h q hq hqm
    have hk : q - 1 ∈ Finset.Icc 1 m := by
      have := hq.two_le
      rw [Finset.mem_Icc]; omega
    have h1 := h (q - 1) hk
    have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
    rw [geomSum, hq1] at h1
    exact modEq_one_of_dvd_geom_sum hq h1
  · intro h k hk
    rw [Finset.mem_Icc] at hk
    rw [geomSum]
    refine dvd_geom_sum_of_forall_prime (k + 1) p fun q hq hqk => h q hq ?_
    have := Nat.le_of_dvd (by omega) hqk
    omega

/-- The condition is downward closed in `m`. -/
theorem MeanIntegralUpTo.mono {p m m' : ℕ} (h : MeanIntegralUpTo p m) (hm : m' ≤ m) :
    MeanIntegralUpTo p m' := fun k hk =>
  h k (Finset.Icc_subset_Icc le_rfl hm hk)

/-- If the condition holds at `m` and fails at `m + 1`, then `largestM p = m`. -/
theorem largestM_eq {p m : ℕ} (h1 : MeanIntegralUpTo p m) (h2 : ¬ MeanIntegralUpTo p (m + 1)) :
    largestM p = m := by
  have hset : {m' | MeanIntegralUpTo p m'} = Set.Iic m := by
    ext m'
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    refine ⟨fun h => ?_, fun h => h1.mono h⟩
    by_contra hlt
    exact h2 (h.mono (by omega))
  rw [largestM, hset, csSup_Iic]

/-- For `2 ≤ p` the set of admissible `m` is bounded, so `m ≤ largestM p` iff the condition
holds at `m`. -/
theorem le_largestM_iff {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    m ≤ largestM p ↔ MeanIntegralUpTo p m := by
  obtain ⟨q, hpq, hq⟩ := Nat.exists_infinite_primes p
  have hbdd : BddAbove {m' | MeanIntegralUpTo p m'} := by
    refine ⟨q, fun m' hm' => ?_⟩
    by_contra hlt
    have hmod := (meanIntegralUpTo_iff p m').1 hm' q hq (by omega)
    rcases Nat.eq_or_lt_of_le hpq with heq | hlt'
    · subst heq
      have : p % p = 1 % p := hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · have : p % q = 1 % q := hmod
      rw [Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt hq.one_lt] at this
      omega
  have hne : ({m' | MeanIntegralUpTo p m'} : Set ℕ).Nonempty :=
    ⟨0, fun k hk => by simp at hk⟩
  constructor
  · intro hm
    exact (Nat.sSup_mem hne hbdd).mono hm
  · intro hm
    exact le_csSup hbdd hm

/-- Divisibility by the primorial `A002110 j` is divisibility by each of the first `j` primes. -/
theorem A002110_dvd_iff (j n : ℕ) :
    A002110 j ∣ n ↔ ∀ i < j, Nat.nth Nat.Prime i ∣ n := by
  induction j with
  | zero => simp [A002110]
  | succ j ih =>
    rw [A002110, Finset.prod_range_succ, ← A002110]
    have hpj : (Nat.nth Nat.Prime j).Prime := Nat.prime_nth_prime j
    have hcop : Nat.Coprime (A002110 j) (Nat.nth Nat.Prime j) := by
      refine Nat.Coprime.prod_left fun i hi => ?_
      rw [Finset.mem_range] at hi
      refine (Nat.coprime_primes (Nat.prime_nth_prime i) hpj).2 ?_
      exact ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) hi).ne
    constructor
    · intro h i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact (ih.1 (dvd_trans (dvd_mul_right _ _) h)) i hi
      · exact dvd_trans (dvd_mul_left _ _) h
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (ih.2 fun i hi => h i (by omega)) (h j (by omega))

/-- The primes below the `j`-th prime (0-indexed) are exactly the `Nat.nth Nat.Prime i`, `i < j`. -/
theorem forall_prime_lt_nth_iff (P : ℕ → Prop) (j : ℕ) :
    (∀ q : ℕ, q.Prime → q < Nat.nth Nat.Prime j → P q) ↔ ∀ i < j, P (Nat.nth Nat.Prime i) := by
  constructor
  · intro h i hi
    exact h _ (Nat.prime_nth_prime i) ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) hi)
  · intro h q hq hqj
    have hq' := Nat.nth_count hq
    rw [← hq'] at hqj ⊢
    exact h _ ((Nat.nth_lt_nth Nat.infinite_setOfPred_prime).1 hqj)

/-- `p ≡ 1 (mod n)` is `n ∣ p - 1` for `1 ≤ p`. -/
theorem modEq_one_iff_dvd_sub_one {p n : ℕ} (hp : 1 ≤ p) : p ≡ 1 [MOD n] ↔ n ∣ p - 1 := by
  rw [Nat.ModEq.comm]; exact Nat.modEq_iff_dvd' hp

/-- **Main lemma (prime-free form).** For `2 ≤ p` and any `j`, the `(j+1)`-st prime
`Nat.nth Nat.Prime j` satisfies `Nat.nth Nat.Prime j ≤ largestM p + 2` iff
`p ≡ 1 (mod A002110 j)`. -/
theorem nth_prime_le_largestM_add_two_iff {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    Nat.nth Nat.Prime j ≤ largestM p + 2 ↔ p ≡ 1 [MOD A002110 j] := by
  have h2 : 2 ≤ Nat.nth Nat.Prime j := (Nat.prime_nth_prime j).two_le
  have hstep1 : Nat.nth Nat.Prime j ≤ largestM p + 2 ↔
      Nat.nth Nat.Prime j - 2 ≤ largestM p := by omega
  have hstep2 : (∀ q : ℕ, q.Prime → q ≤ Nat.nth Nat.Prime j - 2 + 1 → p ≡ 1 [MOD q]) ↔
      ∀ q : ℕ, q.Prime → q < Nat.nth Nat.Prime j → p ≡ 1 [MOD q] := by
    refine forall_congr' fun q => forall_congr' fun _ => ?_
    constructor
    · intro h hq; exact h (by omega)
    · intro h hq; exact h (by omega)
  rw [hstep1, le_largestM_iff hp, meanIntegralUpTo_iff, hstep2,
    forall_prime_lt_nth_iff (fun q => p ≡ 1 [MOD q]) j,
    modEq_one_iff_dvd_sub_one (by omega), A002110_dvd_iff]
  exact forall₂_congr fun i _ => modEq_one_iff_dvd_sub_one (by omega)

/-- **Structure of the terms.** For `2 ≤ p`, `largestM p + 2` is prime: it is the least prime
`q` with `p ≢ 1 (mod q)`. -/
theorem prime_largestM_add_two {p : ℕ} (hp : 2 ≤ p) : (largestM p + 2).Prime := by
  set L := largestM p with hL
  have hin : MeanIntegralUpTo p L := (le_largestM_iff hp L).1 le_rfl
  have hout : ¬ MeanIntegralUpTo p (L + 1) := fun h =>
    absurd ((le_largestM_iff hp (L + 1)).2 h) (by omega)
  rw [meanIntegralUpTo_iff] at hin hout
  push Not at hout
  obtain ⟨q, hq, hqL, hqmod⟩ := hout
  have hqeq : q = L + 2 := by
    by_contra hne
    exact hqmod (hin q hq (by omega))
  rwa [← hqeq]

/-! ## Ground truth against the listed terms -/

example : largestM 2 = 0 := largestM_eq (by decide) (by decide)
example : largestM 3 = 1 := largestM_eq (by decide) (by decide)
example : largestM 7 = 3 := largestM_eq (by decide) (by decide)
example : largestM 31 = 5 := largestM_eq (by decide) (by decide)
example : largestM 211 = 9 := largestM_eq (by decide) (by decide)

example : prime 4 = 7 := Nat.nth_prime_three_eq_seven
example : a 1 = 0 := by
  rw [a, prime, Nat.sub_self, Nat.nth_prime_zero_eq_two]; exact largestM_eq (by decide) (by decide)
example : a 2 = 1 := by
  rw [a, prime, show 2 - 1 = 1 from rfl, Nat.nth_prime_one_eq_three]
  exact largestM_eq (by decide) (by decide)
example : a 3 = 1 := by
  rw [a, prime, show 3 - 1 = 2 from rfl, Nat.nth_prime_two_eq_five]
  exact largestM_eq (by decide) (by decide)
example : a 4 = 3 := by
  rw [a, prime, show 4 - 1 = 3 from rfl, Nat.nth_prime_three_eq_seven]
  exact largestM_eq (by decide) (by decide)
example : a 5 = 1 := by
  rw [a, prime, show 5 - 1 = 4 from rfl, Nat.nth_prime_four_eq_eleven]
  exact largestM_eq (by decide) (by decide)

/-- Values of the primorial used by the special cases: `A002110 2 = 6`. -/
theorem A002110_two : A002110 2 = 6 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- `A002110 3 = 30`. -/
theorem A002110_three : A002110 3 = 30 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five]

/-- `A002110 4 = 210`. -/
theorem A002110_four : A002110 4 = 210 := by
  simp [A002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-! ## The conjecture -/

/-- **A359262 conjecture (Amiram Eldar, Dec 23 2022), proved.**

Verbatim formula line: "a(n) >= prime(k) - 2 iff prime(n) == 1 (mod A002110(k-1))."

Here `a n` is the largest `m` such that the arithmetic mean of `{1, p, …, p^k}`, `p = prime n`,
is an integer for all `k` in `1..m`, and `A002110 (k-1)` is the product of the first `k - 1`
primes (`A002110 0 = 1`). Since `prime k ≥ 2`, the inequality `a(n) ≥ prime(k) - 2` is stated
subtraction-free as `prime k ≤ a n + 2`. The guards `1 ≤ n`, `1 ≤ k` record the OEIS offsets;
the proof does not need them. -/
theorem conjecture (n k : ℕ) (_hn : 1 ≤ n) (_hk : 1 ≤ k) :
    prime k ≤ a n + 2 ↔ prime n ≡ 1 [MOD A002110 (k - 1)] := by
  have hp : 2 ≤ prime n := (Nat.prime_nth_prime (n - 1)).two_le
  have hpk : prime k = Nat.nth Nat.Prime (k - 1) := rfl
  rw [hpk, a]
  exact nth_prime_le_largestM_add_two_iff hp (k - 1)

/-- **Proved formula line of A359262**: "a(n) >= 3 iff prime(n) == 1 (mod 6)". -/
theorem three_le_a_iff (n : ℕ) (hn : 1 ≤ n) : 3 ≤ a n ↔ prime n ≡ 1 [MOD 6] := by
  have h := conjecture n 3 hn (by norm_num)
  rw [show prime 3 = 5 from Nat.nth_prime_two_eq_five, show 3 - 1 = 2 from rfl,
    A002110_two] at h
  rw [← h]; omega

/-- **Conjecture line of A359262 (Amiram Eldar, Dec 23 2022), proved**:
"a(n) >= 5 iff prime(n) == 1 (mod 30)". -/
theorem five_le_a_iff (n : ℕ) (hn : 1 ≤ n) : 5 ≤ a n ↔ prime n ≡ 1 [MOD 30] := by
  have h := conjecture n 4 hn (by norm_num)
  rw [show prime 4 = 7 from Nat.nth_prime_three_eq_seven, show 4 - 1 = 3 from rfl,
    A002110_three] at h
  rw [← h]; omega

/-- **Conjecture line of A359262 (Amiram Eldar, Dec 23 2022), proved**:
"a(n) >= 9 iff prime(n) == 1 (mod 210)". -/
theorem nine_le_a_iff (n : ℕ) (hn : 1 ≤ n) : 9 ≤ a n ↔ prime n ≡ 1 [MOD 210] := by
  have h := conjecture n 5 hn (by norm_num)
  rw [show prime 5 = 11 from Nat.nth_prime_four_eq_eleven, show 5 - 1 = 4 from rfl,
    A002110_four] at h
  rw [← h]; omega

/-- **Comment of A359262, proved**: "Apparently, all the terms are of the form prime(k)-2":
for every `n ≥ 1` there is `k ≥ 1` with `a n + 2 = prime k`. -/
theorem exists_a_add_two_eq_prime (n : ℕ) (_hn : 1 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ a n + 2 = prime k := by
  have hp : 2 ≤ prime n := (Nat.prime_nth_prime (n - 1)).two_le
  have hq : (a n + 2).Prime := prime_largestM_add_two hp
  refine ⟨Nat.count Nat.Prime (a n + 2) + 1, by omega, ?_⟩
  rw [prime, Nat.add_sub_cancel, Nat.nth_count hq]

/-- **Formula line of A359262**: "a(n) >= 1 for n >= 2". -/
theorem one_le_a (n : ℕ) (hn : 2 ≤ n) : 1 ≤ a n := by
  have hodd : prime n ≡ 1 [MOD 2] := by
    have hpr : (prime n).Prime := Nat.prime_nth_prime (n - 1)
    have hne : prime n ≠ 2 := by
      intro h2
      have h0 : Nat.nth Nat.Prime (n - 1) = Nat.nth Nat.Prime 0 := by
        rw [Nat.nth_prime_zero_eq_two]; exact h2
      have := Nat.nth_injective Nat.infinite_setOfPred_prime h0
      omega
    exact Nat.odd_iff.1 (hpr.odd_of_ne_two hne)
  have h := conjecture n 2 (by omega) (by norm_num)
  rw [show prime 2 = 3 from Nat.nth_prime_one_eq_three, show 2 - 1 = 1 from rfl] at h
  have h1 : A002110 1 = 2 := by simp [A002110, Nat.nth_prime_zero_eq_two]
  rw [h1] at h
  have := h.2 hodd
  omega

end Candidates.A359262PrimeLargestDivides
