/-
# A065091 — Ordowski: the next prime is the least odd `m > p` with `∑ k^(m-1) ≡ p-1 (mod m)`

## OEIS source (retrieved 2026-10-21 with `oeis show A065091`)

```
NAME:     Odd primes.
TERMS:    3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,
          97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,...
COMMENT (the conjecture):
  Conjecture: a(n) is the smallest odd number m > prime(n) such that
  Sum_{k=1..prime(n)-1} k^(m-1) == prime(n)-1 (mod m). This is an extension
  of the Agoh-Giuga conjecture. - _Thomas Ordowski_, Aug 01 2018
```

No later comment in the entry retracts or amends the conjecture.  Offsets:
A065091 has offset 1 (`a(1) = 3`) and `prime(1) = 2`, so `a(n) = prime(n+1)`.

## Status

This module **refutes** the conjecture.  For `p = 198139` (prime) the odd
composite `m = 198151 = 19 * 10429` satisfies
`Sum_{k=1..p-1} k^(m-1) ≡ p - 1 (mod m)`, while the next prime after `p` is
`198173`.  So the least odd `m > p` with the congruence is at most `198151`,
not the next prime.  The congruence is checked by the Chinese remainder
theorem: modulo each prime factor `q` of `m`, Fermat's little theorem
(`x^q = x` in `ZMod q`) lowers the exponent `198150` to `6` (for `q = 19`) and
to `18` (for `q = 10429`), and periodicity of `k ↦ k^e` modulo `q` reduces the
sum to at most `10429` terms, which the kernel evaluates.
-/
import Mathlib

set_option autoImplicit false
-- The two kernel evaluations of `10^4`-term sums below are checked sequentially:
-- run concurrently under the shared virtual-memory cap, the asynchronous
-- elaboration threads fail to start (`failed to create thread`).
set_option Elab.async false

namespace Candidates.A065091Refutation

open Finset

/-! ## Definitions -/

/-- A065091, the odd primes, indexed from `0`: `oddPrime n` is the `n`-th
(0-indexed) prime that is odd, so `oddPrime 0 = 3`.  The OEIS term `a(n)`
(offset `1`) is `oddPrime (n - 1)`. -/
noncomputable def oddPrime (n : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ Odd p) n

/-- Ordowski's congruence for the pair `(p, m)`:
`Sum_{k=1..p-1} k^(m-1) ≡ p - 1 (mod m)`.  In the conjecture it is only used
with `p` prime and `p < m`, so `m - 1` and `p - 1` are true differences. -/
def OrdowskiCong (p m : ℕ) : Prop :=
  (∑ k ∈ Ico 1 p, k ^ (m - 1)) ≡ p - 1 [MOD m]

instance (p m : ℕ) : Decidable (OrdowskiCong p m) := by
  unfold OrdowskiCong
  infer_instance

/-- **Ordowski's conjecture (A065091, Thomas Ordowski, Aug 01 2018).**

Verbatim: "Conjecture: a(n) is the smallest odd number m > prime(n) such that
Sum_{k=1..prime(n)-1} k^(m-1) == prime(n)-1 (mod m)."

With 0-based indices, `prime(n)` is `Nat.nth Nat.Prime n` (so the `0`-th prime
is `2`) and `a(n)` is `oddPrime n`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, IsLeast
    {m : ℕ | Odd m ∧ Nat.nth Nat.Prime n < m ∧ OrdowskiCong (Nat.nth Nat.Prime n) m}
    (oddPrime n)

/-! ## Ground truth -/

/-- The odd primes form an infinite set. -/
theorem infinite_setOf_prime_and_odd :
    (Set.ofPred fun p : ℕ => p.Prime ∧ Odd p).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (a + 3)
  refine ⟨p, ⟨hp, hp.odd_of_ne_two (by omega)⟩, by omega⟩

/-- Every term of A065091 is an odd prime. -/
theorem oddPrime_prime_and_odd (n : ℕ) : (oddPrime n).Prime ∧ Odd (oddPrime n) :=
  Nat.nth_mem_of_infinite infinite_setOf_prime_and_odd n

/-- If `n` is an odd prime with exactly `i` odd primes below it, then
`oddPrime i = n`: the tool for the ground-truth checks below. -/
theorem oddPrime_eq_of_count_eq {i n : ℕ} (hn : n.Prime ∧ Odd n)
    (hcount : Nat.count (fun p => p.Prime ∧ Odd p) n = i) : oddPrime i = n := by
  rw [← hcount]
  exact Nat.nth_count hn

/-- First terms of A065091: `3, 5, 7, 11, 13`, and the tenth term `31`. -/
example : oddPrime 0 = 3 ∧ oddPrime 1 = 5 ∧ oddPrime 2 = 7 ∧ oddPrime 3 = 11 ∧
    oddPrime 4 = 13 ∧ oddPrime 9 = 31 :=
  ⟨oddPrime_eq_of_count_eq (by decide) (by decide),
    oddPrime_eq_of_count_eq (by decide) (by decide),
    oddPrime_eq_of_count_eq (by decide) (by decide),
    oddPrime_eq_of_count_eq (by decide) (by decide),
    oddPrime_eq_of_count_eq (by decide) (by decide),
    oddPrime_eq_of_count_eq (by decide) (by decide)⟩

/-- Ordowski's congruence at small primes: it holds for `(p, m) = (2, 3)`,
`(3, 5)`, `(5, 7)`, `(7, 11)`, and fails for the odd `m = 9` with `p = 7`. -/
example : OrdowskiCong 2 3 ∧ OrdowskiCong 3 5 ∧ OrdowskiCong 5 7 ∧
    OrdowskiCong 7 11 ∧ ¬ OrdowskiCong 7 9 := by
  decide

/-- The `n = 3` instance of the conjecture holds: with `prime(3) = 7` (0-based),
the least odd `m > 7` with `Sum_{k=1..6} k^(m-1) ≡ 6 (mod m)` is `11 = oddPrime 3`
(the only odd candidate below it, `m = 9`, fails).  So `Conjecture` is not
vacuous or trivially false at small indices. -/
example : IsLeast
    {m : ℕ | Odd m ∧ Nat.nth Nat.Prime 3 < m ∧ OrdowskiCong (Nat.nth Nat.Prime 3) m}
    (oddPrime 3) := by
  have h3 : oddPrime 3 = 11 := oddPrime_eq_of_count_eq (by decide) (by decide)
  rw [Nat.nth_prime_three_eq_seven, h3]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  rintro m ⟨hodd, hlt, hcong⟩
  by_contra hm
  have hm9 : m = 8 ∨ m = 9 ∨ m = 10 := by omega
  rcases hm9 with rfl | rfl | rfl
  · exact absurd hodd (by decide)
  · exact absurd hcong (by decide)
  · exact absurd hodd (by decide)

/-! ## Fermat reduction and periodicity modulo a prime -/

/-- Fermat's little theorem in the form used here: in `ZMod q` (`q` prime), the
exponent of `x ^ n` with `1 ≤ n` may be raised by any multiple of `q - 1`. -/
theorem zmod_pow_add_mul (q : ℕ) [Fact q.Prime] (x : ZMod q) {n : ℕ} (hn : 1 ≤ n)
    (t : ℕ) : x ^ (n + (q - 1) * t) = x ^ n := by
  have hq : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : n + (q - 1) * (t + 1) = (n - 1 + (q - 1) * t) + q := by
      rw [Nat.mul_succ]
      omega
    have hsucc : n - 1 + (q - 1) * t + 1 = n + (q - 1) * t := by omega
    rw [hsplit, pow_add, ZMod.pow_card, ← pow_succ, hsucc, ih]

/-- Periodicity of `k ↦ k ^ e` in `ZMod q`: a sum over `q * t + r` consecutive
residues is `t` full periods plus the first `r` terms. -/
theorem sum_range_mul_add (q e t r : ℕ) :
    ∑ k ∈ range (q * t + r), (k : ZMod q) ^ e =
      t * ∑ k ∈ range q, (k : ZMod q) ^ e + ∑ k ∈ range r, (k : ZMod q) ^ e := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : q * (t + 1) + r = q + (q * t + r) := by ring
    have hshift : ∑ k ∈ range (q * t + r), ((q + k : ℕ) : ZMod q) ^ e =
        ∑ k ∈ range (q * t + r), (k : ZMod q) ^ e := by
      simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [hsplit, sum_range_add, hshift, ih]
    push_cast
    ring

/-- For a positive exponent the `k = 0` term vanishes, so the sum may start at
`0` instead of `1`. -/
theorem sum_Ico_one_eq_sum_range (q e p : ℕ) (he : 1 ≤ e) :
    ∑ k ∈ Ico 1 p, (k : ZMod q) ^ e = ∑ k ∈ range p, (k : ZMod q) ^ e := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · rw [sum_range_eq_add_Ico _ hp]
    simp [zero_pow (by omega : e ≠ 0)]

/-- The reduction of `Sum_{k=1..qT+r-1} k^(e + (q-1)t)` modulo a prime `q` to
two short sums with the small exponent `e ≥ 1`: a full period (residue `a`) and
the first `r` terms (residue `b`). -/
theorem sum_Ico_pow_eq_of_mod (q : ℕ) [Fact q.Prime] {e : ℕ} (he : 1 ≤ e)
    (t T r a b : ℕ) (ha : (∑ k ∈ range q, k ^ e) % q = a)
    (hb : (∑ k ∈ range r, k ^ e) % q = b) :
    ∑ k ∈ Ico 1 (q * T + r), (k : ZMod q) ^ (e + (q - 1) * t) =
      (T : ZMod q) * (a : ZMod q) + (b : ZMod q) := by
  have hpow : ∀ k ∈ Ico 1 (q * T + r),
      (k : ZMod q) ^ (e + (q - 1) * t) = (k : ZMod q) ^ e :=
    fun k _ => zmod_pow_add_mul q (k : ZMod q) he t
  have hcast : ∀ s : ℕ, ∑ k ∈ range s, (k : ZMod q) ^ e =
      (((∑ k ∈ range s, k ^ e) % q : ℕ) : ZMod q) := by
    intro s
    push_cast [ZMod.natCast_mod]
    rfl
  rw [sum_congr rfl hpow, sum_Ico_one_eq_sum_range q e _ he, sum_range_mul_add,
    hcast q, hcast r, ha, hb]

/-! ## The counterexample `p = 198139`, `m = 198151 = 19 * 10429` -/

/-- A full period of `k ^ 6` modulo `19` sums to `0`. -/
theorem sum_range_pow_six_mod_nineteen : (∑ k ∈ range 19, k ^ 6) % 19 = 0 := by
  decide +kernel

/-- The first `7` terms of `k ^ 6` modulo `19` sum to `6`. -/
theorem sum_range_seven_pow_six_mod_nineteen : (∑ k ∈ range 7, k ^ 6) % 19 = 6 := by
  decide +kernel

/-- A full period of `k ^ 18` modulo `10429` sums to `0` (kernel evaluation). -/
theorem sum_range_pow_eighteen_mod_10429 :
    (∑ k ∈ range 10429, k ^ 18) % 10429 = 0 := by
  decide +kernel

/-- The first `10417` terms of `k ^ 18` modulo `10429` sum to `10416` (kernel
evaluation). -/
theorem sum_range_10417_pow_eighteen_mod_10429 :
    (∑ k ∈ range 10417, k ^ 18) % 10429 = 10416 := by
  decide +kernel

/-- The congruence modulo `19`: `198139 = 19 * 10428 + 7` and
`198150 = 6 + 18 * 11008`. -/
theorem sum_modEq_nineteen : (∑ k ∈ Ico 1 198139, k ^ 198150) ≡ 198138 [MOD 19] := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h := sum_Ico_pow_eq_of_mod 19 (e := 6) (by norm_num) 11008 10428 7 0 6
    sum_range_pow_six_mod_nineteen sum_range_seven_pow_six_mod_nineteen
  rw [show 19 * 10428 + 7 = 198139 by norm_num,
    show 6 + (19 - 1) * 11008 = 198150 by norm_num] at h
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [h, ← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  decide

/-- The congruence modulo `10429`: `198139 = 10429 * 18 + 10417` and
`198150 = 18 + 10428 * 19`. -/
theorem sum_modEq_10429 : (∑ k ∈ Ico 1 198139, k ^ 198150) ≡ 198138 [MOD 10429] := by
  haveI : Fact (Nat.Prime 10429) := ⟨by norm_num⟩
  have h := sum_Ico_pow_eq_of_mod 10429 (e := 18) (by norm_num) 19 18 10417 0 10416
    sum_range_pow_eighteen_mod_10429 sum_range_10417_pow_eighteen_mod_10429
  rw [show 10429 * 18 + 10417 = 198139 by norm_num,
    show 18 + (10429 - 1) * 19 = 198150 by norm_num] at h
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [h, ← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  decide

/-- **The witness.** Ordowski's congruence holds for `p = 198139` and the odd
composite `m = 198151 = 19 * 10429`:
`Sum_{k=1..198138} k^198150 ≡ 198138 (mod 198151)`. -/
theorem ordowskiCong_198139_198151 : OrdowskiCong 198139 198151 := by
  unfold OrdowskiCong
  have e1 : (198151 : ℕ) - 1 = 198150 := by norm_num
  have e2 : (198139 : ℕ) - 1 = 198138 := by norm_num
  have e3 : (198151 : ℕ) = 19 * 10429 := by norm_num
  rw [e1, e2, e3]
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)).1
    ⟨sum_modEq_nineteen, sum_modEq_10429⟩

/-- `198151 = 19 * 10429` is odd and composite, and there is no prime in
`(198139, 198151]` (the next prime after `198139` is `198173`). -/
theorem not_prime_of_198139_lt_of_le_198151 (q : ℕ) (hlo : 198139 < q)
    (hhi : q ≤ 198151) : ¬ q.Prime := by
  interval_cases q <;> norm_num

/-- **Refutation of Ordowski's conjecture (A065091).**  For `p = 198139`
(prime), the odd composite `m = 198151 = 19 * 10429` satisfies
`Sum_{k=1..p-1} k^(m-1) ≡ p - 1 (mod m)`, so the least odd `m > p` with the
congruence is at most `198151`, whereas the next odd prime after `p` is
`198173`.  No corrected form is evident: the comment presents the claim as
an extension of the Agoh-Giuga conjecture, and the witness `m` is odd,
squarefree and composite, so it is excluded by none of the hypotheses the
author states. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  set i := Nat.count Nat.Prime 198139
  have hpi : Nat.nth Nat.Prime i = 198139 := Nat.nth_count (by norm_num)
  have hleast := h i
  rw [hpi] at hleast
  have hmem : (198151 : ℕ) ∈
      {m : ℕ | Odd m ∧ 198139 < m ∧ OrdowskiCong 198139 m} :=
    ⟨by decide, by norm_num, ordowskiCong_198139_198151⟩
  have hle : oddPrime i ≤ 198151 := hleast.2 hmem
  have hgt : 198139 < oddPrime i := hleast.1.2.1
  exact not_prime_of_198139_lt_of_le_198151 (oddPrime i) hgt hle
    (oddPrime_prime_and_odd i).1

end Candidates.A065091Refutation
