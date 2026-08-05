import Enumerative.ZumkellerSigmaHalf
import Enumerative.ZumkellerTauSigma

/-!
# Neder's gap bound for A083207: consecutive Zumkeller numbers differ by at most `12`

OEIS **A083207**, "Zumkeller or integer-perfect numbers: numbers n whose divisors can be
partitioned into two disjoint sets with equal sum", pulled live with `goof oeis show
A083207` on **2026-08-05**.  Its `terms` field is, byte for byte,

> 6,12,20,24,28,30,40,42,48,54,56,60,66,70,78,80,84,88,90,96,102,104,108,112,114,120,
> 126,132,138,140,150,156,160,168,174,176,180,186,192,198,204,208,210,216,220,222,224,
> 228,234,240,246,252,258,260,264,270,272

(line-wrapped here only; the field itself is a single line).  The result formalised here is
the comment of **Charlie Neder, Jan 15 2019**, quoted verbatim from that pull:

> The numbers 3 * 2^k for k > 0 are all Zumkeller numbers: half of one such partition is
> {3*2^k, 3*2^(k-2), ...}, replacing 3 with 2 if it appears. With this and the lemma that
> the product of a Zumkeller number and a number coprime to it is again a Zumkeller number
> (see A179527), we have that all numbers divisible by 6 but not 9 (or numbers congruent
> to 6 or 12 modulo 18) are Zumkeller numbers, proving that the difference between
> consecutive Zumkeller numbers is at most 12. - _Charlie Neder_, Jan 15 2019

The same residue classes are recorded independently by **Ivan N. Ianakiev, Jan 02 2024**,
also verbatim from that pull:

> For k >= 0, numbers of the form 18k + 6 and 18k + 12 are terms (see Remark 2.3. in Somu
> et al., 2023). Corollary: The maximum difference between any two consecutive terms is at
> most 12. - _Ivan N. Ianakiev_, Jan 02 2024

## What is new here, and what was already in the tree

Neder's argument has three steps.  The first two are **already formalised in this
repository** and are re-used, not re-proved:

* `3 * 2 ^ k` is Zumkeller for `k ≥ 1` — `ZumkellerTauSigma.isZumkeller_two_pow_mul_three`;
* the coprime-closure step, giving every multiple of `6` that is not a multiple of `9` —
  `ZumkellerTauSigma.isZumkeller_of_six_dvd_of_not_nine_dvd`, built on the closure engine
  `IsZumkeller.mul_of_coprime` of `Enumerative.IsZumkeller`.

This file supplies the third step — the covering argument and the gap statement:

* `isZumkeller_of_mod_eighteen` — Neder's classes in residue form, `n % 18 ∈ {6, 12}`;
* `exists_add_mod_eighteen_eq_six_or_twelve` — the purely arithmetic covering fact that
  every `12` consecutive residues modulo `18` meet `{6, 12}` (the longest run avoiding
  them, `13, …, 23`, has length `11`);
* `exists_isZumkeller_mem_Ico` — every `12` consecutive naturals contain a Zumkeller
  number lying in Neder's classes;
* `exists_isZumkeller_lt_le_add_twelve` — the next Zumkeller number after `n` is at most
  `n + 12`;
* `le_add_twelve_of_forall_not_isZumkeller` — if no Zumkeller number lies strictly between
  `n` and `m`, then `m ≤ n + 12`;
* `nth_isZumkeller_succ_le_add_twelve` — **the headline**: in the OEIS enumeration
  `a = Nat.nth IsZumkeller` of A083207, `a(i+1) ≤ a(i) + 12` for every index `i`.

The enumeration is guarded: `Nat.nth p` returns the junk value `0` past the last term of a
finite predicate, so `nth_isZumkeller_succ_le_add_twelve` would be about junk were A083207
finite.  It is not — `infinite_setOf_isZumkeller` (`Enumerative.ZumkellerSigmaHalf`) — and
`isZumkeller_nth` together with `nth_isZumkeller_lt_succ` record that `Nat.nth IsZumkeller`
really is a strictly increasing enumeration of terms.  Note the offset: A083207 is indexed
from `1` while `Nat.nth` is indexed from `0`, so `Nat.nth IsZumkeller i` is OEIS `a(i+1)`;
the in-tree anchors `nth_isZumkeller_zero : Nat.nth IsZumkeller 0 = 6` and
`nth_isZumkeller_one : Nat.nth IsZumkeller 1 = 12` pin the two conventions together.

## Sharpness

The constant `12` cannot be lowered: `282` and `294` are consecutive terms of A083207
(`isZumkeller_282`, `isZumkeller_294`, `forall_not_isZumkeller_between_282_294`) and
differ by exactly `12`.  This is the first such pair; a subset-sum sweep over the divisors
of every `n ≤ 2 · 10 ^ 5` (plain `python3`; no `sage` on this machine) finds `45927` terms,
maximum consecutive difference `12`, first attained at `(282, 294)`.  That sweep is
orientation only — the eleven non-membership facts `283, …, 293` are kernel-checked below.

## Deviation from Neder's own witness

Neder's half-partition of `3 * 2 ^ k` is `{3*2^k, 3*2^(k-2), …}` with `3` replaced by `2`
when it occurs.  The in-tree derivation of `isZumkeller_two_pow_mul_three` runs through the
`2`-adic coefficient engine `isZumkeller_two_pow_mul_of_sum_divisors_le` instead, whose
witness at `m = 3` decodes to the uniform set `{3 * 2 ^ k} ∪ {2, 4, …, 2 ^ (k-1)}` — a
different half-partition with the same sum `2 ^ (k+2) - 2 = σ(3 * 2 ^ k) / 2`.  Only the
existence of *some* half-partition is used, so the two routes are interchangeable here.
-/

set_option autoImplicit false

open Finset

/-! ## Neder's residue classes -/

/-- **Neder's criterion, residue form.**  Every `n` congruent to `6` or `12` modulo `18`
is a Zumkeller number.

These are exactly the multiples of `6` that are not multiples of `9`, so this is the OEIS
comment's "all numbers divisible by 6 but not 9 (or numbers congruent to 6 or 12 modulo
18) are Zumkeller numbers" restated for the covering argument below.  The divisibility form
is `ZumkellerTauSigma.isZumkeller_of_six_dvd_of_not_nine_dvd`. -/
theorem isZumkeller_of_mod_eighteen {n : ℕ} (h : n % 18 = 6 ∨ n % 18 = 12) :
    IsZumkeller n := by
  have h6 : 6 ∣ n := by omega
  have h9 : ¬ (9 ∣ n) := by omega
  exact ZumkellerTauSigma.isZumkeller_of_six_dvd_of_not_nine_dvd h6 h9

-- Ground truth: the classes at their two smallest members, cross-checked against the
-- kernel decision procedure and against the A083207 prefix `6, 12, 20, 24, …`.
example : IsZumkeller 6 := isZumkeller_of_mod_eighteen (by decide)
example : IsZumkeller 12 := isZumkeller_of_mod_eighteen (by decide)
example : IsZumkeller 6 ∧ IsZumkeller 12 := by decide

-- Not every Zumkeller number lies in Neder's classes: `20` is the third term of A083207
-- and `20 % 18 = 2`.  The criterion is sufficient, never necessary.
example : IsZumkeller 20 ∧ (20 : ℕ) % 18 = 2 := by decide

/-! ## The covering argument -/

/-- Every block of `12` consecutive residues modulo `18` meets `{6, 12}`: for every `n`
there is an offset `k < 12` with `(n + k) % 18 ∈ {6, 12}`.

This is sharp — the run `13, 14, …, 23` of length `11` avoids both classes — and it is the
only arithmetic input to Neder's gap bound. -/
theorem exists_add_mod_eighteen_eq_six_or_twelve (n : ℕ) :
    ∃ k < 12, (n + k) % 18 = 6 ∨ (n + k) % 18 = 12 := by
  have key : ∀ r < 18, ∃ k < 12, (r + k) % 18 = 6 ∨ (r + k) % 18 = 12 := by decide
  obtain ⟨k, hk12, hk⟩ := key (n % 18) (Nat.mod_lt _ (by norm_num))
  exact ⟨k, hk12, by omega⟩

-- Sharpness of the covering: `11` consecutive residues are not enough, since none of
-- `13, 14, …, 23` is congruent to `6` or `12` modulo `18`.
example : ∀ k < 11, ¬ ((13 + k) % 18 = 6 ∨ (13 + k) % 18 = 12) := by decide

/-- **Window form.**  Every `12` consecutive naturals `n, n+1, …, n+11` contain a Zumkeller
number, and one lying in Neder's residue classes `6, 12` modulo `18`.

This settles T. D. Noe's Mar 31 2010 conjecture on A083207 ("any 12 consecutive numbers
include at least one Zumkeller number"), which is strictly weaker than Neder's residue
theorem but strictly stronger than the bare consecutive-gap bound.

No lower bound on `n` is needed: the window `0, …, 11` already contains `6`. -/
theorem exists_isZumkeller_mem_Ico (n : ℕ) :
    ∃ z ∈ Finset.Ico n (n + 12), IsZumkeller z ∧ (z % 18 = 6 ∨ z % 18 = 12) := by
  obtain ⟨k, hk12, hk⟩ := exists_add_mod_eighteen_eq_six_or_twelve n
  refine ⟨n + k, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, ?_, hk⟩
  exact isZumkeller_of_mod_eighteen hk

/-! ## The gap bound -/

/-- **Next-term form.**  The next Zumkeller number strictly above `n` is at most `n + 12`;
in particular A083207 has no gap longer than `12` anywhere. -/
theorem exists_isZumkeller_lt_le_add_twelve (n : ℕ) :
    ∃ m, n < m ∧ m ≤ n + 12 ∧ IsZumkeller m := by
  obtain ⟨z, hz, hzZ, -⟩ := exists_isZumkeller_mem_Ico (n + 1)
  rw [Finset.mem_Ico] at hz
  exact ⟨z, by omega, by omega, hzZ⟩

/-- **Consecutive-difference form.**  If no Zumkeller number lies strictly between `n` and
`m`, then `m ≤ n + 12`.

Applied to a pair of consecutive terms of A083207 this is exactly the OEIS comment's "the
difference between consecutive Zumkeller numbers is at most 12".  The hypothesis is what
carries the content; `IsZumkeller n`, `IsZumkeller m` and `n < m` are not needed and are
therefore not assumed. -/
theorem le_add_twelve_of_forall_not_isZumkeller {n m : ℕ}
    (h : ∀ k, n < k → k < m → ¬ IsZumkeller k) : m ≤ n + 12 := by
  by_contra hlt
  obtain ⟨z, hz1, hz2, hzZ⟩ := exists_isZumkeller_lt_le_add_twelve n
  exact h z hz1 (by omega) hzZ

/-! ## The enumeration form

`Nat.nth IsZumkeller` is the increasing enumeration of A083207; it is a totalised operator
that falls back on `0` past the last term of a finite predicate, so the two lemmas below
record that this junk branch is not in play. -/

/-- `Nat.nth IsZumkeller i` really is a term of A083207, for every index `i`. -/
theorem isZumkeller_nth (i : ℕ) : IsZumkeller (Nat.nth IsZumkeller i) :=
  Nat.nth_mem_of_infinite infinite_setOf_isZumkeller i

/-- The enumeration of A083207 is strictly increasing, so consecutive indices really do
name consecutive terms. -/
theorem nth_isZumkeller_lt_succ (i : ℕ) :
    Nat.nth IsZumkeller i < Nat.nth IsZumkeller (i + 1) :=
  (Nat.nth_lt_nth infinite_setOf_isZumkeller).mpr (Nat.lt_succ_self i)

/-- **Neder's gap bound for A083207.**  Writing `a = Nat.nth IsZumkeller` for the
increasing enumeration of the Zumkeller numbers, `a(i+1) ≤ a(i) + 12` for every `i`: the
difference between consecutive Zumkeller numbers is at most `12`.

`Nat.nth` is `0`-indexed and A083207 is `1`-indexed, so `Nat.nth IsZumkeller i` is the OEIS
`a(i+1)`; `nth_isZumkeller_zero` and `nth_isZumkeller_one` anchor the two conventions.  The
bound is attained — see `forall_not_isZumkeller_between_282_294`. -/
theorem nth_isZumkeller_succ_le_add_twelve (i : ℕ) :
    Nat.nth IsZumkeller (i + 1) ≤ Nat.nth IsZumkeller i + 12 := by
  by_contra hlt
  obtain ⟨m, hlow, hhigh, hmZ⟩ :=
    exists_isZumkeller_lt_le_add_twelve (Nat.nth IsZumkeller i)
  have hmlt : m < Nat.nth IsZumkeller (i + 1) := by omega
  have hmle : m ≤ Nat.nth IsZumkeller i := Nat.le_nth_of_lt_nth_succ hmlt hmZ
  omega

-- Ground truth against the A083207 prefix: at `i = 0` the bound reads `a(2) ≤ a(1) + 12`,
-- i.e. `12 ≤ 6 + 12`, using the in-tree anchors of `Enumerative.ZumkellerSigmaHalf`.
example : (12 : ℕ) ≤ 6 + 12 := by
  have h := nth_isZumkeller_succ_le_add_twelve 0
  rwa [nth_isZumkeller_zero, nth_isZumkeller_one] at h

/-! ## Sharpness: the pair `(282, 294)`

`282 = 18 · 15 + 12` and `294 = 18 · 16 + 6` both lie in Neder's classes, and none of the
eleven integers between them is Zumkeller.  Ten of the eleven are settled by kernel
`decide` on the definition; `288 = 2 ^ 5 · 3 ^ 2` has `σ(288) = 819` odd and is settled by
parity instead, its `18` divisors putting the powerset search out of kernel reach. -/

/-- `282 = 18 · 15 + 12` is a Zumkeller number, by Neder's criterion. -/
theorem isZumkeller_282 : IsZumkeller 282 := isZumkeller_of_mod_eighteen (by decide)

/-- `294 = 18 · 16 + 6` is a Zumkeller number, by Neder's criterion. -/
theorem isZumkeller_294 : IsZumkeller 294 := isZumkeller_of_mod_eighteen (by decide)

/-- `288` is not a Zumkeller number: `σ(288) = 819` is odd, and an equal-sum split of the
divisors doubles one side (`IsZumkeller.two_dvd_sum_divisors`).  Stated separately because
`288` has `18` divisors, so the `2 ^ 18`-element powerset search behind `decide` on the
definition is out of kernel reach. -/
theorem not_isZumkeller_288 : ¬ IsZumkeller 288 := fun h => by
  have h2 : 2 ∣ ∑ d ∈ (288 : ℕ).divisors, d := h.two_dvd_sum_divisors
  revert h2
  decide

set_option maxRecDepth 8000 in
/-- No Zumkeller number lies strictly between `282` and `294`, so those two are consecutive
terms of A083207. -/
theorem forall_not_isZumkeller_between_282_294 :
    ∀ k, 282 < k → k < 294 → ¬ IsZumkeller k := by
  intro k h1 h2
  interval_cases k <;> first | exact not_isZumkeller_288 | decide

-- Sharpness, and the joint instantiation of the hypothesis of
-- `le_add_twelve_of_forall_not_isZumkeller`: at the consecutive pair `(282, 294)` the
-- conclusion reads `294 ≤ 294`, so the constant `12` cannot be lowered.
example : (294 : ℕ) ≤ 282 + 12 :=
  le_add_twelve_of_forall_not_isZumkeller forall_not_isZumkeller_between_282_294

/-! ## Axiom audit

Disclosure: the import cone of this file contains two `sorry`s, both pre-existing and both
in declarations this file never mentions — `Nat.coleman_multiperfect_practical`
(`Enumerative.Practical`, Coleman's conjecture) and
`ZumkellerTauSigma.isZumkeller_of_sigma_zero_mul_sigma_one` (Ianakiev's open conjecture).
Neither reaches anything here; every declaration below reports exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.  No `native_decide` is used:
every decision procedure invoked here is kernel `decide`. -/

#print axioms isZumkeller_of_mod_eighteen
#print axioms exists_add_mod_eighteen_eq_six_or_twelve
#print axioms exists_isZumkeller_mem_Ico
#print axioms exists_isZumkeller_lt_le_add_twelve
#print axioms le_add_twelve_of_forall_not_isZumkeller
#print axioms isZumkeller_nth
#print axioms nth_isZumkeller_lt_succ
#print axioms nth_isZumkeller_succ_le_add_twelve
#print axioms isZumkeller_282
#print axioms isZumkeller_294
#print axioms not_isZumkeller_288
#print axioms forall_not_isZumkeller_between_282_294
