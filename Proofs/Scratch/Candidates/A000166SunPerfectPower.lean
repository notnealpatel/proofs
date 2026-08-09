/-
# A000166 — Sun's "derangement numbers are never perfect powers" conjecture

## OEIS source (re-pulled verbatim with `goof oeis show A000166`, 2026-08-05)

```
NAME:     Subfactorial or rencontres numbers, or derangements: number of
          permutations of n elements with no fixed points.
TERMS:    1,0,1,2,9,44,265,1854,14833,133496,1334961,14684570,176214841,
          2290792932,32071101049,481066515734,7697064251745,130850092279664,
          2355301661033953,44750731559645106,895014631192902121,
          18795307255050944540,413496759611120779881,9510425471055777937262
KEYWORDS: core,nonn,easy,nice
COMMENT (the conjecture, last line of the comment block):
  Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with
  a(4) = 3^2. This has been verified for n <= 1000. - _Zhi-Wei Sun_, Jan 09 2025
```

Supporting comment used below (Euler 1809, per the entry's first comment):
```
  Euler (1809) not only gives the first ten or so terms of the sequence, he also
  proves both recurrences a(n) = (n-1)*(a(n-1) + a(n-2)) and
  a(n) = n*a(n-1) + (-1)^n.
```

The offset is `0`: `a(0) = 1`, `a(1) = 0`, `a(2) = 1`, `a(3) = 2`, `a(4) = 9`.
Mathlib's `numDerangements` uses exactly this indexing
(`numDerangements 0 = 1`, `numDerangements 1 = 0`), so no offset shim is needed.

## Status

Open, and very fresh (Jan 2025).  Verified for `n ≤ 1000` per Sun's comment.

## Why the `n > 2` guard is not decoration

`a(0) = 1 = 1^2` and `a(1) = 0 = 0^2` and `a(2) = 1 = 1^2` are all perfect
powers under the permissive reading `∃ b k, 1 < k ∧ m = b ^ k`.  The guard
`n > 2` is what makes the statement nonvacuous *and* nonfalse.  Under the
restrictive reading `∃ b k, 1 < b ∧ 1 < k ∧ m = b ^ k` (the one Sun uses for the
sibling A000041 conjecture — "No a(n) has the form x^m with m > 1 and x > 1")
the small terms are excluded automatically.  Both readings are given below and
their agreement for `n > 2` is in the PROVABLE layer, because a reader must be
able to check that the guard is doing the work the source intends.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A000166

/-! ## Definition layer

`leandoc` findings (all `mode:"exact"` unless noted):

* `numDerangements : ℕ → ℕ`
  `| 0 => 1 | 1 => 0 | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))`
  (`mathlib/Mathlib/Combinatorics/Derangements/Finite.lean:66`).  This is Euler's
  first recurrence with the OEIS indexing, so A000166 is Mathlib-native.
* `derangements (α : Type*) : Set (Perm α)`
  (`mathlib/Mathlib/Combinatorics/Derangements/Basic.lean:36`) with
  `card_derangements_fin_eq_numDerangements {n : ℕ} :
     card (derangements (Fin n)) = numDerangements n` — the semantic anchor
  tying the recurrence back to the combinatorial definition in the OEIS NAME.
  Every statement below is phrased over `numDerangements`; the anchor lemma is
  what licenses that.
* `numDerangements_succ (n : ℕ) :
     (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) - (-1) ^ n`
  — Euler's second recurrence, already in Mathlib, in `ℤ` (correctly: the `(-1)^n`
  makes `ℕ` the wrong home).
* `numDerangements_sum`, `numDerangements_add_two`, `numDerangements_zero`,
  `numDerangements_one`.

Nothing about perfect powers exists in Mathlib under that name (`leandoc
"perfect power"` returns only `PerfectField`/`PerfectRing`/`Topology.Perfect`
noise), so `IsPerfectPower` is defined fresh here.  It is deliberately kept
identical in shape to what the sibling A000041 card needs, so the two can share
it once either lands outside `Scratch`. -/

/-- `m` is a perfect power, permissive reading: `m = b ^ k` for some `k > 1`.
Under this reading `0 = 0 ^ 2` and `1 = 1 ^ 2` are perfect powers, matching
A001597's convention that `1` is a perfect power. -/
def IsPerfectPower (m : ℕ) : Prop := ∃ b k : ℕ, 1 < k ∧ m = b ^ k

/-- `m` is a perfect power, restrictive reading: `m = b ^ k` with `b > 1` and
`k > 1`.  This is the phrasing Sun uses verbatim for the A000041 sibling
("No a(n) has the form x^m with m > 1 and x > 1", Zhi-Wei Sun, Dec 02 2013). -/
def IsPerfectPower' (m : ℕ) : Prop := ∃ b k : ℕ, 1 < b ∧ 1 < k ∧ m = b ^ k

/-! ## The conjecture -/

/-- **Sun's derangement perfect-power conjecture (A000166, Zhi-Wei Sun, Jan 09 2025).**

Verbatim: "Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with
a(4) = 3^2. This has been verified for n <= 1000."

Formalized with the permissive `IsPerfectPower`; `sun_derangement_perfectPower'`
below uses the restrictive reading and the two are equivalent for `n > 2`
(`isPerfectPower_iff_of_two_lt`, PROVABLE).

**Mathlib primitives available.**  `numDerangements` and its recurrences;
`Nat.Prime`, `Nat.factorization`, `Nat.isPrimePow`, `Nat.Prime.pow_dvd_of_dvd_mul_pow`;
`Nat.sqrt` and `Nat.exists_mul_self` for the square case; `ZMod` for congruence
sieving; `Nat.factorization_pow : (a ^ n).factorization = n • a.factorization`
which is *the* characterization to attack a perfect-power claim
(`IsPerfectPower m ↔ 1 < Nat.gcd of the exponent multiset`, for `m ≥ 2`).

**Sketch of an attack.**
1. *Parity/2-adic valuation.*  `numDerangements_succ` gives
   `D(n+1) = (n+1) D(n) - (-1)^n`, so consecutive terms are coprime-ish:
   `gcd(D(n), D(n+1)) ∣ 1`.  In fact `D(n+1) + (-1)^n = (n+1) D(n)` shows
   `gcd(D(n), D(n+1)) ∣ 1`, i.e. **consecutive derangement numbers are coprime**.
   That is a real, provable lemma and probably the first thing to land.
2. *Congruence sieving.*  The entry records
   `a(n+k) ≡ (-1)^k a(n) (mod k)` (Peter Bala, Nov 21 2017) — so `D(n) mod k`
   is eventually periodic with period dividing `2k`.  For a fixed exponent `k`,
   the `k`-th powers occupy a thin residue class mod suitable primes; sieving
   kills all but finitely many `n mod M`.  This is exactly the shape that gets
   verified computations to `n ≤ 1000` and exactly the shape that does *not*
   close, because no single modulus kills all residues.
3. *Size/irrationality.*  `D(n) = round(n!/e)`, so `D(n)` is within `1/2` of
   `n!/e`.  A perfect power `b^k = D(n)` forces `b ≈ (n!/e)^{1/k}`; for `k = 2`
   this is a square-near-`n!/e` problem, structurally identical to Brocard
   (see `A146968Brocard.lean` in this directory) and equally out of reach.

**Tactic families.**  `decide`/`norm_num` for ground terms (`numDerangements` is
computable and the recurrence unfolds by `simp [numDerangements]`);
`Nat.rec`/`Nat.strong_induction_on` for the recurrences;
`omega` for the parity leaves; `interval_cases` for bounded exponent searches;
`native_decide` for an `n ≤ 60` sweep (the terms exceed `2^63` from `n = 21`, so
the sweep runs on `Nat` bignums — note the enlarged trust surface).

**Related work in this repo.**  Direct sibling: the carded A000041 perfect-power
conjecture (`Formalize/` card).  `IsPerfectPower` here is written to be shared.
Structural sibling: `A146968Brocard.lean` in this directory (same
"factorial-scale value is almost never a perfect power" shape). -/
theorem sun_derangement_perfectPower (n : ℕ) (hn : 2 < n)
    (hpp : IsPerfectPower (numDerangements n)) : n = 4 := by
  sorry

/-- The same claim under Sun's own A000041 phrasing (`x > 1`, `m > 1`). -/
theorem sun_derangement_perfectPower' (n : ℕ) (hn : 2 < n)
    (hpp : IsPerfectPower' (numDerangements n)) : n = 4 := by
  sorry

/-- Weaker, and the natural first target: no derangement number above `a(4)` is a
perfect **square**.  Squares are the only exponent that has ever been ruled out
by hand for factorial-adjacent sequences, so this is where a partial result
would land. -/
theorem sun_derangement_not_square (n : ℕ) (hn : 4 < n) :
    ¬ IsSquare (numDerangements n) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the two perfect-power readings agree on the range that matters.
-- For `n > 2` one has `numDerangements n ≥ 2`, which excludes `b ∈ {0, 1}`.
theorem isPerfectPower_iff_of_two_lt (n : ℕ) (hn : 2 < n) :
    IsPerfectPower (numDerangements n) ↔ IsPerfectPower' (numDerangements n) := by
  sorry

-- PROVABLE: the exceptional value.  `a(4) = 9 = 3 ^ 2`.
example : numDerangements 4 = 9 := by decide

-- PROVABLE: satisfiability — the hypothesis of `sun_derangement_perfectPower` is
-- jointly instantiable at `n = 4`, so the theorem is not vacuous.
example : IsPerfectPower' (numDerangements 4) := ⟨3, 2, by norm_num, by norm_num, by decide⟩

-- PROVABLE: the guard `2 < n` is load-bearing.  Without it `n = 0` and `n = 2`
-- are counterexamples under the permissive reading.
example : IsPerfectPower (numDerangements 0) := ⟨1, 2, by norm_num, by decide⟩
example : IsPerfectPower (numDerangements 2) := ⟨1, 2, by norm_num, by decide⟩
example : IsPerfectPower (numDerangements 1) := ⟨0, 2, by norm_num, by decide⟩

-- PROVABLE: the conclusion is not overshooting — `a(3) = 2` and `a(5) = 44` are
-- not perfect powers, so `n = 4` really is isolated among small `n`.
example : numDerangements 3 = 2 ∧ numDerangements 5 = 44 := by decide

-- PROVABLE (window check): no `3 ≤ n ≤ 60` other than `4` gives a perfect power.
-- Search bound: `b ^ k = D(n)` with `k > 1` forces `b ≤ Nat.sqrt (D n)`, so the
-- decidable form quantifies `b` over `Finset.range (Nat.sqrt (D n) + 1)` and `k`
-- over `Finset.Icc 2 (Nat.log 2 (D n) + 1)`.  Spelled out here so the sweep is
-- auditable rather than magic.
example : ∀ n ∈ Finset.Icc 3 60,
    (∃ b ∈ Finset.range (Nat.sqrt (numDerangements n) + 1),
      ∃ k ∈ Finset.Icc 2 (Nat.log 2 (numDerangements n) + 1),
        numDerangements n = b ^ k) → n = 4 := by
  native_decide

/-! ## Notes for a follow-up card

The provable-today lemma in this neighbourhood is coprimality of consecutive
derangement numbers:

```lean
theorem coprime_numDerangements_succ (n : ℕ) :
    Nat.Coprime (numDerangements n) (numDerangements (n + 1))
```

which follows from `numDerangements_succ` by `Nat.Coprime.add_mul_left_right`
style manipulation in `ℤ` and descent to `ℕ`.  It is a genuine (if small) result
about A000166 that Mathlib does not have, and it is a standard ingredient in the
sieving attack sketched above. -/

/-!
## Adversarial review verdict — **PASS** (no defects)

Independent re-pull of A000166 by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* Sun's conjecture quote and the `Zhi-Wei Sun, Jan 09 2025` attribution are
  character-exact.
* `%O A000166 0,4` — offset `0`, as claimed.
* Mathlib's `numDerangements` reproduces the DATA line `1, 0, 1, 2, 9, 44` on
  its own recursion, so no offset shim is needed.
* The permissive/restrictive perfect-power readings are genuinely equivalent
  for `n > 2` (all `numDerangements n ≥ 2` there, which excludes `b ∈ {0, 1}`).
* Mathlib has no perfect-power predicate; `IsPrimePow` is a different notion.
* `numDerangements_succ`, `card_derangements_fin_eq_numDerangements`,
  `numDerangements_sum`, `Nat.factorization_pow`, `Nat.exists_mul_self` all
  exist with compatible signatures.
* **The coprimality claim in the attack sketch survives**: `gcd(D(n), D(n+1)) = 1`
  was verified computationally for all `n ≤ 99`, and the proof sketch via
  `numDerangements_succ` is sound.
-/

end Candidates.A000166
