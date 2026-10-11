/-
# A131646 — Sloane: numbers writable in bases 2..18 with digits 0..9 only

## OEIS source (re-pulled verbatim with `goof oeis show A131646`, 2026-08-05)

```
NAME:     Numbers that can be written from base 2 to base 18 using only the
          digits 0 to 9 (conjectured to be complete).
TERMS:    0,1,2,3,4,5,6,7,8,9,18,19,20,1027,1028,1029,14745,9020076688681,
          9439828025162228377,9439829801208141318
KEYWORDS: nonn,base
COMMENTS:
  Originally checked to 2^20356 (or 5.8*10^6127) in Nov 2008.
  It appears that 19 and 20 are the only numbers > 9 that can be written up to
  base 19 only using digits 0 to 9 and 20 is the only number > 9 that can be
  written up to base 20 only using digits 0 to 9.
  It is a plausible conjecture that there are no more terms, but this has not
  been proved. - _N. J. A. Sloane_, Nov 17 2017
XREFS:
  Cf. A146025, A146026, A146027, A146028, A146029.
```

Exactly `20` terms are listed, and the sequence starts at `0`.

## Verification performed before writing this card

The predicate and the term list were checked computationally: every one of the
20 listed terms satisfies "all base-`b` digits are `≤ 9` for `2 ≤ b ≤ 18`", and
an exhaustive sweep of `n < 200000` returns exactly
`0,1,…,9,18,19,20,1027,1028,1029,14745` — the first 17 terms and nothing else.
The two 19-digit terms and `9020076688681` are above that sweep bound and were
checked individually.  The base-19/base-20 remarks in the comment also check
out: `19` and `20` both survive bases `2..19`, and `20` survives bases `2..20`.

## Status

Open.  Sloane 2017.  Checked to `2^20356 ≈ 5.8 · 10^6127`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A131646

/-! ## Definition layer

`leandoc` findings (all `mode:"exact"`):

* `Nat.digits : ℕ → ℕ → List ℕ`
  (`mathlib/Mathlib/Data/Nat/Digits/Defs.lean:78`), little-endian, with
  `Nat.digits b 0 = []`.
* `Nat.digits_lt_base {b m d : ℕ} (hb : 1 < b) (hd : d ∈ digits b m) : d < b`
  — this is the lemma that makes the "only bases `11..18` matter" reduction a
  one-liner.
* `Nat.ofDigits {α} [Semiring α] (b : α) : List ℕ → α`, with
  `Nat.ofDigits_digits`.
* `Nat.lt_base_pow_length_digits {b m : ℕ} (hb : 1 < b) : m < b ^ (digits b m).length`
  and `Nat.base_pow_length_digits_le` — the size bounds a finiteness argument
  would need.

**Degeneracy watch.**  `Nat.digits b 0 = []`, so `∀ d ∈ Nat.digits b 0, d ≤ 9`
is *vacuously true* — which is why `0` is legitimately the first term rather
than an artefact.  Similarly `Nat.digits 0 n` and `Nat.digits 1 n` are junk
(`digitsAux0`/`digitsAux1`), so the base range must start at `2`; it does.

No fresh sequence-specific machinery is required. -/

/-- `n` is *low-digit in base `b`*: every base-`b` digit of `n` is at most `9`. -/
def LowDigits (b n : ℕ) : Prop := ∀ d ∈ Nat.digits b n, d ≤ 9

instance (b n : ℕ) : Decidable (LowDigits b n) := by unfold LowDigits; infer_instance

/-- Membership in A131646: low-digit in every base from `2` to `18`. -/
def MemA131646 (n : ℕ) : Prop := ∀ b ∈ Finset.Icc 2 18, LowDigits b n

instance (n : ℕ) : Decidable (MemA131646 n) := by unfold MemA131646; infer_instance

/-- The 20 listed terms, as a `Finset`. -/
def knownTerms : Finset ℕ :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 18, 19, 20, 1027, 1028, 1029, 14745,
   9020076688681, 9439828025162228377, 9439829801208141318}

/-! ## The conjecture -/

/-- **Sloane's completeness conjecture (A131646, N. J. A. Sloane, Nov 17 2017).**

Verbatim: "It is a plausible conjecture that there are no more terms, but this
has not been proved."

Together with the DATA line this says: `MemA131646 n ↔ n ∈ knownTerms`.  The
`←` direction is a finite check (PROVABLE, below); the `→` direction is the
conjecture.

**Mathlib primitives available.**  `Nat.digits` and its full API
(`Nat.digits_len`, `Nat.digits_add_two_add_one`, `Nat.digits_append`,
`Nat.ofDigits_digits`, `Nat.digits_lt_base`, `Nat.lt_base_pow_length_digits`);
`Nat.log` for digit counts; `Finset.Icc`.  Nothing sequence-specific.

**Sketch of an attack.**  A heuristic count is what makes the conjecture
"plausible": for a random `n` of size `N`, the base-`b` digits are roughly
uniform in `{0,…,b−1}`, so the chance all are `≤ 9` is about
`(10/b)^{log_b N}` = `N^{log(10/b)/log b}`.  Summing the exponents over
`b = 11,…,18` gives a total exponent
`Σ_{b=11}^{18} log(10/b)/log b = −1.0528…`, so `Σ_N N^{−1.053}` converges and
finitely many terms are expected.  The margin over the critical exponent `−1` is
*thin* (`0.053`), which is why the conjecture is "plausible" rather than
morally certain — a slightly different digit model would flip it.
(An earlier draft of this file quoted `≈ −1.6`; that was wrong by ~50% and was
caught by the adversarial reviewer.  The per-base terms are
`−0.0397, −0.0734, −0.1023, −0.1275, −0.1497, −0.1695, −0.1873, −0.2034`.)
Turning that into a proof requires
*independence* of digit conditions across bases, which is exactly the kind of
statement that is open for every multi-base digit problem (cf. the
`3^n mod 2^n` / Mahler `Z`-number circle).  **There is no known route.**

The **provable** part is the base reduction: for `b ≤ 10`, `Nat.digits_lt_base`
gives every digit `< b ≤ 10`, hence `≤ 9`, so the conditions for `b ∈ [2,10]`
are automatic and only `b ∈ [11,18]` carry content.  See
`memA131646_iff_high_bases`.

**Tactic families.** `decide` for individual small terms; `native_decide` for
the two 19-digit terms (`Nat.digits` on `9439829801208141318 ≈ 9.4·10^18`
overflows `UInt64` but `Nat` bignums handle it — note the enlarged trust surface
at the `native_decide` site); `simp [Nat.digits]` unfolds only for literal bases;
`interval_cases b` for the base range; `omega` for digit-bound arithmetic.

**Related work in this repo.** `Enumerative.StanleyDigits` uses `Nat.digits 3` /
`Nat.ofDigits 3` for A005836-style digit predicates — the closest existing
digit-manipulation infrastructure.  Adjacent card in this directory:
`A351243SelfridgeLacampagne.lean` (also base-3 digit-constrained, but *balanced*
ternary — see that file's correction note). -/
theorem sloane_a131646_complete (n : ℕ) (h : MemA131646 n) : n ∈ knownTerms := by
  sorry

/-- The finiteness form — strictly weaker, and the form a density argument would
target. -/
theorem sloane_a131646_finite : {n : ℕ | MemA131646 n}.Finite := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the base reduction.  Bases `2..10` impose no condition, because
-- `Nat.digits_lt_base` already forces every digit `< b ≤ 10`.
theorem memA131646_iff_high_bases (n : ℕ) :
    MemA131646 n ↔ ∀ b ∈ Finset.Icc 11 18, LowDigits b n := by
  sorry

-- PROVABLE: `0` is a term, and it is a term *vacuously* (`Nat.digits b 0 = []`).
-- Flagged explicitly because a vacuous membership is exactly the kind of
-- degeneracy STYLE.md warns about; here it is genuinely intended by the source.
example : MemA131646 0 := by decide

-- PROVABLE: the easy direction — every listed term really is in the set.
-- Split into a small-term batch (kernel-feasible) and the three large terms.
example : ∀ n ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 18, 19, 20, 1027, 1028, 1029, 14745} :
    Finset ℕ), MemA131646 n := by decide

-- PROVABLE: the three large terms, via `native_decide` (bignum digit extraction).
example : MemA131646 9020076688681 := by native_decide
example : MemA131646 9439828025162228377 := by native_decide
example : MemA131646 9439829801208141318 := by native_decide

-- PROVABLE: satisfiability and nondegeneracy — `10` is *not* a term
-- (`10 = A₁₈` in base 18, digit `10 > 9`), so `MemA131646` is not everything.
example : ¬ MemA131646 10 := by decide

-- PROVABLE: `21` is not a term, so the gap after `20` is real.
example : ¬ MemA131646 21 := by decide

-- PROVABLE (window check): the listed terms are exactly the members below
-- `2 * 10^5`.  Externally verified: the sweep returns
-- `0,…,9, 18, 19, 20, 1027, 1028, 1029, 14745` and nothing else.
example : ∀ n ∈ Finset.range 200000, MemA131646 n → n ∈ knownTerms := by
  native_decide

-- PROVABLE: the entry's base-19/base-20 side remark.
--   "19 and 20 are the only numbers > 9 that can be written up to base 19…"
example : (∀ b ∈ Finset.Icc 2 19, LowDigits b 19) ∧
    (∀ b ∈ Finset.Icc 2 20, LowDigits b 20) := by decide

/-! ## Notes for a follow-up card

`memA131646_iff_high_bases` is provable today from `Nat.digits_lt_base` in a
handful of lines and is a genuinely useful reduction (it cuts the decidable
predicate's work by more than half).  It should be discharged, not archived.

Beyond that the card is archive-only.  The one structural observation worth
recording: `1027, 1028, 1029` and `9439828025162228377, 9439829801208141318`
come in near-consecutive runs, which is what one expects if the binding
constraint is the *leading* digits in the high bases; a card could formalize
"if `n` is a term then so is `n ± 1` whenever the low digits permit", which is
false in general but true for these clusters, and might be the seed of a
structure theorem. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A131646 by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* Quotes verbatim including the `N. J. A. Sloane, Nov 17 2017` attribution;
  `%O A131646 1,3`, so `a(1) = 0` and the sequence does start at `0`.
* Exactly `20` DATA terms, matching `knownTerms` element by element.
* All four predicate checks pass: every listed term satisfies the base-`2..18`
  condition; the `n < 200000` sweep returns exactly the first 17 terms; bases
  `≤ 10` are automatic; and `19, 20` survive bases `2..19` with `20` surviving
  `2..20`.
* `Nat.digits b 0 = []` (so `MemA131646 0` is vacuously true — correctly
  flagged), and `Nat.digits 0 n`, `Nat.digits 1 n` really are junk
  (`digitsAux0` gives `[n]`; `digitsAux1` gives `List.replicate n 1`).
* `sloane_a131646_complete` and the weaker `sloane_a131646_finite` are correctly
  related, and `memA131646_iff_high_bases` is true via `Nat.digits_lt_base`.

One defect, **FIXED**:
1. The heuristic exponent `Σ_{b=11}^{18} log(10/b)/log b` was quoted as `≈ −1.6`.
   The true value is `−1.0528…`.  The convergence conclusion survives (still
   `< −1`) but the margin is *thin*, which changes the reading of "plausible".
   The corrected value and the per-base terms are now in the docstring.
-/

end Candidates.A131646
