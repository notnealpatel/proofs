/-
# A080210 — multiplicity lower bound for disjoint covering systems

## ⚠ FOUNDATION FLAG — read before using this card

The OEIS entry defines **almost nothing**.  Complete raw pull
(`curl "https://oeis.org/search?q=id:A080210&fmt=text"`, 2026-08-05) — every
line reproduced, nothing elided:

```
%I A080210 #5 Mar 30 2012 18:39:15
%S A080210 1,2,3,2,5,2,7,2,3,3,11,2,13,4,3,2,17,2,19,3,5,6,23,2,5,7,3,4,29,2,31,
%T A080210 2,7,9,5,2,37,10,9,3,41,3,43,6,3,12,47,2,7,3,11,7,53,2,9,4,13,15,59,2,
%U A080210 61,16,5,2,10,4,67,9,15,3,71,2,73,19,3,10,9,5,79,3,3,21,83,3,13,22,19,6,89
%N A080210 Lower bound for the multiplicity of a disjoint covering system of congruences.
%H A080210 T. Zamojski, <a href="http://www.math.mcgill.ca/~dsavitt/nt/projects/zamojski.ps">Survey on covering congruences</a>.
%F A080210 a(n) = floor(Lpf(n)*phi(n)/n) + 1 where Lpf(n) is the largest prime factor of n and phi is the Euler totient function.
%Y A080210 Cf. A080340.
%K A080210 nonn
%O A080210 1,2
%A A080210 _Benoit Cloitre_, Mar 20 2003
```

There is **no `%C` (comment) and no `%D` (reference)**, hence no definition of
"multiplicity" in the entry itself.  The `%F` line *is* the sequence's
definition; there is consequently nothing to prove unless a semantic reading is
supplied from outside.  A card that states "a(n) = floor(…) + 1" as a theorem
would be asserting `rfl`.

**There is, however, one `%H` link** — T. Zamojski, *Survey on covering
congruences*, a McGill student project (supervised by David Savitt) at
`http://www.math.mcgill.ca/~dsavitt/nt/projects/zamojski.ps`.  That PostScript
file is the single most likely place the definition and the formula live, and
**it has not been read**.  (An earlier draft of this header asserted "no links,
no references" — that was wrong; the `goof oeis show` JSON strips `%H` and `%A`,
and the draft relayed a summary instead of the raw pull.  Caught by the
adversarial reviewer.  Anyone continuing this card should fetch the Zamojski
survey **first**.)

Author: **Benoit Cloitre, Mar 20 2003**.  Offset `1`.

Two things were established before writing this file, and two were not:

**Established.**
1. "`Lpf`" means **largest** prime factor (A006530), despite the lowercase `l`
   suggesting "least".  Numeric check over `n = 1..40`: the largest-prime-factor
   reading reproduces the DATA line exactly; the smallest-prime-factor reading
   diverges immediately (it gives `1` at `n = 6`, DATA says `2`).
   The candidates document quoted the `%F` line faithfully, but "Lpf" is
   ambiguous enough that it is worth pinning: **greatest**, not least.
2. The intended quantity is almost certainly the multiplicity of the
   **largest** modulus, not of an arbitrary modulus.  Reason: for `n = 4`, the
   system `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` is a disjoint covering system
   in which modulus `4` occurs **once**, contradicting `a(4) = 2` under the
   "any modulus" reading.  Restricting to systems whose *largest* modulus is
   `4` restores it: densities must sum to `1` from `{1/1, 1/2, 1/3, 1/4}` with
   at least one `1/4`, and `3/4` is only `1/2 + 1/4`, forcing a second
   modulus-`4` class.  The same argument at `n = 6` gives `2`: `5/6 = 1/2 + 1/3`
   is the only decomposition, but a class mod `3` always meets a class mod `2`
   in `ℤ/6`, so a single modulus-`6` class cannot work.

   Both minima were confirmed by brute-force exact-cover search over `ℤ/12`
   (moduli `≤ 4`) and `ℤ/60` (moduli `≤ 6`): the minimum multiplicity of the
   largest modulus is `2` in each case, matching `a(4) = a(6) = 2`.
   `n = 8, 9, 10, 12` are infeasible by that method (`lcm(1..n)` reaches
   `840, 2520, 2520, 27720`).

**Not established.**
3. No literature definition of "multiplicity of a DCS" was located.  Searches
   over the Znám / Burshtein / Berger–Felzenbaum–Fraenkel / Porubský covering-system
   literature did not produce a definition matching this formula.
   **The Zamojski survey linked from the entry has not been read** and is the
   obvious next step.
4. No named theorem matching `⌊gpf(n)·φ(n)/n⌋ + 1` was found.  The candidates
   document's guess ("likely folklore-proved in the DCS literature (Znám-era
   results)") is **unconfirmed**.  What *is* in the literature is
   Berger–Felzenbaum–Fraenkel (Discrete Math. 65 (1987) 23–44), reproving
   Znám's bound: the largest modulus `N` of a DCS occurs at least `p` times
   where `p` is the **smallest** prime dividing `N`.  That is *weaker* than this
   formula (at `n = 42`: Znám gives `2`, the formula gives `3`), so A080210
   asserts something strictly stronger than the standard citation.

**Consequence: this card is not proof-ready.**  Items 3 and 4 must be settled
from a primary source before anyone attempts `dcs_multiplicity_lower_bound`.
The statements below are written so that the *reconstructed* reading is explicit
and falsifiable rather than silently assumed.

## A080340 (the only xref), for orientation

`%N A080340 First known infinite sequence containing no odd integer of the form
2^m+p (p prime).` — Erdős's 1950 covering-system construction answering
Romanoff's question.  This is the arithmetic progression the repo's covering arc
already works on (`Proofs/Erdos/Covering/Erdos1950Instance.lean`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A080210

/-! ## Definition layer

`leandoc` findings:

* `Nat.totient (n : ℕ) : ℕ` (`mathlib/Mathlib/Data/Nat/Totient.lean:38`) — `φ`.
* `Nat.primeFactors (n : ℕ) : Finset ℕ` — greatest prime factor is
  `n.primeFactors.max' _` or `n.primeFactors.sup id`; Mathlib has **no**
  `Nat.greatestPrimeFactor`, so it is spelled out.
* `Nat.minFac` exists (least prime factor) but is the *wrong* one here.
* `Int.emod`, `Int.ModEq`, `ZMod` — for the congruence classes.
* Covering systems: the repo has `Proofs/Erdos/Covering/Basic.lean`; check it
  before duplicating.  Mathlib has nothing (`leandoc "covering system"` is
  topology noise).

The DCS definition below is over `ℤ` with `Finset`-indexed congruences, using
`∀ x : ℤ, ∃! i, …` to say "exactly one class", which is the literal reading of
"disjoint covering". -/

/-- Greatest prime factor (A006530).  Mathlib has `Nat.minFac` but no maximum
counterpart, so this is fresh.

Edge case, stated because it bites: `Nat.primeFactors 1 = ∅` and
`Finset.sup id ∅ = ⊥ = 0`, so **`gpf 1 = 0`**, *not* `1`.  A006530 uses the
convention `a(1) = 1`; the discrepancy is absorbed by the `n ≤ 1` guard in
`a080210` rather than by patching `gpf`, so that `gpf` stays a plain `sup`. -/
def gpf (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The A080210 formula, as a definition (which is all the entry gives).
`a(1) = 1` by the `gpf 1 = 0` convention below plus the `n = 1` special case;
see `a080210_one`. -/
def a080210 (n : ℕ) : ℕ := if n ≤ 1 then 1 else gpf n * n.totient / n + 1

/-- A **disjoint covering system**: a finite indexed family of congruences
`x ≡ r i (mod m i)` such that every integer lies in exactly one class.
Moduli are required positive; `m i = 0` would make `Int.ModEq 0` equality and
break the density accounting. -/
structure DCS (ι : Type) [Fintype ι] where
  /-- The moduli. -/
  m : ι → ℕ
  /-- The residues. -/
  r : ι → ℤ
  /-- Every modulus is positive. -/
  m_pos : ∀ i, 0 < m i
  /-- Every integer is in exactly one class. -/
  exact : ∀ x : ℤ, ∃! i : ι, (x : ℤ) ≡ r i [ZMOD (m i : ℤ)]

/-- The **multiplicity** of a modulus `n` in a DCS: how many congruences use it.

⚠ This is the *reconstructed* reading (see the header) — the OEIS entry supplies
no definition. -/
def DCS.multiplicity {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : DCS ι) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i => S.m i = n).card

/-- `n` is the largest modulus of `S`. -/
def DCS.LargestModulus {ι : Type} [Fintype ι] (S : DCS ι) (n : ℕ) : Prop :=
  (∃ i, S.m i = n) ∧ ∀ i, S.m i ≤ n

/-! ## The statement -/

/-- **A080210, under the reconstructed reading.**

The `%F` line, verbatim: "a(n) = floor(Lpf(n)*phi(n)/n) + 1 where Lpf(n) is the
largest prime factor of n and phi is the Euler totient function."

Reconstructed as: in any disjoint covering system whose **largest** modulus is
`n`, that modulus occurs at least `⌊gpf(n)·φ(n)/n⌋ + 1` times.

⚠ **Do not attempt this until the header's items 3 and 4 are settled.**  If the
intended notion of "multiplicity" turns out to be something else (e.g. the
number of *distinct* moduli, or a weighted count), this statement is simply the
wrong theorem and proving it would be worse than useless.

**Mathlib primitives available.**  `Nat.totient` and its API
(`Nat.totient_mul`, `Nat.totient_prime_pow`, `Nat.sum_totient`);
`Nat.primeFactors`, `Nat.factorization`; `Int.ModEq`, `ZMod`,
`ZMod.natCast_self_eq_zero`… (careful: that name does **not** exist; use
`ZMod.natCast_self : (n : ZMod n) = 0`); `Nat.chineseRemainder`;
`Finset.card_filter`, `Finset.sum_div`.

**Sketch of the standard argument (Znám's, which is weaker).**  Let `p = lpf(n)`.
Reduce the DCS mod `n`.  The classes with modulus `< n` cannot separate residues
that are congruent mod `n/p`, so at least `p` classes of modulus exactly `n` are
needed.  Getting from `p` to `⌊gpf(n)·φ(n)/n⌋ + 1` needs a different and
stronger argument; `gpf(n)·φ(n)/n = φ(n)/(n/gpf(n))` is the number of units mod
`n` per residue class mod `n/gpf(n)`, which is suggestive but not a proof.

**Tactic families.**  `decide` on `ZMod n` for finite verifications;
`Finset.card_le_card` and pigeonhole (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`)
for the counting core; `Nat.totient` simp lemmas; `omega` for the floor
arithmetic (`Nat.div` is floor division, so `gpf n * n.totient / n` is already
`⌊·⌋` with no guard needed — `n ≥ 2` keeps the divisor nonzero).

**Related work in this repo.**  `Proofs/Erdos/Covering/Basic.lean`,
`Erdos1950Instance.lean`, `ErdosMinus2k.lean`, `ErdosRows.lean` — the covering
arc.  A DCS is a covering system with the disjointness strengthening, so the
existing `Basic.lean` predicates should be reused rather than duplicated;
**check that file before landing `DCS` above.** -/
theorem dcs_multiplicity_lower_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : DCS ι) (n : ℕ) (hn : 2 ≤ n) (hmax : S.LargestModulus n) :
    a080210 n ≤ S.multiplicity n := by
  sorry

/-- The reading that is **false**, recorded so it cannot be adopted by accident.

Counterexample from the header: `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` is a
disjoint covering system in which modulus `4` occurs once, but `a(4) = 2`.
So dropping `LargestModulus` from `dcs_multiplicity_lower_bound` breaks it. -/
theorem dcs_multiplicity_needs_largest :
    ∃ S : DCS (Fin 4), (∃ i, S.m i = 4) ∧ S.multiplicity 4 < a080210 4 := by
  sorry

/-! ## Sanity layer

The only things here that are *certain* are facts about the formula, because the
formula is all the entry supplies.  They are worth having: they pin `gpf` (the
least/greatest ambiguity) against the DATA line. -/

-- PROVABLE: `gpf` ground truth.
example : gpf 1 = 0 := by decide     -- empty sup; hence the `n ≤ 1` case split
example : gpf 2 = 2 := by decide
example : gpf 6 = 3 := by decide
example : gpf 42 = 7 := by decide
example : gpf 45 = 5 := by decide

-- PROVABLE: `a080210 1 = 1`, matching the DATA line's first term.
theorem a080210_one : a080210 1 = 1 := by decide

-- PROVABLE: the formula reproduces the DATA line.  **This is the decisive
-- least-vs-greatest check**: with `Nat.minFac` in place of `gpf` the value at
-- `n = 6` would be `1`, not `2`.
example : List.map a080210 (List.range' 1 40)
    = [1, 2, 3, 2, 5, 2, 7, 2, 3, 3, 11, 2, 13, 4, 3, 2, 17, 2, 19, 3,
       5, 6, 23, 2, 5, 7, 3, 4, 29, 2, 31, 2, 7, 9, 5, 2, 37, 10, 9, 3] := by
  native_decide

-- PROVABLE: the contrast case.  `⌊minFac(42)·φ(42)/42⌋ + 1 = ⌊2·12/42⌋ + 1 = 1`,
-- but `a(42) = 3 = ⌊7·12/42⌋ + 1`.  So "Lpf" is unambiguously *largest*.
example : Nat.minFac 42 * Nat.totient 42 / 42 + 1 = 1 := by decide
example : gpf 42 * Nat.totient 42 / 42 + 1 = 3 := by decide

-- PROVABLE: `a080210 p = p` for prime `p`, since `gpf p = p` and `φ(p) = p − 1`
-- give `p(p−1)/p = p − 1`.  Consistent with the DATA at `2, 3, 5, 7, 11, …`.
theorem a080210_prime {p : ℕ} (hp : p.Prime) : a080210 p = p := by
  sorry

-- PROVABLE: satisfiability of `DCS` — a disjoint covering system exists, so the
-- structure is not vacuous.  `{0 mod 2, 1 mod 2}` is the trivial example.
example : ∃ S : DCS (Fin 2), S.LargestModulus 2 := by
  sorry

-- PROVABLE: the `n = 4` counterexample to the "any modulus" reading, spelled
-- out: `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` partitions `ℤ`.
example : ∀ x : ZMod 8, (x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) ∨ (x = 0 ∨ x = 4) ∨
    x = 2 ∨ x = 6 := by decide

/-! ## Notes for a follow-up card

**Do not proceed to proof work.**  The blocking item is bibliographic, not
mathematical: find a primary source that defines "multiplicity of a disjoint
covering system" and states the `⌊gpf(n)·φ(n)/n⌋ + 1` bound.  Places to look,
in order:

1. **T. Zamojski, *Survey on covering congruences*** — the entry's own `%H`
   link, `http://www.math.mcgill.ca/~dsavitt/nt/projects/zamojski.ps`.  This is
   the only reference Cloitre attached and is by far the most likely source.
   Fetch it first (`goof fetch` handles `.ps` poorly; convert with `ps2pdf`).
2. Znám, *On exactly covering systems of arithmetic sequences*, Math. Ann. 180
   (1969) 227–232 — the origin of the "least prime factor" multiplicity bound.
3. Berger, Felzenbaum, Fraenkel, Discrete Math. 65 (1987) 23–44 — the nonanalytic
   proof of the Newman–Znám result; the sharpest multiplicity results.
4. Porubský & Schönheim's survey, *Covering systems of Paul Erdős: past,
   present and future* (in *Paul Erdős and his Mathematics I*, 2002).
5. Cloitre's other Mar 2003 sequences — the definition may live in a sibling
   entry from the same batch.

If none of them yields the formula, the honest conclusion is that A080210 is an
*unsourced* entry and the card should be dropped rather than archived, since
there is no claim to archive.

If the source *is* found, the provable-today items become:
* `a080210_prime` — free.
* Znám's `lpf(n) ≤ multiplicity` bound — a real theorem, and a good warm-up.
* The full formula — genuinely hard, and worth doing only once the statement is
  known to be the right one. -/

/-!
## Adversarial review verdict — **FLAG, one serious defect, now FIXED**

Independent raw pull of A080210 plus brute-force exact-cover computation,
2026-08-05.

**Serious defect (FIXED).**  The header claimed `%H (no links)` and omitted
`%A`, while *asserting* a `curl` cross-check had been done.  The raw pull has
**`%H A080210 T. Zamojski, "Survey on covering congruences"** (a McGill student
project) and **`%A A080210 _Benoit Cloitre_, Mar 20 2003`**.  `goof oeis show`
strips `%H` and `%A`, and the draft relayed a subagent summary as if it were the
raw pull.  The header now reproduces **every line** of the text-format output,
names Cloitre, and puts the Zamojski survey at the top of the follow-up reading
list — it is the single most likely source of the missing definition.

**Second defect (FIXED).**  The `gpf` docstring said "with the OEIS convention
`gpf 1 = 1`", but `Finset.sup id ∅ = 0`, so `gpf 1 = 0`.  The discrepancy is
absorbed by the `n ≤ 1` guard in `a080210`; the docstring now says so.

Confirmed:
* The entry genuinely has **no `%C` and no `%D`**.
* **"Lpf" means GREATEST prime factor**: the largest-prime-factor reading
  reproduces the DATA line for `n = 1..40`; the least-prime-factor reading
  diverges at 20 of those 40 values, first at `n = 6`.
* **The largest-modulus reconstruction is right.**
  `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` really partitions `ℤ` with modulus `4`
  appearing once, refuting the "any modulus" reading.  Brute-force exact-cover
  over `ℤ/12` (moduli `≤ 4`) and `ℤ/60` (moduli `≤ 6`) gives minimum
  multiplicity `2` in both cases, matching `a(4) = a(6) = 2`.
  `n = 8, 9, 10, 12` are infeasible by that method.
* `Int.ModEq`'s `[ZMOD n]` notation exists; `ZMod.natCast_self` is the right
  name and `ZMod.natCast_self_eq_zero` does not exist, as the file says.
* `DCS.exact` (`∀ x, ∃! i, …`) correctly encodes disjoint covering, and
  `dcs_multiplicity_needs_largest` is non-vacuous.
* **The FOUNDATION FLAG is justified**: no primary source defines "multiplicity
  of a DCS" or states this formula, and Berger–Felzenbaum–Fraenkel's published
  bound (least prime factor) is strictly weaker.  This card is not proof-ready.
-/

end Candidates.A080210
