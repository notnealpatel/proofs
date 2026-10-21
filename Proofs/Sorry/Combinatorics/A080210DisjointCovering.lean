/-
# A080210 — multiplicity lower bound for disjoint covering systems

## ⚠ FOUNDATION FLAG — read before using this card

**Current retrieval gate (reported by the covering-source reader).** The OEIS
entry supplies the formula and sequence name only. Retrieval of the linked
Zamojski PostScript returned HTTP 404. The Berger–Felzenbaum–Fraenkel (1987)
abstract and primary arXiv `math/0306099` multiplicity statements do not supply
the exact `floor(gpf(n) * phi(n) / n) + 1` bound at the numerically largest
modulus; the divisibility-maximal versus numerically largest bridge remains
unpaid. The reconstructed statement `dcs_multiplicity_lower_bound` is now
**REFUTED** (kernel-checked, `dcs_multiplicity_lower_bound_false`): the disjoint
covering system `{0 mod 10, 5 mod 10, 1 mod 5, 2 mod 5, 3 mod 5, 4 mod 5}` has
largest modulus `10` occurring twice, while `a(10) = 3`. Its original text is
kept in a comment above the refutation. The refutation concerns this
reconstructed reading only, not whatever the unretrieved source meant. The elementary prime
formula and finite witnesses are independent of this gate. Historical retrieval
and review notes below are retained; their “not read” language describes the
earlier state, not a pending retrieval task.

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
2. The proposed, unverified interpretation is the multiplicity of the
   **largest** modulus, not of an arbitrary modulus.  Reason: for `n = 4`, the
   system `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` is a disjoint covering system
   in which modulus `4` occurs **once**, contradicting `a(4) = 2` under the
   "any modulus" reading.  The historical small-case computations below
   suggested the largest-modulus reading. The earlier density-only justification
   is not a proof: `3/4 = 1/4 + 1/4 + 1/4` and `5/6 = 1/2 + 1/6 + 1/6` are
   additional decompositions. No largest-modulus bound is established by this
   density sketch.

   Historical, non-certified computation report: exact-cover searches over
   `ℤ/12` with moduli `≤ 4` and `ℤ/60` with moduli `≤ 6` were reported to give
   multiplicity `2`. Their preserved description does not specify whether the
   largest modulus was constrained to be exactly `4` or `6`; no lower-bound
   conclusion is drawn from this report. Larger cases were reported infeasible
   by that method.

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
   where `p` is the **smallest** prime dividing `N`.  At `n = 42`, the
   least-prime-factor bound gives `2` while the reconstructed candidate formula
   gives `3`. This comparison concerns the candidate statement, not a certified
   assertion of the OEIS entry.

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

/-- The four-class system `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` partitions
all integers, including negative integers. -/
def dcs_four : DCS (Fin 4) where
  m := ![2, 4, 8, 8]
  r := ![1, 0, 2, 6]
  m_pos := by decide
  exact := by
    intro x
    have hres : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
        x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
    have hcover : ∃ i : Fin 4,
        Int.ModEq ((![2, 4, 8, 8] i : ℕ) : ℤ) x (![1, 0, 2, 6] i) := by
      rcases hres with h | h | h | h | h | h | h | h
      · exact ⟨1, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨0, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨2, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨0, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨1, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨0, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨3, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨0, by dsimp [Int.ModEq]; omega⟩
    obtain ⟨i, hi⟩ := hcover
    refine ⟨i, hi, ?_⟩
    intro j hj
    fin_cases i <;> fin_cases j <;> dsimp [Int.ModEq] at hi hj ⊢ <;> omega

example : dcs_four.m = ![2, 4, 8, 8] := rfl
example : dcs_four.r = ![1, 0, 2, 6] := rfl
example : dcs_four.multiplicity 4 = 1 := by decide
example : ¬ dcs_four.LargestModulus 4 := by
  intro hmax
  have hle : 8 ≤ 4 := hmax.2 (2 : Fin 4)
  omega

/-! ## The statement (refuted)

The original sorry-bearing declaration is preserved verbatim below as a comment;
it is **false** and has been replaced by `dcs_multiplicity_lower_bound_false`.

```
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

**No proof route is established.** The earlier reduction sketch is inapplicable
to this unrestricted DCS definition: a smaller modulus need not divide the
largest modulus, so reducing the whole system modulo that largest modulus is
unjustified. The ratio `φ(n)/(n/gpf(n))` is an average, not a uniform per-residue
unit count. No named-source attribution or implication to the displayed bound
is certified here.

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
```
-/

/-- The six-class system `{0 mod 10, 5 mod 10, 1 mod 5, 2 mod 5, 3 mod 5,
4 mod 5}` partitions all integers: the multiples of `5` split by the parity of
`x / 5` into the two classes modulo `10`, and every other integer lies in
exactly one nonzero class modulo `5`. -/
def dcs_ten : DCS (Fin 6) where
  m := ![10, 10, 5, 5, 5, 5]
  r := ![0, 5, 1, 2, 3, 4]
  m_pos := by decide
  exact := by
    intro x
    have hres : x % 10 = 0 ∨ x % 10 = 1 ∨ x % 10 = 2 ∨ x % 10 = 3 ∨
        x % 10 = 4 ∨ x % 10 = 5 ∨ x % 10 = 6 ∨ x % 10 = 7 ∨
        x % 10 = 8 ∨ x % 10 = 9 := by omega
    have hcover : ∃ i : Fin 6,
        Int.ModEq ((![10, 10, 5, 5, 5, 5] i : ℕ) : ℤ) x (![0, 5, 1, 2, 3, 4] i) := by
      rcases hres with h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨2, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨3, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨4, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨5, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨1, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨2, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨3, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨4, by dsimp [Int.ModEq]; omega⟩
      · exact ⟨5, by dsimp [Int.ModEq]; omega⟩
    obtain ⟨i, hi⟩ := hcover
    refine ⟨i, hi, ?_⟩
    intro j hj
    fin_cases i <;> fin_cases j <;> dsimp [Int.ModEq] at hi hj ⊢ <;> omega

example : dcs_ten.m = ![10, 10, 5, 5, 5, 5] := rfl
example : dcs_ten.r = ![0, 5, 1, 2, 3, 4] := rfl

/-- `10` is the largest modulus of `dcs_ten`. -/
theorem dcs_ten_largestModulus : dcs_ten.LargestModulus 10 :=
  ⟨⟨0, rfl⟩, by decide⟩

/-- The largest modulus `10` occurs exactly twice in `dcs_ten`. -/
theorem dcs_ten_multiplicity : dcs_ten.multiplicity 10 = 2 := by decide

/-- The A080210 formula at `10`: `⌊gpf(10)·φ(10)/10⌋ + 1 = ⌊5·4/10⌋ + 1 = 3`,
matching the DATA term `a(10) = 3`. -/
theorem a080210_ten : a080210 10 = 3 := by
  have hf : Nat.primeFactorsList 10 = [2, 5] := by simp
  simp only [a080210, gpf, Nat.primeFactors, hf]
  decide

/-- **Refutation of `dcs_multiplicity_lower_bound`.**

Original claim (reconstructed reading of A080210): "in any disjoint covering
system whose largest modulus is `n ≥ 2`, that modulus occurs at least
`⌊gpf(n)·φ(n)/n⌋ + 1` times", formally
`∀ ι S n, 2 ≤ n → S.LargestModulus n → a080210 n ≤ S.multiplicity n`.

This is false.  Counterexample: `dcs_ten`, the disjoint covering system
`{0 mod 10, 5 mod 10, 1 mod 5, 2 mod 5, 3 mod 5, 4 mod 5}`, has largest modulus
`10`, which occurs only twice, while `a080210 10 = 3`.  The same construction
`{0 mod 2m, m mod 2m} ∪ {r mod m : 1 ≤ r < m}` gives largest-modulus
multiplicity `2` for every `2m`.

Source of the discrepancy: the OEIS entry A080210 gives only the `%F` formula
and the name "Lower bound for the multiplicity of a disjoint covering system";
the multiplicity/largest-modulus reading was reconstructed in this file, and the
cited Zamojski survey could not be retrieved, so the intended meaning is
unknown.  The bound established in the literature for the largest modulus of a
disjoint (exact) covering system is the Newman–Znám bound (reproved by
Berger–Felzenbaum–Fraenkel 1987): it occurs at least `minFac n` times, with the
*least* prime factor; the `gpf`-based formula exceeds that bound at `n = 10`. -/
theorem dcs_multiplicity_lower_bound_false :
    ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : DCS ι) (n : ℕ),
      2 ≤ n → S.LargestModulus n → a080210 n ≤ S.multiplicity n := by
  intro hclaim
  have hbound : a080210 10 ≤ dcs_ten.multiplicity 10 :=
    hclaim (Fin 6) dcs_ten 10 (by norm_num) dcs_ten_largestModulus
  rw [a080210_ten, dcs_ten_multiplicity] at hbound
  omega


/-- The reading that is **false**, recorded so it cannot be adopted by accident.

Counterexample from the header: `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` is a
disjoint covering system in which modulus `4` occurs once, but `a(4) = 2`.
So dropping `LargestModulus` from `dcs_multiplicity_lower_bound` breaks it. -/
theorem dcs_multiplicity_needs_largest :
    ∃ S : DCS (Fin 4), (∃ i, S.m i = 4) ∧ S.multiplicity 4 < a080210 4 := by
  refine ⟨dcs_four, ?_, ?_⟩
  · exact ⟨1, rfl⟩
  · have hf : Nat.primeFactorsList 4 = [2, 2] := by simp
    simp only [a080210, gpf, Nat.primeFactors, hf]
    decide

/-! ## Sanity layer

The only things here that are *certain* are facts about the formula, because the
formula is all the entry supplies.  They are worth having: they pin `gpf` (the
least/greatest ambiguity) against the DATA line. -/

-- PROVABLE: `gpf` ground truth.
example : gpf 1 = 0 := by simp [gpf]
example : gpf 2 = 2 := by simp [gpf, Nat.prime_two.primeFactors]
example : gpf 6 = 3 := by
  have hf : Nat.primeFactorsList 6 = [2, 3] := by simp
  simp only [gpf, Nat.primeFactors, hf]
  decide
example : gpf 42 = 7 := by
  have hf : Nat.primeFactorsList 42 = [2, 3, 7] := by simp
  simp only [gpf, Nat.primeFactors, hf]
  decide
example : gpf 45 = 5 := by
  have hf : Nat.primeFactorsList 45 = [3, 3, 5] := by simp
  simp only [gpf, Nat.primeFactors, hf]
  decide

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
example : gpf 42 * Nat.totient 42 / 42 + 1 = 3 := by
  have hf : Nat.primeFactorsList 42 = [2, 3, 7] := by simp
  simp only [gpf, Nat.primeFactors, hf]
  decide

-- PROVABLE: `a080210 p = p` for prime `p`, since `gpf p = p` and `φ(p) = p − 1`
-- give `p(p−1)/p = p − 1`.  Consistent with the DATA at `2, 3, 5, 7, 11, …`.
/-- At every prime input, the formula equals that prime. -/
theorem a080210_prime {p : ℕ} (hp : p.Prime) : a080210 p = p := by
  have hgpf : gpf p = p := by
    simp [gpf, hp.primeFactors]
  have hp_le : 2 ≤ p := hp.two_le
  have hguard : ¬ p ≤ 1 := by omega
  rw [a080210, if_neg hguard, hgpf, Nat.totient_prime hp,
    Nat.mul_div_cancel_left (p - 1) hp.pos]
  exact Nat.sub_add_cancel hp.one_le

example : (2 : ℕ).Prime ∧ a080210 2 = 2 :=
  ⟨Nat.prime_two, a080210_prime Nat.prime_two⟩

-- PROVABLE: satisfiability of `DCS` — a disjoint covering system exists, so the
-- structure is not vacuous.  `{0 mod 2, 1 mod 2}` is the trivial example.
/-- The two parity classes form a disjoint covering system with largest modulus two. -/
theorem dcs_two_exists : ∃ S : DCS (Fin 2), S.LargestModulus 2 := by
  let S : DCS (Fin 2) := {
    m := fun _ => 2
    r := ![0, 1]
    m_pos := by intro i; decide
    exact := by
      intro x
      have hres : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hcover : ∃ i : Fin 2, Int.ModEq 2 x (![0, 1] i) := by
        rcases hres with h | h
        · exact ⟨0, by change x % 2 = 0; exact h⟩
        · exact ⟨1, by change x % 2 = 1; exact h⟩
      obtain ⟨i, hi⟩ := hcover
      refine ⟨i, hi, ?_⟩
      intro j hj
      fin_cases i <;> fin_cases j <;> dsimp [Int.ModEq] at hi hj ⊢ <;> omega }
  refine ⟨S, ?_⟩
  exact ⟨⟨0, rfl⟩, fun _ => Nat.le_refl 2⟩

example : ∃ S : DCS (Fin 2), S.LargestModulus 2 := dcs_two_exists

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

If the sources checked do not yield the intended definition and formula, the
entry remains unsupported by those sources; this does not establish that no
source exists. The admitted candidate statement must remain explicitly
unverified. If a suitable source is found, its exact definitions and hypotheses
must be checked before attempting the main theorem. The elementary declarations
below have independent proofs and do not discharge that source or proof
obligation. -/

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
* **The arbitrary-modulus reading is refuted.** The formal witness
  `{1 mod 2, 0 mod 4, 2 mod 8, 6 mod 8}` partitions `ℤ` with modulus `4`
  appearing once. The numerical-largest-modulus reading remains an unverified
  reconstruction of the OEIS meaning. Historical small-case searches were
  reported, but their unpreserved search-domain details do not certify that
  interpretation.
* `Int.ModEq`'s `[ZMOD n]` notation exists; `ZMod.natCast_self` is the right
  name and `ZMod.natCast_self_eq_zero` does not exist, as the file says.
* `DCS.exact` (`∀ x, ∃! i, …`) correctly encodes disjoint covering, and
  `dcs_multiplicity_needs_largest` is non-vacuous.
* **The FOUNDATION FLAG remains justified**: no retrieved source has
  established the exact intended definition and displayed formula. The
  inaccessible survey and unsuccessful retrievals do not establish absence from
  all primary sources. The main bound remains an unsupported-source admission,
  not a theorem certified here.
-/

end Candidates.A080210
