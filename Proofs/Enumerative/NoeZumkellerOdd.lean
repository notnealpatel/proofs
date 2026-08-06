import Enumerative.IsZumkeller

/-!
# A174865 and Noe's odd-Zumkeller conjecture: the odd perfect number obstruction

T. D. Noe observed that the odd Zumkeller numbers appear to be exactly the odd
abundant numbers of even abundance (OEIS A174865).  This file archives that
statement and proves the one structural fact that decides how hard it is: the
"easy" direction is **not** easy — it is equivalent to the nonexistence of odd
perfect numbers.

## Sources, pinned verbatim

`goof oeis show A174865`, pulled live 2026-08-05.  Name:

> "Odd abundant numbers whose abundance is even."

Comment:

> "This is a subsequence of the odd abundant numbers, A005231. The first term in
> A005231 but not in this sequence is 11025."

Mathematica program (the operational definition this file mirrors):

> `goodQ[n_] := Module[{ds=DivisorSigma[1,n]}, ds>2n && EvenQ[ds]]; Select[Range[1,1000000,2], goodQ]`

Terms:

> "945,1575,2205,2835,3465,4095,4725,5355,5775,5985,6435,6615,6825,7245,7425,
> 7875,8085,8415,8505,8925,9135,9555,9765,10395,11655,12285,12705,12915,13545,
> 14175,14805,15015,15435,16065,16695,17325,17955,18585"

Author (from the raw OEIS record at `https://oeis.org/search?q=id:A174865&fmt=json`;
the `author` field is not surfaced by `goof oeis show`):

> `"author": "_T. D. Noe_, Mar 31 2010"`

**The conjecture itself is not in A174865.**  It is a comment on A083207
(`goof oeis show A083207`, pulled live 2026-08-05):

> "The 229026 Zumkeller numbers less than 10^6 have a maximum difference of 12.
> This leads to the conjecture that any 12 consecutive numbers include at least
> one Zumkeller number. There are 1989 odd Zumkeller numbers less than 10^6; they
> are exactly the odd abundant numbers that have even abundance, A174865.
> - _T. D. Noe_, Mar 31 2010"

and, sharpened later:

> "All 205283 odd abundant numbers less than 10^8 that have even abundance (see
> A174865) are Zumkeller numbers. - _T. D. Noe_, Nov 14 2010"

Note that the second comment asserts only the *converse* direction
(A174865 ⊆ A083207), and asserts it as verified computation, not as a theorem.

A171641 (`goof oeis show A171641`, pulled live 2026-08-05).  Name:

> "Non-deficient numbers with even sigma which are not Zumkeller."

Comment:

> "Numbers which are non-deficient (sigma(n) >= 2n) [A023196] such that sigma(n)
> [A000203] is even but which are not Zumkeller numbers [A083207], i.e., the
> positive factors of n cannot be partitioned into two disjoint parts so that the
> sums of the two parts are equal."

Terms:

> "738,748,774,846,954,1062,1098,1206,1278,1314,1422,1494,1602,1746,1818,1854,
> 1926,1962,2034,2286,2358,2466,2502,2682,2718,2826,2934,3006,3114,3222,3258,
> 3438,3474,3492,3546,3582,3636,3708,3798,3852,3924,4014,4068,4086"

## What is proved here

The headline is `noeOddZumkellerForward_iff_not_exists_odd_perfect`: the direction
"odd and Zumkeller ⟹ in A174865" holds for all `n` **if and only if** there is no
odd perfect number.  The obstruction is exact and elementary.  A perfect number is
Zumkeller — split its divisors as `{n}` against the proper divisors — so an odd
perfect number would be an odd Zumkeller number that is *not* abundant, since
A174865 demands `2n < σ(n)` strictly.  Conversely, a Zumkeller number always
satisfies `2n ≤ σ(n)`, and ruling out equality is exactly ruling out perfection.

Consequently `NoeOddZumkeller.not_exists_odd_perfect`: Noe's conjecture as stated
implies there is no odd perfect number, so it is at least as hard as that problem.

What *is* unconditionally provable is the same direction with `≤` in place of `<`:
`isOddNonDeficientEvenSigma_of_odd_isZumkeller`.  Replacing "abundant" by
"non-deficient" repairs the statement, and
`noeOddZumkellerRepaired_iff_forall_isA171641_not_odd` identifies the repaired
conjecture with a sentence about an existing OEIS sequence: **A171641 contains no
odd term**.  That reformulation loses nothing — the two versions of the conjecture
differ only on odd perfect numbers — and it is the version a formalization can
actually make progress on.

The remaining content of Noe's conjecture, the converse `A174865 ⊆ A083207`, is
recorded as `NoeOddZumkellerConverse` and is **open**: it is not proved here, not
assumed anywhere, and no `sorry` stands behind it.  It is instantiated at the first
term, `945`, by `isZumkeller_945`.

## Deviation from the lane brief

The brief located the conjecture at A174865 and predicted "Easy direction (odd
Zumkeller → A174865) should be provable from the existing `IsZumkeller` and
`ZumkellerSigmaHalf` infrastructure. Hard direction is the sorry."  Both halves are
wrong and the file reflects the sources instead:

* the conjecture is a comment on A083207, not on A174865 (A174865 carries no
  Zumkeller comment at all);
* the "easy" direction is equivalent to the nonexistence of odd perfect numbers
  (`noeOddZumkellerForward_iff_not_exists_odd_perfect`), hence open, and no
  infrastructure could have discharged it.

`Enumerative.ZumkellerSigmaHalf` is *not* imported: its content is the practical
number bridge, and no odd number above `1` is practical, so it cannot bear on odd
Zumkeller numbers.  Nothing here is sorried; the open statements are archived as
`Prop`-valued definitions in the style of `IanakievSigmaHalf`.
-/

set_option autoImplicit false

open Finset

/-! ## Divisor sums of the pinned witnesses

Computed through `Nat.Coprime.sum_divisors_mul` rather than by kernel evaluation of
`Nat.divisors`; the multiplicative route keeps every `decide` below a few dozen
elements. -/

/-- `σ(945) = 1920`, via `945 = 27 · 35` with `σ(27) = 40` and `σ(35) = 48`. -/
theorem sum_divisors_945 : (∑ d ∈ (945 : ℕ).divisors, d) = 1920 := by
  have h : (945 : ℕ) = 27 * 35 := by norm_num
  rw [h, Nat.Coprime.sum_divisors_mul (by decide)]
  decide

/-- `σ(11025) = 22971`, via `11025 = 225 · 49` with `σ(225) = 403` and `σ(49) = 57`.
The value is **odd**, which is what keeps `11025` out of A174865. -/
theorem sum_divisors_11025 : (∑ d ∈ (11025 : ℕ).divisors, d) = 22971 := by
  have h : (11025 : ℕ) = 225 * 49 := by norm_num
  rw [h, Nat.Coprime.sum_divisors_mul (by decide)]
  decide

/-- `σ(738) = 1638`, via `738 = 18 · 41` with `σ(18) = 39` and `σ(41) = 42`. -/
theorem sum_divisors_738 : (∑ d ∈ (738 : ℕ).divisors, d) = 1638 := by
  have h : (738 : ℕ) = 18 * 41 := by norm_num
  rw [h, Nat.Coprime.sum_divisors_mul (by decide)]
  decide

/-! ## A174865 -/

/-- Mathlib's `Nat.Abundant` (`n < ∑ proper divisors`) in divisor-sum form.  The two
agree at every `n`, including `n = 0`, where both sides are false. -/
theorem Nat.abundant_iff_two_mul_lt_sum_divisors (n : ℕ) :
    n.Abundant ↔ 2 * n < ∑ d ∈ n.divisors, d := by
  rw [Nat.Abundant, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- **OEIS A174865**: "Odd abundant numbers whose abundance is even."

The abundance `σ(n) - 2n` is taken in `ℤ`, so the subtraction is the real one and
carries no `Nat` truncation.  Positivity needs no separate guard: `Odd n` already
forces `n ≠ 0`, and `Nat.Abundant 0` is false. -/
def IsA174865 (n : ℕ) : Prop :=
  Odd n ∧ n.Abundant ∧ Even (((∑ d ∈ n.divisors, d : ℕ) : ℤ) - 2 * (n : ℤ))

/-- A174865 in the form of its own OEIS Mathematica program,
`ds > 2n && EvenQ[ds]` restricted to odd `n`: evenness of the abundance is
evenness of `σ(n)`, since `2n` is even. -/
theorem isA174865_iff (n : ℕ) :
    IsA174865 n ↔ Odd n ∧ 2 * n < (∑ d ∈ n.divisors, d) ∧ 2 ∣ ∑ d ∈ n.divisors, d := by
  rw [IsA174865, Nat.abundant_iff_two_mul_lt_sum_divisors]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [Int.even_iff]
  omega

instance : DecidablePred IsA174865 := fun n => decidable_of_iff _ (isA174865_iff n).symm

/-- Every term of A174865 is positive. -/
theorem IsA174865.pos {n : ℕ} (h : IsA174865 n) : 0 < n := h.2.1.pos

/-- Ground truth, first term of A174865: `945` is odd, `σ(945) = 1920 > 1890 = 2·945`,
and the abundance `30` is even. -/
theorem isA174865_945 : IsA174865 945 := by
  rw [isA174865_iff, sum_divisors_945]
  refine ⟨by decide, by norm_num, by norm_num⟩

/-- Ground truth for the A174865 comment "The first term in A005231 but not in this
sequence is 11025": `11025` **is** odd and abundant, `σ(11025) = 22971 > 22050`. -/
theorem odd_abundant_11025 : Odd 11025 ∧ (11025 : ℕ).Abundant := by
  refine ⟨by decide, ?_⟩
  rw [Nat.abundant_iff_two_mul_lt_sum_divisors, sum_divisors_11025]
  norm_num

/-- Ground truth, the excluded number: `11025` is **not** in A174865, because
`σ(11025) = 22971` is odd, so its abundance `921` is odd. -/
theorem not_isA174865_11025 : ¬ IsA174865 11025 := by
  rw [isA174865_iff, sum_divisors_11025]
  rintro ⟨-, -, hdvd⟩
  omega

/-! ## Two facts about Zumkeller numbers

Neither is in `Enumerative.IsZumkeller`; both are needed to locate the obstruction. -/

/-- A Zumkeller number is non-deficient: `2n ≤ σ(n)`.  The divisor `n` lies in one
side of the equal-sum split, so each side sums to at least `n`. -/
theorem IsZumkeller.two_mul_le_sum_divisors {n : ℕ} (h : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, A, hA_pow, hsum⟩ := h
  have hA : A ⊆ n.divisors := Finset.mem_powerset.mp hA_pow
  have hsplit : ∑ d ∈ n.divisors \ A, d + ∑ a ∈ A, a = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hA
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hn_le : n ≤ ∑ a ∈ A, a := by
    by_cases hnA : n ∈ A
    · exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hnA
    · have hmem' : n ∈ n.divisors \ A := Finset.mem_sdiff.mpr ⟨hmem, hnA⟩
      have hle : n ≤ ∑ d ∈ n.divisors \ A, d :=
        Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hmem'
      omega
  omega

/-- **A perfect number is Zumkeller**: split its divisors as `{n}` against the
proper divisors, whose sum is `n` by perfection.  This is what makes an odd perfect
number a counterexample to the "easy" direction of Noe's conjecture. -/
theorem Nat.Perfect.isZumkeller {n : ℕ} (h : n.Perfect) : IsZumkeller n := by
  have hn : 0 < n := h.2
  rw [isZumkeller_iff_two_mul_sum_eq_sum_divisors hn]
  refine ⟨{n}, Finset.mem_powerset.mpr ?_, ?_⟩
  · exact Finset.singleton_subset_iff.mpr (Nat.mem_divisors_self n hn.ne')
  · rw [Finset.sum_singleton, (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp h]

/-- Ground truth for `Nat.Perfect.isZumkeller` at the first perfect number, `6`;
cross-checked against the direct decision procedure, which also gives `6`. -/
theorem isZumkeller_six_of_perfect : IsZumkeller 6 :=
  Nat.Perfect.isZumkeller ⟨by decide, by norm_num⟩

example : IsZumkeller 6 := by decide

/-! ## Noe's conjecture, as stated -/

/-- **Noe's conjecture** (OEIS A083207 comment, T. D. Noe, Mar 31 2010), OPEN: the
odd Zumkeller numbers are exactly the terms of A174865, the odd abundant numbers of
even abundance.

This is the sentence and nothing more.  It is **not** proved here and **not**
assumed anywhere in this repository; no `sorry` stands behind it.  See
`NoeOddZumkeller.not_exists_odd_perfect` for why it is at least as hard as the odd
perfect number problem. -/
def NoeOddZumkeller : Prop :=
  ∀ n : ℕ, IsA174865 n ↔ Odd n ∧ IsZumkeller n

/-- The direction of Noe's conjecture that the lane brief called easy: every odd
Zumkeller number is an odd abundant number of even abundance.  It is not easy —
`noeOddZumkellerForward_iff_not_exists_odd_perfect` shows it is equivalent to the
nonexistence of odd perfect numbers. -/
def NoeOddZumkellerForward : Prop :=
  ∀ n : ℕ, Odd n → IsZumkeller n → IsA174865 n

/-- The substantive direction of Noe's conjecture, and the only part Noe reported
verifying to `10^8`: every term of A174865 is a Zumkeller number.  OPEN. -/
def NoeOddZumkellerConverse : Prop :=
  ∀ n : ℕ, IsA174865 n → IsZumkeller n

/-- Noe's conjecture splits into its two directions.  The `Odd n` half of the
right-hand side is free: it is the first conjunct of `IsA174865`. -/
theorem noeOddZumkeller_iff_forward_and_converse :
    NoeOddZumkeller ↔ NoeOddZumkellerForward ∧ NoeOddZumkellerConverse := by
  constructor
  · intro h
    exact ⟨fun n hodd hzum => (h n).mpr ⟨hodd, hzum⟩, fun n hn => ((h n).mp hn).2⟩
  · rintro ⟨hfwd, hconv⟩ n
    exact ⟨fun hn => ⟨hn.1, hconv n hn⟩, fun hn => hfwd n hn.1 hn.2⟩

/-! ## The obstruction: the "easy" direction is the odd perfect number problem -/

/-- **The obstruction, exactly.** Every odd Zumkeller number is abundant **iff**
there is no odd perfect number.

Forward: an odd perfect number is odd and Zumkeller (`Nat.Perfect.isZumkeller`) but
has `σ(n) = 2n`, contradicting the strict `2n < σ(n)` demanded by A174865.
Backward: a Zumkeller number has `2n ≤ σ(n)` (`IsZumkeller.two_mul_le_sum_divisors`)
and `2 ∣ σ(n)` (`IsZumkeller.two_dvd_sum_divisors`); equality `σ(n) = 2n` would make
it perfect, which the hypothesis forbids for odd `n`, so the inequality is strict. -/
theorem noeOddZumkellerForward_iff_not_exists_odd_perfect :
    NoeOddZumkellerForward ↔ ¬ ∃ n : ℕ, Odd n ∧ n.Perfect := by
  constructor
  · rintro hfwd ⟨n, hodd, hperf⟩
    have hzum : IsZumkeller n := hperf.isZumkeller
    have hmem : IsA174865 n := hfwd n hodd hzum
    have hlt : 2 * n < ∑ d ∈ n.divisors, d := ((isA174865_iff n).mp hmem).2.1
    have heq : ∑ d ∈ n.divisors, d = 2 * n :=
      (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
    omega
  · intro hno n hodd hzum
    have hle : 2 * n ≤ ∑ d ∈ n.divisors, d := hzum.two_mul_le_sum_divisors
    have hdvd : 2 ∣ ∑ d ∈ n.divisors, d := hzum.two_dvd_sum_divisors
    have hne : ∑ d ∈ n.divisors, d ≠ 2 * n := by
      intro heq
      exact hno ⟨n, hodd, (Nat.perfect_iff_sum_divisors_eq_two_mul hzum.pos).mpr heq⟩
    exact (isA174865_iff n).mpr ⟨hodd, by omega, hdvd⟩

/-- **Noe's conjecture implies there is no odd perfect number.**  So it is at least
as hard as the odd perfect number problem, and the direction the lane brief expected
to be routine is in fact the open one. -/
theorem NoeOddZumkeller.not_exists_odd_perfect (h : NoeOddZumkeller) :
    ¬ ∃ n : ℕ, Odd n ∧ n.Perfect :=
  noeOddZumkellerForward_iff_not_exists_odd_perfect.mp
    (noeOddZumkeller_iff_forward_and_converse.mp h).1

/-! ## The repaired statement

Weakening "abundant" to "non-deficient" — `2n ≤ σ(n)` instead of `2n < σ(n)` —
removes the odd perfect obstruction and nothing else, since the two differ exactly
on odd perfect numbers.  The forward direction then becomes a theorem. -/

/-- The repaired membership condition: odd, non-deficient, with even divisor sum. -/
def IsOddNonDeficientEvenSigma (n : ℕ) : Prop :=
  Odd n ∧ 2 * n ≤ (∑ d ∈ n.divisors, d) ∧ 2 ∣ ∑ d ∈ n.divisors, d

instance : DecidablePred IsOddNonDeficientEvenSigma := fun n =>
  inferInstanceAs (Decidable (Odd n ∧ 2 * n ≤ (∑ d ∈ n.divisors, d) ∧
    2 ∣ ∑ d ∈ n.divisors, d))

/-- **The forward direction, unconditionally.**  Every odd Zumkeller number is odd,
non-deficient, and has even divisor sum.  This is the strongest form of Noe's
"easy" direction that is provable today: strengthening `≤` to `<` here is exactly
the odd perfect number problem. -/
theorem isOddNonDeficientEvenSigma_of_odd_isZumkeller {n : ℕ} (hodd : Odd n)
    (h : IsZumkeller n) : IsOddNonDeficientEvenSigma n :=
  ⟨hodd, h.two_mul_le_sum_divisors, h.two_dvd_sum_divisors⟩

/-- **Noe's conjecture, repaired**: the odd Zumkeller numbers are exactly the odd
non-deficient numbers with even divisor sum.  Unlike `NoeOddZumkeller` this does not
imply the nonexistence of odd perfect numbers.  Still OPEN. -/
def NoeOddZumkellerRepaired : Prop :=
  ∀ n : ℕ, IsOddNonDeficientEvenSigma n ↔ Odd n ∧ IsZumkeller n

/-- The repaired conjecture reduces to its converse direction alone: the forward
direction is `isOddNonDeficientEvenSigma_of_odd_isZumkeller`, already a theorem. -/
theorem noeOddZumkellerRepaired_iff_converse :
    NoeOddZumkellerRepaired ↔ ∀ n : ℕ, IsOddNonDeficientEvenSigma n → IsZumkeller n := by
  constructor
  · intro h n hn
    exact ((h n).mp hn).2
  · intro h n
    exact ⟨fun hn => ⟨hn.1, h n hn⟩,
      fun hn => isOddNonDeficientEvenSigma_of_odd_isZumkeller hn.1 hn.2⟩

/-! ## A171641: the repaired conjecture is a sentence about an OEIS sequence -/

/-- **OEIS A171641**: "Non-deficient numbers with even sigma which are not
Zumkeller."  The `0 < n` guard is required: at `n = 0` the divisor sum is `0`, so
`2·0 ≤ 0` and `2 ∣ 0` hold and `0` is not Zumkeller, which would make `0` a
spurious member of a sequence of positive integers. -/
def IsA171641 (n : ℕ) : Prop :=
  0 < n ∧ 2 * n ≤ (∑ d ∈ n.divisors, d) ∧ 2 ∣ (∑ d ∈ n.divisors, d) ∧ ¬ IsZumkeller n

instance : DecidablePred IsA171641 := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ 2 * n ≤ (∑ d ∈ n.divisors, d) ∧
    2 ∣ (∑ d ∈ n.divisors, d) ∧ ¬ IsZumkeller n))

set_option maxRecDepth 100000 in
/-- Ground truth, first term of A171641: `738` is non-deficient
(`σ(738) = 1638 ≥ 1476`) with even divisor sum, and is not Zumkeller.

The `¬ IsZumkeller 738` conjunct is a kernel search over the `2 ^ 12` subsets of the
twelve divisors of `738`; the raised `maxRecDepth` is for that search alone. -/
theorem isA171641_738 : IsA171641 738 := by
  refine ⟨by norm_num, ?_, ?_, by decide⟩
  · rw [sum_divisors_738]; norm_num
  · rw [sum_divisors_738]; norm_num

/-- **The repaired conjecture is exactly "A171641 has no odd term."**  This is the
reformulation a formalization can attack: it is a statement about a single existing
OEIS sequence, with no reference to abundance, perfection, or the `<`/`≤` boundary
that entangles the original with the odd perfect number problem. -/
theorem noeOddZumkellerRepaired_iff_forall_isA171641_not_odd :
    NoeOddZumkellerRepaired ↔ ∀ n : ℕ, IsA171641 n → ¬ Odd n := by
  rw [noeOddZumkellerRepaired_iff_converse]
  constructor
  · rintro h n ⟨-, hle, hdvd, hnz⟩ hodd
    exact hnz (h n ⟨hodd, hle, hdvd⟩)
  · rintro h n ⟨hodd, hle, hdvd⟩
    by_contra hnz
    exact h n ⟨hodd.pos, hle, hdvd, hnz⟩ hodd

/-! ## Satisfiability

Every conjecture statement above quantifies over a hypothesis that must be
inhabited, or the statement says nothing.  `945` inhabits all of them at once: it is
odd, Zumkeller, and a term of A174865. -/

/-- `945` is a Zumkeller number: `σ(945) = 1920` and the divisors `15` and `945` sum
to `960`, half of `1920`.  This is the first term of A174865, so it witnesses the
open converse `NoeOddZumkellerConverse` at its least instance — the hypothesis
`IsA174865 n` is satisfiable and the conjecture is not vacuous. -/
theorem isZumkeller_945 : IsZumkeller 945 := by
  rw [isZumkeller_iff_two_mul_sum_eq_sum_divisors (by norm_num)]
  refine ⟨{15, 945}, Finset.mem_powerset.mpr ?_, ?_⟩
  · refine Finset.insert_subset ?_ (Finset.singleton_subset_iff.mpr ?_)
    · exact Nat.mem_divisors.mpr ⟨by norm_num, by norm_num⟩
    · exact Nat.mem_divisors_self 945 (by norm_num)
  · rw [sum_divisors_945, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-- Joint satisfiability of `NoeOddZumkellerForward`'s hypotheses at `945`: it is
odd and Zumkeller, so the direction equivalent to the odd perfect number problem is
not vacuously true. -/
theorem odd_isZumkeller_945 : Odd 945 ∧ IsZumkeller 945 := ⟨by decide, isZumkeller_945⟩

/-- Noe's conjecture holds at its first instance, `945`, in the strong biconditional
form: `945 ∈ A174865` and `945` is an odd Zumkeller number. -/
theorem noeOddZumkeller_945 : IsA174865 945 ↔ Odd 945 ∧ IsZumkeller 945 :=
  ⟨fun _ => odd_isZumkeller_945, fun _ => isA174865_945⟩

/-- The repaired condition is satisfiable at `945` too, so
`NoeOddZumkellerRepaired` is not vacuous. -/
theorem isOddNonDeficientEvenSigma_945 : IsOddNonDeficientEvenSigma 945 :=
  isOddNonDeficientEvenSigma_of_odd_isZumkeller (by decide) isZumkeller_945

/-- `945` is not a counterexample to the repaired conjecture's reformulation: it is
odd but not in A171641. -/
theorem not_isA171641_945 : ¬ IsA171641 945 := fun h => h.2.2.2 isZumkeller_945

/-! ## Axiom audit -/

#print axioms sum_divisors_945
#print axioms sum_divisors_11025
#print axioms sum_divisors_738
#print axioms Nat.abundant_iff_two_mul_lt_sum_divisors
#print axioms isA174865_iff
#print axioms isA174865_945
#print axioms odd_abundant_11025
#print axioms not_isA174865_11025
#print axioms IsZumkeller.two_mul_le_sum_divisors
#print axioms Nat.Perfect.isZumkeller
#print axioms noeOddZumkeller_iff_forward_and_converse
#print axioms noeOddZumkellerForward_iff_not_exists_odd_perfect
#print axioms NoeOddZumkeller.not_exists_odd_perfect
#print axioms isOddNonDeficientEvenSigma_of_odd_isZumkeller
#print axioms noeOddZumkellerRepaired_iff_converse
#print axioms isA171641_738
#print axioms noeOddZumkellerRepaired_iff_forall_isA171641_not_odd
#print axioms isZumkeller_945
#print axioms noeOddZumkeller_945
#print axioms not_isA171641_945

-- The conjecture statements themselves, printed so a reader can audit the
-- elaborated forms rather than the sugar.
#print NoeOddZumkeller
#print NoeOddZumkellerConverse
#print NoeOddZumkellerRepaired
#print IsA174865
#print IsA171641
