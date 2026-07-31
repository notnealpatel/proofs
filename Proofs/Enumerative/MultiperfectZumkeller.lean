import Enumerative.Practical
import Enumerative.IsZumkeller
import Enumerative.ZumkellerSigmaHalf

/-!
# Multiply-perfect numbers and A083207 (OEIS A007691 ⊆ A083207)

OEIS A083207 lists, among its cross-references (pulled live 2026-07-31),

> Conjectured subsequences: A007691, A331668 (after their initial 1's), A351548
> (apart from 0-terms).

so the claim of the lane card is: **every multiply-perfect number `n > 1` is a
Zumkeller number**.  This is OPEN.  Nothing in this file proves it; what lands is

* `Nat.Perfect.isZumkeller` — the abundancy-`2` slice, **unconditionally** and with no
  practicality or evenness hypothesis.  A083207 records this as an *unconditional*
  cross-reference, "Subsequences: A000396, …" (A000396 = perfect numbers), one line
  above the conjectured A007691 line; it is the anchor lemma the card asked for;
* `Nat.IsMultiperfect.isZumkeller_of_practical` — the realization engine: a
  multiply-perfect `n > 1` *known to be practical* is Zumkeller, via the published
  Bhaskara Rao–Peng bridge `Nat.Practical.isZumkeller` in `Enumerative.ZumkellerSigmaHalf`
  (arXiv:0912.0052, proposition `proppraczu`; J. Number Theory **133** (2013) 1135–1155);
* nine unconditional A083207 instances obtained by running that engine over the
  sorry-free Coleman realization layer of `Enumerative.Practical`;
* `Nat.isZumkeller_of_isMultiperfect_of_coleman` — the conjecture-ordering remark,
  stated as the conditional it is, with Coleman's conjecture as an explicit hypothesis.

Everything here is consolidation of published or OEIS-recorded material; no priority
is claimed for any statement.

## Conjecture ordering (the point of the conditional)

Coleman's conjecture — OEIS A007691, comment of Jaycob Coleman, Oct 15 2013, "every
multiply-perfect number is practical (A005153)", archived in `Enumerative.Practical`
as its single intended `sorry` — implies the card's conjecture, through the bridge:
practical forces `2 ∣ n` (`Nat.Practical.two_dvd`), `n ∣ σ(n)` then forces `2 ∣ σ(n)`,
and the bridge concludes.  That is `Nat.isZumkeller_of_isMultiperfect_of_coleman`.
No converse implication is claimed here.

The route is however more expensive than the target needs on the abundancy-`2` slice.
There, the card's conjecture is a theorem of this file with no hypothesis at all —
`Nat.Perfect.isZumkeller` covers a hypothetical *odd* perfect number just as it covers
`6` — whereas Coleman's conjecture implies that no odd perfect number exists at all
(`Nat.not_perfect_of_odd_of_coleman`, the in-tree OPN-hardness reduction, whose only
use of `H` is at perfect numbers).  So the perfect case is where the Coleman hypothesis
is most expensive and where this file needs none of it; the open content of the card's
conjecture is abundancy `≥ 3`.

## Deviation from the lane card

Card `Formalize/A007691-multiperfect-zumkeller.md` planned a file-local multiperfect
predicate and file-local OEIS ground checks.  Both already exist upstream of this file:
`Nat.IsMultiperfect` (with the `0 < n` guard, decidability instance, and the
discriminating scan "exactly `1, 6, 28, 120` below `200`") lives in
`Enumerative.Practical`, and `IsZumkeller` in `Enumerative.IsZumkeller`.  They are
imported and reused rather than restated, so this file adds no definitions.  The card's
suggested route for the anchor lemma ("`n` itself is one side minus adjustments") is
replaced by the direct split `{n} ⊔ n.properDivisors`, which is what perfection says.
-/

set_option autoImplicit false

namespace Nat

/-! ## The anchor: perfect numbers, unconditionally -/

/-- Every perfect number is Zumkeller — **directly**, with no practicality and no
evenness hypothesis: `{n}` and `n.properDivisors` are complementary subsets of
`n.divisors` with equal sums, which is the definition of perfection.

OEIS A083207 xref, "Subsequences: A000396, …" (A000396 = perfect numbers), pulled live
2026-07-31.  The statement is unconditional in `n`, so it applies to a hypothetical odd
perfect number as well; it is the abundancy-`2` slice of the card's conjecture,
settled. -/
theorem Perfect.isZumkeller {n : ℕ} (h : n.Perfect) : IsZumkeller n := by
  have hpos : 0 < n := h.2
  refine (isZumkeller_iff_two_mul_sum_eq_sum_divisors hpos).mpr ⟨{n}, ?_, ?_⟩
  · exact Finset.mem_powerset.mpr
      (Finset.singleton_subset_iff.mpr (Nat.mem_divisors_self n hpos.ne'))
  · rw [Finset.sum_singleton]
    exact ((Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp h).symm

-- Satisfiability of `Nat.Perfect.isZumkeller`: the hypothesis is instantiated at the
-- perfect number `6` and the conclusion is produced (`IsZumkeller 6` is independently
-- `decide`-checked in `Enumerative.IsZumkeller`).
example : IsZumkeller 6 := Perfect.isZumkeller ⟨by decide, by norm_num⟩

/-! ## Multiperfect numbers: feeding the bridge -/

/-- A multiply-perfect `n` with `2 ∣ n` has even divisor sum: `2 ∣ n ∣ σ(n)`. -/
theorem IsMultiperfect.two_dvd_sum_divisors {n : ℕ} (h : n.IsMultiperfect)
    (h2 : 2 ∣ n) : 2 ∣ ∑ d ∈ n.divisors, d :=
  h2.trans h.2

/-- **The realization engine.**  A multiply-perfect `n > 1` that is *known* to be
practical is Zumkeller — no Coleman hypothesis needed.  Evenness is not an extra
assumption: `Nat.Practical.two_dvd` supplies `2 ∣ n`, and `2 ∣ n ∣ σ(n)` then feeds the
Bhaskara Rao–Peng bridge `Nat.Practical.isZumkeller`.  This is what turns each
sorry-free Coleman realization instance of `Enumerative.Practical` into an
unconditional A083207 instance. -/
theorem IsMultiperfect.isZumkeller_of_practical {n : ℕ} (hm : n.IsMultiperfect)
    (hp : n.Practical) (h1 : 1 < n) : IsZumkeller n :=
  hp.isZumkeller (hm.two_dvd_sum_divisors (hp.two_dvd h1))

-- Joint satisfiability of the engine's three hypotheses at `n = 6`.
example : (6 : ℕ).IsMultiperfect ∧ (6 : ℕ).Practical ∧ 1 < 6 := by decide

/-! ## The Coleman conditional -/

/-- **Conjecture-ordering remark, stated as a conditional.**  Under Coleman's
conjecture `H` — the ∀-closure of the archived `Nat.coleman_multiperfect_practical`
(OEIS A007691 comment, Jaycob Coleman, Oct 15 2013) — every multiply-perfect `n > 1` is
Zumkeller.  Composing three recorded facts: the A007691 comment, the Bhaskara Rao–Peng
bridge, and evenness of practical numbers `> 1`.

Conditional by design: `H` is open, so this is a statement about the strength of
Coleman's conjecture, not a fact about exhibited numbers.  Every hypothesis other than
`H` is jointly witnessed at `n = 6` below, and nine unconditional instances of the
conclusion follow the theorem.

The `1 < n` guard is sharp: `1` is multiply-perfect and not Zumkeller (`σ(1) = 1` is
odd), which is exactly the "(after their initial 1's)" hedge in the A083207 xref
"Conjectured subsequences: A007691, A331668 (after their initial 1's), …". -/
theorem isZumkeller_of_isMultiperfect_of_coleman
    (H : ∀ m : ℕ, m.IsMultiperfect → m.Practical)
    {n : ℕ} (hn : n.IsMultiperfect) (h1 : 1 < n) : IsZumkeller n :=
  hn.isZumkeller_of_practical (H n hn) h1

-- Joint satisfiability of the non-`H` hypotheses at `n = 6`.
example : (6 : ℕ).IsMultiperfect ∧ 1 < 6 := by decide

-- Headline packaging: Coleman's conjecture implies the A083207 xref
-- "Conjectured subsequences: A007691 … (after their initial 1's)".
example (H : ∀ m : ℕ, m.IsMultiperfect → m.Practical) :
    ∀ n : ℕ, n.IsMultiperfect → 1 < n → IsZumkeller n :=
  fun _ hn h1 => isZumkeller_of_isMultiperfect_of_coleman H hn h1

end Nat

/-!
## Nine unconditional A083207 instances

Each of the ten sorry-free Coleman realization instances in `Enumerative.Practical`
supplies `IsMultiperfect n ∧ n.Practical`; the engine above converts it.  **Nine, not
ten**: `Nat.coleman_instance_1` is excluded because `σ(1) = 1` is odd and `1 ∉ A083207`
(`not_isZumkeller_one`) — the "(after their initial 1's)" hedge again.

Only `1 < n` is discharged here, by `norm_num`, so no `σ` value is recomputed by the
kernel; these are far cheaper than the practical certificates they rest on.  A direct
`decide` on `IsZumkeller 523776` is out of reach — `523776 = 2⁹ · 3 · 11 · 31` has `80`
divisors and `σ(523776) = 1571328`, so the powerset search has `2⁸⁰` members.
-/

theorem zumkeller_instance_6 : IsZumkeller 6 :=
  Nat.coleman_instance_6.1.isZumkeller_of_practical Nat.coleman_instance_6.2 (by norm_num)

theorem zumkeller_instance_28 : IsZumkeller 28 :=
  Nat.coleman_instance_28.1.isZumkeller_of_practical Nat.coleman_instance_28.2 (by norm_num)

theorem zumkeller_instance_120 : IsZumkeller 120 :=
  Nat.coleman_instance_120.1.isZumkeller_of_practical Nat.coleman_instance_120.2 (by norm_num)

theorem zumkeller_instance_496 : IsZumkeller 496 :=
  Nat.coleman_instance_496.1.isZumkeller_of_practical Nat.coleman_instance_496.2 (by norm_num)

theorem zumkeller_instance_672 : IsZumkeller 672 :=
  Nat.coleman_instance_672.1.isZumkeller_of_practical Nat.coleman_instance_672.2 (by norm_num)

theorem zumkeller_instance_8128 : IsZumkeller 8128 :=
  Nat.coleman_instance_8128.1.isZumkeller_of_practical Nat.coleman_instance_8128.2 (by norm_num)

theorem zumkeller_instance_30240 : IsZumkeller 30240 :=
  Nat.coleman_instance_30240.1.isZumkeller_of_practical Nat.coleman_instance_30240.2
    (by norm_num)

theorem zumkeller_instance_32760 : IsZumkeller 32760 :=
  Nat.coleman_instance_32760.1.isZumkeller_of_practical Nat.coleman_instance_32760.2
    (by norm_num)

theorem zumkeller_instance_523776 : IsZumkeller 523776 :=
  Nat.coleman_instance_523776.1.isZumkeller_of_practical Nat.coleman_instance_523776.2
    (by norm_num)

/-!
## Sharpness of the `1 < n` guard

`1` is the initial term of A007691 and is not a term of A083207; every theorem above
that concludes `IsZumkeller n` from multiperfection carries `1 < n` for this reason.
-/

-- Neither the engine nor the Coleman conditional can be relaxed to `n = 1`, even with
-- the practicality certificate in hand: `1` is practical (`Nat.practical_one`) and
-- multiply-perfect, yet not Zumkeller.  So `1 < n` is doing real work in both.
example : Nat.IsMultiperfect 1 ∧ (1 : ℕ).Practical ∧ ¬ IsZumkeller 1 := by decide

/-! ## Axiom audit -/

#print axioms Nat.Perfect.isZumkeller
#print axioms Nat.IsMultiperfect.two_dvd_sum_divisors
#print axioms Nat.IsMultiperfect.isZumkeller_of_practical
#print axioms Nat.isZumkeller_of_isMultiperfect_of_coleman
#print axioms zumkeller_instance_6
#print axioms zumkeller_instance_28
#print axioms zumkeller_instance_120
#print axioms zumkeller_instance_496
#print axioms zumkeller_instance_672
#print axioms zumkeller_instance_8128
#print axioms zumkeller_instance_30240
#print axioms zumkeller_instance_32760
#print axioms zumkeller_instance_523776
