import Enumerative.Practical
import Enumerative.IsZumkeller

/-!
# Practical numbers and the σ-parity bridge to A083207

A practical number is a Zumkeller number exactly when its divisor sum is even.  This
is a **published** result and this file is consolidation, not new mathematics:

> K. P. S. Bhaskara Rao and Yuejian Peng, *On Zumkeller numbers*,
> J. Number Theory **133** (2013), no. 4, 1135–1155; arXiv:0912.0052.

The statement is the proposition labelled `proppraczu` in the arXiv source (local
corpus copy `References/arXiv-0912-0052/paper.tex`, line 285): "A practical number
`n` is a Zumkeller number if and only if `σ(n)` is even."  The proof formalised in
`Nat.Practical.isZumkeller` is the paper's own: `σ(n)/2 < σ(n)` is represented as a
sum of distinct divisors because `n` is practical, and the complementary divisors
carry the other half.  The two sharpness witnesses recorded below (`70`, and the
converse direction) are the paper's own examples from the Remark following
`proppraczu`.  The same equivalence is recorded at OEIS A083207 as the comment of
David A. Corneth, Nov 03 2024 — "This sequence contains A378541, the intersection of
the practical numbers (A005153) with numbers with even sum of divisors (A028983)" —
pulled live 2026-07-31.

Contents:

* `Nat.Practical.isZumkeller` — the bridge, the substantive direction of `proppraczu`;
* `Nat.Practical.isZumkeller_iff_two_dvd_sum_divisors` — `proppraczu` itself; the
  converse direction is the in-tree `IsZumkeller.two_dvd_sum_divisors`, which needs no
  practicality;
* `infinite_setOf_isZumkeller` — A083207 is infinite, so `Nat.nth IsZumkeller`
  enumerates it faithfully rather than degenerating to the `Nat.nth` junk value;
* `IanakievSigmaHalf` — the **statement** of the open conjecture this lane card was
  opened for, unproved and unassumed;
* `upstreamIsPractical` and `practical_iff_upstream` — the definitional delta against
  `google-deepmind/formal-conjectures`.

## Deviation from the lane card

Card `Formalize/A083207-ianakiev-sigma-half.md` asked for the Ianakiev conjecture
(OEIS A083207 comment, Apr 03 2017): among any four consecutive Zumkeller numbers
some `k` has `σ(k)/2` Zumkeller.  The card records "ROUTE: none visible", and none has
appeared; nothing in this file proves it or assumes it.  What lands instead is the
σ-half material that *is* settled — the published Bhaskara Rao–Peng characterisation —
together with a formal statement of the card's conjecture and the infinitude lemma
that makes the enumeration in that statement well defined.  The card's suggested
`IsZumkeller` definition is already in-tree (`Enumerative.IsZumkeller`) and is reused
here rather than restated.
-/

set_option autoImplicit false

namespace Nat

/-! ## The bridge -/

/-- **The practical ⟹ Zumkeller bridge** (Bhaskara Rao–Peng, arXiv:0912.0052,
`proppraczu`, substantive direction).  A practical number with even divisor sum is
Zumkeller: `Nat.Practical.exists_sum_eq_of_le_sum_divisors` represents `σ(n)/2` as a
subset sum of `n.divisors`, and the complementary subset then carries the other half.

Set-theoretically this is `A005153 ∩ A028983 ⊆ A083207`, i.e. `A378541 ⊆ A083207`
(OEIS A083207 comment of David A. Corneth, Nov 03 2024). -/
theorem Practical.isZumkeller {n : ℕ} (h : n.Practical)
    (hσ : 2 ∣ ∑ d ∈ n.divisors, d) : IsZumkeller n := by
  obtain ⟨t, ht⟩ := hσ
  -- the strong characterisation represents the half-sum `t = σ(n)/2`
  obtain ⟨S, hS_sub, hS_sum⟩ := h.exists_sum_eq_of_le_sum_divisors (m := t) (by omega)
  refine (isZumkeller_iff_two_mul_sum_eq_sum_divisors h.pos).mpr
    ⟨S, Finset.mem_powerset.mpr hS_sub, ?_⟩
  omega

/-- **Bhaskara Rao–Peng, `proppraczu`**: a practical number is Zumkeller if and only if
its divisor sum is even.  The converse direction is the in-tree
`IsZumkeller.two_dvd_sum_divisors`, which holds for every Zumkeller number and uses no
practicality.  Sharpness of the `2 ∣ σ(n)` hypothesis is witnessed at `n = 18` below. -/
theorem Practical.isZumkeller_iff_two_dvd_sum_divisors {n : ℕ} (h : n.Practical) :
    IsZumkeller n ↔ 2 ∣ ∑ d ∈ n.divisors, d :=
  ⟨IsZumkeller.two_dvd_sum_divisors, h.isZumkeller⟩

end Nat

/-!
## Sharpness and satisfiability

Three witnesses pin the shape of the bridge; `70` is Bhaskara Rao–Peng's own example
from the Remark following `proppraczu`.
-/

-- Joint satisfiability of the bridge's hypotheses at `n = 6`.
example : (6 : ℕ).Practical ∧ 2 ∣ ∑ d ∈ (6 : ℕ).divisors, d := by decide

-- SHARPNESS of `2 ∣ σ(n)`: `18` is practical with `σ(18) = 39` odd, and is NOT
-- Zumkeller.  So the hypothesis cannot be dropped.
example : (18 : ℕ).Practical ∧ ¬ IsZumkeller 18 := by decide

-- The CONVERSE of the bridge fails: `70 = 2 · 5 · 7` is Zumkeller but not practical
-- (`4` is not a subset sum of `{1, 2, 5, 7, 10, 14, 35, 70}`; Stewart's ascending
-- bound fails at `5 > 1 + σ(2) = 4`), so `IsZumkeller → Practical` is false.  This is
-- Bhaskara Rao–Peng's own example, arXiv:0912.0052, Remark following `proppraczu`.
-- Their other example there is the odd Zumkeller number `945`, which is not practical
-- by `Nat.not_practical_of_odd_of_one_lt` — already witnessed in `Enumerative.Practical`
-- and so not repeated here.
set_option maxRecDepth 40000 in
example : IsZumkeller 70 ∧ ¬ (70 : ℕ).Practical := by decide

/-!
## A083207 is infinite

`Nat.nth IsZumkeller` is the increasing enumeration of A083207 only when the predicate
holds infinitely often; otherwise `Nat.nth` returns its junk value past the last term.
Infinitude follows from the in-tree coprime closure engine alone: `6` is Zumkeller and
`6 * 5 ^ k` is coprime-closed off it.
-/

/-- A083207 is infinite: `6 * 5 ^ k` is Zumkeller for every `k`, by
`IsZumkeller.mul_of_coprime` off the base case `6`. -/
theorem infinite_setOf_isZumkeller : {n : ℕ | IsZumkeller n}.Infinite := by
  have hinj : Function.Injective fun k : ℕ => 6 * 5 ^ k := by
    intro a b hab
    have hab' : 6 * 5 ^ a = 6 * 5 ^ b := hab
    have h5 : (5 : ℕ) ^ a = 5 ^ b := Nat.eq_of_mul_eq_mul_left (by norm_num) hab'
    exact Nat.pow_right_injective (by norm_num) h5
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro k
  exact IsZumkeller.mul_of_coprime (by decide) (Nat.Coprime.pow_right k (by decide))

/-- The enumeration `Nat.nth IsZumkeller` starts at the first term of A083207, `6`:
no `m < 6` is Zumkeller, so `Nat.count IsZumkeller 6 = 0`. -/
theorem nth_isZumkeller_zero : Nat.nth IsZumkeller 0 = 6 := by
  have hcount : Nat.count IsZumkeller 6 = 0 := by decide
  simpa [hcount] using Nat.nth_count (p := IsZumkeller) (n := 6) (by decide)

/-- The enumeration agrees with the A083207 prefix at index `1`. -/
theorem nth_isZumkeller_one : Nat.nth IsZumkeller 1 = 12 := by
  have hcount : Nat.count IsZumkeller 12 = 1 := by decide
  simpa [hcount] using Nat.nth_count (p := IsZumkeller) (n := 12) (by decide)

/-!
## The card's conjecture, as a statement

OEIS A083207, comment of **Ivan N. Ianakiev, Apr 03 2017** (pulled live 2026-07-31):
"Conjecture: Any 4 consecutive terms include at least one number k such that
sigma(k)/2 is also a Zumkeller number (verified for the first 10^5 Zumkeller
numbers)."

`IanakievSigmaHalf` below is that sentence and nothing more.  It is **not** proved
here and **not** assumed anywhere in this repository; no `sorry` stands behind it.
`σ(k)/2` is spelled multiplicatively as `∃ m, 2 * m = σ(k) ∧ IsZumkeller m`, so no
`Nat` division appears and the halving is exact by construction (the existence of `m`
is automatic for Zumkeller `k` by `IsZumkeller.two_dvd_sum_divisors`; the content is
that `m` is again Zumkeller).
-/

/-- Ianakiev's condition at index `i`: among the four consecutive A083207 terms
`Nat.nth IsZumkeller i, …, Nat.nth IsZumkeller (i + 3)` there is one, `k`, whose half
divisor sum is again a Zumkeller number.  `σ(k)/2` is spelled multiplicatively as
`2 * m = σ(k)`, so no `Nat` division occurs. -/
def IanakievSigmaHalfAt (i : ℕ) : Prop :=
  ∃ j < 4, ∃ m : ℕ,
    2 * m = (∑ d ∈ (Nat.nth IsZumkeller (i + j)).divisors, d) ∧ IsZumkeller m

/-- **Ianakiev's conjecture** (OEIS A083207 comment, Apr 03 2017), OPEN: among any four
consecutive terms of the increasing enumeration of A083207 there is a term `k` whose
half divisor sum `σ(k)/2` is again a Zumkeller number.

The enumeration is `Nat.nth IsZumkeller`, faithful by `infinite_setOf_isZumkeller`,
pinned to the OEIS data at indices `0` and `1` by `nth_isZumkeller_zero` and
`nth_isZumkeller_one`. -/
def IanakievSigmaHalf : Prop :=
  ∀ i : ℕ, IanakievSigmaHalfAt i

/-- Ground-truth check on the two definitions above: the conjecture's condition holds
at `i = 0`, witnessed at `j = 0` by the first term `6` — `σ(6) = 12 = 2 · 6` and `6` is
Zumkeller. -/
theorem ianakievSigmaHalfAt_zero : IanakievSigmaHalfAt 0 := by
  unfold IanakievSigmaHalfAt
  refine ⟨0, by norm_num, 6, ?_, by decide⟩
  rw [Nat.add_zero, nth_isZumkeller_zero]
  decide

/-!
## Prior art: the upstream `Nat.IsPractical` admits `0`

`google-deepmind/formal-conjectures` carries a practical-number definition at
`FormalConjecturesForMathlib/NumberTheory/PracticalNumbers.lean` (enumerated
2026-07-31 from the repository's recursive git tree, 1230 paths), consumed by
`FormalConjectures/ErdosProblems/18.lean`:

```
def subsetSums (A : Set M) : Set M := {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}
def Nat.IsPractical (n : ℕ) : Prop := ∀ m, m ≤ n → m ∈ subsetSums n.divisors
```

It carries **no positivity guard**, so it admits `0`: `Nat.divisors 0 = ∅`, the only
`m ≤ 0` is `0`, and `B = ∅` represents it.  A005153 is a sequence of positive integers
beginning `1, 2, 4, 6, …`, so `0` is not a practical number and the upstream predicate
is satisfied by a non-member.  `Nat.Practical` in `Enumerative.Practical` carries the
`0 < n` conjunct precisely to exclude this.  The defect is benign for the upstream
conjecture statements, which quantify `∃ᶠ … in atTop`; it is recorded here because
this file is where `Nat.Practical` meets an external consumer, and it is a defensible
upstream PR hook.
-/

/-- Faithful local mirror of `Nat.IsPractical` from
`google-deepmind/formal-conjectures`, with `subsetSums` inlined. -/
def upstreamIsPractical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → ∃ B : Finset ℕ, ↑B ⊆ (n.divisors : Set ℕ) ∧ m = ∑ i ∈ B, i

/-- The upstream predicate is satisfied at `0`, which is not a term of A005153. -/
example : upstreamIsPractical 0 := by
  intro m hm
  have hm0 : m = 0 := Nat.le_zero.mp hm
  exact ⟨∅, by simp, by simp [hm0]⟩

/-- The guarded in-tree predicate rejects `0`. -/
example : ¬ (0 : ℕ).Practical := Nat.not_practical_zero

/-- On positive `n` the two definitions agree, so the missing guard is the *only*
difference between `Nat.Practical` and the upstream `Nat.IsPractical`. -/
theorem practical_iff_upstream {n : ℕ} (hn : 0 < n) :
    n.Practical ↔ upstreamIsPractical n := by
  rw [Nat.practical_iff_exists_subset]
  constructor
  · rintro ⟨-, hrep⟩ m hm
    obtain ⟨S, hS_sub, hS_sum⟩ := hrep m hm
    exact ⟨S, by exact_mod_cast hS_sub, hS_sum.symm⟩
  · intro hrep
    refine ⟨hn, fun m hm => ?_⟩
    obtain ⟨B, hB_sub, hB_sum⟩ := hrep m hm
    exact ⟨B, by exact_mod_cast hB_sub, hB_sum.symm⟩

-- Joint instantiation of `practical_iff_upstream` at `n = 6`: the hypothesis `0 < 6`
-- and the left-hand side both hold, and the theorem transports them to the right.
example : upstreamIsPractical 6 := (practical_iff_upstream (by norm_num)).mp (by decide)

/-! ## Axiom audit -/

#print axioms Nat.Practical.isZumkeller
#print axioms Nat.Practical.isZumkeller_iff_two_dvd_sum_divisors
#print axioms infinite_setOf_isZumkeller
#print axioms nth_isZumkeller_zero
#print axioms nth_isZumkeller_one
#print axioms ianakievSigmaHalfAt_zero
#print axioms practical_iff_upstream

-- The conjecture statement itself, printed so a reader can audit the elaborated form
-- rather than the sugar.
#print IanakievSigmaHalfAt
