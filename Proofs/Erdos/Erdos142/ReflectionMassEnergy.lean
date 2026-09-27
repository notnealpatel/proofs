/-
  Erdős Problem #142 — finite reflection mass, multiplicity, and energy.

  This file records the finite counting lemmas behind the *reflection mass* route
  for Erdős Problem #142.  Everything here is exact finite combinatorics about an
  arbitrary finite `A : Finset ℤ` confined to the half-open interval `[0,L)`;
  nothing here is asymptotic, and neither the open estimate `(O)` nor the
  candidate estimate `(C)` of the route record is proved or assumed.

  Conventions (the "ordered representation" convention).

  * A *reflection pair* is an ordered pair `(a,b) ∈ A × A` with `a ≠ b` whose
    reflection target `2*a - b` is *in range*, i.e. `0 ≤ 2*a - b < L`.  Note the
    pair is ordered: `(a,b)` and `(b,a)` are different pairs with different
    targets `2*a-b` and `2*b-a`, and both may be in range.
  * `reflectionMass A L` is the number `M` of such ordered in-range pairs.
  * `reflectionMultiplicity A c` is `ν(c)`, the number of ordered nontrivial
    representations `c = 2*a - b` with `a, b ∈ A` and `a ≠ b`.  It carries no
    range restriction, so `ν` is defined for every `c : ℤ`; the in-range targets
    are exactly the `c ∈ [0,L)`.

  Main results.

  1. `card_le_reflectionMass` (universal mass bound, no AP-free hypothesis):
     for `A ⊆ [0,L)` of size `m`,
     `⌊(m-1)²/4⌋ ≤ M`, stated in `ℕ` as `(m-1)^2 / 4 ≤ M`.
  2. `reflectionMultiplicity_le` (universal fixed-target multiplicity): for every
     `c`, `ν(c) ≤ m - 1` (with `m - 1` truncated at `0`, which is the correct
     value for `m = 0, 1`).
  3. `reflectionMass_eq_sum_multiplicity` and `sum_sq_multiplicity_le` (energy):
     `M = ∑_{c ∈ [0,L)} ν(c)` and `∑_{c ∈ [0,L)} ν(c)² ≤ (m-1) * M`.

  The mass bound is proved by the bipartite crossing argument: an unordered pair
  `x < y` of `A` is *bad* (no in-range orientation at all) exactly when
  `2*x < y` and `L ≤ 2*y - x`; badness forces `2*x < L ≤ 2*y`, so the bad pairs
  are the edges of a bipartite graph between the lower half `2*a < L` and the
  upper half `2*a ≥ L` of `A`, and hence number at most `⌊m²/4⌋`.  Since every
  non-bad unordered pair contributes at least one in-range ordered pair, the
  bound `⌊(m-1)²/4⌋ = C(m,2) - ⌊m²/4⌋` follows.

  Boundary behaviour.  No hypothesis is imposed on `A` beyond `0 ≤ a < L` on its
  elements; in particular `A = ∅`, `m ≤ 1`, `L ≤ 0` and `L = 1` are all allowed
  and all statements remain true (see the examples at the end of the file).  The
  lemmas are stated at the weakest hypotheses that the arguments use, and none of
  them assumes `m > N`, `M > 0`, or arithmetic-progression-freeness; those
  conditions belong to the downstream use of the counts, not to the counts.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-! ## Ordered in-range reflection pairs, mass, and multiplicity -/

/-- The ordered nontrivial in-range reflection pairs of `A` inside `[0,L)`: the
pairs `(a,b) ∈ A × A` with `a ≠ b` and `0 ≤ 2*a - b < L`. -/
def reflectionPairs (A : Finset ℤ) (L : ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ 0 ≤ 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 < L)

/-- The reflection mass `M` of `A` inside `[0,L)`: the number of ordered
nontrivial in-range reflection pairs of `A`. -/
def reflectionMass (A : Finset ℤ) (L : ℤ) : ℕ := (reflectionPairs A L).card

/-- The fixed-target reflection multiplicity `ν(c)`: the number of ordered
nontrivial representations `c = 2*a - b` with `a, b ∈ A` and `a ≠ b`. -/
def reflectionMultiplicity (A : Finset ℤ) (c : ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ 2 * p.1 - p.2 = c)).card

/-- Membership in the set of in-range reflection pairs. -/
theorem mem_reflectionPairs {A : Finset ℤ} {L : ℤ} {p : ℤ × ℤ} :
    p ∈ reflectionPairs A L ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧ 0 ≤ 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 < L := by
  simp [reflectionPairs, and_assoc]

/-- Membership in the set of ordered nontrivial representations of `c`. -/
theorem mem_representationPairs {A : Finset ℤ} {c : ℤ} {p : ℤ × ℤ} :
    p ∈ (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ 2 * p.1 - p.2 = c) ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧ 2 * p.1 - p.2 = c := by
  simp [and_assoc]

/-! ## Fixed-target multiplicity: `ν(c) ≤ m - 1`

After the substitution `b = 2*a - c`, the representations of `c` are the elements
`a ∈ A` with `2*a - c ∈ A` and `a ≠ c`.  If that set were all of `A`, then the
largest element `x` of `A` would satisfy `2*x - c ≤ x`, i.e. `x ≤ c`, while the
smallest element `y` would satisfy `y ≤ 2*y - c`, i.e. `c ≤ y`; hence
`c ≤ y ≤ x ≤ c`, forcing `x = c` and contradicting `x ≠ c`.  So the
representation set misses at least one element of `A`.
-/

/-- The representations of `c` are the centres `a ∈ A` with `2*a - c ∈ A` and
`a ≠ c`.  This is the substitution `b = 2*a - c` made explicit. -/
theorem representationPairs_eq_image_filter (A : Finset ℤ) (c : ℤ) :
    (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ 2 * p.1 - p.2 = c) =
      (A.filter (fun a : ℤ => 2 * a - c ∈ A ∧ a ≠ c)).image (fun a : ℤ => (a, 2 * a - c)) := by
  ext p
  rw [mem_representationPairs, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2, hne, heq⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨h1, by rw [← heq]; convert h2 using 1; ring, fun h => hne (by omega)⟩
    · rw [Prod.mk.injEq]
      exact ⟨rfl, by rw [← heq]; ring⟩
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_filter] at ha
    exact ⟨ha.1, ha.2.1, fun h => ha.2.2 (by omega), by ring⟩

/-- The representation count of `c` equals the number of admissible centres. -/
theorem reflectionMultiplicity_eq_card_filter (A : Finset ℤ) (c : ℤ) :
    reflectionMultiplicity A c = (A.filter (fun a : ℤ => 2 * a - c ∈ A ∧ a ≠ c)).card := by
  rw [reflectionMultiplicity, representationPairs_eq_image_filter,
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1)]

/-- The admissible centres of `c` number at most `|A| - 1`: they cannot be all of
`A`, because the maximal element `x` of `A` would then force `x ≤ c` and the
minimal element `y` would force `c ≤ y`. -/
theorem card_filter_double_le (D : Finset ℤ) (c : ℤ) :
    (D.filter (fun a : ℤ => 2 * a - c ∈ D ∧ a ≠ c)).card ≤ D.card - 1 := by
  rcases D.eq_empty_or_nonempty with hD | hne
  · rw [hD]; simp
  · rw [Nat.le_sub_iff_add_le (Finset.card_pos.2 hne)]
    by_contra hlt
    have hsub : (D.filter (fun a : ℤ => 2 * a - c ∈ D ∧ a ≠ c)) ⊆ D := Finset.filter_subset _ _
    have hle : (D.filter (fun a : ℤ => 2 * a - c ∈ D ∧ a ≠ c)).card ≤ D.card :=
      Finset.card_le_card hsub
    have heq : D.filter (fun a : ℤ => 2 * a - c ∈ D ∧ a ≠ c) = D :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : ∀ a ∈ D, 2 * a - c ∈ D ∧ a ≠ c := by
      intro a ha
      have : a ∈ D.filter (fun a : ℤ => 2 * a - c ∈ D ∧ a ≠ c) := by rw [heq]; exact ha
      exact (Finset.mem_filter.1 this).2
    obtain ⟨hdbl, hne'⟩ := hmem (D.max' hne) (Finset.max'_mem D hne)
    have hxle : 2 * (D.max' hne) - c ≤ D.max' hne := Finset.le_max' D _ hdbl
    obtain ⟨hdbl₂, _⟩ := hmem (D.min' hne) (Finset.min'_mem D hne)
    have hyle : D.min' hne ≤ 2 * (D.min' hne) - c := Finset.min'_le D _ hdbl₂
    have hyx : D.min' hne ≤ D.max' hne := Finset.min'_le D _ (Finset.max'_mem D hne)
    exact hne' (by omega)

/-- **Universal fixed-target multiplicity bound.**  For every `A : Finset ℤ` and
every target `c : ℤ`, the number of ordered nontrivial representations
`c = 2*a - b` with `a, b ∈ A` is at most `|A| - 1`.  No range or AP-free
hypothesis is needed.  The statement uses truncated subtraction, so it also
covers `|A| = 0` (where `ν(c) = 0 ≤ 0`) and `|A| = 1` (where `ν(c) = 0 ≤ 0`). -/
theorem reflectionMultiplicity_le (A : Finset ℤ) (c : ℤ) :
    reflectionMultiplicity A c ≤ A.card - 1 := by
  rw [reflectionMultiplicity_eq_card_filter]
  exact card_filter_double_le A c

/-! ## The universal mass bound

Write `A = S ⊔ T` with `S = {a ∈ A : 2*a < L}` the lower half and
`T = {a ∈ A : L ≤ 2*a}` the upper half.  An unordered pair `x < y` of `A` has no
in-range orientation at all (it is *bad*) exactly when `2*x < y` and
`L ≤ 2*y - x`.  Badness gives `2*x < y < L`, so `x ∈ S`, and gives
`L ≤ 2*y - x ≤ 2*y`, so `y ∈ T`: the bad pairs form a bipartite graph across
`(S,T)`, whence at most `|S| * |T| ≤ ⌊m²/4⌋` of them.  Every other unordered
pair `x < y` contributes at least one in-range ordered pair — `(x,y)` if
`2*x ≥ y`, and `(y,x)` otherwise, the latter exactly when `2*x < y` and
`2*y - x < L`.  Hence `M ≥ C(m,2) - ⌊m²/4⌋ = ⌊(m-1)²/4⌋`. -/

/-- The pairs `x < y` of `A`, one representative per unordered pair. -/
def smallerPairs (A : Finset ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 < p.2)

/-- The pairs `x < y` of `A` whose smaller-first orientation `(x,y)` is already
in range, i.e. `0 ≤ 2*x - y`.  For `x < y` the companion range condition
`2*x - y < L` is then automatic from `x < y < L`. -/
def smallerInRange (A : Finset ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 < p.2 ∧ 0 ≤ 2 * p.1 - p.2)

/-- The pairs `x < y` of `A` whose *flipped* orientation `(y,x)` is in range:
`2*x < y` (so the smaller-first target `2*x - y` is negative) together with
`2*y - x < L`. -/
def smallerFlipped (A : Finset ℤ) (L : ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 < p.2 ∧ 2 * p.1 - p.2 < 0 ∧ 2 * p.2 - p.1 < L)

/-- The *bad* pairs `x < y` of `A` inside `[0,L)`: neither orientation is in
range, i.e. `2*x - y < 0` and `L ≤ 2*y - x`. -/
def badPairs (A : Finset ℤ) (L : ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 < p.2 ∧ 2 * p.1 - p.2 < 0 ∧ L ≤ 2 * p.2 - p.1)

/-- The lower half of `A` relative to `[0,L)`: the elements `a` with `2*a < L`. -/
def lowerHalf (A : Finset ℤ) (L : ℤ) : Finset ℤ := A.filter (fun a : ℤ => 2 * a < L)

/-- The upper half of `A` relative to `[0,L)`: the elements `a` with `L ≤ 2*a`. -/
def upperHalf (A : Finset ℤ) (L : ℤ) : Finset ℤ := A.filter (fun a : ℤ => ¬ 2 * a < L)

/-- The number of pairs `x < y` in `A` is `C(|A|,2)`. -/
theorem card_smallerPairs (A : Finset ℤ) :
    (smallerPairs A).card = A.card * (A.card - 1) / 2 := by
  rw [smallerPairs, Finset.card_product_filter_lt, Nat.choose_two_right]

/-- Every pair `x < y` of `A` is either in range in its own orientation, in range
after flipping, or bad.  These three cases are the arithmetic trichotomy on
`0 ≤ 2*x - y` and on `2*y - x < L`. -/
theorem smallerPairs_eq_union (A : Finset ℤ) (L : ℤ) :
    smallerPairs A = (smallerInRange A ∪ smallerFlipped A L) ∪ badPairs A L := by
  ext p
  simp only [smallerPairs, smallerInRange, smallerFlipped, badPairs, Finset.mem_union,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp, hlt⟩
    by_cases h1 : 0 ≤ 2 * p.1 - p.2
    · exact Or.inl (Or.inl ⟨hp, hlt, h1⟩)
    · by_cases h2 : 2 * p.2 - p.1 < L
      · exact Or.inl (Or.inr ⟨hp, hlt, by omega, h2⟩)
      · exact Or.inr ⟨hp, hlt, by omega, by omega⟩
  · rintro (⟨⟨hp, hlt, _⟩ | ⟨hp, hlt, _, _⟩⟩ | ⟨hp, hlt, _, _⟩) <;> exact ⟨hp, hlt⟩

/-- The two in-range cases are mutually exclusive. -/
theorem disjoint_smallerInRange_smallerFlipped (A : Finset ℤ) (L : ℤ) :
    Disjoint (smallerInRange A) (smallerFlipped A L) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [smallerInRange, smallerFlipped, Finset.mem_filter, Finset.mem_product] at hp1 hp2
  omega

/-- The in-range cases are disjoint from the bad case. -/
theorem disjoint_union_badPairs (A : Finset ℤ) (L : ℤ) :
    Disjoint (smallerInRange A ∪ smallerFlipped A L) (badPairs A L) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [smallerInRange, smallerFlipped, badPairs, Finset.mem_union, Finset.mem_filter,
    Finset.mem_product] at hp1 hp2
  rcases hp1 with h | h <;> omega

/-- The coordinate swap of `ℤ × ℤ` is injective. -/
theorem swap_injective : Function.Injective (fun p : ℤ × ℤ => (p.2, p.1)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.2 h.1

/-- The smaller-first in-range pairs are in-range reflection pairs: for `x < y`
the upper range condition `2*x - y < L` is automatic from `2*x - y < x < L`. -/
theorem smallerInRange_subset_reflectionPairs (A : Finset ℤ) (L : ℤ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) : smallerInRange A ⊆ reflectionPairs A L := by
  intro p hp
  simp only [smallerInRange, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hlt, hnn⟩ := hp
  obtain ⟨-, h1lt⟩ := hA p.1 h1
  simp only [reflectionPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨h1, h2⟩, by omega, hnn, by omega⟩

/-- Flipping the smaller-first pairs with negative target `2*x - y < 0` and
in-range flipped target `2*y - x < L` produces in-range reflection pairs. -/
theorem image_smallerFlipped_subset_reflectionPairs (A : Finset ℤ) (L : ℤ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) :
    (smallerFlipped A L).image (fun p : ℤ × ℤ => (p.2, p.1)) ⊆ reflectionPairs A L := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
  simp only [smallerFlipped, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hlt, hneg, hL⟩ := hp
  obtain ⟨h1nn, -⟩ := hA p.1 h1
  simp only [reflectionPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨h2, h1⟩, by omega, by omega, hL⟩

/-- The two in-range contributions are disjoint subsets of the in-range pairs:
the smaller-first ones have increasing coordinates, the flipped ones decreasing. -/
theorem disjoint_smallerInRange_image_smallerFlipped (A : Finset ℤ) (L : ℤ) :
    Disjoint (smallerInRange A) ((smallerFlipped A L).image (fun p : ℤ × ℤ => (p.2, p.1))) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  simp only [smallerInRange, Finset.mem_filter, Finset.mem_product] at hq1
  obtain ⟨⟨h1, h2⟩, hlt, -⟩ := hq1
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq2
  simp only [smallerFlipped, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨g1, g2⟩, glt, -, -⟩ := hp
  omega

/-- Every bad pair `x < y` of `A` inside `[0,L)` lies in the lower half in its
first coordinate and in the upper half in its second coordinate: `2*x < y < L`
and `L ≤ 2*y - x ≤ 2*y`. -/
theorem badPairs_subset (A : Finset ℤ) (L : ℤ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) :
    badPairs A L ⊆ lowerHalf A L ×ˢ upperHalf A L := by
  intro p hp
  simp only [badPairs, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hlt, hneg, hL⟩ := hp
  obtain ⟨h1nn, h1lt⟩ := hA p.1 h1
  obtain ⟨h2nn, h2lt⟩ := hA p.2 h2
  simp only [lowerHalf, upperHalf, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨h1, by omega⟩, ⟨h2, by omega⟩⟩

/-- The two halves partition `A`. -/
theorem card_lowerHalf_add_card_upperHalf (A : Finset ℤ) (L : ℤ) :
    (lowerHalf A L).card + (upperHalf A L).card = A.card := by
  simpa [lowerHalf, upperHalf] using
    Finset.card_filter_add_card_filter_not (fun a : ℤ => 2 * a < L) (s := A)

/-- The elementary product bound: if `s + t = m` then `s * t ≤ m * m / 4`, because
`4*s*t ≤ (s+t)^2 = m^2`. -/
theorem mul_le_sq_div_four (s t m : ℕ) (h : s + t = m) : s * t ≤ m * m / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  have h4 : ((s : ℤ) + t) = (m : ℤ) := by exact_mod_cast h
  have hkey : ((s : ℤ) * t) * 4 ≤ (m : ℤ) * m := by nlinarith [sq_nonneg ((s : ℤ) - t)]
  exact_mod_cast hkey

/-- `2` divides the product of consecutive integers `m * (m-1)`. -/
theorem two_dvd_mul_pred_self (m : ℕ) : 2 ∣ m * (m - 1) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h]
    exact dvd_zero 2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simpa [Nat.mul_comm] using even_iff_two_dvd.1 (Nat.even_mul_succ_self k)

/-- **Universal reflection mass bound.**  For every finite `A ⊆ [0,L)` of size
`m`, the number of ordered nontrivial in-range reflection pairs is at least
`⌊(m-1)²/4⌋`, stated in `ℕ` as `(m-1)^2 / 4 ≤ M`.  No AP-free hypothesis, no
condition `m > L`, and no condition `M > 0` is used; the hypothesis `0 ≤ a < L`
on the elements of `A` is the only one, and it is needed (both `x < L` for the
smaller-first orientation and `0 ≤ x` for the crossing argument). -/
theorem card_le_reflectionMass (A : Finset ℤ) (L : ℤ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) :
    (A.card - 1) ^ 2 / 4 ≤ reflectionMass A L := by
  rcases Nat.lt_or_ge A.card 2 with hm | hm
  · have hz : A.card - 1 = 0 := by omega
    rw [hz]
    simp
  · set m := A.card with hmdef
    have hcard : (smallerPairs A).card
        = (smallerInRange A).card + (smallerFlipped A L).card + (badPairs A L).card := by
      rw [smallerPairs_eq_union A L,
        Finset.card_union_of_disjoint (disjoint_union_badPairs A L),
        Finset.card_union_of_disjoint (disjoint_smallerInRange_smallerFlipped A L)]
    have hM : (smallerInRange A).card + (smallerFlipped A L).card ≤ reflectionMass A L := by
      have hsub1 := smallerInRange_subset_reflectionPairs A L hA
      have hsub2 := image_smallerFlipped_subset_reflectionPairs A L hA
      have hcard2 : ((smallerFlipped A L).image (fun p : ℤ × ℤ => (p.2, p.1))).card
          = (smallerFlipped A L).card :=
        Finset.card_image_of_injective _ swap_injective
      have hle := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      rw [Finset.card_union_of_disjoint (disjoint_smallerInRange_image_smallerFlipped A L),
        hcard2] at hle
      exact hle
    have hbad : (badPairs A L).card ≤ (lowerHalf A L).card * (upperHalf A L).card := by
      have hle := Finset.card_le_card (badPairs_subset A L hA)
      rwa [Finset.card_product] at hle
    have hsp : (smallerPairs A).card = m * (m - 1) / 2 := by
      rw [card_smallerPairs, ← hmdef]
    have hchain : m * (m - 1) / 2
        ≤ reflectionMass A L + (lowerHalf A L).card * (upperHalf A L).card := by
      omega
    have hsum : (lowerHalf A L).card + (upperHalf A L).card = m := by
      rw [card_lowerHalf_add_card_upperHalf, ← hmdef]
    have hst : (lowerHalf A L).card * (upperHalf A L).card ≤ m * m / 4 :=
      mul_le_sq_div_four _ _ _ hsum
    have hF1 : m * (m - 1) ≤ 2 * (reflectionMass A L
        + (lowerHalf A L).card * (upperHalf A L).card) := by
      have h2 : 2 * (m * (m - 1) / 2) = m * (m - 1) := by
        rw [Nat.mul_comm 2, Nat.div_mul_cancel (two_dvd_mul_pred_self m)]
      omega
    have hkey : ((m - 1 : ℕ) : ℤ) ^ 2 ≤ 4 * (reflectionMass A L : ℤ) + 3 := by
      have hF1z : (m : ℤ) * ((m : ℤ) - 1)
          ≤ 2 * ((reflectionMass A L : ℤ)
            + (((lowerHalf A L).card * (upperHalf A L).card : ℕ) : ℤ)) := by
        have hcast : ((m * (m - 1) : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
          norm_num
        rw [← hcast]
        exact_mod_cast hF1
      have hF2z : 4 * ((((lowerHalf A L).card * (upperHalf A L).card : ℕ)) : ℤ)
          ≤ (m : ℤ) * m := by
        have h4 : (lowerHalf A L).card * (upperHalf A L).card * 4 ≤ m * m := by
          rw [← Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
          exact hst
        have h4z : (((lowerHalf A L).card * (upperHalf A L).card : ℕ) : ℤ) * 4
            ≤ (m : ℤ) * m := by
          exact_mod_cast h4
        linarith
      have hcast1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 :=
        Nat.cast_sub (by omega : 1 ≤ m)
      rw [hcast1]
      nlinarith [hF1z, hF2z]
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 4)]
    norm_num
    exact_mod_cast hkey


/-! ## The energy layer

The mass is the sum of the target multiplicities over the exact target set
`[0,L)`, and the pointwise multiplicity bound `ν(c) ≤ m - 1` turns that into the
second-moment (energy) bound `∑_{c ∈ [0,L)} ν(c)² ≤ (m-1) * M`.  Both statements
are universal: no range hypothesis on `A` is used beyond the target set `[0,L)`
itself, and the bound holds with `m - 1` truncated for `m = 0, 1`. -/

/-- For an in-range target `c ∈ [0,L)`, the reflection pairs with target `c` are
exactly the ordered nontrivial representations of `c`; the range conditions of
`reflectionPairs` are then implied by `c ∈ [0,L)`. -/
theorem filter_reflectionPairs_eq (A : Finset ℤ) (L : ℤ) {c : ℤ}
    (hc : c ∈ Finset.Ico 0 L) :
    (reflectionPairs A L).filter (fun p : ℤ × ℤ => 2 * p.1 - p.2 = c) =
      (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2 ∧ 2 * p.1 - p.2 = c) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, mem_reflectionPairs]
  constructor
  · rintro ⟨⟨h1, h2, hne, -, -⟩, heq⟩
    exact ⟨⟨h1, h2⟩, hne, heq⟩
  · rintro ⟨⟨h1, h2⟩, hne, heq⟩
    obtain ⟨h0, hL⟩ := Finset.mem_Ico.1 hc
    exact ⟨⟨h1, h2, hne, by omega, by omega⟩, heq⟩

/-- **Mass identity.**  The reflection mass is the sum of the target
multiplicities over the exact finite target set `[0,L)`: `M = ∑_{c ∈ [0,L)} ν(c)`.
No hypothesis on `A` is needed. -/
theorem reflectionMass_eq_sum_multiplicity (A : Finset ℤ) (L : ℤ) :
    reflectionMass A L = ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c := by
  have hmap : Set.MapsTo (fun p : ℤ × ℤ => 2 * p.1 - p.2) ↑(reflectionPairs A L)
      ↑(Finset.Ico (0 : ℤ) L) := by
    intro p hp
    rw [Finset.mem_coe, mem_reflectionPairs] at hp
    exact Finset.mem_Ico.2 ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  rw [reflectionMass,
    Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => 2 * p.1 - p.2) hmap]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [filter_reflectionPairs_eq A L hc]
  rfl

/-- **Energy (second moment) bound.**  With `M` the reflection mass and `ν` the
target multiplicity, `∑_{c ∈ [0,L)} ν(c)² ≤ (m-1) * M`.  The proof is the
pointwise multiplicity bound `ν(c) ≤ m - 1` summed over the target set, using the
mass identity.  No hypothesis on `A` is needed. -/
theorem sum_sq_multiplicity_le (A : Finset ℤ) (L : ℤ) :
    ∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2
      ≤ (A.card - 1) * reflectionMass A L := by
  rw [reflectionMass_eq_sum_multiplicity]
  have hsq : ∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2
      = ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c * reflectionMultiplicity A c :=
    Finset.sum_congr rfl fun c _ => by ring
  have hmono : ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c * reflectionMultiplicity A c
      ≤ ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c * (A.card - 1) :=
    Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (reflectionMultiplicity_le A c)
  have hfactor : ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c * (A.card - 1)
      = (A.card - 1) * ∑ c ∈ Finset.Ico 0 L, reflectionMultiplicity A c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Nat.mul_comm _ _
  rw [hsq]
  exact hmono.trans (le_of_eq hfactor)

/-! ## `ℕ`-indexed mass corollary

Downstream use of the counts is usually phrased for `A ⊆ [0,N)` with `A : Finset ℕ`
and `N : ℕ`; the mass of such an `A` is by definition the mass of its image in `ℤ`,
which is injective and hence cardinality preserving. -/

/-- The `ℕ`-indexed reflection mass: the mass of the image of `A` in `ℤ` inside
`[0,L)`. -/
def reflectionMassNat (A : Finset ℕ) (L : ℕ) : ℕ :=
  reflectionMass (A.image (fun n : ℕ => (n : ℤ))) (L : ℤ)

/-- The `ℕ`-indexed fixed-target multiplicity: the number of ordered nontrivial
representations `c = 2*a - b` with `a, b ∈ A`.  The target `c` is an integer
because `2*a - b` can be negative. -/
def reflectionMultiplicityNat (A : Finset ℕ) (c : ℤ) : ℕ :=
  reflectionMultiplicity (A.image (fun n : ℕ => (n : ℤ))) c

/-- The image of `A : Finset ℕ` in `ℤ` has the same cardinality. -/
theorem card_image_natCast (A : Finset ℕ) :
    (A.image (fun n : ℕ => (n : ℤ))).card = A.card :=
  Finset.card_image_of_injective _ (fun a b h => by simpa using h)

/-- **`ℕ`-indexed universal mass bound.**  For `A ⊆ [0,L)` with `A : Finset ℕ` and
`L : ℕ`, `⌊(|A|-1)²/4⌋ ≤ M`.  The only hypothesis is `a < L` for `a ∈ A`; the
nonnegativity half of the `ℤ` statement is automatic. -/
theorem card_le_reflectionMassNat (A : Finset ℕ) (L : ℕ) (hA : ∀ a ∈ A, a < L) :
    (A.card - 1) ^ 2 / 4 ≤ reflectionMassNat A L := by
  rw [← card_image_natCast A, reflectionMassNat]
  refine card_le_reflectionMass _ _ fun a ha => ?_
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 ha
  exact ⟨Int.natCast_nonneg n, by exact_mod_cast hA n hn⟩

/-- **`ℕ`-indexed fixed-target multiplicity bound**: `ν(c) ≤ |A| - 1`. -/
theorem reflectionMultiplicityNat_le (A : Finset ℕ) (c : ℤ) :
    reflectionMultiplicityNat A c ≤ A.card - 1 := by
  have h := reflectionMultiplicity_le (A.image (fun n : ℕ => (n : ℤ))) c
  rwa [card_image_natCast A] at h

/-- **`ℕ`-indexed mass identity**: `M = ∑_{c ∈ [0,L)} ν(c)` for `A : Finset ℕ`. -/
theorem reflectionMassNat_eq_sum_multiplicity (A : Finset ℕ) (L : ℕ) :
    reflectionMassNat A L = ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ), reflectionMultiplicityNat A c :=
  reflectionMass_eq_sum_multiplicity _ _

/-- **`ℕ`-indexed energy bound**: `∑_{c ∈ [0,L)} ν(c)² ≤ (|A|-1) * M`. -/
theorem sum_sq_multiplicityNat_le (A : Finset ℕ) (L : ℕ) :
    ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ), (reflectionMultiplicityNat A c) ^ 2
      ≤ (A.card - 1) * reflectionMassNat A L := by
  have h := sum_sq_multiplicity_le (A.image (fun n : ℕ => (n : ℤ))) (L : ℤ)
  rwa [card_image_natCast A] at h

/-! ## Ground truth and boundary audit

The examples below pin the definitions at concrete inputs, including the empty set,
`L ≤ 0`, `L = 1`, `m = 0, 1`, `M = 0`, a tight multiplicity case, and a case
where the target multiplicity `ν(c) = m - 1` is attained. -/

/-- `A = {0,1,2}` inside `[0,3)` has exactly the two in-range pairs `(1,0)`
(target `2`) and `(1,2)` (target `0`), so its mass is `2`. -/
example : reflectionMass ({0, 1, 2} : Finset ℤ) 3 = 2 := by decide

/-- At `A = {0,1,2}`, `L = 3` the target multiplicities are `ν(0) = 1` and
`ν(2) = 1`, and `M = ν(0) + ν(2) = 2`. -/
example : reflectionMultiplicity ({0, 1, 2} : Finset ℤ) 0 = 1 ∧
    reflectionMultiplicity ({0, 1, 2} : Finset ℤ) 2 = 1 ∧
    reflectionMass ({0, 1, 2} : Finset ℤ) 3 = 2 := by decide

/-- The mass bound at `A = {0,1,2}`, `L = 3`: `⌊(3-1)²/4⌋ = 1 ≤ M = 2`. -/
example : (({0, 1, 2} : Finset ℤ).card - 1) ^ 2 / 4 ≤ reflectionMass ({0, 1, 2} : Finset ℤ) 3 :=
  card_le_reflectionMass ({0, 1, 2} : Finset ℤ) 3 (by decide)

/-- The empty set: `m = 0`, `M = 0`, and the bound `⌊(0-1)²/4⌋ = 0` holds. -/
example : reflectionMass (∅ : Finset ℤ) 0 = 0 ∧
    ((∅ : Finset ℤ).card - 1) ^ 2 / 4 ≤ reflectionMass (∅ : Finset ℤ) 0 := by decide

/-- The empty set satisfies the mass-bound hypothesis vacuously, and the theorem
applies at it. -/
example : ((∅ : Finset ℤ).card - 1) ^ 2 / 4 ≤ reflectionMass (∅ : Finset ℤ) 0 :=
  card_le_reflectionMass (∅ : Finset ℤ) 0 (by simp)

/-- `L = 0` and `L = 1` with `A = {0}`: `m = 1`, `M = 0`, and the bound
`⌊(1-1)²/4⌋ = 0` holds; this is the degenerate `[0,L)` regime, where no ordered
pair with `0 ≤ 2*a - b < L` can exist. -/
example : reflectionMass ({(0 : ℤ)}) 0 = 0 ∧ reflectionMass ({(0 : ℤ)}) 1 = 0 ∧
    reflectionMass ({(0 : ℤ)}) (-3) = 0 := by decide

/-- Satisfiability of the mass-bound hypothesis at a concrete nonempty `A ⊆ [0,L)`
with `m = 3`, and of the conclusion via the theorem. -/
example : (∀ a ∈ ({0, 1, 2} : Finset ℤ), 0 ≤ a ∧ a < 3) ∧
    (({0, 1, 2} : Finset ℤ).card - 1) ^ 2 / 4 ≤ reflectionMass ({0, 1, 2} : Finset ℤ) 3 :=
  ⟨by decide, card_le_reflectionMass ({0, 1, 2} : Finset ℤ) 3 (by decide)⟩

/-- `M = 0` is attainable with `m ≥ 2`: the pair `{0,3}` inside `[0,4)` is bad,
so `M = 0`, and the bound `⌊(2-1)²/4⌋ = 0` is attained. -/
example : reflectionMass ({0, 3} : Finset ℤ) 4 = 0 ∧ (0 : ℕ) = 0 :=
  ⟨by decide, rfl⟩

/-- The mass bound is attained with equality at `A = {0,2,5}` inside `[0,6)`: the
pairs `{0,5}` and `{2,5}` are bad and `{0,2}` contributes the single in-range pair
`(2,0)` with target `4`, so `M = 3 - 2 = 1 = ⌊(3-1)²/4⌋`. -/
example : reflectionMass ({0, 2, 5} : Finset ℤ) 6 = 1 ∧
    (({0, 2, 5} : Finset ℤ).card - 1) ^ 2 / 4 = 1 :=
  ⟨by decide, by decide⟩

/-- The energy bound holds in the degenerate case `M = 0` (here `A = {0,1}` inside
`[0,2)` has no in-range pair, since `(0,1)` has negative target and `(1,0)` has
target `2 = L`), where it reads `0 ≤ (2-1) * 0 = 0`. -/
example : reflectionMass ({0, 1} : Finset ℤ) 2 = 0 ∧
    (∑ c ∈ Finset.Ico (0 : ℤ) 2, (reflectionMultiplicity ({0, 1} : Finset ℤ) c) ^ 2)
      ≤ (({0, 1} : Finset ℤ).card - 1) * reflectionMass ({0, 1} : Finset ℤ) 2 :=
  ⟨by decide, sum_sq_multiplicity_le _ 2⟩

/-- Tight multiplicity: `A = {1,2,4,8}` has `m = 4` and the three ordered
representations `2*1-2 = 2*2-4 = 2*4-8 = 0`, so `ν(0) = 3 = m - 1`. -/
example : reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 0 = 3 :=
  le_antisymm (reflectionMultiplicity_le _ 0) (by decide)

/-- The multiplicity bound is not vacuous at `c ∉ A` either:
`ν(3) = 1` for `A = {1,2,4,8}` (from `2*2 - 1 = 3`). -/
example : reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 3 = 1 := by decide

/-- Energy bookkeeping at `A = {1,2,4,8}` inside `[0,9)`: `M = 6`, the nonzero
targets are `0, 3, 6, 7` with multiplicities `3, 1, 1, 1`, so the energy is
`9 + 1 + 1 + 1 = 12 ≤ 3 * 6 = 18`. -/
example : reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9 = 6 ∧
    (∑ c ∈ Finset.Ico (0 : ℤ) 9, (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2)
      = 12 := by decide

/-- The energy bound at `A = {1,2,4,8}`, `L = 9`, instantiated through the theorem
rather than by evaluation. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) 9,
      (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2) ≤
    (4 - 1) * reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9 :=
  sum_sq_multiplicity_le _ 9

/-- The mass identity at `A = {1,2,4,8}`, `L = 9`. -/
example : reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9 =
    ∑ c ∈ Finset.Ico (0 : ℤ) 9, reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c :=
  reflectionMass_eq_sum_multiplicity _ 9

/-- The `ℕ`-indexed corollary at a concrete `A ⊆ [0,5)`. -/
example : (({0, 1, 2, 3} : Finset ℕ).card - 1) ^ 2 / 4 ≤ reflectionMassNat ({0, 1, 2, 3} : Finset ℕ) 5 :=
  card_le_reflectionMassNat ({0, 1, 2, 3} : Finset ℕ) 5 (by decide)

/-- The `ℕ`-indexed mass at `A = {0,1,2,3}` inside `[0,5)` is `6` (the six
in-range ordered pairs are `(1,0),(1,2),(2,0),(2,1),(2,3),(3,2)`), the target
multiplicities are `ν(0)=ν(1)=ν(2)=ν(3)=1` and `ν(4)=2`, and the energy is
`1+1+1+1+4 = 8 ≤ 3 * 6`. -/
example : reflectionMassNat ({0, 1, 2, 3} : Finset ℕ) 5 = 6 ∧
    reflectionMultiplicityNat ({0, 1, 2, 3} : Finset ℕ) 4 = 2 ∧
    (∑ c ∈ Finset.Ico (0 : ℤ) (5 : ℤ),
      (reflectionMultiplicityNat ({0, 1, 2, 3} : Finset ℕ) c) ^ 2) = 8 := by decide

/-- The `ℕ`-indexed mass identity at `A = {0,1,2,3}` inside `[0,5)`. -/
example : reflectionMassNat ({0, 1, 2, 3} : Finset ℕ) 5 =
    ∑ c ∈ Finset.Ico (0 : ℤ) (5 : ℤ), reflectionMultiplicityNat ({0, 1, 2, 3} : Finset ℕ) c :=
  reflectionMassNat_eq_sum_multiplicity _ 5

/-- The `ℕ`-indexed energy bound at `A = {0,1,2,3}` inside `[0,5)`. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) (5 : ℤ),
      (reflectionMultiplicityNat ({0, 1, 2, 3} : Finset ℕ) c) ^ 2) ≤
    (({0, 1, 2, 3} : Finset ℕ).card - 1) * reflectionMassNat ({0, 1, 2, 3} : Finset ℕ) 5 :=
  sum_sq_multiplicityNat_le _ 5

end Erdos142
