/-
  BilinearComplexity/Capset — cap sets in `(ZMod 3)^n` through Mathlib's
  `ThreeAPFree`: the characteristic-3 "line" bridge and the extremal
  cap-set numbers (OEIS A090245).

  A cap set is a subset of `(ZMod 3)^n` containing no affine line. In
  characteristic 3 a line through pairwise distinct points `a, b, c` is
  exactly a zero-sum triple `a + b + c = 0`, and a 3-term arithmetic
  progression `a + c = b + b` is the same equation (`b + b = -b`); the
  degenerate triples `a = b = c` satisfy both sides trivially, so the
  distinctness bookkeeping is where the content lives. This file proves
  that bridge and instantiates the extremal question:

    · `add_add_self_eq_zero`   — 3-torsion in `ZMod 3`-modules.
    · `eq_of_add_self_add_eq_zero` — zero-sum triples with two equal
      entries are fully degenerate.
    · `add_eq_add_self_iff_add_add_eq_zero` — pointwise AP ↔ zero-sum.
    · `threeAPFree_iff_forall_add_add_eq_zero_imp` — set-level bridge,
      "every zero-sum triple is degenerate" form (no distinctness).
    · `threeAPFree_iff_no_line` — set-level bridge, "no pairwise
      distinct zero-sum triple" (cap set) form.
    · `capsetNumber n` — `addRothNumber` of the whole space, i.e. the
      maximum size of a 3AP-free subset of `(ZMod 3)^n` (A090245),
      with the order API `card_le_capsetNumber`,
      `exists_threeAPFree_card_capsetNumber`, `capsetNumber_le_pow`.
    · Ground values against A090245 = 1, 2, 4, 9, 20, 45, 112:
      `capsetNumber_zero/one/two` (exhaustive, kernel `decide`) and
      witness lower bounds `nine_le_capsetNumber_three`,
      `twenty_le_capsetNumber_four` (`capWitness3`, `capWitness4`).

  Verified against `oeis show A090245`: exact values for n = 0, 1, 2;
  witness lower bounds for n = 3, 4. The n = 3, 4 upper bounds (and
  everything from n = 5 on) are beyond cheap kernel search and are not
  claimed here.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false

namespace BilinearComplexity

/-! ## 1. The characteristic-3 bridge -/

section Char3Bridge

-- `AddCommGroup G` follows from `Module (ZMod 3) G` over an `AddCommMonoid`
-- (`Module.addCommMonoidToAddCommGroup`); stated explicitly to avoid a
-- neg-diamond with downstream callers that also assume `AddCommGroup`.
variable {G : Type*} [AddCommGroup G] [Module (ZMod 3) G]

/-- In a module over `ZMod 3` every element is 3-torsion: `x + x + x = 0`. -/
theorem add_add_self_eq_zero (x : G) : x + x + x = 0 := by
  have h3 : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  calc x + x + x = ((1 : ZMod 3) + 1 + 1) • x := by rw [add_smul, add_smul, one_smul]
    _ = (0 : ZMod 3) • x := by rw [h3]
    _ = 0 := zero_smul (ZMod 3) x

/-- Zero-sum triples with two equal entries are fully degenerate in
characteristic 3: if `a + a + c = 0` then `c = a`. -/
theorem eq_of_add_self_add_eq_zero {a c : G} (h : a + a + c = 0) : c = a :=
  add_left_cancel (h.trans (add_add_self_eq_zero a).symm)

/-- Pointwise characteristic-3 bridge: the 3-AP equation `a + c = b + b` and
the line (zero-sum) equation `a + b + c = 0` coincide, with no distinctness
hypothesis — both are satisfied by every degenerate triple `a = b = c`. -/
theorem add_eq_add_self_iff_add_add_eq_zero (a b c : G) :
    a + c = b + b ↔ a + b + c = 0 := by
  constructor
  · intro h
    calc a + b + c = a + c + b := add_right_comm a b c
      _ = b + b + b := by rw [h]
      _ = 0 := add_add_self_eq_zero b
  · intro h
    have hb : b + b + b = 0 := add_add_self_eq_zero b
    have hcb : a + c + b = b + b + b := by rw [add_right_comm, h, hb]
    exact add_right_cancel hcb

/-- Set-level characteristic-3 bridge, implication form: a set in a `ZMod 3`-
module is 3AP-free iff each of its zero-sum triples is degenerate. -/
theorem threeAPFree_iff_forall_add_add_eq_zero_imp {s : Set G} :
    ThreeAPFree s ↔
      ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a + b + c = 0 → a = b := by
  constructor
  · intro hs a ha b hb c hc h
    exact hs ha hb hc ((add_eq_add_self_iff_add_add_eq_zero a b c).mpr h)
  · intro hs a ha b hb c hc h
    exact hs ha hb hc ((add_eq_add_self_iff_add_add_eq_zero a b c).mp h)

/-- **Characteristic-3 bridge.** A set in a `ZMod 3`-module is 3AP-free iff it
is a cap set: it contains no line, i.e. no three *pairwise distinct* elements
summing to `0`. Distinctness is load-bearing: every degenerate triple
`a = b = c` sums to zero (`add_add_self_eq_zero`), so without it the right-hand
side would be falsified by any nonempty set. -/
theorem threeAPFree_iff_no_line {s : Set G} :
    ThreeAPFree s ↔
      ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s →
        a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0 := by
  rw [threeAPFree_iff_forall_add_add_eq_zero_imp]
  constructor
  · intro hs a ha b hb c hc hab hac hbc habc
    exact hab (hs ha hb hc habc)
  · intro hs a ha b hb c hc h
    by_contra hab
    have hac : a ≠ c := by
      rintro rfl
      rw [add_right_comm] at h
      exact hab (eq_of_add_self_add_eq_zero h).symm
    have hbc : b ≠ c := by
      rintro rfl
      have hcancel : a + b + b = b + b + b := h.trans (add_add_self_eq_zero b).symm
      exact hab (add_right_cancel (add_right_cancel hcancel))
    exact hs ha hb hc hab hac hbc h

end Char3Bridge

/-- Satisfiability of the degenerate side: `{0}` is 3AP-free even though its
(degenerate) triple `0, 0, 0` sums to zero. A "no zero-sum triple" bridge
without pairwise distinctness would already be falsified here. -/
example : ThreeAPFree ({0} : Set (Fin 1 → ZMod 3)) ∧
    ∃ a ∈ ({0} : Set (Fin 1 → ZMod 3)), a + a + a = 0 :=
  ⟨threeAPFree_singleton 0, 0, rfl, add_add_self_eq_zero 0⟩

/-- Satisfiability of the nondegenerate side: dimension-1 space is itself a
line — `![0], ![1], ![2]` are pairwise distinct and sum to zero — so it is not
3AP-free, via the backward direction of `threeAPFree_iff_no_line`. -/
example : ¬ ThreeAPFree (Set.univ : Set (Fin 1 → ZMod 3)) := by
  rw [threeAPFree_iff_no_line]
  intro hs
  exact hs (Set.mem_univ ![0]) (Set.mem_univ ![1]) (Set.mem_univ ![2])
    (by decide) (by decide) (by decide) (by decide)

/-- Satisfiability: a concrete nonempty, non-singleton 3AP-free set, decided
by the kernel through Mathlib's `ThreeAPFree` finset instance. -/
example : ThreeAPFree (↑({![0], ![1]} : Finset (Fin 1 → ZMod 3)) :
    Set (Fin 1 → ZMod 3)) := by decide

/-! ## 2. Cap-set numbers (OEIS A090245) -/

section CapsetNumber

/-- `capsetNumber n` is the maximum size of a 3AP-free subset of `(ZMod 3)^n` —
equivalently (`threeAPFree_iff_no_line`) the maximum size of a cap set, the
largest number of SET cards with no SET among `n`-attribute cards. This is
Mathlib's additive Roth number of the whole space. OEIS A090245:
`1, 2, 4, 9, 20, 45, 112, ...`. -/
def capsetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- `capsetNumber` is definitionally the additive Roth number of the full
space; recorded for downstream rewriting. -/
theorem capsetNumber_def (n : ℕ) :
    capsetNumber n = addRothNumber (Finset.univ : Finset (Fin n → ZMod 3)) :=
  rfl

/-- Any 3AP-free finset of `(ZMod 3)^n` has size at most `capsetNumber n`. -/
theorem card_le_capsetNumber {n : ℕ} {s : Finset (Fin n → ZMod 3)}
    (hs : ThreeAPFree (s : Set (Fin n → ZMod 3))) : s.card ≤ capsetNumber n :=
  hs.le_addRothNumber (Finset.subset_univ s)

/-- `capsetNumber n` is attained: some 3AP-free finset has exactly this size
(the empty set is 3AP-free, so the maximum is over a nonempty family). -/
theorem exists_threeAPFree_card_capsetNumber (n : ℕ) :
    ∃ s : Finset (Fin n → ZMod 3),
      s.card = capsetNumber n ∧ ThreeAPFree (s : Set (Fin n → ZMod 3)) := by
  obtain ⟨t, -, htcard, ht⟩ :=
    addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  exact ⟨t, htcard, ht⟩

/-- Trivial upper bound: a cap set lives inside the `3 ^ n`-point space. -/
theorem capsetNumber_le_pow (n : ℕ) : capsetNumber n ≤ 3 ^ n :=
  calc capsetNumber n ≤ (Finset.univ : Finset (Fin n → ZMod 3)).card :=
        addRothNumber_le _
    _ = 3 ^ n := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-! ### Ground values, checked against `oeis show A090245` -/

/-- A090245(0) = 1: the one-point space `(ZMod 3)^0` is itself a cap.
Exhaustive kernel decision. -/
theorem capsetNumber_zero : capsetNumber 0 = 1 := by decide

/-- A090245(1) = 2: a line is 3 points, so a cap in `(ZMod 3)^1` has at most 2.
Exhaustive kernel decision over all 8 subsets. -/
theorem capsetNumber_one : capsetNumber 1 = 2 := by decide

set_option maxRecDepth 8000 in
/-- A090245(2) = 4: exhaustive kernel decision over all 512 subsets of the
9-point plane (`maxRecDepth` raised for the powerset recursion). -/
theorem capsetNumber_two : capsetNumber 2 = 4 := by decide

/-- The graph `{(x, y, x² + y²) : x y : ZMod 3}` in `(ZMod 3)^3`: a cap of
size `9`, witnessing the A090245(3) lower bound (`nine_le_capsetNumber_three`).
Any zero-sum triple of graph points has zero-sum `x`- and `y`-coordinates, and
in `ZMod 3` a zero-sum triple of squares `x²` is `0` only when the three `x`
agree; distinct graph points force `Σ(x² + y²) ∈ {1, 2}`. -/
def capWitness3 : Finset (Fin 3 → ZMod 3) :=
  {![0, 0, 0], ![0, 1, 1], ![0, 2, 1],
   ![1, 0, 1], ![1, 1, 2], ![1, 2, 2],
   ![2, 0, 1], ![2, 1, 2], ![2, 2, 2]}

/-- Ground check: `capWitness3` has the claimed size. -/
example : capWitness3.card = 9 := by decide

/-- Ground check: `capWitness3` is 3AP-free (kernel-decided, all 9³ triples). -/
example : ThreeAPFree (capWitness3 : Set (Fin 3 → ZMod 3)) := by decide

/-- A090245(3) = 9, lower bound: the explicit cap `capWitness3`. The matching
upper bound needs an exhaustive search over `C(27, 10) ≈ 8.4·10⁶` subsets and
is not attempted here. -/
theorem nine_le_capsetNumber_three : 9 ≤ capsetNumber 3 := by
  have hfree : ThreeAPFree (capWitness3 : Set (Fin 3 → ZMod 3)) := by decide
  have hcard : capWitness3.card = 9 := by decide
  calc 9 = capWitness3.card := hcard.symm
    _ ≤ capsetNumber 3 := card_le_capsetNumber hfree

/-- A 20-point cap in `(ZMod 3)^4`, witnessing the A090245(4) lower bound
(`twenty_le_capsetNumber_four`). Found by randomized greedy search with local
perturbation; certified below by kernel `decide`, so its provenance carries no
trust weight. -/
def capWitness4 : Finset (Fin 4 → ZMod 3) :=
  {![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 0, 2],
   ![0, 2, 0, 1], ![0, 2, 1, 1], ![1, 0, 1, 1], ![1, 0, 1, 2],
   ![1, 1, 0, 0], ![1, 1, 0, 2], ![1, 2, 0, 2], ![1, 2, 1, 2],
   ![2, 0, 0, 1], ![2, 0, 2, 1], ![2, 1, 1, 2], ![2, 1, 2, 2],
   ![2, 2, 0, 1], ![2, 2, 0, 2], ![2, 2, 1, 1], ![2, 2, 1, 2]}

/-- Ground check: `capWitness4` has the claimed size. -/
example : capWitness4.card = 20 := by decide

/-- Ground check: `capWitness4` is 3AP-free (kernel-decided, all 20³ triples). -/
example : ThreeAPFree (capWitness4 : Set (Fin 4 → ZMod 3)) := by decide

/-- A090245(4) = 20, lower bound: the explicit cap `capWitness4`. The matching
upper bound (and all of `n ≥ 5`, where A090245 continues `45, 112`) is beyond
cheap kernel search and is not claimed here. -/
theorem twenty_le_capsetNumber_four : 20 ≤ capsetNumber 4 := by
  have hfree : ThreeAPFree (capWitness4 : Set (Fin 4 → ZMod 3)) := by decide
  have hcard : capWitness4.card = 20 := by decide
  calc 20 = capWitness4.card := hcard.symm
    _ ≤ capsetNumber 4 := card_le_capsetNumber hfree

end CapsetNumber

end BilinearComplexity
