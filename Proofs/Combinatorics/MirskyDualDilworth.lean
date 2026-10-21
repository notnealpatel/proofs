/-
# Mirsky's theorem (the dual of Dilworth's theorem) for finite posets

## Source

L. Mirsky, "A dual of Dilworth's decomposition theorem",
Amer. Math. Monthly 78 (1971), 876–877.  The theorem is the main
(and only) result of that note.

## Informal statement (as recorded in the target spec)

> In a finite poset, if every chain has at most k elements, then the poset
> is a union of k antichains. Equivalently, the maximum chain size equals
> the minimum number of antichains needed to cover the poset.

Recorded 2026-10-21.

## Formal rendering

The finite poset is a `Finset s` in an ambient `PartialOrder α`.  A
decomposition of `s` into `k` antichains is encoded as a labelling
`f : α → ℕ` with `f x < k` for every `x ∈ s`, each of whose level sets
`{x ∈ s | f x = i}` is an antichain; the level sets partition `s` into at
most `k` (possibly empty) antichains.  An `ℕ`-valued labelling is used
instead of `α → Fin k` because for `k = 0`, `s = ∅` and nonempty `α` there
is no function `α → Fin 0`, although the empty poset is a union of zero
antichains.

* `exists_antichain_labelling_of_chain_card_le` — Mirsky's direction:
  chains of size `≤ k` force a partition into `k` antichains.
* `mirsky` — the "equivalently" form: every chain has at most `k`
  elements iff `s` is a union of `k` antichains; i.e. the maximum chain
  size equals the minimum number of covering antichains.

## Mathlib absence check

`leandoc` searches ("union of antichains chain height", "partition into
antichains height", "antichain cover chainHeight", "Mirsky") and a grep
for `Dilworth`/`Mirsky` over Mathlib found no statement of the theorem;
only the ingredients `Order.height`, `Set.chainHeight` exist.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MirskyDualDilworth

open Finset

variable {α : Type*} [PartialOrder α]

/-- Rank function for Mirsky's theorem: if every chain contained in the finite
set `s` has at most `k` elements, then there is a labelling `r : α → ℕ` with
`r x < k` on `s` that is strictly monotone on `s`
(`r x` is one less than the largest size of a chain in `s` lying below `x`). -/
theorem exists_strictMonoOn_rank_lt (s : Finset α) (k : ℕ)
    (h : ∀ t ⊆ s, IsChain (· ≤ ·) (t : Set α) → #t ≤ k) :
    ∃ r : α → ℕ, (∀ x ∈ s, r x < k) ∧ ∀ x ∈ s, ∀ y ∈ s, x < y → r x < r y := by
  classical
  let C : α → Finset (Finset α) := fun x =>
    s.powerset.filter (fun t => IsChain (· ≤ ·) (t : Set α) ∧ ∀ y ∈ t, y ≤ x)
  let H : α → ℕ := fun x => (C x).sup Finset.card
  have hmem : ∀ x ∈ s, {x} ∈ C x := by
    intro x hx
    simp only [C, mem_filter, mem_powerset, singleton_subset_iff, coe_singleton,
      IsChain.singleton, mem_singleton, forall_eq, le_refl, and_self]
    exact ⟨hx, trivial⟩
  have hpos : ∀ x ∈ s, 1 ≤ H x := fun x hx => by
    have hsup : #({x} : Finset α) ≤ H x := Finset.le_sup (f := Finset.card) (hmem x hx)
    rwa [card_singleton] at hsup
  have hle : ∀ x, H x ≤ k := fun x => by
    refine Finset.sup_le fun t ht => ?_
    simp only [C, mem_filter, mem_powerset] at ht
    exact h t ht.1 ht.2.1
  have hlt : ∀ x ∈ s, ∀ y ∈ s, x < y → H x < H y := by
    intro x hx y hy hxy
    obtain ⟨t, ht, htH⟩ := Finset.exists_mem_eq_sup (C x) ⟨_, hmem x hx⟩ Finset.card
    simp only [C, mem_filter, mem_powerset] at ht
    obtain ⟨hts, htc, htx⟩ := ht
    have hyt : y ∉ t := fun hyt => (htx y hyt).not_gt hxy
    have hins : insert y t ∈ C y := by
      simp only [C, mem_filter, mem_powerset, coe_insert]
      refine ⟨insert_subset hy hts, ?_, ?_⟩
      · refine htc.insert fun b hb _ => Or.inr ((htx b hb).trans hxy.le)
      · intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact le_rfl
        · exact (htx z hz).trans hxy.le
    have hcard : #(insert y t) = #t + 1 := card_insert_of_notMem hyt
    calc H x = #t := htH
      _ < #(insert y t) := by omega
      _ ≤ H y := Finset.le_sup (f := Finset.card) hins
  refine ⟨fun x => H x - 1, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · show H x - 1 < k
    have := hpos x hx
    have := hle x
    omega
  · show H x - 1 < H y - 1
    have := hpos x hx
    have := hlt x hx y hy hxy
    omega

/-- **Mirsky's theorem** (L. Mirsky, 1971).  If every chain contained in the
finite set `s` of a partially ordered type has at most `k` elements, then `s` is
a union of `k` antichains: there is a labelling `f : α → ℕ` with `f x < k` for
all `x ∈ s` such that every level set `{x ∈ s | f x = i}` is an antichain. -/
theorem exists_antichain_labelling_of_chain_card_le (s : Finset α) (k : ℕ)
    (h : ∀ t ⊆ s, IsChain (· ≤ ·) (t : Set α) → #t ≤ k) :
    ∃ f : α → ℕ, (∀ x ∈ s, f x < k) ∧
      ∀ i, IsAntichain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α) := by
  obtain ⟨r, hrk, hrmono⟩ := exists_strictMonoOn_rank_lt s k h
  refine ⟨r, hrk, fun i x hx y hy hxy hle => ?_⟩
  obtain ⟨hxs, hxi⟩ := hx
  obtain ⟨hys, hyi⟩ := hy
  have hlt : r x < r y := hrmono x hxs y hys (lt_of_le_of_ne hle hxy)
  omega

/-- The easy converse: if `s` is a union of `k` antichains (given as the level
sets of a labelling `f` with values `< k` on `s`), then every chain in `s` has at
most `k` elements, since a chain meets each antichain in at most one point. -/
theorem chain_card_le_of_antichain_labelling (s : Finset α) (k : ℕ) (f : α → ℕ)
    (hfk : ∀ x ∈ s, f x < k)
    (hf : ∀ i, IsAntichain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α)) :
    ∀ t ⊆ s, IsChain (· ≤ ·) (t : Set α) → #t ≤ k := by
  intro t hts htc
  have hinj : Set.InjOn f (t : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have hxs : x ∈ s := hts hx
    have hys : y ∈ s := hts hy
    rcases htc hx hy hne with hle | hle
    · exact hf (f x) ⟨hxs, rfl⟩ ⟨hys, hxy.symm⟩ hne hle
    · exact hf (f x) ⟨hys, hxy.symm⟩ ⟨hxs, rfl⟩ (Ne.symm hne) hle
  have hmaps : Set.MapsTo f (t : Set α) (range k : Set ℕ) := fun x hx => by
    simpa using hfk x (hts hx)
  simpa using card_le_card_of_injOn f hmaps hinj

/-- **Mirsky's theorem, "equivalently" form.**  For a finite set `s` in a
partially ordered type and `k : ℕ`, every chain contained in `s` has at most `k`
elements if and only if `s` is a union of `k` antichains (the level sets of a
labelling `f` with values `< k` on `s`).  Hence the maximum size of a chain in
`s` equals the minimum number of antichains covering `s`. -/
theorem mirsky (s : Finset α) (k : ℕ) :
    (∀ t ⊆ s, IsChain (· ≤ ·) (t : Set α) → #t ≤ k) ↔
      ∃ f : α → ℕ, (∀ x ∈ s, f x < k) ∧
        ∀ i, IsAntichain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α) :=
  ⟨exists_antichain_labelling_of_chain_card_le s k,
    fun ⟨f, hfk, hf⟩ => chain_card_le_of_antichain_labelling s k f hfk hf⟩

/-! ## Non-vacuity checks -/

/-- The chain `{0, 1, 2}` in `ℕ` has a chain of size `3`, so it is not a union of
`2` antichains: the hypothesis of Mirsky's theorem is not vacuous. -/
example : ¬ ∀ t ⊆ ({0, 1, 2} : Finset ℕ), IsChain (· ≤ ·) (t : Set ℕ) → #t ≤ 2 := by
  intro h
  have h3 := h {0, 1, 2} subset_rfl (isChain_of_trichotomous _)
  simp at h3

/-- The three-element chain `{0, 1, 2}` in `ℕ` is a union of `3` antichains
(singletons, labelled by the identity). -/
example : ∃ f : ℕ → ℕ, (∀ x ∈ ({0, 1, 2} : Finset ℕ), f x < 3) ∧
    ∀ i, IsAntichain (· ≤ ·) ({x | x ∈ ({0, 1, 2} : Finset ℕ) ∧ f x = i} : Set ℕ) := by
  refine ⟨id, by decide, fun i x hx y hy hxy _ => hxy ?_⟩
  exact hx.2.trans hy.2.symm

end Candidates.MirskyDualDilworth
