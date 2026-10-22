/-
# Dilworth's chain decomposition theorem for finite posets

R. P. Dilworth, *A decomposition theorem for partially ordered sets*,
Ann. of Math. (2) 51 (1950), 161–166, Theorem 1.1 (finite case):
a finite poset of width `w` can be partitioned into `w` chains.
The proof follows F. Galvin, *A proof of Dilworth's chain decomposition
theorem*, Amer. Math. Monthly 101 (1994), 352–353.

## Formal rendering

The finite poset is a `Finset s` in an ambient `PartialOrder α`.  A partition
of `s` into `w` chains is encoded as a labelling `f : α → ℕ` with `f x < w` for
every `x ∈ s`, each of whose level sets `{x ∈ s | f x = i}` is a chain.  An
`ℕ`-valued labelling is used instead of `α → Fin w` because for `w = 0`,
`s = ∅` and nonempty `α` there is no function `α → Fin 0`, although the empty
poset is a union of zero chains (the same convention as the repository's
`Candidates.MirskyDualDilworth`).

* `exists_chain_labelling_of_antichain_card_le` — if every antichain in `s` has
  at most `w` elements, then `s` is a union of `w` (possibly empty) chains.
* `dilworth` — the source form: if moreover some antichain in `s` has exactly
  `w` elements (so `w` is the size of a largest antichain), then `s` is
  partitioned into exactly `w` *nonempty* chains.
* `dilworth_iff` — every antichain has at most `w` elements iff `s` is a union
  of `w` chains; i.e. the width equals the minimum number of covering chains.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.DilworthChainDecomposition

open Finset

variable {α : Type*} [PartialOrder α]

/-- The easy direction: if `s` is a union of `w` chains (the level sets of a
labelling `f` with values `< w` on `s`), then every antichain in `s` has at most
`w` elements, since an antichain meets each chain in at most one point. -/
theorem antichain_card_le_of_chain_labelling (s : Finset α) (w : ℕ) (f : α → ℕ)
    (hfw : ∀ x ∈ s, f x < w)
    (hf : ∀ i, IsChain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α)) :
    ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → #t ≤ w := by
  intro t hts hta
  have hinj : Set.InjOn f (t : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    rcases hf (f x) ⟨hts hx, rfl⟩ ⟨hts hy, hxy.symm⟩ hne with hle | hle
    · exact hta hx hy hne hle
    · exact hta hy hx (Ne.symm hne) hle
  have hmaps : Set.MapsTo f (t : Set α) (range w : Set ℕ) := fun x hx => by
    simpa using hfw x (hts hx)
  simpa using card_le_card_of_injOn f hmaps hinj

/-- An antichain with `w` elements inside a union of `w` chains meets every one
of the chains: every label `i < w` is attained on the antichain. -/
theorem exists_mem_label_eq_of_card_eq (s : Finset α) (w : ℕ) (f : α → ℕ)
    (hfw : ∀ x ∈ s, f x < w)
    (hf : ∀ i, IsChain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α))
    (A : Finset α) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α)) (hcard : #A = w) :
    ∀ i < w, ∃ x ∈ A, f x = i := by
  classical
  have hinj : Set.InjOn f (A : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    rcases hf (f x) ⟨hAs hx, rfl⟩ ⟨hAs hy, hxy.symm⟩ hne with hle | hle
    · exact hA hx hy hne hle
    · exact hA hy hx (Ne.symm hne) hle
  have hsub : A.image f ⊆ range w := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    exact mem_range.mpr (hfw x (hAs hx))
  have hcard' : #(range w) ≤ #(A.image f) := by
    rw [card_image_of_injOn hinj, card_range, hcard]
  have heq : A.image f = range w := eq_of_subset_of_card_le hsub hcard'
  intro i hi
  have hmem : i ∈ A.image f := heq ▸ mem_range.mpr hi
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hmem
  exact ⟨x, hx, hxi⟩

/-- A nonempty finite set contained in a chain has a greatest element. -/
theorem exists_greatest_of_isChain (u : Finset α) (hu : u.Nonempty)
    (hc : IsChain (· ≤ ·) (u : Set α)) : ∃ x ∈ u, ∀ y ∈ u, y ≤ x := by
  obtain ⟨x, hxu, hxmax⟩ := u.exists_maximal hu
  refine ⟨x, hxu, fun y hy => ?_⟩
  by_cases hyx : y = x
  · exact hyx ▸ le_rfl
  · rcases hc hy hxu hyx with hle | hle
    · exact hle
    · exact hxmax hy hle

/-- **Dilworth's theorem, labelling form** (R. P. Dilworth, 1950; proof of
F. Galvin, 1994).  If every antichain contained in the finite set `s` of a
partially ordered type has at most `w` elements, then `s` is a union of `w`
chains: there is a labelling `f : α → ℕ` with `f x < w` for all `x ∈ s` such
that every level set `{x ∈ s | f x = i}` is a chain. -/
theorem exists_chain_labelling_of_antichain_card_le (s : Finset α) (w : ℕ)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → #t ≤ w) :
    ∃ f : α → ℕ, (∀ x ∈ s, f x < w) ∧
      ∀ i, IsChain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α) := by
  classical
  induction s using Finset.strongInduction generalizing w with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => 0, fun x hx => absurd hx (notMem_empty x), fun i => ?_⟩
    intro x hx
    exact absurd hx.1 (notMem_empty x)
  -- Galvin's step: remove a maximal element `a`.
  obtain ⟨a, has, hamax⟩ := s.exists_maximal hne
  set s' := s.erase a with hs'
  have hs's : s' ⊆ s := erase_subset a s
  -- `w'` is the width of `s'`, attained by the antichain `A0`.
  let W : Finset (Finset α) := s'.powerset.filter (fun t => IsAntichain (· ≤ ·) (t : Set α))
  set w' := W.sup Finset.card with hw'def
  have hw' : ∀ t ⊆ s', IsAntichain (· ≤ ·) (t : Set α) → #t ≤ w' := fun t ht hta =>
    Finset.le_sup (f := Finset.card) (by simp [W, ht, hta])
  obtain ⟨A0, hA0W, hA0card⟩ := Finset.exists_mem_eq_sup W ⟨∅, by simp [W]⟩ Finset.card
  have hA0s : A0 ⊆ s' := (mem_powerset.mp (mem_filter.mp hA0W).1)
  have hA0 : IsAntichain (· ≤ ·) (A0 : Set α) := (mem_filter.mp hA0W).2
  replace hA0card : w' = #A0 := hA0card
  have hw'w : w' ≤ w := hA0card ▸ h A0 (hA0s.trans hs's) hA0
  obtain ⟨g, hgw, hg⟩ := ih s' (erase_ssubset has) w' hw'
  -- `Good`: elements of `s'` lying in some maximum antichain of `s'`.
  let Good : Finset α := s'.filter
    (fun x => ∃ A ⊆ s', IsAntichain (· ≤ ·) (A : Set α) ∧ #A = w' ∧ x ∈ A)
  -- `T`: the top element of `Good` in each chain `g = i`.
  let T : Finset α := Good.filter (fun x => ∀ y ∈ Good, g y = g x → y ≤ x)
  have hsurj : ∀ A ⊆ s', IsAntichain (· ≤ ·) (A : Set α) → #A = w' →
      ∀ i < w', ∃ z ∈ A, g z = i := fun A hAs hA hAc =>
    exists_mem_label_eq_of_card_eq s' w' g hgw hg A hAs hA hAc
  have hGood : ∀ A ⊆ s', IsAntichain (· ≤ ·) (A : Set α) → #A = w' → ∀ x ∈ A, x ∈ Good :=
    fun A hAs hA hAc x hx => mem_filter.mpr ⟨hAs hx, A, hAs, hA, hAc, hx⟩
  have hT_top : ∀ i < w', ∃ x ∈ T, g x = i := by
    intro i hi
    let u : Finset α := Good.filter (fun x => g x = i)
    obtain ⟨z, hzA0, hzi⟩ := hsurj A0 hA0s hA0 hA0card.symm i hi
    have hune : u.Nonempty := ⟨z, mem_filter.mpr ⟨hGood A0 hA0s hA0 hA0card.symm z hzA0, hzi⟩⟩
    have huc : IsChain (· ≤ ·) (u : Set α) := (hg i).mono fun y hy => by
      have hy' := mem_filter.mp hy
      exact ⟨(mem_filter.mp hy'.1).1, hy'.2⟩
    obtain ⟨x, hxu, hxmax⟩ := exists_greatest_of_isChain u hune huc
    have hxu' := mem_filter.mp hxu
    refine ⟨x, mem_filter.mpr ⟨hxu'.1, fun y hy hyx => ?_⟩, hxu'.2⟩
    exact hxmax y (mem_filter.mpr ⟨hy, hyx.trans hxu'.2⟩)
  have hT_anti : IsAntichain (· ≤ ·) (T : Set α) := by
    intro x hx y hy hxy hle
    have hx' := mem_filter.mp hx
    have hy' := mem_filter.mp hy
    have hgxy : g x ≠ g y := fun he =>
      hxy (le_antisymm hle (hx'.2 y hy'.1 he.symm))
    obtain ⟨A, hAs, hA, hAc, hyA⟩ := (mem_filter.mp hy'.1).2
    obtain ⟨z, hzA, hzx⟩ := hsurj A hAs hA hAc (g x) (hgw x (mem_filter.mp hx'.1).1)
    have hzx' : z ≤ x := hx'.2 z (hGood A hAs hA hAc z hzA) hzx
    have hzy : z ≠ y := fun he => hgxy (he ▸ hzx).symm
    exact hA hzA hyA hzy (hzx'.trans hle)
  have hT_card : w' ≤ #T := by
    have hsub : range w' ⊆ T.image g := by
      intro i hi
      obtain ⟨x, hxT, hxi⟩ := hT_top i (mem_range.mp hi)
      exact mem_image.mpr ⟨x, hxT, hxi⟩
    calc w' = #(range w') := (card_range w').symm
      _ ≤ #(T.image g) := card_le_card hsub
      _ ≤ #T := card_image_le
  have hTs' : T ⊆ s' := fun x hx => (mem_filter.mp (mem_filter.mp hx).1).1
  have haT : a ∉ T := fun ha => (notMem_erase a s) (hTs' ha)
  by_cases hcase : ∃ x ∈ T, x ≤ a
  · -- Case 1: some top `x` (of label `j`) lies below `a`; remove the chain
    -- `K = {a} ∪ {z ∈ s' | g z = j ∧ z ≤ x}` and recurse on the rest `R`.
    obtain ⟨x, hxT, hxa⟩ := hcase
    have hx' := mem_filter.mp hxT
    have hxs' : x ∈ s' := (mem_filter.mp hx'.1).1
    set j := g x with hj
    have hjw : j < w' := hgw x hxs'
    let R : Finset α := s'.filter (fun z => ¬ (g z = j ∧ z ≤ x))
    have hRs' : R ⊆ s' := filter_subset _ _
    have hRs : R ⊂ s := lt_of_le_of_lt hRs' (erase_ssubset has)
    have hR : ∀ B ⊆ R, IsAntichain (· ≤ ·) (B : Set α) → #B ≤ w' - 1 := by
      intro B hBR hB
      have hBw : #B ≤ w' := hw' B (hBR.trans hRs') hB
      by_contra hcon
      have hBc : #B = w' := by omega
      obtain ⟨z, hzB, hzj⟩ := hsurj B (hBR.trans hRs') hB hBc j hjw
      have hzx : z ≤ x := hx'.2 z (hGood B (hBR.trans hRs') hB hBc z hzB) hzj
      exact (mem_filter.mp (hBR hzB)).2 ⟨hzj, hzx⟩
    obtain ⟨f0, hf0w, hf0⟩ := ih R hRs (w' - 1) hR
    refine ⟨fun z => if z ∈ R then f0 z else w' - 1, fun z hz => ?_, fun i => ?_⟩
    · dsimp only
      split_ifs with hzR
      · have := hf0w z hzR
        omega
      · omega
    · -- Elements of `s` outside `R` form the chain `K`.
      have hK : ∀ z ∈ s, z ∉ R → z ≤ a ∧ (z = a ∨ (z ∈ s' ∧ g z = j)) := by
        intro z hz hzR
        by_cases hza : z = a
        · exact ⟨hza ▸ le_rfl, Or.inl hza⟩
        · have hzs' : z ∈ s' := mem_erase.mpr ⟨hza, hz⟩
          have hzK : g z = j ∧ z ≤ x := by
            by_contra hc
            exact hzR (mem_filter.mpr ⟨hzs', hc⟩)
          exact ⟨hzK.2.trans hxa, Or.inr ⟨hzs', hzK.1⟩⟩
      intro y hy z hz hyz
      obtain ⟨hys, hyi⟩ := hy
      obtain ⟨hzs, hzi⟩ := hz
      dsimp only at hyi hzi
      by_cases hyR : y ∈ R <;> by_cases hzR : z ∈ R <;>
        simp only [hyR, hzR, if_true, if_false] at hyi hzi
      · exact hf0 i ⟨hyR, hyi⟩ ⟨hzR, hzi⟩ hyz
      · have := hf0w y hyR
        omega
      · have := hf0w z hzR
        omega
      · obtain ⟨hya, hy'⟩ := hK y hys hyR
        obtain ⟨hza, hz'⟩ := hK z hzs hzR
        rcases hy' with rfl | ⟨hys', hyj⟩
        · exact Or.inr hza
        rcases hz' with rfl | ⟨hzs', hzj⟩
        · exact Or.inl hya
        exact hg j ⟨hys', hyj⟩ ⟨hzs', hzj⟩ hyz
  · -- Case 2: no top lies below `a`, so `T ∪ {a}` is an antichain of size
    -- `w' + 1`; give `a` the fresh label `w'`.
    push Not at hcase
    have hTa : IsAntichain (· ≤ ·) ((insert a T : Finset α) : Set α) := by
      rw [coe_insert]
      refine hT_anti.insert (fun x hx _ => hcase x hx) (fun x hx hax hle => ?_)
      have hxs : x ∈ s := hs's (hTs' hx)
      exact hax (le_antisymm hle (hamax hxs hle))
    have hcardTa : #(insert a T) = #T + 1 := card_insert_of_notMem haT
    have hlt : w' < w := by
      have := h (insert a T) (insert_subset has (hTs'.trans hs's)) hTa
      omega
    refine ⟨fun z => if z = a then w' else g z, fun z hz => ?_, fun i => ?_⟩
    · dsimp only
      split_ifs with hza
      · exact hlt
      · exact (hgw z (mem_erase.mpr ⟨hza, hz⟩)).trans hlt
    · intro y hy z hz hyz
      obtain ⟨hys, hyi⟩ := hy
      obtain ⟨hzs, hzi⟩ := hz
      dsimp only at hyi hzi
      by_cases hya : y = a <;> by_cases hza : z = a <;>
        simp only [hya, hza, if_true, if_false] at hyi hzi
      · exact absurd (hya.trans hza.symm) hyz
      · have := hgw z (mem_erase.mpr ⟨hza, hzs⟩)
        omega
      · have := hgw y (mem_erase.mpr ⟨hya, hys⟩)
        omega
      · exact hg i ⟨mem_erase.mpr ⟨hya, hys⟩, hyi⟩ ⟨mem_erase.mpr ⟨hza, hzs⟩, hzi⟩ hyz

/-- **Dilworth's theorem** (R. P. Dilworth, 1950), source form.  Let `s` be a
finite set in a partially ordered type whose largest antichain has `w` elements:
every antichain contained in `s` has at most `w` elements and some antichain
`A ⊆ s` has exactly `w` elements.  Then `s` is partitioned into `w` chains: there
is a labelling `f : α → ℕ` with `f x < w` on `s`, every level set
`{x ∈ s | f x = i}` is a chain, and every label `i < w` is used, so the `w`
chains are nonempty and pairwise disjoint with union `s`. -/
theorem dilworth (s : Finset α) (w : ℕ)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → #t ≤ w)
    (A : Finset α) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α)) (hcard : #A = w) :
    ∃ f : α → ℕ, (∀ x ∈ s, f x < w) ∧
      (∀ i, IsChain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α)) ∧
      ∀ i < w, ∃ x ∈ s, f x = i := by
  obtain ⟨f, hfw, hf⟩ := exists_chain_labelling_of_antichain_card_le s w h
  refine ⟨f, hfw, hf, fun i hi => ?_⟩
  obtain ⟨x, hxA, hxi⟩ := exists_mem_label_eq_of_card_eq s w f hfw hf A hAs hA hcard i hi
  exact ⟨x, hAs hxA, hxi⟩

/-- **Dilworth's theorem, "equivalently" form.**  For a finite set `s` in a
partially ordered type and `w : ℕ`, every antichain contained in `s` has at most
`w` elements if and only if `s` is a union of `w` chains (the level sets of a
labelling `f` with values `< w` on `s`).  Hence the maximum size of an antichain
in `s` equals the minimum number of chains covering `s`. -/
theorem dilworth_iff (s : Finset α) (w : ℕ) :
    (∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → #t ≤ w) ↔
      ∃ f : α → ℕ, (∀ x ∈ s, f x < w) ∧
        ∀ i, IsChain (· ≤ ·) ({x | x ∈ s ∧ f x = i} : Set α) :=
  ⟨exists_chain_labelling_of_antichain_card_le s w,
    fun ⟨f, hfw, hf⟩ => antichain_card_le_of_chain_labelling s w f hfw hf⟩

/-! ## Examples -/

/-- The hypotheses of `dilworth` hold jointly: the chain `{0, 1, 2}` in `ℕ` has
largest antichain `{0}` of size `1`. -/
example : (∀ t ⊆ ({0, 1, 2} : Finset ℕ), IsAntichain (· ≤ ·) (t : Set ℕ) → #t ≤ 1) ∧
    ({0} : Finset ℕ) ⊆ {0, 1, 2} ∧ IsAntichain (· ≤ ·) (({0} : Finset ℕ) : Set ℕ) ∧
    #({0} : Finset ℕ) = 1 := by
  refine ⟨fun t _ hta => ?_, by decide, ?_, rfl⟩
  · exact card_le_one_iff_subsingleton_coe.mpr
      ((Set.subsingleton_coe _).mpr (hta.subsingleton))
  · rw [coe_singleton]
    exact Set.subsingleton_singleton.isAntichain _

/-- The width hypothesis is not vacuous: in `ℕ × ℕ` the two-element set
`{(0, 1), (1, 0)}` is an antichain, so it is not covered by the bound `w = 1`. -/
example : ¬ ∀ t ⊆ ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)),
    IsAntichain (· ≤ ·) (t : Set (ℕ × ℕ)) → #t ≤ 1 := by
  intro h
  have hA : IsAntichain (· ≤ ·) (({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rw [coe_insert, coe_singleton]
    refine IsAntichain.insert (Set.subsingleton_singleton.isAntichain _) ?_ ?_ <;>
      · intro b hb _
        rw [Set.mem_singleton_iff] at hb
        subst hb
        decide
  have h2 := h _ subset_rfl hA
  simp at h2

end Candidates.DilworthChainDecomposition
