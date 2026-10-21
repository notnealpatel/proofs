/-
# Ore — a finite group is cyclic iff its subgroup lattice is distributive

## Source

S. Palcoux, *Ore's theorem on cyclic subfactor planar algebras and beyond*,
arXiv:1702.02124, Section 2.2, Theorem `ore1` and Theorem `ore2`
(with Claims `max`, `preore2`, `topred`).  Both are classical results of
O. Ore, *Structures and group theory II*, Duke Math. J. 4 (1938), Theorems 4
and 7, which the paper reproves.

Verbatim (LaTeX of the source):

```
\begin{theorem} \label{ore1}
A finite group $ G $ is cyclic if and only if its subgroup lattice
$ \mathcal{L}(G) $ is distributive.
\end{theorem}

\begin{definition} \label{Hcy}
An interval of finite groups $ [H,G] $ is said to be $ H $-cyclic if there
is $ g \in G $ such that $ \langle H,g \rangle = G $.
\end{definition}

\begin{theorem} \label{ore2}
A distributive interval $ [H,G] $ is $ H $-cyclic.
\end{theorem}
```

The paper proves (⇐) of `ore1` as the case `H = {e}` of `ore2`, and (⇒) by
the correspondence between subgroups of `ℤ/n` and divisors of `n`
(join = lcm, meet = gcd).

## Status

Known (Ore 1938), reproved in the paper.  Date of this card: 2026-10-21.

## Proof here

* (⇒) In a finite cyclic group, `x ∈ H ↔ orderOf x ∣ |H|` (counting:
  `#{a | a ^ |H| = 1} ≤ |H|`), every divisor of `|G|` is the order of a
  subgroup, so `|A ⊓ B| = gcd`, `|A ⊔ B| = lcm`, `A ≤ B ↔ |A| ∣ |B|`, and the
  law reduces to `lcm a (gcd b c) = gcd (lcm a b) (lcm a c)`.
* `ore2` is proved without the paper's Boolean top-interval lemma: for any
  finite family of distinct coatoms `M, M₁, …, Mₖ` above `H`, distributivity
  gives `M ⊔ (M₁ ⊓ ⋯ ⊓ Mₖ) = G`; by induction one finds `g` outside every
  coatom above `H` (if `b` avoids `M₁ … Mₖ` but `b ∈ M`, take
  `a ∈ (M₁ ⊓ ⋯ ⊓ Mₖ) \ M` and `g = a b`), and then `⟨H, g⟩ = G` because a
  proper subgroup lies below a coatom.
* (⇐) of `ore1` is `ore2` at `H = ⊥`, as in the paper.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.OreDistributiveCyclic

open Subgroup

/-! ## Arithmetic -/

/-- `lcm` distributes over `gcd` on positive naturals:
`lcm a (gcd b c) = gcd (lcm a b) (lcm a c)`. -/
theorem lcm_gcd_eq_gcd_lcm (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.lcm a (Nat.gcd b c) = Nat.gcd (Nat.lcm a b) (Nat.lcm a c) := by
  have hbc : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have hab : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hac : Nat.lcm a c ≠ 0 := Nat.lcm_ne_zero ha hc
  apply Nat.eq_of_factorization_eq (Nat.lcm_ne_zero ha hbc) (Nat.gcd_ne_zero_left hab)
  intro p
  rw [Nat.factorization_lcm ha hbc, Nat.factorization_gcd hb hc,
    Nat.factorization_gcd hab hac, Nat.factorization_lcm ha hb, Nat.factorization_lcm ha hc]
  simp only [Finsupp.sup_apply, Finsupp.inf_apply]
  exact sup_inf_left _ _ _

/-! ## Subgroups of a finite cyclic group -/

section Cyclic

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/-- In a finite cyclic group, `x ∈ H` iff the order of `x` divides `|H|`. -/
theorem mem_iff_orderOf_dvd_card (H : Subgroup G) (x : G) :
    x ∈ H ↔ orderOf x ∣ Nat.card H := by
  refine ⟨fun hx => H.orderOf_dvd_natCard hx, fun hdvd => ?_⟩
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set d := Nat.card H with hd
  have hd0 : 0 < d := Nat.card_pos
  by_contra hxH
  have hS := IsCyclic.card_pow_eq_one_le (α := G) hd0
  have hsub : insert x (Finset.univ.filter (· ∈ H)) ⊆
      Finset.univ.filter (fun a : G => a ^ d = 1) := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_filter] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    rcases ha with rfl | ⟨-, haH⟩
    · exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    · exact orderOf_dvd_iff_pow_eq_one.mp (H.orderOf_dvd_natCard haH)
  have hcardH : (Finset.univ.filter (· ∈ H)).card = d := by
    rw [hd, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hnot : x ∉ Finset.univ.filter (· ∈ H) := by simpa using hxH
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hcardH] at hle
  omega

/-- In a finite cyclic group, `H ≤ K` iff `|H|` divides `|K|`. -/
theorem le_iff_card_dvd (H K : Subgroup G) : H ≤ K ↔ Nat.card H ∣ Nat.card K := by
  refine ⟨card_dvd_of_le, fun hdvd x hx => ?_⟩
  exact (mem_iff_orderOf_dvd_card K x).mpr
    (((mem_iff_orderOf_dvd_card H x).mp hx).trans hdvd)

/-- A finite cyclic group has a subgroup of every order dividing `|G|`. -/
theorem exists_card_eq {d : ℕ} (hd : d ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hq0 : Nat.card G / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd)
      (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn0))).ne'
  refine ⟨zpowers (g ^ (Nat.card G / d)), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hq0 (hg.symm ▸ Nat.div_dvd_of_dvd hd), hg,
    Nat.div_div_self hd hn0]

/-- In a finite cyclic group, `|B ⊓ C| = gcd (|B|, |C|)`. -/
theorem card_inf (B C : Subgroup G) :
    Nat.card (B ⊓ C : Subgroup G) = Nat.gcd (Nat.card B) (Nat.card C) := by
  obtain ⟨S, hS⟩ := exists_card_eq (G := G)
    ((Nat.gcd_dvd_left (Nat.card B) (Nat.card C)).trans (card_subgroup_dvd_card B))
  have hSB : S ≤ B := (le_iff_card_dvd S B).mpr (hS ▸ Nat.gcd_dvd_left _ _)
  have hSC : S ≤ C := (le_iff_card_dvd S C).mpr (hS ▸ Nat.gcd_dvd_right _ _)
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)
  · rw [← hS]
    exact card_dvd_of_le (le_inf hSB hSC)

/-- In a finite cyclic group, `|A ⊔ B| = lcm (|A|, |B|)`. -/
theorem card_sup (A B : Subgroup G) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.lcm (Nat.card A) (Nat.card B) := by
  obtain ⟨S, hS⟩ := exists_card_eq (G := G)
    (Nat.lcm_dvd (card_subgroup_dvd_card A) (card_subgroup_dvd_card B))
  have hAS : A ≤ S := (le_iff_card_dvd A S).mpr (hS ▸ Nat.dvd_lcm_left _ _)
  have hBS : B ≤ S := (le_iff_card_dvd B S).mpr (hS ▸ Nat.dvd_lcm_right _ _)
  apply Nat.dvd_antisymm
  · rw [← hS]
    exact card_dvd_of_le (sup_le hAS hBS)
  · exact Nat.lcm_dvd (card_dvd_of_le le_sup_left) (card_dvd_of_le le_sup_right)

/-- (⇒) of Ore's theorem (Palcoux, Theorem `ore1`): the subgroup lattice of a
finite cyclic group is distributive. -/
theorem sup_inf_eq_of_isCyclic (A B C : Subgroup G) :
    A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) := by
  apply le_antisymm (le_inf (sup_le_sup_left inf_le_left A) (sup_le_sup_left inf_le_right A))
  rw [le_iff_card_dvd, card_sup, card_inf, card_inf, card_sup, card_sup,
    lcm_gcd_eq_gcd_lcm _ _ _ Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne']

end Cyclic

/-! ## Distributive intervals are `H`-cyclic (Ore's Theorem 7) -/

section Interval

variable {G : Type*} [Group G]

/-- If the interval `[H, G]` is distributive, `M` is a coatom above `H` and `s`
is a finite set of coatoms above `H` not containing `M`, then
`M ⊔ ⨅ s = G`. -/
theorem coatom_sup_finset_inf_eq_top (H : Subgroup G)
    (hd : ∀ A B C : Subgroup G, H ≤ A → H ≤ B → H ≤ C → A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C))
    {M : Subgroup G} (hM : IsCoatom M) (hHM : H ≤ M) (s : Finset (Subgroup G))
    (hs : ∀ M' ∈ s, IsCoatom M' ∧ H ≤ M') (hMs : M ∉ s) :
    M ⊔ s.inf id = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert M' s hM's ih =>
    have hs' : ∀ N ∈ s, IsCoatom N ∧ H ≤ N := fun N hN => hs N (Finset.mem_insert_of_mem hN)
    have hM' := hs M' (Finset.mem_insert_self M' s)
    have hne : M ≠ M' := by
      rintro rfl
      exact hMs (Finset.mem_insert_self M s)
    have hHinf : H ≤ s.inf id := Finset.le_inf fun N hN => (hs' N hN).2
    rw [Finset.inf_insert, id, hd M M' (s.inf id) hHM hM'.2 hHinf,
      hM.sup_eq_top_of_ne hM'.1 hne, ih hs' (fun h => hMs (Finset.mem_insert_of_mem h)),
      inf_top_eq]

/-- If the interval `[H, G]` is distributive, then for every finite set `s` of
coatoms above `H` some element of `G` lies in none of them. -/
theorem exists_forall_notMem_of_distrib (H : Subgroup G)
    (hd : ∀ A B C : Subgroup G, H ≤ A → H ≤ B → H ≤ C → A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C))
    (s : Finset (Subgroup G)) (hs : ∀ M ∈ s, IsCoatom M ∧ H ≤ M) :
    ∃ g : G, ∀ M ∈ s, g ∉ M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun M hM => absurd hM (Finset.notMem_empty M)⟩
  | insert M s hMs ih =>
    have hs' : ∀ N ∈ s, IsCoatom N ∧ H ≤ N := fun N hN => hs N (Finset.mem_insert_of_mem hN)
    have hM := hs M (Finset.mem_insert_self M s)
    obtain ⟨b, hb⟩ := ih hs'
    by_cases hbM : b ∈ M
    · have htop : M ⊔ s.inf id = ⊤ := coatom_sup_finset_inf_eq_top H hd hM.1 hM.2 s hs' hMs
      have hnle : ¬ s.inf id ≤ M := by
        intro hle
        rw [sup_eq_left.mpr hle] at htop
        exact hM.1.1 htop
      obtain ⟨a, haN, haM⟩ := SetLike.not_le_iff_exists.mp hnle
      refine ⟨a * b, fun N hN => ?_⟩
      rcases Finset.mem_insert.mp hN with rfl | hNs
      · intro hab
        apply haM
        have h' : a * b * b⁻¹ = a := by group
        rw [← h']
        exact N.mul_mem hab (N.inv_mem hbM)
      · intro hab
        apply hb N hNs
        have haN' : a ∈ N := Finset.inf_le (f := id) hNs haN
        have h' : a⁻¹ * (a * b) = b := by group
        rw [← h']
        exact N.mul_mem (N.inv_mem haN') hab
    · refine ⟨b, fun N hN => ?_⟩
      rcases Finset.mem_insert.mp hN with rfl | hNs
      · exact hbM
      · exact hb N hNs

/-- Ore's Theorem 7 (Palcoux, Theorem `ore2`): if `G` is finite and the
interval `[H, G]` of the subgroup lattice is distributive, then `[H, G]` is
`H`-cyclic: some `g ∈ G` satisfies `⟨H, g⟩ = G`. -/
theorem exists_sup_zpowers_eq_top_of_distrib [Finite G] (H : Subgroup G)
    (hd : ∀ A B C : Subgroup G, H ≤ A → H ≤ B → H ≤ C → A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C)) :
    ∃ g : G, H ⊔ zpowers g = ⊤ := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  let s : Finset (Subgroup G) := Finset.univ.filter fun M => IsCoatom M ∧ H ≤ M
  obtain ⟨g, hg⟩ := exists_forall_notMem_of_distrib H hd s
    (fun M hM => (Finset.mem_filter.mp hM).2)
  refine ⟨g, ?_⟩
  rcases eq_top_or_exists_le_coatom (H ⊔ zpowers g) with htop | ⟨M, hM, hle⟩
  · exact htop
  · exfalso
    have hMs : M ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ M, hM, le_sup_left.trans hle⟩
    exact hg M hMs (hle (Subgroup.mem_sup_right (mem_zpowers g)))

end Interval

/-! ## Ore's theorem -/

/-- Ore's theorem (Ore 1938, Theorem 4; Palcoux arXiv:1702.02124, Theorem
`ore1`): a finite group `G` is cyclic if and only if its subgroup lattice is
distributive, i.e. `A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C)` for all subgroups
`A B C`. -/
theorem isCyclic_iff_sup_inf_eq {G : Type*} [Group G] [Finite G] :
    IsCyclic G ↔ ∀ A B C : Subgroup G, A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) := by
  refine ⟨fun _ => sup_inf_eq_of_isCyclic, fun hD => ?_⟩
  obtain ⟨g, hg⟩ := exists_sup_zpowers_eq_top_of_distrib (⊥ : Subgroup G)
    (fun A B C _ _ _ => hD A B C)
  rw [bot_sup_eq] at hg
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, hg⟩

/-! ## Non-vacuity: both sides of the equivalence occur -/

/-- The cyclic group `ℤ/6` has a distributive subgroup lattice. -/
example : ∀ A B C : Subgroup (Multiplicative (ZMod 6)),
    A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) :=
  isCyclic_iff_sup_inf_eq.mp inferInstance

/-- The Klein four-group `ℤ/2 × ℤ/2` does not have a distributive subgroup
lattice. -/
example : ¬ ∀ A B C : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
    A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) := by
  rw [← isCyclic_iff_sup_inf_eq, Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  rw [Nat.card_eq_fintype_card] at h
  simp at h

/-- The interval hypothesis of `exists_sup_zpowers_eq_top_of_distrib` holds for
a nontrivial instance: `H = ⊥` in `ℤ/6`. -/
example : ∀ A B C : Subgroup (Multiplicative (ZMod 6)), (⊥ : Subgroup _) ≤ A →
    ⊥ ≤ B → ⊥ ≤ C → A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) :=
  fun A B C _ _ _ => sup_inf_eq_of_isCyclic A B C

end Candidates.OreDistributiveCyclic
