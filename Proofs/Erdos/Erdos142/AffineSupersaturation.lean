/-
  Erdős Problem #142 — sharp bounded affine-window multiplicity.

  This file completes the finite affine-window argument.  A local progression
  occurrence is injected into its global canonical edge, its positive local
  gap `s`, and its starting position `j`.  The affine transport identity makes
  the global gap `s*d`; hence `s` recovers the window difference `d` by
  cancellation, and the affine incidence equation then recovers the shifted
  base.  Counting all admissible `(s,j)` pairs gives the sharp coefficient
  `∑ s ∈ Icc 1 ((L-1)/2), (L-2*s)` without imposing a divisibility condition.

  This is an exact finite supersaturation inequality, not an asymptotic
  resolution of Erdős Problem #142.
-/

import Erdos.Erdos142.AffineWindows

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos142

/-- The total number of local canonical edges in all boundary-allowed affine
windows is at most the number of global edges times the number of possible
positive local gaps and starting positions. -/
theorem sum_threeAPCount_affineWindow_le_gapMultiplicity
    (A : Finset ℕ) (N L D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
      ∑ b ∈ Finset.range (N + (L - 1) * d),
        threeAPCount (affineWindow A L d b)) ≤
      (∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s)) * threeAPCount A := by
  classical
  let occurrence :=
    (Finset.Icc 1 D).sigma fun d =>
      (Finset.range (N + (L - 1) * d)).sigma fun b =>
        threeAPEdges (affineWindow A L d b)
  let gapSigma :=
    (Finset.Icc 1 ((L - 1) / 2)).sigma fun s => Finset.range (L - 2 * s)
  let flatten : (Σ _s : ℕ, ℕ) → ℕ × ℕ := fun z => (z.1, z.2)
  let gaps : Finset (ℕ × ℕ) := gapSigma.image flatten
  let target := (threeAPEdges A).product gaps
  let ordered : Finset ℕ → ℕ × ℕ := fun e =>
    if h : ∃ x q : ℕ, 0 < q ∧ e = {x, x + q, x + 2 * q} then
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    else (0, 0)
  have hordered {B e : Finset ℕ} (he : e ∈ threeAPEdges B) :
      0 < (ordered e).2 ∧
        e = {(ordered e).1, (ordered e).1 + (ordered e).2,
          (ordered e).1 + 2 * (ordered e).2} := by
    have hex := exists_ordered_threeAP_of_mem_threeAPEdges he
    simp only [ordered, dif_pos hex]
    exact Classical.choose_spec (Classical.choose_spec hex)
  let mapOccurrence : (Σ _d : ℕ, Σ _b : ℕ, Finset ℕ) →
      Finset ℕ × (ℕ × ℕ) := fun o =>
    (o.2.2.image (affineWindowValue L o.1 o.2.1),
      ((ordered o.2.2).2, (ordered o.2.2).1))
  have hmaps : Set.MapsTo mapOccurrence occurrence target := by
    intro o ho
    rcases o with ⟨d, ⟨b, e⟩⟩
    change (⟨d, ⟨b, e⟩⟩ : Σ _d : ℕ, Σ _b : ℕ, Finset ℕ) ∈ occurrence at ho
    dsimp only [occurrence] at ho
    rw [mem_sigma, mem_sigma] at ho
    rcases ho with ⟨hd, hb, he⟩
    have hord := hordered he
    let x := (ordered e).1
    let s := (ordered e).2
    have hs : 0 < s := hord.1
    have heq : e = {x, x + s, x + 2 * s} := hord.2
    have hedata := mem_threeAPEdges.mp he
    have hx : x ∈ affineWindow A L d b := by
      apply hedata.1
      rw [heq]
      simp
    have hxs : x + s ∈ affineWindow A L d b := by
      apply hedata.1
      rw [heq]
      simp
    have hxss : x + 2 * s ∈ affineWindow A L d b := by
      apply hedata.1
      rw [heq]
      simp
    have htwo : 2 * s < L := by
      have hlt := (mem_affineWindow_iff.mp hxss).1
      omega
    have hsUpper : s ≤ (L - 1) / 2 := by omega
    have hxUpper : x < L - 2 * s := by
      have hlt := (mem_affineWindow_iff.mp hxss).1
      omega
    change mapOccurrence ⟨d, ⟨b, e⟩⟩ ∈
      ((threeAPEdges A).product gaps : Set (Finset ℕ × (ℕ × ℕ)))
    refine Finset.mem_product.mpr
      ⟨image_mem_threeAPEdges_of_mem_affineWindow (mem_Icc.mp hd).1 he, ?_⟩
    dsimp only [gaps]
    rw [mem_image]
    refine ⟨⟨s, x⟩, ?_, rfl⟩
    dsimp only [gapSigma]
    rw [mem_sigma, mem_Icc, mem_range]
    exact ⟨⟨hs, hsUpper⟩, hxUpper⟩
  have hinjective : Set.InjOn mapOccurrence occurrence := by
    rintro ⟨d₁, ⟨b₁, e₁⟩⟩ ho₁ ⟨d₂, ⟨b₂, e₂⟩⟩ ho₂ hmap
    change (⟨d₁, ⟨b₁, e₁⟩⟩ : Σ _d : ℕ, Σ _b : ℕ, Finset ℕ) ∈ occurrence at ho₁
    change (⟨d₂, ⟨b₂, e₂⟩⟩ : Σ _d : ℕ, Σ _b : ℕ, Finset ℕ) ∈ occurrence at ho₂
    dsimp only [occurrence] at ho₁ ho₂
    rw [mem_sigma, mem_sigma] at ho₁ ho₂
    rcases ho₁ with ⟨hd₁, hb₁, he₁⟩
    rcases ho₂ with ⟨hd₂, hb₂, he₂⟩
    have hord₁ := hordered he₁
    have hord₂ := hordered he₂
    let x₁ := (ordered e₁).1
    let s₁ := (ordered e₁).2
    let x₂ := (ordered e₂).1
    let s₂ := (ordered e₂).2
    have hs₁ : 0 < s₁ := hord₁.1
    have hs₂ : 0 < s₂ := hord₂.1
    have heq₁ : e₁ = {x₁, x₁ + s₁, x₁ + 2 * s₁} := hord₁.2
    have heq₂ : e₂ = {x₂, x₂ + s₂, x₂ + 2 * s₂} := hord₂.2
    have hedata₁ := mem_threeAPEdges.mp he₁
    have hedata₂ := mem_threeAPEdges.mp he₂
    have hx₁ : x₁ ∈ affineWindow A L d₁ b₁ := by
      apply hedata₁.1
      rw [heq₁]
      simp
    have hxs₁ : x₁ + s₁ ∈ affineWindow A L d₁ b₁ := by
      apply hedata₁.1
      rw [heq₁]
      simp
    have hxss₁ : x₁ + 2 * s₁ ∈ affineWindow A L d₁ b₁ := by
      apply hedata₁.1
      rw [heq₁]
      simp
    have hx₂ : x₂ ∈ affineWindow A L d₂ b₂ := by
      apply hedata₂.1
      rw [heq₂]
      simp
    have hxs₂ : x₂ + s₂ ∈ affineWindow A L d₂ b₂ := by
      apply hedata₂.1
      rw [heq₂]
      simp
    have hxss₂ : x₂ + 2 * s₂ ∈ affineWindow A L d₂ b₂ := by
      apply hedata₂.1
      rw [heq₂]
      simp
    have hpair :
        (e₁.image (affineWindowValue L d₁ b₁), (s₁, x₁)) =
          (e₂.image (affineWindowValue L d₂ b₂), (s₂, x₂)) := hmap
    have hglobal := congrArg Prod.fst hpair
    have hsx := congrArg Prod.snd hpair
    have hs : s₁ = s₂ := congrArg Prod.fst hsx
    have hx : x₁ = x₂ := congrArg Prod.snd hsx
    have himage₁ := affineWindow_ordered_threeAP_transport hx₁ hxs₁ hxss₁
    have himage₂ := affineWindow_ordered_threeAP_transport hx₂ hxs₂ hxss₂
    rw [heq₁] at hglobal
    rw [heq₂] at hglobal
    have horderedGlobal :
        ({affineWindowValue L d₁ b₁ x₁,
            affineWindowValue L d₁ b₁ x₁ + s₁ * d₁,
            affineWindowValue L d₁ b₁ x₁ + 2 * (s₁ * d₁)} : Finset ℕ) =
          {affineWindowValue L d₂ b₂ x₂,
            affineWindowValue L d₂ b₂ x₂ + s₂ * d₂,
            affineWindowValue L d₂ b₂ x₂ + 2 * (s₂ * d₂)} := by
      rw [← himage₁, ← himage₂]
      exact hglobal
    have hglobalData := ordered_threeAP_finset_injective
      (Nat.mul_pos hs₁ (mem_Icc.mp hd₁).1)
      (Nat.mul_pos hs₂ (mem_Icc.mp hd₂).1) horderedGlobal
    have hvalue : affineWindowValue L d₁ b₁ x₁ =
        affineWindowValue L d₂ b₂ x₂ := hglobalData.1
    have hgap : s₁ * d₁ = s₂ * d₂ := hglobalData.2
    have hd : d₁ = d₂ := by
      rw [hs] at hgap
      exact Nat.mul_left_cancel hs₂ hgap
    have hrel₁ := (mem_affineWindow_iff.mp hx₁).2.2
    have hrel₂ := (mem_affineWindow_iff.mp hx₂).2.2
    rw [← hd, ← hx] at hrel₂ hvalue
    have hb : b₁ = b₂ := by omega
    have he : e₁ = e₂ := by rw [heq₁, heq₂, hs, hx]
    exact by
      cases hd
      cases hb
      cases he
      rfl
  have hcard := Finset.card_le_card_of_injOn mapOccurrence hmaps hinjective
  have hOccurrenceCard : occurrence.card =
      ∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          threeAPCount (affineWindow A L d b) := by
    simp only [occurrence, card_sigma, threeAPCount]
  have hflatten : Function.Injective flatten := by
    rintro ⟨s₁, j₁⟩ ⟨s₂, j₂⟩ h
    simp only [flatten, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  have hGapsCard : gaps.card =
      ∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s) := by
    dsimp only [gaps]
    rw [card_image_of_injective gapSigma hflatten]
    simp only [gapSigma, card_sigma, card_range]
  have hTargetCard : target.card =
      (∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s)) * threeAPCount A := by
    dsimp only [target]
    calc
      ((threeAPEdges A).product gaps).card =
          (threeAPEdges A).card * gaps.card := Finset.card_product _ _
      _ = (∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s)) *
          threeAPCount A := by
        rw [hGapsCard]
        simp only [threeAPCount]
        ac_rfl
  rw [hOccurrenceCard, hTargetCard] at hcard
  exact hcard

/-- Sharp balanced boundary-allowed affine-window supersaturation.  For
`A ⊆ range N`, every point has load `L*D`, there are
`F = D*N + (L-1)*D*(D+1)/2` windows, and every global edge has load at most
`M = ∑ s ∈ Icc 1 ((L-1)/2), (L-2*s)`. -/
theorem affineWindow_sharp_supersaturation
    (A : Finset ℕ) {N L D : ℕ} (hAN : A ⊆ Finset.range N) :
    L * D * A.card ≤
      (D * N + (L - 1) * D * (D + 1) / 2) * rothNumberNat L +
        (∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s)) * threeAPCount A := by
  apply affineWindow_incidence_bound_of_threeAP_multiplicity A hAN
  exact sum_threeAPCount_affineWindow_le_gapMultiplicity A N L D

/-- The sharp theorem's hypotheses are jointly satisfiable at the smallest
nontrivial parameters, with the progression-containing set `{0,1,2}`. -/
example :
    let A : Finset ℕ := {0, 1, 2}
    let N := 3
    let L := 3
    let D := 1
    A ⊆ Finset.range N ∧ L ≤ N ∧ 3 ≤ L ∧ 1 ≤ D ∧
      L * D * A.card ≤
        (D * N + (L - 1) * D * (D + 1) / 2) * rothNumberNat L +
          (∑ s ∈ Finset.Icc 1 ((L - 1) / 2), (L - 2 * s)) * threeAPCount A := by
  dsimp only
  have hAN : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range 3 := by decide
  exact ⟨hAN, by omega, by omega, by omega,
    affineWindow_sharp_supersaturation _ hAN⟩

#check @sum_threeAPCount_affineWindow_le_gapMultiplicity
#check @affineWindow_sharp_supersaturation

#print axioms sum_threeAPCount_affineWindow_le_gapMultiplicity
#print axioms affineWindow_sharp_supersaturation

end Erdos142
