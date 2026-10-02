/-
Erdős–Gyárfás problem 64 — local pruning for maximum-degree-three edge expanders.

This module proves a finite cut lemma.  Starting from a prescribed small set of vertices in a
finite graph of maximum degree three, it enlarges that set by minimizing a cut potential.  The
remaining vertices retain half of the original edge expansion, while every part added by the
minimization has many edges back into the rest of the deleted set.
-/

import Erdos.Erdos64.FiberExpansion

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Erdos64

open SimpleGraph

universe u

section Cuts

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The oriented edges of `G` whose first endpoint is in `A` and second endpoint is in `B`. -/
def EdgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (V × V) :=
  Finset.univ.filter fun e : V × V => e.1 ∈ A ∧ e.2 ∈ B ∧ G.Adj e.1 e.2

/-- Expansion restricted to cuts of a specified set of surviving vertices. -/
def EdgeExpandsOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (eta : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ H →
    eta * min (A.card : ℝ) ((H \ A).card : ℝ) ≤ ((EdgesBetween G A (H \ A)).card : ℝ)

/-- Membership in `EdgesBetween` unfolds to the two endpoint conditions and adjacency. -/
@[simp] theorem mem_edgesBetween {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {e : V × V} :
    e ∈ EdgesBetween G A B ↔ e.1 ∈ A ∧ e.2 ∈ B ∧ G.Adj e.1 e.2 := by
  simp [EdgesBetween]

/-- An ordinary edge cut is an edge count between a set and its complement. -/
theorem edgeCut_eq_edgesBetween {G : SimpleGraph V} [DecidableRel G.Adj] (A : Finset V) :
    EdgeCut G A = EdgesBetween G A (Finset.univ \ A) := by
  ext e
  simp only [mem_edgeCut, mem_edgesBetween, Finset.mem_sdiff, Finset.mem_univ, true_and]

/-- Reversing every edge shows that the number of edges between two sets is symmetric. -/
theorem card_edgesBetween_comm {G : SimpleGraph V} [DecidableRel G.Adj] (A B : Finset V) :
    (EdgesBetween G A B).card = (EdgesBetween G B A).card := by
  classical
  refine Finset.card_bij (fun e _ => (e.2, e.1)) ?_ ?_ ?_
  · intro e he
    rw [mem_edgesBetween] at he ⊢
    exact ⟨he.2.1, he.1, (G.adj_comm _ _).mp he.2.2⟩
  · intro e₁ _ e₂ _ he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro e he
    refine ⟨(e.2, e.1), ?_, rfl⟩
    rw [mem_edgesBetween] at he ⊢
    exact ⟨he.2.1, he.1, (G.adj_comm _ _).mp he.2.2⟩

private theorem edgesBetween_union_left {G : SimpleGraph V} [DecidableRel G.Adj]
    (A B C : Finset V) :
    EdgesBetween G (A ∪ B) C = EdgesBetween G A C ∪ EdgesBetween G B C := by
  ext e
  simp only [mem_edgesBetween, Finset.mem_union]
  aesop

private theorem edgesBetween_union_right {G : SimpleGraph V} [DecidableRel G.Adj]
    (A B C : Finset V) :
    EdgesBetween G A (B ∪ C) = EdgesBetween G A B ∪ EdgesBetween G A C := by
  ext e
  simp only [mem_edgesBetween, Finset.mem_union]
  aesop

private theorem disjoint_edgesBetween_left {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B C : Finset V} (hAB : Disjoint A B) :
    Disjoint (EdgesBetween G A C) (EdgesBetween G B C) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  exact (Finset.disjoint_left.mp hAB (mem_edgesBetween.mp heA).1
    (mem_edgesBetween.mp heB).1)

private theorem disjoint_edgesBetween_right {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B C : Finset V} (hBC : Disjoint B C) :
    Disjoint (EdgesBetween G A B) (EdgesBetween G A C) := by
  rw [Finset.disjoint_left]
  intro e heB heC
  exact (Finset.disjoint_left.mp hBC (mem_edgesBetween.mp heB).2.1
    (mem_edgesBetween.mp heC).2.1)

private theorem card_edgesBetween_union_left {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B C : Finset V} (hAB : Disjoint A B) :
    (EdgesBetween G (A ∪ B) C).card =
      (EdgesBetween G A C).card + (EdgesBetween G B C).card := by
  rw [edgesBetween_union_left, Finset.card_union_of_disjoint]
  exact disjoint_edgesBetween_left hAB

private theorem card_edgesBetween_union_right {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B C : Finset V} (hBC : Disjoint B C) :
    (EdgesBetween G A (B ∪ C)).card =
      (EdgesBetween G A B).card + (EdgesBetween G A C).card := by
  rw [edgesBetween_union_right, Finset.card_union_of_disjoint]
  exact disjoint_edgesBetween_right hBC

/-- Maximum degree three bounds every edge count by three times its left vertex count. -/
theorem card_edgesBetween_le_three_mul_card {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (A B : Finset V) :
    (EdgesBetween G A B).card ≤ 3 * A.card := by
  classical
  let T : Finset (Σ _v : V, V) := A.sigma fun v => G.neighborFinset v
  have hcard : (EdgesBetween G A B).card ≤ T.card := by
    let f : V × V → (Σ _v : V, V) := fun e => ⟨e.1, e.2⟩
    have hfmem : ∀ e ∈ EdgesBetween G A B, f e ∈ T := by
      intro e he
      rw [Finset.mem_sigma]
      exact ⟨(mem_edgesBetween.mp he).1,
        ((G.mem_neighborFinset e.1 e.2).mpr (mem_edgesBetween.mp he).2.2)⟩
    have hfinj : ∀ e₁ ∈ EdgesBetween G A B, ∀ e₂ ∈ EdgesBetween G A B,
        f e₁ = f e₂ → e₁ = e₂ := by
      intro e₁ _ e₂ _ he
      exact Prod.ext (congrArg Sigma.fst he) (congrArg Sigma.snd he)
    exact Finset.card_le_card_of_injOn f hfmem hfinj
  calc
    (EdgesBetween G A B).card ≤ T.card := hcard
    _ = ∑ v ∈ A, (G.neighborFinset v).card := Finset.card_sigma _ _
    _ ≤ ∑ _v ∈ A, 3 := Finset.sum_le_sum fun v _ => hdeg v
    _ = 3 * A.card := by simp [Nat.mul_comm]

/-- Maximum degree three also bounds an edge count by three times its right vertex count. -/
theorem card_edgesBetween_le_three_mul_card_right {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (A B : Finset V) :
    (EdgesBetween G A B).card ≤ 3 * B.card := by
  rw [card_edgesBetween_comm]
  exact card_edgesBetween_le_three_mul_card hdeg B A

/-- Adding a disjoint block to a cut gives the basic potential-addition identity. -/
theorem edgeCut_addition_identity {G : SimpleGraph V} [DecidableRel G.Adj]
    {D A : Finset V} (hA : A ⊆ Finset.univ \ D) :
    (EdgeCut G (D ∪ A)).card + (EdgesBetween G D A).card =
      (EdgeCut G D).card + (EdgesBetween G A ((Finset.univ \ D) \ A)).card := by
  classical
  let B := (Finset.univ \ D) \ A
  have hDA : Disjoint D A := by
    rw [Finset.disjoint_left]
    exact fun v hvD hvA => (Finset.mem_sdiff.mp (hA hvA)).2 hvD
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    exact fun v hvA hvB => (Finset.mem_sdiff.mp hvB).2 hvA
  have hDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    exact fun v hvD hvB => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvB).1).2 hvD
  have hcompUnion : Finset.univ \ D = A ∪ B := by
    ext v
    simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hv
      by_cases ha : v ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨hv, ha⟩
    · intro hv
      rcases hv with ha | hb
      · exact (Finset.mem_sdiff.mp (hA ha)).2
      · exact hb.1
  have hcompAdd : Finset.univ \ (D ∪ A) = B := by
    ext v
    simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
  have hcutAdd : (EdgeCut G (D ∪ A)).card =
      (EdgesBetween G D B).card + (EdgesBetween G A B).card := by
    rw [edgeCut_eq_edgesBetween, hcompAdd, card_edgesBetween_union_left hDA]
  have hcutD : (EdgeCut G D).card =
      (EdgesBetween G D A).card + (EdgesBetween G D B).card := by
    rw [edgeCut_eq_edgesBetween, hcompUnion, card_edgesBetween_union_right hAB]
  change (EdgeCut G (D ∪ A)).card + (EdgesBetween G D A).card =
    (EdgeCut G D).card + (EdgesBetween G A B).card
  rw [hcutAdd, hcutD, card_edgesBetween_comm D A]
  omega

/-- Removing a block from a cut gives the basic potential-removal identity. -/
theorem edgeCut_removal_identity {G : SimpleGraph V} [DecidableRel G.Adj]
    {D A : Finset V} (hA : A ⊆ D) :
    (EdgeCut G D).card + (EdgesBetween G A (D \ A)).card =
      (EdgeCut G (D \ A)).card + (EdgesBetween G A (Finset.univ \ D)).card := by
  classical
  let C := D \ A
  let H := Finset.univ \ D
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    exact fun v hvA hvC => (Finset.mem_sdiff.mp hvC).2 hvA
  have hAH : Disjoint A H := by
    rw [Finset.disjoint_left]
    exact fun v hvA hvH => (Finset.mem_sdiff.mp hvH).2 (hA hvA)
  have hCH : Disjoint C H := by
    rw [Finset.disjoint_left]
    exact fun v hvC hvH => (Finset.mem_sdiff.mp hvH).2 (Finset.mem_sdiff.mp hvC).1
  have hD : D = A ∪ C := by
    ext v
    simp only [C, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hv
      by_cases ha : v ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨hv, ha⟩
    · aesop
  have hcompC : Finset.univ \ C = A ∪ H := by
    ext v
    simp only [C, H, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hv
      by_cases ha : v ∈ A
      · exact Or.inl ha
      · exact Or.inr fun hd => hv ⟨hd, ha⟩
    · intro hv
      rcases hv with ha | hh
      · exact fun hc => hc.2 ha
      · exact fun hc => hh hc.1
  have hcutD : (EdgeCut G D).card =
      (EdgesBetween G A H).card + (EdgesBetween G C H).card := by
    rw [edgeCut_eq_edgesBetween, show Finset.univ \ D = H by rfl, hD,
      card_edgesBetween_union_left hAC]
  have hcutC : (EdgeCut G C).card =
      (EdgesBetween G C A).card + (EdgesBetween G C H).card := by
    rw [edgeCut_eq_edgesBetween, hcompC, card_edgesBetween_union_right hAH]
  change (EdgeCut G D).card + (EdgesBetween G A C).card =
    (EdgeCut G C).card + (EdgesBetween G A H).card
  rw [hcutD, hcutC, card_edgesBetween_comm A C]
  omega

/-- The cut of a subset of `D` splits across `D \ A` and the complement of `D`. -/
theorem edgeCut_subset_identity {G : SimpleGraph V} [DecidableRel G.Adj]
    {D A : Finset V} (hA : A ⊆ D) :
    (EdgeCut G A).card = (EdgesBetween G A (D \ A)).card +
      (EdgesBetween G A (Finset.univ \ D)).card := by
  classical
  have hdisj : Disjoint (D \ A) (Finset.univ \ D) := by
    rw [Finset.disjoint_left]
    exact fun v hvD hvH => (Finset.mem_sdiff.mp hvH).2 (Finset.mem_sdiff.mp hvD).1
  have hcomp : Finset.univ \ A = (D \ A) ∪ (Finset.univ \ D) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hva
      by_cases hd : v ∈ D
      · exact Or.inl ⟨hd, hva⟩
      · exact Or.inr hd
    · intro hv
      rcases hv with hv | hv
      · exact hv.2
      · intro ha
        exact hv (hA ha)
  rw [edgeCut_eq_edgesBetween, hcomp, card_edgesBetween_union_right hdisj]

end Cuts

section LocalPruning

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem edgeExpands_of_twice_card_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {h : ℝ} (hG : EdgeExpands G h) {S : Finset V}
    (hS : 2 * S.card ≤ Fintype.card V) :
    h * (S.card : ℝ) ≤ ((EdgeCut G S).card : ℝ) := by
  have hcomp : (Finset.univ \ S).card = Fintype.card V - S.card := by
    rw [Finset.card_sdiff]
    simp
  have hle : S.card ≤ (Finset.univ \ S).card := by omega
  have hleR : (S.card : ℝ) ≤ ((Finset.univ \ S).card : ℝ) := by
    exact_mod_cast hle
  simpa [min_eq_left hleR] using hG S

/-- Local pruning in a finite graph of maximum degree three.  A prescribed sufficiently small
set can be enlarged so that its complement retains expansion `h / 2`, while every subset of the
newly added vertices sends at least `h / 4` edges into the rest of the deleted set. -/
theorem exists_localPruningSet (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ)
    (D₀ : Finset V) (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3)
    (hG : EdgeExpands G h) (hh : 0 < h) (hh_one : h ≤ 1)
    (hD₀ : (D₀.card : ℝ) ≤ h ^ 2 * (Fintype.card V : ℝ) / 144) :
    ∃ D : Finset V,
      D₀ ⊆ D ∧
      (D.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 ∧
      (D.card : ℝ) ≤ 6 * (D₀.card : ℝ) / h ∧
      EdgeExpandsOn G (Finset.univ \ D) (h / 2) ∧
      ∀ A : Finset V, A ⊆ D \ D₀ →
        (h / 4) * (A.card : ℝ) ≤ ((EdgesBetween G A (D \ A)).card : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  let potential : Finset V → ℝ := fun S => ((EdgeCut G S).card : ℝ) - (h / 2) * S.card
  let candidates : Finset (Finset V) :=
    Finset.univ.powerset.filter fun S => D₀ ⊆ S ∧ 2 * S.card ≤ Fintype.card V
  have hn : 0 ≤ n := by positivity
  have hh_sq : h ^ 2 ≤ 1 := by nlinarith
  have hD₀halfR : (2 : ℝ) * D₀.card ≤ n := by
    have hsqn : h ^ 2 * n ≤ n := by nlinarith
    dsimp [n] at hsqn ⊢
    linarith
  have hD₀half : 2 * D₀.card ≤ Fintype.card V := by
    have hcast := hD₀halfR
    dsimp [n] at hcast
    exact_mod_cast hcast
  have hcandidates : candidates.Nonempty := by
    refine ⟨D₀, ?_⟩
    simp [candidates, hD₀half]
  obtain ⟨D, hDcand, hDmin⟩ := Finset.exists_min_image candidates potential hcandidates
  have hDcand' : D₀ ⊆ D ∧ 2 * D.card ≤ Fintype.card V := by
    simpa [candidates] using hDcand
  have hminimal {E : Finset V} (hD₀E : D₀ ⊆ E)
      (hEhalf : 2 * E.card ≤ Fintype.card V) : potential D ≤ potential E := by
    apply hDmin E
    simp [candidates, hD₀E, hEhalf]
  have hcutD : h * (D.card : ℝ) ≤ ((EdgeCut G D).card : ℝ) :=
    edgeExpands_of_twice_card_le hG hDcand'.2
  have hcutD₀ : ((EdgeCut G D₀).card : ℝ) ≤ 3 * (D₀.card : ℝ) := by
    rw [edgeCut_eq_edgesBetween]
    exact_mod_cast card_edgesBetween_le_three_mul_card hdeg D₀ (Finset.univ \ D₀)
  have hpot : potential D ≤ potential D₀ := hminimal (fun _ hmem => hmem) hD₀half
  have hDmul : h * (D.card : ℝ) ≤ 6 * (D₀.card : ℝ) := by
    dsimp [potential] at hpot
    have hnonneg : 0 ≤ h * (D₀.card : ℝ) := by positivity
    nlinarith
  have hDquot : (D.card : ℝ) ≤ 6 * (D₀.card : ℝ) / h := by
    rw [le_div_iff₀ hh]
    nlinarith
  have hDsmall : (D.card : ℝ) ≤ h * n / 24 := by
    have h6 : 6 * (D₀.card : ℝ) ≤ h ^ 2 * n / 24 := by
      dsimp [n]
      linarith
    have hmul := hDmul.trans h6
    nlinarith
  have hDhalfR : (D.card : ℝ) ≤ n / 2 := by
    have hcast : (2 : ℝ) * D.card ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hDcand'.2
    dsimp [n]
    linarith
  let H := Finset.univ \ D
  have hHsmall : ∀ A : Finset V, A ⊆ H → 2 * A.card ≤ H.card →
      (h / 2) * (A.card : ℝ) ≤ ((EdgesBetween G A (H \ A)).card : ℝ) := by
    intro A hAH hAhalf
    have hDA : Disjoint D A := by
      rw [Finset.disjoint_left]
      exact fun v hvD hvA => (Finset.mem_sdiff.mp (hAH hvA)).2 hvD
    have hcardUnion : (D ∪ A).card = D.card + A.card :=
      Finset.card_union_of_disjoint hDA
    by_cases hfeasible : 2 * (D ∪ A).card ≤ Fintype.card V
    · have hD₀union : D₀ ⊆ D ∪ A := fun v hv => Finset.mem_union_left A (hDcand'.1 hv)
      have hminUnion := hminimal hD₀union hfeasible
      have hadd := edgeCut_addition_identity (G := G) hAH
      have hcardReal : ((D ∪ A).card : ℝ) = D.card + A.card := by
        exact_mod_cast hcardUnion
      dsimp [potential] at hminUnion
      change (h / 2) * (A.card : ℝ) ≤
        ((EdgesBetween G A ((Finset.univ \ D) \ A)).card : ℝ)
      have haddR : ((EdgeCut G (D ∪ A)).card : ℝ) + (EdgesBetween G D A).card =
          (EdgeCut G D).card + (EdgesBetween G A ((Finset.univ \ D) \ A)).card := by
        exact_mod_cast hadd
      rw [hcardReal] at hminUnion
      nlinarith [show (0 : ℝ) ≤ (EdgesBetween G D A).card by positivity]
    · have hlargeNat : Fintype.card V < 2 * (D.card + A.card) := by
        rw [hcardUnion] at hfeasible
        omega
      have hlarge : n < 2 * ((D.card : ℝ) + A.card) := by
        dsimp [n]
        exact_mod_cast hlargeNat
      have hAglobal : 2 * A.card ≤ Fintype.card V := by
        have hHcard : H.card = Fintype.card V - D.card := by
          dsimp [H]
          rw [Finset.card_sdiff]
          simp
        omega
      have hglobal := edgeExpands_of_twice_card_le hG hAglobal
      have hcutA := edgeCut_subset_identity (G := G) (D := H) hAH
      have hcompH : Finset.univ \ H = D := by
        dsimp [H]
        ext v
        simp
      rw [hcompH] at hcutA
      have hcutAR : ((EdgeCut G A).card : ℝ) =
          (EdgesBetween G A (H \ A)).card + (EdgesBetween G A D).card := by
        exact_mod_cast hcutA
      have hdegree : ((EdgesBetween G A D).card : ℝ) ≤ 3 * (D.card : ℝ) := by
        exact_mod_cast card_edgesBetween_le_three_mul_card_right hdeg A D
      by_contra hbad
      push Not at hbad
      have hupper : h * (A.card : ℝ) < 6 * (D.card : ℝ) := by
        rw [hcutAR] at hglobal
        nlinarith
      have h24 : 24 * (D.card : ℝ) ≤ h * n := by nlinarith
      have hmulLarge : h * n < 2 * h * (D.card : ℝ) + 2 * h * (A.card : ℝ) := by
        nlinarith
      have hd1 : h * (D.card : ℝ) ≤ D.card := by nlinarith
      have hlower : 11 * (D.card : ℝ) < h * (A.card : ℝ) := by nlinarith
      nlinarith
  have hHexpand : EdgeExpandsOn G H (h / 2) := by
    intro A hAH
    by_cases hside : A.card ≤ (H \ A).card
    · rw [min_eq_left (by exact_mod_cast hside)]
      apply hHsmall A hAH
      have hHcard : H.card = A.card + (H \ A).card := by
        have hpartition := Finset.card_sdiff_add_card_eq_card hAH
        omega
      omega
    · let B := H \ A
      have hBH : B ⊆ H := Finset.sdiff_subset
      have hBA : 2 * B.card ≤ H.card := by
        have hpartition := Finset.card_sdiff_add_card_eq_card hAH
        have hBcard : B.card = (H \ A).card := rfl
        omega
      have hsmallB := hHsmall B hBH hBA
      have hHB : H \ B = A := by
        dsimp [B]
        ext v
        simp only [Finset.mem_sdiff]
        constructor
        · intro hv
          by_contra hva
          exact hv.2 ⟨hv.1, hva⟩
        · exact fun hva => ⟨hAH hva, fun hv => hv.2 hva⟩
      rw [hHB] at hsmallB
      rw [min_eq_right (by exact_mod_cast le_of_not_ge hside)]
      rw [card_edgesBetween_comm]
      exact hsmallB
  refine ⟨D, hDcand'.1, ?_, hDquot, ?_, ?_⟩
  · simpa [n] using hDhalfR
  · simpa [H] using hHexpand
  · intro A hA
    have hAD : A ⊆ D := fun v hv => (Finset.mem_sdiff.mp (hA hv)).1
    have hD₀remove : D₀ ⊆ D \ A := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨hDcand'.1 hv, fun hav => (Finset.mem_sdiff.mp (hA hav)).2 hv⟩
    have hremoveHalf : 2 * (D \ A).card ≤ Fintype.card V := by
      have hcardle : (D \ A).card ≤ D.card := Finset.card_le_card Finset.sdiff_subset
      omega
    have hminRemove := hminimal hD₀remove hremoveHalf
    have hremove := edgeCut_removal_identity (G := G) hAD
    have hsubset := edgeCut_subset_identity (G := G) hAD
    have hcardDA : D.card = (D \ A).card + A.card := by
      rw [← Finset.card_sdiff_add_card_eq_card hAD]
    have hAhalf : 2 * A.card ≤ Fintype.card V := by
      have hacard : A.card ≤ D.card := Finset.card_le_card hAD
      omega
    have hglobal := edgeExpands_of_twice_card_le hG hAhalf
    have hremoveR : ((EdgeCut G D).card : ℝ) + (EdgesBetween G A (D \ A)).card =
        (EdgeCut G (D \ A)).card + (EdgesBetween G A (Finset.univ \ D)).card := by
      exact_mod_cast hremove
    have hsubsetR : ((EdgeCut G A).card : ℝ) =
        (EdgesBetween G A (D \ A)).card +
          (EdgesBetween G A (Finset.univ \ D)).card := by
      exact_mod_cast hsubset
    have hcardDAR : (D.card : ℝ) = (D \ A).card + A.card := by exact_mod_cast hcardDA
    dsimp [potential] at hminRemove
    rw [hcardDAR] at hminRemove
    rw [hsubsetR] at hglobal
    have hdiff : ((EdgesBetween G A (Finset.univ \ D)).card : ℝ) ≤
        (EdgesBetween G A (D \ A)).card + (h / 2) * A.card := by
      linarith [hremoveR]
    linarith

/-- Ground-truth check for `EdgesBetween`: the complete graph on two vertices has one oriented
edge from `{0}` to `{1}`. -/
example : EdgesBetween (⊤ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2)) ({1} : Finset (Fin 2)) =
    ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by decide

/-- Ground-truth check that positive expansion on a nontrivial survivor is not vacuous. -/
example : ¬ EdgeExpandsOn (⊥ : SimpleGraph (Fin 2)) (Finset.univ : Finset (Fin 2)) 1 := by
  intro hexp
  have h := hexp ({0} : Finset (Fin 2)) (Finset.subset_univ _)
  have hedge : EdgesBetween (⊥ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2))
      (Finset.univ \ ({0} : Finset (Fin 2))) = ∅ := by decide
  have hcard : ({0} : Finset (Fin 2)).card = 1 := by decide
  have hcomp : (Finset.univ \ ({0} : Finset (Fin 2))).card = 1 := by decide
  rw [hedge, hcard, hcomp] at h
  norm_num at h

/-- Joint satisfiability check for every hypothesis of `exists_localPruningSet`: the complete graph
on two vertices, expansion parameter one, and an empty prescribed set satisfy the assumptions and
therefore instantiate the theorem's full conclusion. -/
example :
    ∃ D : Finset (Fin 2),
      (∅ : Finset (Fin 2)) ⊆ D ∧
      (D.card : ℝ) ≤ (Fintype.card (Fin 2) : ℝ) / 2 ∧
      (D.card : ℝ) ≤ 6 * ((∅ : Finset (Fin 2)).card : ℝ) / 1 ∧
      EdgeExpandsOn (⊤ : SimpleGraph (Fin 2)) (Finset.univ \ D) (1 / 2) ∧
      ∀ A : Finset (Fin 2), A ⊆ D \ (∅ : Finset (Fin 2)) →
        (1 / 4 : ℝ) * (A.card : ℝ) ≤
          ((EdgesBetween (⊤ : SimpleGraph (Fin 2)) A (D \ A)).card : ℝ) := by
  apply exists_localPruningSet (⊤ : SimpleGraph (Fin 2)) 1 ∅
  · intro v
    fin_cases v <;> decide
  · intro S
    have hle : S.card ≤ 2 := by
      simpa using Finset.card_le_univ S
    have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
      subst S
      norm_num [EdgeCut]
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      fin_cases v
      · change 1 * min (({0} : Finset (Fin 2)).card : ℝ)
          ((Finset.univ \ ({0} : Finset (Fin 2))).card : ℝ) ≤
            ((EdgeCut (⊤ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2))).card : ℝ)
        have hcomp : (Finset.univ \ ({0} : Finset (Fin 2))).card = 1 := by decide
        have hcut : (EdgeCut (⊤ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2))).card = 1 := by
          decide
        rw [hcomp, hcut]
        norm_num
      · change 1 * min (({1} : Finset (Fin 2)).card : ℝ)
          ((Finset.univ \ ({1} : Finset (Fin 2))).card : ℝ) ≤
            ((EdgeCut (⊤ : SimpleGraph (Fin 2)) ({1} : Finset (Fin 2))).card : ℝ)
        have hcomp : (Finset.univ \ ({1} : Finset (Fin 2))).card = 1 := by decide
        have hcut : (EdgeCut (⊤ : SimpleGraph (Fin 2)) ({1} : Finset (Fin 2))).card = 1 := by
          decide
        rw [hcomp, hcut]
        norm_num
    · have hS : S = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simpa using htwo.ge)
      subst S
      norm_num [EdgeCut]
  · norm_num
  · norm_num
  · norm_num

end LocalPruning

end Erdos64
