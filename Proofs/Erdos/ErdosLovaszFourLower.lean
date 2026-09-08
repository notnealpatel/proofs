import Erdos.CoveringNumber

set_option autoImplicit false

/-!
# The lower bound for the fourth Erdős–Lovász number

Primary source: A. Tripathi, *A result on intersecting families with maximum
transversal size*, arXiv:1409.4610, §2, Theorem 2.1.
https://arxiv.org/abs/1409.4610

The canonical TeX was retrieved with `tool_arxiv`; the historical
`References/Erdos/arXiv-1409-4610/paper.tex` pointer in the main file is absent
from this checkout. No reference artifact is modified by this proof.

This proof follows the source's degree-three-vertex reduction, but neither
assumes minimality nor invokes its uniqueness assertion for the five-edge
family. Incidence counting proves directly that the residual family is
2-regular on ten vertices. The three edges through the removed vertex use
nine different residual vertices. There are consequently ten degree-three
vertices and one further vertex. Any two degree-three vertices must occur
together, otherwise pairing the remaining edges gives a three-point cover.
A degree-three vertex adjacent to the further vertex would therefore have
ten different neighbours in three four-element edges, which have room for
only nine. This last local count replaces the source's global pair count.

All ground types are allowed, without a finite-ground-set bound. The
nonexistence conclusion is derived from the actual uniformity, intersection,
and no-small-cover hypotheses; no finite enumeration or archived result is
used. The joint satisfiability check using `witnessFour` is in the importing
`Erdos.ErdosLovasz` module, beside its lower-bound bridge.
-/

namespace ErdosLovaszFourLower

private theorem pair_cover {α : Type*} (F : Finset (Finset α)) (k : ℕ)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) (hc : F.card ≤ 2 * k) :
    ∃ T : Finset α, T.card ≤ k ∧ IsTransversal F T := by
  classical
  induction k generalizing F with
  | zero =>
      have hF : F = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨∅, by simp, hF ▸ isTransversal_empty_left ∅⟩
  | succ k ih =>
      by_cases htwo : 2 ≤ F.card
      · obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp htwo
        obtain ⟨x, hxA, hxB⟩ := Finset.not_disjoint_iff.mp (hint A hA B hB)
        let G := (F.erase A).erase B
        have hsub : G ⊆ F := fun C hC =>
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
        have hcG : G.card ≤ 2 * k := by
          have heA := Finset.card_erase_of_mem hA
          have heB := Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hAB.symm, hB⟩)
          change ((F.erase A).erase B).card ≤ 2 * k
          omega
        obtain ⟨T, hcT, hT⟩ := ih G (fun C hC D hD => hint C (hsub hC) D (hsub hD)) hcG
        refine ⟨insert x T, (Finset.card_insert_le x T).trans (by omega), ?_⟩
        intro C hC
        by_cases hCA : C = A
        · exact ⟨x, hCA ▸ hxA, Finset.mem_insert_self x T⟩
        by_cases hCB : C = B
        · exact ⟨x, hCB ▸ hxB, Finset.mem_insert_self x T⟩
        obtain ⟨y, hyC, hyT⟩ := hT C
          (Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hC⟩⟩)
        exact ⟨y, hyC, Finset.mem_insert_of_mem hyT⟩
      · by_cases hF : F.Nonempty
        · obtain ⟨A, hA⟩ := hF
          obtain ⟨x, hxA, _⟩ := Finset.not_disjoint_iff.mp (hint A hA A hA)
          refine ⟨{x}, by simp, ?_⟩
          intro B hB
          have hBA : B = A := (Finset.card_le_one.mp (show F.card ≤ 1 by omega)) B hB A hA
          exact ⟨x, hBA ▸ hxA, Finset.mem_singleton_self x⟩
        · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
          exact ⟨∅, by simp, he ▸ isTransversal_empty_left ∅⟩

private theorem incidence {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U : Finset α) :
    (∑ x ∈ U, (F.filter (fun A => x ∈ A)).card) =
      ∑ A ∈ F, (U ∩ A).card := by
  simp only [← Finset.filter_mem_eq_inter, Finset.card_filter]
  exact Finset.sum_comm

private theorem edge_incidence {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (A : Finset α) (hA : A ∈ F) :
    F.card + A.card ≤ (∑ x ∈ A, (F.filter (fun B => x ∈ B)).card) + 1 := by
  rw [incidence, ← Finset.sum_erase_add _ _ hA]
  have hlow : (F.erase A).card ≤ ∑ B ∈ F.erase A, (A ∩ B).card := by
    calc (F.erase A).card = ∑ _B ∈ F.erase A, 1 := by simp
      _ ≤ ∑ B ∈ F.erase A, (A ∩ B).card := Finset.sum_le_sum fun B hB =>
        Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp
          (hint A hA B (Finset.mem_of_mem_erase hB)))
  have he := Finset.card_erase_of_mem hA
  rw [Finset.inter_self]
  omega

private theorem residual_gt {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (hcover : ∀ T : Finset α, IsTransversal F T → 4 ≤ T.card)
    (S : Finset α) (k : ℕ) (hsk : S.card + k < 4) :
    2 * k < (F.filter (fun A => Disjoint A S)).card := by
  by_contra hsmall
  let G := F.filter (fun A => Disjoint A S)
  have hsub : G ⊆ F := Finset.filter_subset _ _
  obtain ⟨T, hcT, hT⟩ := pair_cover G k
    (fun A hA B hB => hint A (hsub hA) B (hsub hB)) (by dsimp [G]; omega)
  have hST : IsTransversal F (S ∪ T) := by
    intro A hA
    by_cases hAS : Disjoint A S
    · obtain ⟨x, hxA, hxT⟩ := hT A (Finset.mem_filter.mpr ⟨hA, hAS⟩)
      exact ⟨x, hxA, Finset.mem_union_right S hxT⟩
    · obtain ⟨x, hxA, hxS⟩ := Finset.not_disjoint_iff.mp hAS
      exact ⟨x, hxA, Finset.mem_union_left T hxS⟩
  have hcST := hcover (S ∪ T) hST
  have hle := Finset.card_union_le S T
  omega

/-- An intersecting family of four-element sets with no cover of size less
than four has at least nine members. The argument is uniform in the ground
type and uses only finite incidence counts, not a bounded search. -/
theorem nine_le_card {α : Type*} (F : Finset (Finset α))
    (hsize : ∀ A ∈ F, A.card = 4)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (hcover : ∀ T : Finset α, IsTransversal F T → 4 ≤ T.card) :
    9 ≤ F.card := by
  classical
  by_contra hlarge
  have hm : F.card ≤ 8 := by omega
  have hseven : 7 ≤ F.card := by
    have hres := residual_gt F hint hcover ∅ 3 (by simp)
    exact Nat.succ_le_of_lt (by simpa using hres)
  have havoid (x : α) : 5 ≤ (F.filter (fun A => x ∉ A)).card := by
    have hres := residual_gt F hint hcover {x} 2 (by simp)
    exact Nat.succ_le_of_lt (by simpa using hres)
  have havoid₂ (x y : α) : 3 ≤ (F.filter (fun A => x ∉ A ∧ y ∉ A)).card := by
    have hpair : ({x, y} : Finset α).card ≤ 2 := by
      simpa using Finset.card_insert_le x ({y} : Finset α)
    have hres := residual_gt F hint hcover {x, y} 1 (by omega)
    exact Nat.succ_le_of_lt (by
      simpa only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] using hres)
  let d := fun x : α => (F.filter (fun A => x ∈ A)).card
  have hsplit (x : α) : d x + (F.filter (fun A => x ∉ A)).card = F.card :=
    Finset.card_filter_add_card_filter_not (fun A => x ∈ A)
  have hdeg (x : α) : d x ≤ 3 := by
    have ha := havoid x
    have hs := hsplit x
    omega
  obtain ⟨A₀, hA₀⟩ : F.Nonempty := Finset.card_pos.mp (by omega)
  have hA₀card := hsize A₀ hA₀
  have hinc := edge_incidence F hint A₀ hA₀
  obtain ⟨x, hxA₀, hx⟩ : ∃ x ∈ A₀, d x = 3 := by
    by_contra hnone
    push Not at hnone
    have hle : ∑ x ∈ A₀, d x ≤ 8 := by
      calc ∑ x ∈ A₀, d x ≤ ∑ _x ∈ A₀, 2 := Finset.sum_le_sum fun x hxA => by
              have hdx := hdeg x
              have hne := hnone x hxA
              omega
        _ = 8 := by simp [hA₀card]
    change F.card + A₀.card ≤ (∑ x ∈ A₀, d x) + 1 at hinc
    omega
  let G := F.filter (fun A => x ∉ A)
  have hGsub : G ⊆ F := Finset.filter_subset _ _
  have hGcard : G.card = 5 := by
    have ha := havoid x
    have hs := hsplit x
    dsimp [G]
    omega
  have hm8 : F.card = 8 := by
    have hs := hsplit x
    change d x + G.card = F.card at hs
    omega
  have hGint : ∀ A ∈ G, ∀ B ∈ G, ¬ Disjoint A B :=
    fun A hA B hB => hint A (hGsub hA) B (hGsub hB)
  have hGcover (T : Finset α) (hT : IsTransversal G T) : 3 ≤ T.card := by
    have hext : IsTransversal F (insert x T) := by
      intro A hA
      by_cases hxA : x ∈ A
      · exact ⟨x, hxA, Finset.mem_insert_self x T⟩
      · obtain ⟨y, hyA, hyT⟩ := hT A (Finset.mem_filter.mpr ⟨hA, hxA⟩)
        exact ⟨y, hyA, Finset.mem_insert_of_mem hyT⟩
    have hl := hcover (insert x T) hext
    have hu := Finset.card_insert_le x T
    omega
  have hGdeg (y : α) : (G.filter (fun A => y ∈ A)).card ≤ 2 := by
    have hs := Finset.card_filter_add_card_filter_not (s := G) (fun A => y ∈ A)
    have ha := havoid₂ x y
    have he : G.filter (fun A => y ∉ A) = F.filter (fun A => x ∉ A ∧ y ∉ A) := by
      ext A
      simp only [G, Finset.mem_filter, and_assoc]
    rw [he] at hs
    omega
  let U := G.biUnion id
  have hGU (A : Finset α) (hA : A ∈ G) : A ⊆ U := by
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨A, hA, hy⟩
  have hxU : x ∉ U := by
    intro hxmem
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hxmem
    exact (Finset.mem_filter.mp hA).2 hxA
  have hGtwo (y : α) (hy : y ∈ U) : (G.filter (fun A => y ∈ A)).card = 2 := by
    obtain ⟨A, hA, hyA⟩ := Finset.mem_biUnion.mp hy
    change y ∈ A at hyA
    have hAc := hsize A (hGsub hA)
    have hlow := edge_incidence G hGint A hA
    have hrest : ∑ z ∈ A.erase y, (G.filter (fun B => z ∈ B)).card ≤ 6 := by
      calc ∑ z ∈ A.erase y, (G.filter (fun B => z ∈ B)).card
          ≤ ∑ _z ∈ A.erase y, 2 := Finset.sum_le_sum fun z _ => hGdeg z
        _ = 6 := by simp [Finset.card_erase_of_mem hyA, hAc]
    have hsum := Finset.sum_erase_add A
      (fun z => (G.filter (fun B => z ∈ B)).card) hyA
    have hdy := hGdeg y
    omega
  have hUcard : U.card = 10 := by
    have hcount := incidence G U
    have hl : (∑ y ∈ U, (G.filter (fun A => y ∈ A)).card) = U.card * 2 := by
      calc (∑ y ∈ U, (G.filter (fun A => y ∈ A)).card) = ∑ _y ∈ U, 2 :=
          Finset.sum_congr rfl hGtwo
        _ = U.card * 2 := by simp
    have hr : (∑ A ∈ G, (U ∩ A).card) = 20 := by
      calc
        (∑ A ∈ G, (U ∩ A).card) = ∑ _A ∈ G, 4 := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [Finset.inter_eq_right.mpr (hGU A hA), hsize A (hGsub hA)]
        _ = 20 := by simp [hGcard]
    omega
  let H := F.filter (fun A => x ∈ A)
  have hHcard : H.card = 3 := hx
  have hHsub : H ⊆ F := Finset.filter_subset _ _
  have hHerase (A : Finset α) (hA : A ∈ H) : (A.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hA).2, hsize A (hHsub hA)]
  have hHU (A : Finset α) (hA : A ∈ H) : A.erase x ⊆ U := by
    have ht : IsTransversal G ((A.erase x) ∩ U) := by
      intro B hB
      obtain ⟨y, hyB, hyA⟩ := Finset.not_disjoint_iff.mp (hint B (hGsub hB) A (hHsub hA))
      have hyx : y ≠ x := fun he => (Finset.mem_filter.mp hB).2 (he ▸ hyB)
      exact ⟨y, hyB, Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨hyx, hyA⟩, hGU B hB hyB⟩⟩
    have hcard := hGcover ((A.erase x) ∩ U) ht
    have he : (A.erase x) ∩ U = A.erase x :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hHerase A hA]; exact hcard)
    exact Finset.inter_eq_left.mp he
  have hsplitHG (y : α) :
      (H.filter (fun A => y ∈ A)).card + (G.filter (fun A => y ∈ A)).card = d y := by
    have hs := Finset.card_filter_add_card_filter_not
      (s := F.filter (fun A => y ∈ A)) (fun A => x ∈ A)
    simpa only [H, G, d, Finset.filter_filter, and_comm] using hs
  have hHone (y : α) (hy : y ∈ U) : (H.filter (fun A => y ∈ A)).card ≤ 1 := by
    have hs := hsplitHG y
    have ht := hGtwo y hy
    have hd := hdeg y
    omega
  let T := H.biUnion (fun A => A.erase x)
  have hTU : T ⊆ U := by
    intro y hy
    obtain ⟨A, hA, hyA⟩ := Finset.mem_biUnion.mp hy
    exact hHU A hA hyA
  have hTcard : T.card = 9 := by
    have hdj : (H : Set (Finset α)).PairwiseDisjoint (fun A => A.erase x) := by
      intro A hA B hB hAB
      apply Finset.disjoint_left.mpr
      intro y hyA hyB
      have hyU := hHU A hA hyA
      have hsmall := Finset.card_le_one.mp (hHone y hyU)
      exact hAB (hsmall A (Finset.mem_filter.mpr ⟨hA, Finset.mem_of_mem_erase hyA⟩)
        B (Finset.mem_filter.mpr ⟨hB, Finset.mem_of_mem_erase hyB⟩))
    calc T.card = ∑ A ∈ H, (A.erase x).card := Finset.card_biUnion hdj
      _ = ∑ _A ∈ H, 3 := Finset.sum_congr rfl hHerase
      _ = 9 := by simp [hHcard]
  have hTthree (y : α) (hy : y ∈ T) : d y = 3 := by
    obtain ⟨A, hA, hyA⟩ := Finset.mem_biUnion.mp hy
    have hp : 0 < (H.filter (fun A => y ∈ A)).card := Finset.card_pos.mpr
      ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.mem_of_mem_erase hyA⟩⟩
    have hs := hsplitHG y
    have ht := hGtwo y (hHU A hA hyA)
    have hd := hdeg y
    omega
  have hcooccur (p q : α) (hp : d p = 3) (hq : d q = 3) :
      ∃ A ∈ F, p ∈ A ∧ q ∈ A := by
    by_contra hno
    have hnq (A : Finset α) (hA : A ∈ F) (hpA : p ∈ A) : q ∉ A :=
      fun hqA => hno ⟨A, hA, hpA, hqA⟩
    have he₁ : (F.filter (fun A => q ∉ A)).filter (fun A => p ∈ A) =
        F.filter (fun A => p ∈ A) := by
      ext A
      simp only [Finset.mem_filter]
      constructor
      · exact fun hA => ⟨hA.1.1, hA.2⟩
      · exact fun hA => ⟨⟨hA.1, hnq A hA.1 hA.2⟩, hA.2⟩
    have he₂ : (F.filter (fun A => q ∉ A)).filter (fun A => p ∉ A) =
        F.filter (fun A => p ∉ A ∧ q ∉ A) := by
      simp only [Finset.filter_filter, and_comm]
    have hs := Finset.card_filter_add_card_filter_not
      (s := F.filter (fun A => q ∉ A)) (fun A => p ∈ A)
    rw [he₁, he₂] at hs
    change d p + (F.filter (fun A => p ∉ A ∧ q ∉ A)).card =
      (F.filter (fun A => q ∉ A)).card at hs
    have hqsplit := hsplit q
    have ha := havoid₂ p q
    omega
  let D := insert x T
  have hxT : x ∉ T := fun hmem => hxU (hTU hmem)
  have hDcard : D.card = 10 := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem hxT, hTcard]
  have hDthree (y : α) (hy : y ∈ D) : d y = 3 := by
    rcases Finset.mem_insert.mp hy with rfl | hyT
    · exact hx
    · exact hTthree y hyT
  have hdiffcard : (U \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTU, hUcard, hTcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiffcard
  have hzmem : z ∈ U \ T := by rw [hz]; exact Finset.mem_singleton_self z
  have hzU : z ∈ U := (Finset.mem_sdiff.mp hzmem).1
  have hzT : z ∉ T := (Finset.mem_sdiff.mp hzmem).2
  have hzx : z ≠ x := fun he => hxU (he ▸ hzU)
  have hzD : z ∉ D := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with he | ht
    · exact hzx he
    · exact hzT ht
  obtain ⟨E, hE, hzE⟩ := Finset.mem_biUnion.mp hzU
  change z ∈ E at hzE
  have hEc := hsize E (hGsub hE)
  have hEerase : (E.erase z).card = 3 := by rw [Finset.card_erase_of_mem hzE, hEc]
  obtain ⟨a, ha⟩ : (E.erase z).Nonempty := Finset.card_pos.mp (by omega)
  have haz : a ≠ z := (Finset.mem_erase.mp ha).1
  have haE : a ∈ E := Finset.mem_of_mem_erase ha
  have haT : a ∈ T := by
    by_contra haT
    have hadiff : a ∈ U \ T := Finset.mem_sdiff.mpr ⟨hGU E hE haE, haT⟩
    rw [hz] at hadiff
    exact haz (Finset.mem_singleton.mp hadiff)
  have haD : a ∈ D := Finset.mem_insert_of_mem haT
  have hda : d a = 3 := hDthree a haD
  let K := F.filter (fun A => a ∈ A)
  let W := K.biUnion (fun A => A.erase a)
  have hKcard : K.card = 3 := hda
  have hWcard : W.card ≤ 9 := by
    calc W.card ≤ ∑ A ∈ K, (A.erase a).card := Finset.card_biUnion_le
      _ = ∑ _A ∈ K, 3 := by
        apply Finset.sum_congr rfl
        intro A hA
        obtain ⟨hAF, haA⟩ := Finset.mem_filter.mp hA
        rw [Finset.card_erase_of_mem haA, hsize A hAF]
      _ = 9 := by simp [hKcard]
  have hWsub : insert z (D.erase a) ⊆ W := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbD
    · exact Finset.mem_biUnion.mpr ⟨E, Finset.mem_filter.mpr ⟨hGsub hE, haE⟩,
        Finset.mem_erase.mpr ⟨haz.symm, hzE⟩⟩
    · obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hbD
      obtain ⟨A, hA, haA, hbA⟩ := hcooccur a b hda (hDthree b hb)
      exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, haA⟩,
        Finset.mem_erase.mpr ⟨hba, hbA⟩⟩
  have hten : (insert z (D.erase a)).card = 10 := by
    rw [Finset.card_insert_of_notMem (fun hzmem => hzD (Finset.mem_of_mem_erase hzmem)),
      Finset.card_erase_of_mem haD, hDcard]
  have hfinal := Finset.card_le_card hWsub
  omega

#check @nine_le_card
#print axioms nine_le_card

end ErdosLovaszFourLower
