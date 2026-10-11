import Erdos.CoveringNumber

set_option autoImplicit false

/-! # Classical Erdős–Lovász incidence and peeling bound

The argument removes vertices of degree at least four, then uses degree-three
removal and pairing in the residual intersecting family. Edges are deleted,
never shrunk. All estimates are integral until the consumer's final cast.
-/

namespace ErdosLovaszLower


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


private theorem degree_mono {α : Type*} [DecidableEq α]
    {G F : Finset (Finset α)} (hsub : G ⊆ F) (x : α) :
    (G.filter (fun A => x ∈ A)).card ≤ (F.filter (fun A => x ∈ A)).card := by
  apply Finset.card_le_card
  intro A hA
  obtain ⟨hAG, hxA⟩ := Finset.mem_filter.mp hA
  exact Finset.mem_filter.mpr ⟨hsub hAG, hxA⟩

private theorem extend_cover {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) (T : Finset α)
    (hT : IsTransversal (F.filter (fun A => x ∉ A)) T) :
    IsTransversal F (insert x T) := by
  intro A hA
  by_cases hxA : x ∈ A
  · exact ⟨x, hxA, Finset.mem_insert_self x T⟩
  · obtain ⟨y, hyA, hyT⟩ := hT A (Finset.mem_filter.mpr ⟨hA, hxA⟩)
    exact ⟨y, hyA, Finset.mem_insert_of_mem hyT⟩

/-- An intersecting uniform family of maximum vertex degree three admits
 a cover `T` with `6 |T| ≤ 2 |F| + n + 4`. The empty family is allowed. -/
theorem bounded_degree_cover {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset (Finset α))
    (hsize : ∀ A ∈ F, A.card = n)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (hdeg : ∀ x : α, (F.filter (fun A => x ∈ A)).card ≤ 3) :
    ∃ T : Finset α, IsTransversal F T ∧ 6 * T.card ≤ 2 * F.card + n + 4 := by
  classical
  induction hm : F.card using Nat.strong_induction_on generalizing F with
  | h m ih =>
    by_cases hsmall : F.card ≤ n + 1
    · obtain ⟨T, hcT, hT⟩ := pair_cover F ((F.card + 1) / 2) hint (by omega)
      refine ⟨T, hT, ?_⟩
      omega
    · obtain ⟨A, hA⟩ : F.Nonempty := Finset.card_pos.mp (by omega)
      have hcA := hsize A hA
      have hinc := edge_incidence F hint A hA
      obtain ⟨x, hxA, hx⟩ : ∃ x ∈ A, (F.filter (fun B => x ∈ B)).card = 3 := by
        by_contra hnone
        push Not at hnone
        have hsum : (∑ x ∈ A, (F.filter (fun B => x ∈ B)).card) ≤ 2 * n := by
          calc
            _ ≤ ∑ _x ∈ A, 2 := Finset.sum_le_sum fun x hxA => by
              have hd := hdeg x
              have hne := hnone x hxA
              omega
            _ = 2 * n := by simp [hcA, Nat.mul_comm]
        omega
      let G := F.filter (fun B => x ∉ B)
      have hsub : G ⊆ F := Finset.filter_subset _ _
      have hsplit : 3 + G.card = F.card := by
        have hs := Finset.card_filter_add_card_filter_not (s := F) (fun B => x ∈ B)
        simpa only [hx] using hs
      have hlt : G.card < m := by omega
      obtain ⟨T, hT, hcT⟩ := ih G.card hlt G
        (fun B hB => hsize B (hsub hB))
        (fun B hB C hC => hint B (hsub hB) C (hsub hC))
        (fun y => (degree_mono hsub y).trans (hdeg y)) rfl
      refine ⟨insert x T, extend_cover F x T hT, ?_⟩
      have hi := Finset.card_insert_le x T
      omega

private theorem peel {α : Type*} [DecidableEq α] (F : Finset (Finset α)) :
    ∃ (S : Finset α) (J : Finset (Finset α)),
      J ⊆ F ∧ 4 * S.card + J.card ≤ F.card ∧
      (∀ x : α, (J.filter (fun A => x ∈ A)).card ≤ 3) ∧
      (∀ T : Finset α, IsTransversal J T → IsTransversal F (S ∪ T)) := by
  classical
  induction hm : F.card using Nat.strong_induction_on generalizing F with
  | h m ih =>
    by_cases hdeg : ∀ x : α, (F.filter (fun A => x ∈ A)).card ≤ 3
    · refine ⟨∅, F, Finset.Subset.refl F, by simp [hm], hdeg, ?_⟩
      intro T hT
      simpa using hT
    · push Not at hdeg
      obtain ⟨x, hx⟩ := hdeg
      let G := F.filter (fun A => x ∉ A)
      have hsub : G ⊆ F := Finset.filter_subset _ _
      have hsplit : (F.filter (fun A => x ∈ A)).card + G.card = F.card :=
        Finset.card_filter_add_card_filter_not (fun A => x ∈ A)
      have hlt : G.card < m := by omega
      obtain ⟨S, J, hJG, hcard, hJdeg, hcover⟩ := ih G.card hlt G rfl
      refine ⟨insert x S, J, hJG.trans hsub, ?_, hJdeg, ?_⟩
      · have hi := Finset.card_insert_le x S
        omega
      · intro T hT
        have he := extend_cover F x (S ∪ T) (hcover T hT)
        simpa only [Finset.insert_union] using he

/-- Every positive-uniform intersecting family whose covers have size at
least `n` has at least `(8n-9)/3` edges, expressed without subtraction. -/
theorem eight_mul_le_three_mul_card_add_nine {α : Type*}
    (n : ℕ) (_hn : 0 < n) (F : Finset (Finset α))
    (hsize : ∀ A ∈ F, A.card = n)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (hcover : ∀ T : Finset α, IsTransversal F T → n ≤ T.card) :
    8 * n ≤ 3 * F.card + 9 := by
  classical
  obtain ⟨S, J, hsub, hcard, hdeg, hpeel⟩ := peel F
  by_cases hJ : J = ∅
  · have htrans := hpeel ∅ (hJ ▸ isTransversal_empty_left ∅)
    have hcS : n ≤ S.card := by simpa using hcover (S ∪ ∅) htrans
    have hcJ : J.card = 0 := by simp [hJ]
    omega
  · obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
    have hsizeJ : ∀ B ∈ J, B.card = n := fun B hB => hsize B (hsub hB)
    have hintJ : ∀ B ∈ J, ∀ C ∈ J, ¬ Disjoint B C :=
      fun B hB C hC => hint B (hsub hB) C (hsub hC)
    have hinc := edge_incidence J hintJ A hA
    have hcA := hsizeJ A hA
    have hsum : (∑ x ∈ A, (J.filter (fun B => x ∈ B)).card) ≤ 3 * n := by
      calc
        _ ≤ ∑ _x ∈ A, 3 := Finset.sum_le_sum fun x _ => hdeg x
        _ = 3 * n := by simp [hcA, Nat.mul_comm]
    have hq : J.card ≤ 2 * n + 1 := by omega
    obtain ⟨T, hT, hcT⟩ := bounded_degree_cover n J hsizeJ hintJ hdeg
    have hcST := hcover (S ∪ T) (hpeel T hT)
    have hUnion := Finset.card_union_le S T
    omega

-- A concrete nonempty model jointly satisfies the bounded-degree hypotheses.
example : ∃ T : Finset (Fin 1), IsTransversal ({{0}} : Finset (Finset (Fin 1))) T ∧
    6 * T.card ≤ 2 * ({{0}} : Finset (Finset (Fin 1))).card + 1 + 4 := by
  exact bounded_degree_cover 1 {{0}} (by decide) (by decide) (by decide)

-- A concrete nonempty model jointly satisfies the family-level hypotheses.
example : 8 * 1 ≤ 3 * ({{0}} : Finset (Finset (Fin 1))).card + 9 := by
  apply eight_mul_le_three_mul_card_add_nine 1 (by decide)
  · intro A hA
    have heq : A = {0} := Finset.mem_singleton.mp hA
    simp [heq]
  · intro A hA B hB
    have heqA : A = {0} := Finset.mem_singleton.mp hA
    have heqB : B = {0} := Finset.mem_singleton.mp hB
    simp [heqA, heqB]
  · intro T hT
    obtain ⟨x, _, hxT⟩ := hT {0} (by simp)
    exact Finset.card_pos.mpr ⟨x, hxT⟩

end ErdosLovaszLower
