import Erdos.Erdos64.TwoCubicClawCentersRootSeparation

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

noncomputable local instance smallCyclePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The two retained singleton roots are different auxiliary vertices. -/
theorem roots_ne {V : Type u} (G : SimpleGraph V) :
    (Sum.inl ⟨false⟩ : Node G) ≠ .inl ⟨true⟩ := by
  intro he
  have hb := congrArg ULift.down (Sum.inl.inj he)
  cases hb

/-- Every auxiliary node other than the two roots is an actual triangle. -/
theorem isTriangle_of_ne_roots {V : Type u} (G : SimpleGraph V) {x : Node G}
    (hU : x ≠ .inl ⟨false⟩) (hV : x ≠ .inl ⟨true⟩) : IsTriangle G x := by
  cases x with
  | inl r =>
    rcases r with ⟨r⟩
    cases r
    · exact (hU rfl).elim
    · exact (hV rfl).elim
  | inr A => trivial

/-- If one singleton root is absent, all but at most one term of an injective sequence
are triangle turns. -/
theorem triangle_count_of_missing_root {V : Type u} [Fintype V] (G : SimpleGraph V)
    {m : ℕ} (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (r : ULift.{u} Bool) (hmiss : ∀ i, c i ≠ .inl r) :
    m + 1 ≤ (Finset.univ.filter (fun i => IsTriangle G (c i))).card + 1 := by
  classical
  let H := Finset.univ.filter (fun i => IsTriangle G (c i))
  let R := Finset.univ.filter (fun i => ¬ IsTriangle G (c i))
  have hsub : R.image c ⊆ ({.inl ⟨!r.down⟩} : Finset (Node G)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hni := (Finset.mem_filter.mp hi).2
    cases hci : c i with
    | inl s =>
      rcases r with ⟨r⟩
      rcases s with ⟨s⟩
      cases r <;> cases s
      all_goals first | exact (hmiss i hci).elim | simp
    | inr A => exact (hni (by rw [hci]; trivial)).elim
  have hRcard : R.card ≤ 1 := by
    have he := Finset.card_image_of_injective R hc
    have hb := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hb
    omega
  have hsplit : H.card + R.card = m + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => IsTriangle G (c i)))
  change m + 1 ≤ H.card + 1
  omega

/-- An alternating-root auxiliary square produces an original eight-cycle. Shared
spares are impossible because its two triangles are neighbors of the same root. -/
theorem alternating_four_cycle_false {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (c : Fin 4 → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    (h0 : c 0 = .inl ⟨false⟩) (h2 : c 2 = .inl ⟨true⟩) : False := by
  classical
  have htri (i : Fin 4) (hi0 : i ≠ 0) (hi2 : i ≠ 2) : IsTriangle G (c i) :=
    isTriangle_of_ne_roots G (fun he => hi0 (hc (he.trans h0.symm)))
      (fun he => hi2 (hc (he.trans h2.symm)))
  have h1 : IsTriangle G (c 1) := htri 1 (by decide) (by decide)
  have h3 : IsTriangle G (c 3) := htri 3 (by decide) (by decide)
  obtain ⟨a, ha, hap, han⟩ := exists_third G h1
    (chosenPort G u v (c 1) (c (1 - 1))) (chosenPort G u v (c 1) (c (1 + 1)))
  obtain ⟨b, hb, hbp, hbn⟩ := exists_third G h3
    (chosenPort G u v (c 3) (c (3 - 1))) (chosenPort G u v (c 3) (c (3 + 1)))
  have hab : a ≠ b := by
    cases hx : c 1 with
    | inl r => exact (hx ▸ h1).elim
    | inr A =>
      cases hy : c 3 with
      | inl r => exact (hy ▸ h3).elim
      | inr B =>
        have hA : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inr A) := by
          simpa only [h0, hx, show (0 : Fin 4) + 1 = 1 from rfl] using hadj 0
        have hB : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inr B) := by
          simpa only [h0, hy, show (3 : Fin 4) + 1 = 0 from rfl] using (hadj 3).symm
        have hAB : A ≠ B := by
          intro he
          exact (by decide : (1 : Fin 4) ≠ 3) (hc (hx.trans ((congrArg Sum.inr he).trans hy.symm)))
        have hd := root_neighbors_disjoint G hG huv hCenters hcu hcv hdu hdv hA hB hAB
        have hma : a ∈ A.val := by simpa only [hx, triangle] using ha
        have hmb : b ∈ B.val := by simpa only [hy, triangle] using hb
        intro he
        exact Finset.disjoint_left.mp hd hma (he.symm ▸ hmb)
  let T : Finset (Fin 4) := {1, 3}
  let s : Fin 4 → V := fun i => if i = 1 then a else b
  have hT (i : Fin 4) (hi : i ∈ T) : IsTriangle G (c i) := by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · exact Finset.mem_singleton.mp hi ▸ h3
  have hs (i : Fin 4) (hi : i ∈ T) : s i ∈ triangle G (c i) ∧
      s i ≠ chosenPort G u v (c i) (c (i - 1)) ∧
      s i ≠ chosenPort G u v (c i) (c (i + 1)) := by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa only [s, if_pos rfl] using (show a ∈ triangle G (c 1) ∧ _ from ⟨ha, hap, han⟩)
    · have hi3 := Finset.mem_singleton.mp hi
      subst i
      simpa only [s, if_neg (by decide : (3 : Fin 4) ≠ 1)] using
        (show b ∈ triangle G (c 3) ∧ _ from ⟨hb, hbp, hbn⟩)
  have hfresh (i : Fin 4) (hi : i ∈ T) (j : Fin 4) :=
    cycle_spare_ne_ports G hG huv hCenters hcu hcv hdu hdv c hc hadj
      (hT i hi) (hs i hi).1 (hs i hi).2.1 (hs i hi).2.2 j
  have hinj : Set.InjOn s (↑T : Set (Fin 4)) := by
    intro i hi j hj he
    have hi' : i = 1 ∨ i = 3 := by simpa only [Finset.mem_coe, T, Finset.mem_insert, Finset.mem_singleton] using hi
    have hj' : j = 1 ∨ j = 3 := by simpa only [Finset.mem_coe, T, Finset.mem_insert, Finset.mem_singleton] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · rfl
    · exact (hab (by simpa only [s, if_pos rfl, if_neg (by decide : (3 : Fin 4) ≠ 1)] using he)).elim
    · exact (hab (by simpa only [s, if_pos rfl, if_neg (by decide : (3 : Fin 4) ≠ 1)] using he.symm)).elim
    · rfl
  have hzero (i : Fin 4) : chosenPort G u v (c i) (c (i + 1)) ≠
      chosenPort G u v (c (i + 1)) (c i) := by
    intro he
    have ce := chosen_connector G hG (hadj i)
    rw [← he] at ce
    obtain ⟨A, B, hx, hy⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv ce
    fin_cases i
    · change c 0 = Sum.inr A at hx
      rw [h0] at hx
      cases hx
    · change c 2 = Sum.inr B at hy
      rw [h2] at hy
      cases hy
    · change c 2 = Sum.inr A at hx
      rw [h2] at hx
      cases hx
    · change c 0 = Sum.inr B at hy
      rw [h0] at hy
      cases hy
  have hcardT : T.card = 2 := by decide
  have hcardH : (Finset.univ.filter (fun i => IsTriangle G (c i))).card = 2 := by
    have he : Finset.univ.filter (fun i => IsTriangle G (c i)) = T := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases i
      · change IsTriangle G (c 0) ↔ (0 : Fin 4) = 1 ∨ 0 = 3
        simp [h0, IsTriangle]
      · change IsTriangle G (c 1) ↔ (1 : Fin 4) = 1 ∨ 1 = 3
        simp [h1]
      · change IsTriangle G (c 2) ↔ (2 : Fin 4) = 1 ∨ 2 = 3
        simp [h2, IsTriangle]
      · change IsTriangle G (c 3) ↔ (3 : Fin 4) = 1 ∨ 3 = 3
        simp [h3]
    rw [he, hcardT]
  have hcardE : (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
      chosenPort G u v (c (i + 1)) (c i))).card = 4 := by
    simp [hzero]
  obtain ⟨x, p, hp, hl⟩ := exists_cycle_of_spares G hG huv hCenters hcu hcv hdu hdv
    (m := 3) (by decide) c hc hadj T s hT hs hfresh hinj
    (by rw [hcardT, hcardH, hcardE]; decide)
  have hlen : p.length = 2 ^ 3 := by rw [hl, hcardT, hcardH, hcardE]; decide
  exact hG.not_hasPowerOfTwoCycle ⟨3, by decide, x, p, hp, hlen⟩

end Erdos64.TwoCubicClawCentersQuotient
