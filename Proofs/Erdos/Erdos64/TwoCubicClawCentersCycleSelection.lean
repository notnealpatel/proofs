import Erdos.Erdos64.TwoCubicClawCentersSelection

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

noncomputable local instance cycleSelectionPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

section

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCounterexample G) {u v : V} (huv : u ≠ v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A triangle has a spare different from any two prescribed ports. -/
theorem exists_third {x : Node G} (hx : IsTriangle G x) (a b : V) :
    ∃ d ∈ triangle G x, d ≠ a ∧ d ≠ b := by
  classical
  cases x with
  | inl i => exact hx.elim
  | inr s =>
    let t := s.val.erase a
    have ht : 1 < t.card := by
      have hcard := s.property.card_eq
      by_cases ha : a ∈ s.val
      · have he := Finset.card_erase_add_one ha
        dsimp only [t]
        omega
      · simpa only [t, Finset.erase_eq_of_notMem ha, hcard] using (by decide : 1 < 3)
    obtain ⟨d, hd, hdb⟩ := Finset.exists_mem_ne ht b
    exact ⟨d, (Finset.mem_erase.mp hd).2, (Finset.mem_erase.mp hd).1, hdb⟩

include hG hCenters hcu hcv hdu hdv

/-- Any original label lies in at most two triangle nodes. -/
theorem triangle_nodes_at_most_two {x y z : Node G} {a : V}
    (hx : IsTriangle G x) (hy : IsTriangle G y) (hz : IsTriangle G z)
    (ha : a ∈ triangle G x) (hb : a ∈ triangle G y) (hc : a ∈ triangle G z) :
    x = y ∨ x = z ∨ y = z := by
  cases x with
  | inl i => exact hx.elim
  | inr A =>
    cases y with
    | inl i => exact hy.elim
    | inr B =>
      cases z with
      | inl i => exact hz.elim
      | inr C =>
        have hau : a ≠ u := fun he => center_not_mem_triangle G hdu hcu A (he ▸ ha)
        have hav : a ≠ v := fun he => center_not_mem_triangle G hdv hcv A (he ▸ ha)
        rcases at_most_two_triangles G hG
          (not_claw_of_ne_centers G hCenters hau hav) A B C ha hb hc with he | he | he
        · exact Or.inl (congrArg Sum.inr he)
        · exact Or.inr (Or.inl (congrArg Sum.inr he))
        · exact Or.inr (Or.inr (congrArg Sum.inr he))

/-- Spares assigned to triangle nodes of an injective sequence have fibers of size at most two. -/
theorem spare_fiber_le_two {m : ℕ} (c : Fin (m + 1) → Node G)
    (hc : Function.Injective c) (H : Finset (Fin (m + 1))) (s : Fin (m + 1) → V)
    (hH : ∀ i ∈ H, IsTriangle G (c i)) (hs : ∀ i ∈ H, s i ∈ triangle G (c i))
    (a : V) : (H.filter (fun i => s i = a)).card ≤ 2 := by
  classical
  by_contra hnot
  have hcard : 2 < (H.filter (fun i => s i = a)).card := by omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hcard
  have hfi := Finset.mem_filter.mp hi
  have hfj := Finset.mem_filter.mp hj
  have hfk := Finset.mem_filter.mp hk
  rcases triangle_nodes_at_most_two G hG hCenters hcu hcv hdu hdv
    (hH i hfi.1) (hH j hfj.1) (hH k hfk.1)
    (hfi.2 ▸ hs i hfi.1) (hfj.2 ▸ hs j hfj.1) (hfk.2 ▸ hs k hfk.1) with he | he | he
  · exact hij (hc he)
  · exact hik (hc he)
  · exact hjk (hc he)

include huv

/-- The endpoints of used zero connectors form a disjoint set of twice the number
of those connectors, and every such endpoint is a triangle index. -/
theorem zero_endpoints {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (Z : Finset (Fin (m + 1)))
    (hZ : ∀ i ∈ Z, chosenPort G u v (c i) (c (i + 1)) =
      chosenPort G u v (c (i + 1)) (c i)) :
    (Z ∪ Z.image (fun i => i + 1)).card = 2 * Z.card ∧
      ∀ i ∈ Z ∪ Z.image (fun i => i + 1), IsTriangle G (c i) := by
  classical
  have hzero (i : Fin (m + 1)) (hi : i ∈ Z) :
      Connector G u v (c i) (c (i + 1))
        (chosenPort G u v (c i) (c (i + 1))) (chosenPort G u v (c i) (c (i + 1))) := by
    have he := chosen_connector G hG (hadj i)
    rwa [← hZ i hi] at he
  have hd : Disjoint Z (Z.image (fun i => i + 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
    have hzj := (hzero j hj).symm
    rw [he] at hzj
    have hother := zero_connector_unique G hG huv hCenters hcu hcv hdu hdv hHIGH
      (hzero i hi) hzj
    have hind : i + 1 = j := hc hother
    exact CycleIndex.succ_succ_ne m hm i (by rw [hind, he])
  refine ⟨?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he)]
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨A, B, hx, _⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv (hzero i hi)
      rw [hx]
      trivial
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨A, B, _, hx⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv (hzero j hj)
      rw [hx]
      trivial

/-- Any number of detours whose doubled count is at most the triangle count plus twice
the used-zero count can be chosen with pairwise distinct, globally fresh spare labels. -/
theorem exists_spare_selection {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (k : ℕ)
    (hk : 2 * k ≤ (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
      2 * (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) =
        chosenPort G u v (c (i + 1)) (c i))).card) :
    ∃ T : Finset (Fin (m + 1)), ∃ s : Fin (m + 1) → V,
      T.card = k ∧ (∀ i ∈ T, IsTriangle G (c i)) ∧
      (∀ i ∈ T, s i ∈ triangle G (c i) ∧
        s i ≠ chosenPort G u v (c i) (c (i - 1)) ∧
        s i ≠ chosenPort G u v (c i) (c (i + 1))) ∧
      (∀ i ∈ T, ∀ j, s i ≠ chosenPort G u v (c j) (c (j - 1)) ∧
        s i ≠ chosenPort G u v (c j) (c (j + 1))) ∧
      Set.InjOn s (↑T : Set (Fin (m + 1))) := by
  classical
  let H := Finset.univ.filter (fun i => IsTriangle G (c i))
  let Z := Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) =
    chosenPort G u v (c (i + 1)) (c i))
  let P := Z ∪ Z.image (fun i => i + 1)
  have hH (i : Fin (m + 1)) (hi : i ∈ H) : IsTriangle G (c i) :=
    (Finset.mem_filter.mp hi).2
  have hZ (i : Fin (m + 1)) (hi : i ∈ Z) :
      chosenPort G u v (c i) (c (i + 1)) = chosenPort G u v (c (i + 1)) (c i) :=
    (Finset.mem_filter.mp hi).2
  have hP := zero_endpoints G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hHIGH Z hZ
  have hPH : P ⊆ H := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP.2 i hi⟩
  have hex (i : Fin (m + 1)) : ∃ a : V, IsTriangle G (c i) →
      a ∈ triangle G (c i) ∧ a ≠ chosenPort G u v (c i) (c (i - 1)) ∧
        a ≠ chosenPort G u v (c i) (c (i + 1)) := by
    by_cases hi : IsTriangle G (c i)
    · obtain ⟨a, ha, hp, hn⟩ := exists_third G hi
        (chosenPort G u v (c i) (c (i - 1))) (chosenPort G u v (c i) (c (i + 1)))
      exact ⟨a, fun _ => ⟨ha, hp, hn⟩⟩
    · exact ⟨u, fun h => (hi h).elim⟩
  choose s hs using hex
  have hmem (i : Fin (m + 1)) (hi : i ∈ H) : s i ∈ members G u v (c i) := by
    have ha := (hs i (hH i hi)).1
    cases hci : c i with
    | inl r => exact (hci ▸ hH i hi).elim
    | inr A =>
      change s i ∈ A.val
      simpa only [hci, triangle] using ha
  have hzero (i : Fin (m + 1)) (hi : i ∈ Z) :
      Connector G u v (c i) (c (i + 1))
        (chosenPort G u v (c i) (c (i + 1))) (chosenPort G u v (c i) (c (i + 1))) := by
    have he := chosen_connector G hG (hadj i)
    rwa [← hZ i hi] at he
  have hinc (i : Fin (m + 1)) (hi : i ∈ P) : ∃ y b,
      Connector G u v (c i) y b b ∧
        (b = chosenPort G u v (c i) (c (i - 1)) ∨ b = chosenPort G u v (c i) (c (i + 1))) := by
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ⟨c (i + 1), chosenPort G u v (c i) (c (i + 1)), hzero i hi, Or.inr rfl⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have he := (hzero j hj).symm
      rw [hZ j hj] at he
      exact ⟨c j, chosenPort G u v (c (j + 1)) (c j), he,
        Or.inl (by simp only [add_sub_cancel_right])⟩
  have hprivate : ∀ i ∈ P, ∀ j ∈ H, s i = s j → i = j := by
    intro i hi j hj he
    by_contra hij
    obtain ⟨y, b, ce, hb⟩ := hinc i hi
    have hne : s i ≠ b := by
      rcases hb with hp | hn
      · rw [hp]
        exact (hs i (hH i (hPH hi))).2.1
      · rw [hn]
        exact (hs i (hH i (hPH hi))).2.2
    have hf := private_of_zero G hG huv hCenters hcu hcv hdu hdv hHIGH ce
      (hmem i (hPH hi)) hne (c j) (fun h => hij (hc h.symm))
    exact hf (he.symm ▸ hmem j hj)
  have hfiber (a : V) (_ha : a ∈ (H \ P).image s) :
      ((H \ P).filter (fun i => s i = a)).card ≤ 2 := by
    apply spare_fiber_le_two G hG hCenters hcu hcv hdu hdv c hc (H \ P) s
    · intro i hi
      exact hH i (Finset.mem_sdiff.mp hi).1
    · intro i hi
      exact (hs i (hH i (Finset.mem_sdiff.mp hi).1)).1
  have hcap := card_add_private_le_twice_image H P s hPH hprivate hfiber
  have hkimage : k ≤ (H.image s).card := by
    change 2 * k ≤ H.card + 2 * Z.card at hk
    have hPcard : P.card = 2 * Z.card := hP.1
    omega
  obtain ⟨T₀, hT₀, hinj₀, hcard₀⟩ := exists_injective_representatives H s
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (hcard₀ ▸ hkimage)
  have hTH : T ⊆ H := fun i hi => hT₀ (hT hi)
  refine ⟨T, s, hcard, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hH i (hTH hi)
  · intro i hi
    exact hs i (hH i (hTH hi))
  · intro i hi j
    exact cycle_spare_ne_ports G hG huv hCenters hcu hcv hdu hdv c hc hadj
      (hH i (hTH hi)) (hs i (hH i (hTH hi))).1
      (hs i (hH i (hTH hi))).2.1 (hs i (hH i (hTH hi))).2.2 j
  · intro i hi j hj he
    exact hinj₀ (hT hi) (hT hj) he

end

end Erdos64.TwoCubicClawCentersQuotient
