import Sorry.Combinatorics.CaroWeiEquality

set_option autoImplicit false

namespace ErdosCandidates.CaroWei

attribute [local instance] Classical.propDecidable

/-- Each lost neighbor pays its share of the reciprocal degree gain. -/
private theorem quadratic_reciprocal (m k D t : ℕ) (h : m + t = k)
    (hk : k ≤ D) (_hD : 0 < D) :
    (t : ℝ) ≤ ((D : ℝ) * ((D : ℝ) + 1)) *
      (1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1)) := by
  by_cases ht : t = 0
  · subst t
    simp only [Nat.add_zero] at h
    subst k
    simp
  have hmk : m + 1 ≤ k := by omega
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hid : 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) =
      (t : ℝ) / (((m : ℝ) + 1) * ((k : ℝ) + 1)) := by
    have he : (m : ℝ) + t = k := by exact_mod_cast h
    field_simp
    nlinarith
  rw [hid]
  have hden : ((m : ℝ) + 1) * ((k : ℝ) + 1) ≤ (D : ℝ) * ((D : ℝ) + 1) := by
    have hm' : (m : ℝ) + 1 ≤ D := by exact_mod_cast (hmk.trans hk)
    have hk' : (k : ℝ) ≤ D := by exact_mod_cast hk
    nlinarith
  have htpos : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hmul := mul_le_mul_of_nonneg_left hden
    (div_nonneg htpos (le_of_lt (mul_pos hm hkpos)))
  have he : (t : ℝ) / (((m : ℝ) + 1) * ((k : ℝ) + 1)) *
      (((m : ℝ) + 1) * ((k : ℝ) + 1)) = t := by field_simp
  nlinarith

/-- Original degree splits into residual degree and cross-neighbor count. -/
private theorem induced_degree_split {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (x : {x : V // x ∉ C}) :
    (G.induce {x | x ∉ C}).degree x +
      ((G.neighborFinset x).filter (· ∈ C)).card = G.degree x := by
  classical
  have he : (G.induce {x | x ∉ C}).degree x =
      ((G.neighborFinset x).filter (· ∉ C)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := Function.Embedding.subtype _) ,
      G.map_neighborFinset_induce]
    congr 1
    ext y
    simp
  rw [he, Nat.add_comm]
  exact (G.neighborFinset x).card_filter_add_card_filter_not (· ∈ C)

/-- Every boundary vertex contributes at least one cross incidence. -/
private theorem boundary_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    ((C.filter (fun y => ∃ x, x ∉ C ∧ G.Adj y x)).card : ℝ) ≤
      ∑ x : {x : V // x ∉ C},
        (((G.neighborFinset x).filter (· ∈ C)).card : ℝ) := by
  classical
  let R := {x : V // x ∉ C}
  have hrow (y : V) :
      (if ∃ x, x ∉ C ∧ G.Adj y x then (1 : ℝ) else 0) ≤
        ∑ x : R, if G.Adj y x then (1 : ℝ) else 0 := by
    split_ifs with hy
    · obtain ⟨x, hx, hxy⟩ := hy
      let z : R := ⟨x, hx⟩
      have hz : G.Adj y z := hxy
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset R))
        (f := fun x : R => if G.Adj y x then (1 : ℝ) else 0)
        (fun x _ => by positivity) (Finset.mem_univ z)
      simpa only [if_pos hz] using hs
    · exact Finset.sum_nonneg (fun x _ => by positivity)
  calc
    _ = ∑ y ∈ C, if ∃ x, x ∉ C ∧ G.Adj y x then (1 : ℝ) else 0 := by simp
    _ ≤ ∑ y ∈ C, ∑ x : R, if G.Adj y x then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun y _ => hrow y)
    _ = ∑ x : R, ∑ y ∈ C, if G.Adj y x then (1 : ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have he : C.filter (fun y => G.Adj y x) =
          (G.neighborFinset x).filter (· ∈ C) := by
        ext y
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
      simp [← he]

/-- Removing a minimum-degree closed neighborhood gains enough Caro–Wei weight
at quadratic cost to pay for its boundary, rather than its whole vertex set. -/
private theorem boundary_payment {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ x : V, G.degree x ≤ D) (v : V)
    (hmin : ∀ x : V, G.degree v ≤ G.degree x) :
    let C := insert v (G.neighborFinset v)
    let R := {x : V // x ∉ C}
    ((C.filter (fun y => ∃ x, x ∉ C ∧ G.Adj y x)).card : ℝ) ≤
      ((D : ℝ) * ((D : ℝ) + 1)) *
        (1 + (∑ x : R, 1 / (((G.induce {x | x ∉ C}).degree x : ℝ) + 1)) -
          ∑ x : V, 1 / ((G.degree x : ℝ) + 1)) := by
  classical
  let C := insert v (G.neighborFinset v)
  let R := {x : V // x ∉ C}
  let H : SimpleGraph R := G.induce {x | x ∉ C}
  let f : V → ℝ := fun x => 1 / ((G.degree x : ℝ) + 1)
  let g : R → ℝ := fun x => 1 / ((H.degree x : ℝ) + 1)
  let K : ℝ := (D : ℝ) * ((D : ℝ) + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCcard : C.card = G.degree v + 1 := by
    simp [C, G.card_neighborFinset_eq_degree]
  have hf (x : V) (_hx : x ∈ C) : f x ≤ f v := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (hmin x) 1
  have hunit : (C.card : ℝ) * f v = 1 := by
    rw [hCcard]
    dsimp [f]
    push_cast
    field_simp
  have hCweight : (∑ x ∈ C, f x) ≤ 1 := by
    calc
      _ ≤ ∑ _x ∈ C, f v := Finset.sum_le_sum hf
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, hunit]
  have hpart : (∑ x ∈ C, f x) + (∑ x : R, f x) = ∑ x : V, f x := by
    rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
    exact Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ C) f
  have hgap (x : R) :
      (((G.neighborFinset x).filter (· ∈ C)).card : ℝ) ≤ K * (g x - f x) :=
    quadratic_reciprocal _ _ D _ (induced_degree_split G C x) (hdegree x) (by omega)
  have hsum := Finset.sum_le_sum (fun x (_hx : x ∈ (Finset.univ : Finset R)) => hgap x)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hsurplus : (∑ x : R, g x) - (∑ x : R, f x) ≤
      1 + (∑ x : R, g x) - (∑ x : V, f x) := by linarith
  change ((C.filter (fun y => ∃ x, x ∉ C ∧ G.Adj y x)).card : ℝ) ≤
    K * (1 + (∑ x : R, g x) - (∑ x : V, f x))
  exact (boundary_count G C).trans (hsum.trans (mul_le_mul_of_nonneg_left hsurplus hK))

/-- A graph of maximum degree at most `D`, with `2 ≤ D`, has an independent set
whose Caro–Wei excess pays for deleting vertices with coefficient `D * (D + 1)`
until every two-edge path has adjacent distinct endpoints. The independent set
and the deletion set need not be disjoint. -/
theorem exists_independent_set_stability_quadratic {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v : V, G.degree v ≤ D) :
    ∃ S X : Finset V, G.IsIndepSet (S : Set V) ∧
      (∀ a b c : V, a ∉ X → b ∉ X → c ∉ X →
        G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) ∧
      (X.card : ℝ) ≤ ((D : ℝ) * ((D : ℝ) + 1)) *
        ((S.card : ℝ) - ∑ v : V, 1 / ((G.degree v : ℝ) + 1)) := by
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hlocal : ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c
    · obtain ⟨S, hS, heq⟩ := exists_independent_set_equality G hlocal
      refine ⟨S, ∅, hS, ?_, ?_⟩
      · intro a b c _ _ _ hab hbc hac
        exact hlocal a b c hab hbc hac
      · simp [heq]
    · push Not at hlocal
      obtain ⟨a, _b, _c, _hab, _hbc, _hac, _hnac⟩ := hlocal
      obtain ⟨v, _hv, hminimum⟩ := Finset.exists_min_image
        (Finset.univ : Finset V) (fun x => G.degree x) ⟨a, Finset.mem_univ a⟩
      have hmin (x : V) : G.degree v ≤ G.degree x := hminimum x (Finset.mem_univ x)
      have hstep := boundary_payment G D hD hdegree v hmin
      let C := insert v (G.neighborFinset v)
      let R := {x : V // x ∉ C}
      let H : SimpleGraph R := G.induce {x | x ∉ C}
      have hvC : v ∈ C := Finset.mem_insert_self _ _
      have hsmall : Fintype.card R < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (not_not.mpr hvC)
      have hdeg (x : R) : H.degree x ≤ D := by
        have hm := Finset.card_le_card
          (Finset.inter_subset_left (s₁ := G.neighborFinset x)
            (s₂ := ({x | x ∉ C} : Set V).toFinset))
        rw [← G.map_neighborFinset_induce (s := {x | x ∉ C}) x,
          Finset.card_map] at hm
        exact hm.trans (hdegree x)
      obtain ⟨T, Y, hT, hY, hbound⟩ :=
        ih (Fintype.card R) hsmall H hdeg rfl
      let e : R ↪ V := Function.Embedding.subtype (fun x => x ∉ C)
      let U := T.map e
      let B := C.filter (fun y => ∃ x, x ∉ C ∧ G.Adj y x)
      let X := B ∪ Y.map e
      have hstay (x : V) (hxC : x ∈ C) (hxB : x ∉ B)
          (y : V) (hxy : G.Adj x y) : y ∈ C := by
        by_contra hy
        exact hxB (Finset.mem_filter.mpr ⟨hxC, y, hy, hxy⟩)
      have hfull (x : V) (hxC : x ∈ C) (hxB : x ∉ B) :
          G.neighborFinset x = C.erase x := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          have hxy := (G.mem_neighborFinset x y).mp hy
          exact Finset.mem_erase.mpr ⟨hxy.ne.symm, hstay x hxC hxB y hxy⟩
        · rw [Finset.card_erase_of_mem hxC, G.card_neighborFinset_eq_degree]
          have hCcard : C.card = G.degree v + 1 := by
            simp [C, G.card_neighborFinset_eq_degree]
          rw [hCcard]
          simpa using hmin x
      have hU (x : V) (hx : x ∈ U) : x ∉ C := by
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hvU : v ∉ U := fun hv => hU v hv hvC
      have hUind : G.IsIndepSet (U : Set V) := by
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
        exact hT ha hb (fun he => hxy (congrArg e he))
      have hvnotadj (x : V) (hx : x ∈ U) : ¬ G.Adj v x := by
        intro hadj
        exact hU x hx (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).mpr hadj))
      have hSind : G.IsIndepSet ((insert v U : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact hvnotadj y hy
        · rcases hy with rfl | hy
          · exact fun hadj => hvnotadj x hx hadj.symm
          · exact hUind hx hy hxy
      have hScard : (insert v U).card = T.card + 1 := by
        rw [Finset.card_insert_of_notMem hvU, Finset.card_map]
      have hclosed : ∀ a b c : V, a ∉ X → b ∉ X → c ∉ X →
          G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c := by
        intro a b c ha hb hc hab hbc hac
        have hnotB (x : V) (hx : x ∉ X) : x ∉ B :=
          fun hm => hx (Finset.mem_union_left _ hm)
        by_cases hbC : b ∈ C
        · have haC := hstay b hbC (hnotB b hb) a hab.symm
          have hcC := hstay b hbC (hnotB b hb) c hbc
          apply (G.mem_neighborFinset a c).mp
          rw [hfull a haC (hnotB a ha)]
          exact Finset.mem_erase.mpr ⟨hac.symm, hcC⟩
        · have haC : a ∉ C := by
            intro haC
            exact hbC (hstay a haC (hnotB a ha) b hab)
          have hcC : c ∉ C := by
            intro hcC
            exact hbC (hstay c hcC (hnotB c hc) b hbc.symm)
          let a' : R := ⟨a, haC⟩
          let b' : R := ⟨b, hbC⟩
          let c' : R := ⟨c, hcC⟩
          have hnot (x : R) (hx : (x : V) ∉ X) : x ∉ Y := by
            intro hm
            exact hx (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨x, hm, rfl⟩))
          exact hY a' b' c' (hnot a' ha) (hnot b' hb) (hnot c' hc)
            hab hbc (fun he => hac (congrArg Subtype.val he))
      have hXcard : (X.card : ℝ) ≤ (B.card : ℝ) + (Y.card : ℝ) := by
        have hc := Finset.card_union_le B (Y.map e)
        rw [Finset.card_map] at hc
        exact_mod_cast hc
      refine ⟨insert v U, X, hSind, hclosed, ?_⟩
      rw [hScard, Nat.cast_add, Nat.cast_one]
      change (B.card : ℝ) ≤ ((D : ℝ) * ((D : ℝ) + 1)) *
        (1 + (∑ x : R, (1 : ℝ) / ((H.degree x : ℝ) + 1)) -
          ∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1)) at hstep
      linarith

example : (2 ≤ (2 : ℕ)) ∧
    (∀ v : Fin 3, (⊤ : SimpleGraph (Fin 3)).degree v ≤ 2) := by decide

example : ∃ S X : Finset (Fin 3),
    (⊤ : SimpleGraph (Fin 3)).IsIndepSet (S : Set (Fin 3)) ∧
    (∀ a b c : Fin 3, a ∉ X → b ∉ X → c ∉ X →
      (⊤ : SimpleGraph (Fin 3)).Adj a b → (⊤ : SimpleGraph (Fin 3)).Adj b c →
      a ≠ c → (⊤ : SimpleGraph (Fin 3)).Adj a c) ∧
    (X.card : ℝ) ≤ ((2 : ℝ) * ((2 : ℝ) + 1)) *
      ((S.card : ℝ) - ∑ v : Fin 3, 1 / (((⊤ : SimpleGraph (Fin 3)).degree v : ℝ) + 1)) :=
  exists_independent_set_stability_quadratic ⊤ 2 (by decide) (by decide)

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    (2 ≤ (2 : ℕ)) ∧ (∀ v, G.degree v ≤ 2) ∧
      ¬ (∀ a b c, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) := by
  decide

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    ∃ S X : Finset (Fin 3), G.IsIndepSet (S : Set (Fin 3)) ∧
      (∀ a b c : Fin 3, a ∉ X → b ∉ X → c ∉ X →
        G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) ∧
      (X.card : ℝ) ≤ ((2 : ℝ) * ((2 : ℝ) + 1)) *
        ((S.card : ℝ) - ∑ v : Fin 3, 1 / ((G.degree v : ℝ) + 1)) := by
  let G : SimpleGraph (Fin 3) := SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
  exact exists_independent_set_stability_quadratic G 2 (by decide) (by decide)

end ErdosCandidates.CaroWei
