import Combinatorics.CaroWei
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace ErdosCandidates.CaroWei

private theorem local_configuration {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) :
    ∃ v : V, let C := insert v (G.neighborFinset v)
      (∀ x ∈ C, G.degree v ≤ G.degree x) ∧
      ((∃ y ∈ C, G.degree v < G.degree y) ∨
       ∃ x ∉ C, ∃ y ∈ C, G.Adj x y) := by
  classical
  let K := Finset.univ.filter (G.Reachable a)
  have haK : a ∈ K := by simp [K, SimpleGraph.Reachable.rfl]
  obtain ⟨v, hvK, hmin⟩ := Finset.exists_min_image K (fun x => G.degree x) ⟨a, haK⟩
  have hav : G.Reachable a v := (Finset.mem_filter.mp hvK).2
  let C := insert v (G.neighborFinset v)
  have hreach (x : V) (hx : x ∈ C) : G.Reachable a x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hav
    · exact hav.trans ((G.mem_neighborFinset v x).mp hx).reachable
  have hlocal (x : V) (hx : x ∈ C) : G.degree v ≤ G.degree x :=
    hmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hreach x hx⟩)
  refine ⟨v, hlocal, ?_⟩
  by_cases hhigh : ∃ y ∈ C, G.degree v < G.degree y
  · exact Or.inl hhigh
  right
  by_contra hn
  have hclosed (x : V) (hx : x ∈ C) (y : V) (hxy : G.Adj x y) : y ∈ C := by
    by_contra hy
    exact hn ⟨y, hy, x, hx, hxy.symm⟩
  have hcontained (x : V) (hax : G.Reachable a x) : x ∈ C := by
    have hvx := hav.symm.trans hax
    have hp := (G.reachable_iff_reflTransGen v x).mp hvx
    clear hax hvx
    induction hp with
    | refl => exact Finset.mem_insert_self _ _
    | tail hp hxy ih => exact hclosed _ ih _ hxy
  have hdeg (x : V) (hx : x ∈ C) : G.degree x = G.degree v := by
    have hh : ¬ G.degree v < G.degree x := fun hh => hhigh ⟨x, hx, hh⟩
    exact Nat.le_antisymm (Nat.le_of_not_gt hh) (hlocal x hx)
  have hfull (x : V) (hx : x ∈ C) : G.neighborFinset x = C.erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have hxy := (G.mem_neighborFinset x y).mp hy
      exact Finset.mem_erase.mpr ⟨hxy.ne.symm, hclosed x hx y hxy⟩
    · rw [Finset.card_erase_of_mem hx, G.card_neighborFinset_eq_degree, hdeg x hx]
      simp [C, G.card_neighborFinset_eq_degree]
  have haC := hcontained a SimpleGraph.Reachable.rfl
  have hcC := hcontained c (hab.reachable.trans hbc.reachable)
  have hcN : c ∈ G.neighborFinset a := by
    rw [hfull a haC]
    exact Finset.mem_erase.mpr ⟨hac.symm, hcC⟩
  exact hnac ((G.mem_neighborFinset a c).mp hcN)

private theorem degree_induce_le' {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Set V)
    [DecidablePred (· ∈ R)] (x : R) : (G.induce R).degree x ≤ G.degree x := by
  classical
  have h := Finset.card_le_card
    (Finset.inter_subset_left (s₁ := G.neighborFinset x) (s₂ := R.toFinset))
  rw [← G.map_neighborFinset_induce x, Finset.card_map] at h
  exact h

private theorem degree_induce_lt {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Set V)
    [DecidablePred (· ∈ R)] (x : R) (y : V) (hy : y ∉ R) (hxy : G.Adj x y) :
    (G.induce R).degree x < G.degree x := by
  classical
  have hs : G.neighborFinset x ∩ R.toFinset ⊂ G.neighborFinset x := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hym : y ∈ G.neighborFinset x ∩ R.toFinset := by
      rw [heq]
      exact (G.mem_neighborFinset x y).mpr hxy
    exact hy (by simpa using (Finset.mem_inter.mp hym).2)
  have h := Finset.card_lt_card hs
  rw [← G.map_neighborFinset_induce x, Finset.card_map,
    G.card_neighborFinset_eq_degree] at h
  exact h

private theorem reciprocal_gap (m k D : ℕ) (hmk : m < k) (hkD : k ≤ D) :
    (1 : ℝ) / ((D : ℝ) * ((D : ℝ) + 1)) ≤
      1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD : (0 : ℝ) < D := lt_of_lt_of_le hk (by exact_mod_cast hkD)
  have hmk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast hmk
  have hrec : (1 : ℝ) / k ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hmk'
  have hprod : (k : ℝ) * ((k : ℝ) + 1) ≤ (D : ℝ) * ((D : ℝ) + 1) := by
    have hkD' : (k : ℝ) ≤ D := by exact_mod_cast hkD
    nlinarith
  have hden : (1 : ℝ) / ((D : ℝ) * ((D : ℝ) + 1)) ≤
      1 / ((k : ℝ) * ((k : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) hprod
  have hid : (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) =
      1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
    field_simp
    ring
  rw [hid] at hden
  linarith

private theorem sum_le_card_sub {V : Type*} [DecidableEq V] (C : Finset V)
    (f : V → ℝ) (A : ℝ) (hf : ∀ x ∈ C, f x ≤ A) (y : V) (hy : y ∈ C) :
    ∑ x ∈ C, f x ≤ (C.card : ℝ) * A - (A - f y) := by
  have hs : ∑ x ∈ C.erase y, f x ≤ ∑ _x ∈ C.erase y, A :=
    Finset.sum_le_sum (fun x hx => hf x (Finset.mem_of_mem_erase hx))
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hy] at hs
  have hc : 1 ≤ C.card := Finset.card_pos.mpr ⟨y, hy⟩
  have he : (↑(C.card - 1) : ℝ) = (C.card : ℝ) - 1 := by
    rw [Nat.cast_sub hc, Nat.cast_one]
  have hsum := Finset.sum_erase_add C f hy
  rw [he] at hs
  linarith

/-- An induced three-vertex path supplies a closed-neighborhood removal whose
residual Caro–Wei weight gains at least `1 / (D * (D + 1))`. -/
theorem exists_residual_step {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (D : ℕ) (_hD : 2 ≤ D) (hdegree : ∀ x : V, G.degree x ≤ D)
    (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) :
    ∃ v : V, let C := insert v (G.neighborFinset v)
      (∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
        1 / ((D : ℝ) * ((D : ℝ) + 1)) ≤
      1 + ∑ x : {x : V // x ∉ C},
        (1 : ℝ) / (((G.induce {x | x ∉ C}).degree x : ℝ) + 1) := by
  classical
  obtain ⟨v, hmin, hcases⟩ := local_configuration G a b c hab hbc hac hnac
  let C := insert v (G.neighborFinset v)
  let R := {x : V // x ∉ C}
  let H : SimpleGraph R := G.induce {x | x ∉ C}
  let f : V → ℝ := fun x => 1 / ((G.degree x : ℝ) + 1)
  let g : R → ℝ := fun x => 1 / ((H.degree x : ℝ) + 1)
  let δ : ℝ := 1 / ((D : ℝ) * ((D : ℝ) + 1))
  have hCcard : C.card = G.degree v + 1 := by
    simp [C, G.card_neighborFinset_eq_degree]
  have hf (x : V) (hx : x ∈ C) : f x ≤ f v := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (hmin x hx) 1
  have hunit : (C.card : ℝ) * f v = 1 := by
    rw [hCcard]
    dsimp [f]
    push_cast
    field_simp
  have hCweight : (∑ x ∈ C, f x) ≤ 1 := by
    calc
      _ ≤ ∑ _x ∈ C, f v := Finset.sum_le_sum hf
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, hunit]
  have hmono (x : R) : f x ≤ g x := by
    apply one_div_le_one_div_of_le (by positivity)
    have hd : H.degree x ≤ G.degree x := degree_induce_le' G {x | x ∉ C} x
    exact_mod_cast Nat.add_le_add_right hd 1
  have hgain : (∑ x ∈ C, f x) + δ ≤ 1 + ∑ x : R, (g x - f x) := by
    rcases hcases with ⟨y, hy, hstrict⟩ | ⟨x, hx, y, hy, hxy⟩
    · have hsum := sum_le_card_sub C f (f v) hf y hy
      rw [hunit] at hsum
      have hgap : δ ≤ f v - f y := reciprocal_gap _ _ D hstrict (hdegree y)
      have hn : 0 ≤ ∑ x : R, (g x - f x) :=
        Finset.sum_nonneg (fun x _ => sub_nonneg.mpr (hmono x))
      linarith
    · let z : R := ⟨x, hx⟩
      have hstrict : H.degree z < G.degree z :=
        degree_induce_lt G {x | x ∉ C} z y (by exact not_not.mpr hy) hxy
      have hgap : δ ≤ g z - f z := reciprocal_gap _ _ D hstrict (hdegree z)
      have hsum : g z - f z ≤ ∑ x : R, (g x - f x) :=
        Finset.single_le_sum (fun x _ => sub_nonneg.mpr (hmono x)) (Finset.mem_univ z)
      linarith
  have hpart : (∑ x ∈ C, f x) + (∑ x : R, f x) = ∑ x : V, f x := by
    rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
    exact Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ C) f
  have hdiff : (∑ x : R, (g x - f x)) = (∑ x : R, g x) - ∑ x : R, f x :=
    by rw [Finset.sum_sub_distrib]
  refine ⟨v, ?_⟩
  change (∑ x : V, f x) + δ ≤ 1 + ∑ x : R, g x
  rw [hdiff] at hgain
  linarith

/-- An induced three-vertex path forces a quantitative improvement of the
Caro–Wei bound, witnessed by an actual independent finite vertex set. -/
theorem exists_independent_set_defect {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (_hD : 2 ≤ D)
    (hdegree : ∀ x : V, G.degree x ≤ D)
    (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) (hnac : ¬ G.Adj a c) :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      (∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
        (1 : ℝ) / ((D : ℝ) * ((D : ℝ) + 1)) ≤ (S.card : ℝ) := by
  classical
  obtain ⟨v, hstep⟩ := exists_residual_step G D _hD hdegree a b c hab hbc hac hnac
  let C := insert v (G.neighborFinset v)
  let R := {x : V // x ∉ C}
  let H : SimpleGraph R := G.induce {x | x ∉ C}
  obtain ⟨T, hTind, hTweight⟩ := exists_independent_set H
  let e : R ↪ V := Function.Embedding.subtype (fun x => x ∉ C)
  let U : Finset V := T.map e
  have hU (x : V) (hx : x ∈ U) : x ∉ C := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  have hvC : v ∈ C := Finset.mem_insert_self _ _
  have hvU : v ∉ U := fun hvU => hU v hvU hvC
  have hUind : G.IsIndepSet (U : Set V) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    have hab' : a ≠ b := fun hab' => hxy (congrArg e hab')
    exact hTind ha hb hab'
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
  refine ⟨insert v U, hSind, ?_⟩
  rw [hScard, Nat.cast_add, Nat.cast_one]
  change (∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
    1 / ((D : ℝ) * ((D : ℝ) + 1)) ≤
    1 + ∑ x : R, (1 : ℝ) / ((H.degree x : ℝ) + 1) at hstep
  linarith

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    (2 ≤ (2 : ℕ)) ∧ (∀ x, G.degree x ≤ 2) ∧ G.Adj 0 1 ∧ G.Adj 1 2 ∧
      (0 : Fin 3) ≠ 2 ∧ ¬ G.Adj 0 2 := by
  decide

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    ∃ S : Finset (Fin 3), G.IsIndepSet (S : Set (Fin 3)) ∧
      (∑ x : Fin 3, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
        (1 : ℝ) / ((2 : ℝ) * ((2 : ℝ) + 1)) ≤ (S.card : ℝ) := by
  let G : SimpleGraph (Fin 3) := SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
  exact exists_independent_set_defect G 2 (by decide) (by decide)
    0 1 2 (by decide) (by decide) (by decide) (by decide)

end ErdosCandidates.CaroWei
