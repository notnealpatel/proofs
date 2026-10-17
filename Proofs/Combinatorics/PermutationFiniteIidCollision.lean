import Combinatorics.PermutationFiniteIidCore

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FiniteIidCollisionRepair

/-- Deleting one coordinate bounds any event on which that coordinate is determined. -/
theorem card_determined {d n : ℕ} (i : Fin (d+1))
    (E : Finset (Fin (d+1) → Fin n))
    (h : ∀ z ∈ E, ∀ w ∈ E,
      (∀ k, z (i.succAbove k) = w (i.succAbove k)) → z i = w i) :
    E.card ≤ n ^ d := by
  classical
  have hi : Function.Injective (fun z : E => fun k => z.val (i.succAbove k)) := by
    intro z w he
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      exact h z z.property w w.property (fun k => congrFun he k)
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun he k
  have hc := Fintype.card_le_of_injective _ hi
  simpa using hc

/-- An equality between two distinct coordinates has at most the one-coordinate fiber size. -/
theorem card_collision {d n : ℕ} (i j : Fin (d+1)) (hij : i ≠ j) :
    (Finset.univ.filter (fun z : Fin (d+1) → Fin n => z i = z j)).card ≤ n^d := by
  classical
  apply card_determined i
  intro z hz w hw he
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz' := (Finset.mem_filter.mp hz).2
  have hw' := (Finset.mem_filter.mp hw).2
  rw [hz', hw', ← hk]
  exact he k

/-- An anchor equality has at most the one-coordinate fiber size. -/
theorem card_anchor {d n : ℕ} (i : Fin (d+1)) (a : Fin n) :
    (Finset.univ.filter (fun z : Fin (d+1) → Fin n => z i = a)).card ≤ n^d := by
  classical
  apply card_determined i
  intro z hz w hw _
  exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm

/-- Union bound over unordered coordinate pairs and both anchor events. -/
theorem count_bad {d n : ℕ} (a b : Fin n) :
    (Finset.univ.filter (fun z : Fin (d+1) → Fin n =>
      ¬ (Function.Injective z ∧ ∀ i, z i ≠ a ∧ z i ≠ b))).card ≤
      ((d+1).choose 2 + 2*(d+1)) * n^d := by
  classical
  let P := (Finset.univ : Finset (Fin (d+1))).powersetCard 2
  let C := fun s : Finset (Fin (d+1)) => Finset.univ.filter
    (fun z : Fin (d+1) → Fin n => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ z i = z j)
  let A := fun i : Fin (d+1) => Finset.univ.filter
    (fun z : Fin (d+1) → Fin n => z i = a ∨ z i = b)
  have hC : ∀ s ∈ P, (C s).card ≤ n^d := by
    intro s hs
    have hs2 : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs2
    have he : C {i,j} = Finset.univ.filter (fun z : Fin (d+1) → Fin n => z i = z j) := by
      ext z
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, y, hy, hxy, he⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact he
        · exact he.symm
        · exact (hxy rfl).elim
      · intro he
        exact ⟨i, Or.inl rfl, j, Or.inr rfl, hij, he⟩
    rw [he]
    exact card_collision i j hij
  have hA : ∀ i, (A i).card ≤ 2*n^d := by
    intro i
    have he : A i =
        (Finset.univ.filter (fun z : Fin (d+1) → Fin n => z i = a)) ∪
        (Finset.univ.filter (fun z : Fin (d+1) → Fin n => z i = b)) := by
      ext z
      simp [A]
    rw [he]
    exact (Finset.card_union_le _ _).trans (by
      have ha := card_anchor i a
      have hb := card_anchor i b
      omega)
  have hsub : Finset.univ.filter (fun z : Fin (d+1) → Fin n =>
      ¬ (Function.Injective z ∧ ∀ i, z i ≠ a ∧ z i ≠ b)) ⊆
      P.biUnion C ∪ Finset.univ.biUnion A := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    by_cases hi : Function.Injective z
    · have hex : ∃ i, z i = a ∨ z i = b := by
        by_contra hh
        apply hz'
        exact ⟨hi, by simpa only [not_exists, not_or] using hh⟩
      obtain ⟨i, hi⟩ := hex
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hi⟩⟩)
    · have hex : ∃ i j, i ≠ j ∧ z i = z j := by
        simp only [Function.Injective, not_forall] at hi
        obtain ⟨i,j,hij⟩ := hi
        obtain ⟨he,hne⟩ := hij
        exact ⟨i,j,hne,he⟩
      obtain ⟨i,j,hij,he⟩ := hex
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨{i,j}, ?_, ?_⟩
      · simp [P, hij]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
          i, by simp, j, by simp, hij, he⟩
  calc
    _ ≤ (P.biUnion C ∪ Finset.univ.biUnion A).card := Finset.card_le_card hsub
    _ ≤ (P.biUnion C).card + (Finset.univ.biUnion A).card := Finset.card_union_le _ _
    _ ≤ (∑ s ∈ P, (C s).card) + ∑ i : Fin (d+1), (A i).card :=
      Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ ≤ (∑ _s ∈ P, n^d) + ∑ _i : Fin (d+1), 2*n^d :=
      Nat.add_le_add (Finset.sum_le_sum hC) (Finset.sum_le_sum (fun i _ => hA i))
    _ = _ := by simp [P, Finset.card_powersetCard]; ring

/-- The same count for any positive number of coordinates. -/
theorem count_bad_pos {D n : ℕ} (hD : 0 < D) (a b : Fin n) :
    (Finset.univ.filter (fun z : Fin D → Fin n =>
      ¬ (Function.Injective z ∧ ∀ i, z i ≠ a ∧ z i ≠ b))).card ≤
      (D.choose 2 + 2*D)*n^(D-1) := by
  cases D with
  | zero => omega
  | succ d => simpa using count_bad (d := d) a b

/-- The unconditional iid bad-sample bound, with one event per unordered pair. -/
theorem bad_sample_bound_repaired {m n : ℕ} (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (a b : Fin n) (hab : a ≠ b) :
    let G := Finset.univ.filter (PermutationFiniteIidEndpointLaw.Good (m := m) a b)
    1 - (G.card : ℝ) / (n : ℝ) ^ (2*(m-1)) ≤
      ((Nat.choose (2*m-2) 2 : ℝ) + 2*(2*m-2 : ℕ)) / n := by
  classical
  let d := 2*(m-1)-1
  have hd : 2*(m-1) = d+1 := by dsimp [d]; omega
  have hd' : 2*m-2 = d+1 := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : 0 < (n : ℝ)^(d+1) := pow_pos hn0 _
  let G := Finset.univ.filter (PermutationFiniteIidEndpointLaw.Good (m := m) a b)
  let B := Finset.univ.filter (fun z : Fin (2*(m-1)) → Fin n =>
    ¬ PermutationFiniteIidEndpointLaw.Good a b z)
  have hsum : B.card + G.card = n^(2*(m-1)) := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2*(m-1)) → Fin n)))
      (p := PermutationFiniteIidEndpointLaw.Good a b)
    simpa [B, G, add_comm] using hh
  have hcount : B.card ≤ ((d+1).choose 2 + 2*(d+1))*n^d := by
    have he : B = Finset.univ.filter (fun z : Fin (2*(m-1)) → Fin n =>
        ¬ (Function.Injective z ∧ ∀ i, z i ≠ a ∧ z i ≠ b)) := by
      ext z
      constructor
      · intro hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
    have hc : B.card ≤
        ((2*(m-1)).choose 2 + 2*(2*(m-1)))*n^(2*(m-1)-1) := by
      rw [he]
      exact count_bad_pos (D := 2*(m-1)) (by omega) a b
    calc
      B.card ≤ ((2*(m-1)).choose 2 + 2*(2*(m-1)))*n^(2*(m-1)-1) := hc
      _ = ((d+1).choose 2 + 2*(d+1))*n^d := by rw [hd]; simp
  have hsumR : (B.card : ℝ) + G.card = (n : ℝ)^(d+1) := by
    exact_mod_cast (hsum.trans (by rw [hd]))
  have hcountR : (B.card : ℝ) ≤
      ((Nat.choose (d+1) 2 : ℝ) + 2*(d+1 : ℕ))*(n : ℝ)^d := by
    exact_mod_cast hcount
  change 1 - (G.card : ℝ)/(n : ℝ)^(2*(m-1)) ≤ _
  conv_lhs => arg 2; arg 2; rw [hd]
  rw [hd']
  have heq : 1 - (G.card : ℝ)/(n : ℝ)^(d+1) =
      ((n : ℝ)^(d+1) - G.card)/(n : ℝ)^(d+1) := by
    rw [sub_div, div_self (ne_of_gt hpow)]
  rw [heq]
  apply (div_le_div_iff₀ hpow hn0).mpr
  rw [pow_succ] at hsumR
  rw [pow_succ]
  have hdiff : (n : ℝ)^d * n - G.card = B.card := by linarith [hsumR]
  rw [hdiff]
  calc
    (B.card : ℝ) * n ≤
        (((Nat.choose (d+1) 2 : ℝ) + 2*(d+1 : ℕ))*(n : ℝ)^d)*n :=
      mul_le_mul_of_nonneg_right hcountR hn0.le
    _ = _ := by ring

example : 2 ≤ (2 : ℕ) ∧ 2*2 ≤ (4 : ℕ) ∧ (0 : Fin 4) ≠ 3 := by decide
example : 2 ≤ (2 : ℕ) ∧ 2*2 ≤ (100 : ℕ) ∧ (0 : Fin 100) ≠ 99 := by decide

end FiniteIidCollisionRepair
