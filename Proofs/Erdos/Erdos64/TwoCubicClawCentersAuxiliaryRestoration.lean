import Erdos.Erdos64.TwoCubicClawCentersCycleRestoration
import Erdos.Erdos64.TwoCubicClawCentersAuxiliaryContraction

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph TwoCubicClawCentersContraction

universe u

noncomputable local instance auxiliaryRestorationPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A selected simple cycle of length `m + 1` in the root-contracted auxiliary
restores to one simple auxiliary cycle. Its length and triangle count are respectively
`(m + 1, m + 1)`, `(m + 1, m)`, or `(m + 2, m)`; roots are never repeated. -/
theorem restored_auxiliary_cycle {V : Type u} (G : SimpleGraph V) (u v : V)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    {m : ℕ} (hm : 4 ≤ m + 1)
    (c : Fin (m + 1) → {a : Node G // a ≠ .inl ⟨true⟩})
    (hc : Function.Injective c)
    (hadj : ∀ i, (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).Adj
      (c i) (c (i + 1))) :
    ∃ t : ℕ, ∃ d : Fin (t + 1) → Node G, Function.Injective d ∧
      (∀ i, (auxiliary G u v).Adj (d i) (d (i + 1))) ∧
      ((t = m ∧ (Finset.univ.filter (fun i => IsTriangle G (d i))).card = m + 1) ∨
       (t = m ∧ (Finset.univ.filter (fun i => IsTriangle G (d i))).card = m) ∨
       (t = m + 1 ∧ (Finset.univ.filter (fun i => IsTriangle G (d i))).card = m)) := by
  classical
  by_cases hhit : ∃ z, (c z).val = .inl ⟨false⟩
  · obtain ⟨z, hz⟩ := hhit
    let b : Fin (m + 1) → {a : Node G // a ≠ .inl ⟨true⟩} := fun i => c (i + z)
    have hb : Function.Injective b := by
      intro i j he
      exact add_right_cancel (hc he)
    have hba (i : Fin (m + 1)) :
        (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).Adj (b i) (b (i + 1)) := by
      simpa only [b, add_assoc, add_comm, add_left_comm] using hadj (i + z)
    have hb0 : (b 0).val = .inl ⟨false⟩ := by simpa only [b, zero_add] using hz
    obtain ⟨t, d, hd, hda, hcases⟩ := restore_at_root (auxiliary G u v) _ _ (roots_ne G) hUV
      (IsTriangle G) (by exact not_false) (by exact not_false)
      (fun a hU hV => isTriangle_of_ne_roots G hU hV) hm b hb hba hb0
    exact ⟨t, d, hd, hda, Or.inr hcases⟩
  · let d : Fin (m + 1) → Node G := fun i => (c i).val
    have hd : Function.Injective d := by
      intro i j he
      exact hc (Subtype.ext he)
    have hU (i : Fin (m + 1)) : (c i).val ≠ .inl ⟨false⟩ :=
      fun he => hhit ⟨i, he⟩
    have hda (i : Fin (m + 1)) : (auxiliary G u v).Adj (d i) (d (i + 1)) :=
      adj_of_nonroots (auxiliary G u v) _ _ (hU i) (hU (i + 1)) (hadj i)
    have htri (i : Fin (m + 1)) : IsTriangle G (d i) :=
      isTriangle_of_ne_roots G (hU i) (c i).property
    have hcard : (Finset.univ.filter (fun i => IsTriangle G (d i))).card = m + 1 := by
      simp [htri]
    exact ⟨m, d, hd, hda, Or.inl ⟨rfl, hcard⟩⟩

end Erdos64.TwoCubicClawCentersQuotient
