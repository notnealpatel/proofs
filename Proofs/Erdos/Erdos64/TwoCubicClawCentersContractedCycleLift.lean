import Erdos.Erdos64.TwoCubicClawCentersAuxiliaryRestoration

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TwoCubicClawCentersContraction

universe u

noncomputable local instance contractedCycleLiftPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Every simple selected cycle in the root-contracted auxiliary of length at least
four yields a literal original simple cycle of twice the contracted length. In a
mixed-side restoration the target is twice the contracted, not the expanded, length. -/
theorem contracted_cycle_lifts {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    {x : {a : Node G // a ≠ .inl ⟨true⟩}}
    (p : (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).Walk x x)
    (hp : p.IsCycle) (hlen : 4 ≤ p.length) :
    ∃ a, ∃ q : G.Walk a a, q.IsCycle ∧ q.length = 2 * p.length := by
  classical
  obtain ⟨m, hm, hm3, c, hc, hadj⟩ := walk_cycle_index p hp
  have hm4 : 4 ≤ m + 1 := by omega
  obtain ⟨t, d, hd, hda, hcases⟩ := restored_auxiliary_cycle G u v hUV hm4 c hc hadj
  let H := Finset.univ.filter (fun i => IsTriangle G (d i))
  let Z := Finset.univ.filter (fun i => chosenPort G u v (d i) (d (i + 1)) =
    chosenPort G u v (d (i + 1)) (d i))
  let E := Finset.univ.filter (fun i => chosenPort G u v (d i) (d (i + 1)) ≠
    chosenPort G u v (d (i + 1)) (d i))
  have hsplit : Z.card + E.card = t + 1 := by
    simpa only [ne_eq, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i => chosenPort G u v (d i) (d (i + 1)) = chosenPort G u v (d (i + 1)) (d i)))
  change (t = m ∧ H.card = m + 1) ∨ (t = m ∧ H.card = m) ∨
    (t = m + 1 ∧ H.card = m) at hcases
  have ht : 3 ≤ t + 1 := by rcases hcases with h | h | h <;> omega
  obtain ⟨k, hk, htarget⟩ : ∃ k, 2 * k ≤ H.card + 2 * Z.card ∧
      k + H.card + E.card = 2 * (m + 1) := by
    rcases hcases with h | h | h
    · exact ⟨Z.card, by omega, by omega⟩
    · exact ⟨Z.card + 1, by omega, by omega⟩
    · exact ⟨Z.card, by omega, by omega⟩
  obtain ⟨a, q, hq, hqlen⟩ := exists_cycle_of_detour_count G hG huv hCenters hcu hcv hdu hdv
    hHIGH ht d hd hda k hk (by change 3 ≤ k + H.card + E.card; omega)
  exact ⟨a, q, hq, hqlen.trans (htarget.trans (congrArg (fun n => 2 * n) hm.symm))⟩

end Erdos64.TwoCubicClawCentersQuotient
