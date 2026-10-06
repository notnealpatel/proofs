import Erdos.Erdos64.TwoCubicClawCentersCycleAssembly
import Erdos.Erdos64.TwoCubicClawCentersCycleSelection

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

noncomputable local instance cycleLiftPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- An injective sequence of auxiliary nodes contains at most two singleton roots. -/
theorem triangle_count_bounds {V : Type u} [Fintype V] (G : SimpleGraph V)
    {m : ℕ} (c : Fin (m + 1) → Node G) (hc : Function.Injective c) :
    (Finset.univ.filter (fun i => IsTriangle G (c i))).card ≤ m + 1 ∧
      m + 1 ≤ (Finset.univ.filter (fun i => IsTriangle G (c i))).card + 2 := by
  classical
  let H := Finset.univ.filter (fun i => IsTriangle G (c i))
  let R := Finset.univ.filter (fun i => ¬ IsTriangle G (c i))
  have hR : R.image c ⊆ ({.inl ⟨false⟩, .inl ⟨true⟩} : Finset (Node G)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hni := (Finset.mem_filter.mp hi).2
    cases hci : c i with
    | inl j =>
      rcases j with ⟨j⟩
      cases j <;> simp
    | inr A => exact (hni (by rw [hci]; trivial)).elim
  have hRcard : R.card ≤ 2 := by
    have he := Finset.card_image_of_injective R hc
    have hb := Finset.card_le_card hR
    have hp := Finset.card_le_two (a := (Sum.inl ⟨false⟩ : Node G)) (b := .inl ⟨true⟩)
    omega
  have hsplit : H.card + R.card = m + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => IsTriangle G (c i)))
  change H.card ≤ m + 1 ∧ m + 1 ≤ H.card + 2
  constructor <;> omega

/-- For every support-compatible detour count, an auxiliary simple cycle lifts to an
original simple cycle with its literal short length plus the chosen number of detours. -/
theorem exists_cycle_of_detour_count {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {m : ℕ} (hm : 3 ≤ m + 1) (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1))) (k : ℕ)
    (hk : 2 * k ≤ (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
      2 * (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) =
        chosenPort G u v (c (i + 1)) (c i))).card)
    (hlen : 3 ≤ k + (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
      (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
        chosenPort G u v (c (i + 1)) (c i))).card) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧
      p.length = k + (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
        (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
          chosenPort G u v (c (i + 1)) (c i))).card := by
  obtain ⟨T, s, hcard, htri, hsp, hfresh, hinj⟩ :=
    exists_spare_selection G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hHIGH k hk
  obtain ⟨a, p, hp, hl⟩ := exists_cycle_of_spares G hG huv hCenters hcu hcv hdu hdv
    hm c hc hadj T s htri hsp hfresh hinj (by rwa [hcard])
  exact ⟨a, p, hp, by simpa only [hcard] using hl⟩

/-- Every simple auxiliary cycle of length at least six lifts to an original simple
cycle of twice its length. This covers all dyadic lengths at least eight. -/
theorem exists_doubled_cycle_of_large {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {m : ℕ} (hm : 6 ≤ m + 1) (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1))) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  let H := Finset.univ.filter (fun i => IsTriangle G (c i))
  let Z := Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) =
    chosenPort G u v (c (i + 1)) (c i))
  let E := Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
    chosenPort G u v (c (i + 1)) (c i))
  have hcount := triangle_count_bounds G c hc
  change H.card ≤ m + 1 ∧ m + 1 ≤ H.card + 2 at hcount
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hcount.1
  have hsplit : Z.card + E.card = m + 1 := by
    simpa only [ne_eq, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i => chosenPort G u v (c i) (c (i + 1)) = chosenPort G u v (c (i + 1)) (c i)))
  have hk : 2 * (Z.card + r) ≤ H.card + 2 * Z.card := by omega
  have hl : Z.card + r + H.card + E.card = 2 * (m + 1) := by omega
  obtain ⟨a, p, hp, hpLen⟩ := exists_cycle_of_detour_count G hG huv hCenters hcu hcv hdu hdv
    hHIGH (by omega) c hc hadj (Z.card + r) hk (by change 3 ≤ Z.card + r + H.card + E.card; omega)
  exact ⟨a, p, hp, hpLen.trans hl⟩

/-- A simple auxiliary cycle with enough triangle turns admits an original doubled simple cycle. -/
theorem exists_doubled_cycle_of_many_triangles {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {m : ℕ} (hm : 3 ≤ m + 1) (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    (hsize : 2 * (m + 1) ≤ 3 * (Finset.univ.filter (fun i => IsTriangle G (c i))).card) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  let H := Finset.univ.filter (fun i => IsTriangle G (c i))
  let Z := Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) =
    chosenPort G u v (c (i + 1)) (c i))
  let E := Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
    chosenPort G u v (c (i + 1)) (c i))
  have hcount := triangle_count_bounds G c hc
  change H.card ≤ m + 1 ∧ m + 1 ≤ H.card + 2 at hcount
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hcount.1
  have hsplit : Z.card + E.card = m + 1 := by
    simpa only [ne_eq, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i => chosenPort G u v (c i) (c (i + 1)) = chosenPort G u v (c (i + 1)) (c i)))
  change 2 * (m + 1) ≤ 3 * H.card at hsize
  have hk : 2 * (Z.card + r) ≤ H.card + 2 * Z.card := by omega
  have hl : Z.card + r + H.card + E.card = 2 * (m + 1) := by omega
  obtain ⟨a, p, hp, hpLen⟩ := exists_cycle_of_detour_count G hG huv hCenters hcu hcv hdu hdv
    hHIGH (by omega) c hc hadj (Z.card + r) hk (by change 3 ≤ Z.card + r + H.card + E.card; omega)
  exact ⟨a, p, hp, hpLen.trans hl⟩

end Erdos64.TwoCubicClawCentersQuotient
