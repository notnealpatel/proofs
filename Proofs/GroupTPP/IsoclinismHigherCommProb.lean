import GroupTPP.IsoclinismInvariants
import GroupTPP.HigherCommProb

/-!
# Higher commuting probability under isoclinism

Levit–Shwartz, arXiv:2605.02071, Proposition `prop:isoclinism-invariant`
(source `part1_asymptotics_spectrum_v15.tex`, lines 244–308).
The identity fiber of the lifted commutator map is transported by isoclinism.
Good central-coset tuples are not commuting tuples in the quotient: commuting
in the quotient only says that the original commutator is central.
-/

set_option autoImplicit false
open scoped Classical commutatorElement
open IsoclinismInvariants
noncomputable section

namespace IsoclinismHigherCommProb

/-- A selected lift of a coset modulo the center. -/
def centralRep (G : Type*) [Group G] : G ⧸ Subgroup.center G → G :=
  Function.surjInv (QuotientGroup.mk'_surjective (Subgroup.center G))

/-- The selected representative projects to its original coset. -/
theorem centralRep_mk (G : Type*) [Group G] (q : G ⧸ Subgroup.center G) :
    QuotientGroup.mk (centralRep G q) = q :=
  Function.surjInv_eq (QuotientGroup.mk'_surjective (Subgroup.center G)) q

/-- Central-coset tuples whose selected lifts commute pairwise in `G`. -/
def goodCentralTuples (G : Type*) [Group G] (r : ℕ) :=
  {q : Fin r → G ⧸ Subgroup.center G //
    ∀ i j, Commute (centralRep G (q i)) (centralRep G (q j))}

example (G : Type*) [Group G] (r : ℕ) :
    (fun _ : Fin r => (1 : G ⧸ Subgroup.center G)) ∈
      {q | ∀ i j, Commute (centralRep G (q i)) (centralRep G (q j))} := by
  intro i j
  exact Commute.refl _

/-- Commutation can be tested on any lifts of the same central cosets. -/
theorem commute_iff_of_central_cosets (G : Type*) [Group G] {x y x' y' : G}
    (hx : (QuotientGroup.mk x : G ⧸ Subgroup.center G) = QuotientGroup.mk x')
    (hy : (QuotientGroup.mk y : G ⧸ Subgroup.center G) = QuotientGroup.mk y') :
    Commute x y ↔ Commute x' y' := by
  change x * y = y * x ↔ x' * y' = y' * x'
  rw [← commutatorElement_eq_one_iff_mul_comm,
    ← commutatorElement_eq_one_iff_mul_comm,
    commutatorElement_eq_of_quotient_eq hx hy]

/-- Each good central-coset tuple has exactly one center coordinate per lift coordinate. -/
theorem card_commTuples_eq_good_mul_center (G : Type*) [Group G] (r : ℕ) :
    Nat.card (commTuples G r) =
      Nat.card (goodCentralTuples G r) * Nat.card (Subgroup.center G) ^ r := by
  let π := QuotientGroup.mk' (Subgroup.center G)
  have hrep : ∀ q, π (centralRep G q) = q := centralRep_mk G
  have hmem : ∀ x : G, (centralRep G (π x))⁻¹ * x ∈ Subgroup.center G := by
    intro x
    apply (QuotientGroup.eq_one_iff _).mp
    change π ((centralRep G (π x))⁻¹ * x) = 1
    rw [map_mul, map_inv, hrep, inv_mul_cancel]
  have hproj : ∀ (q : G ⧸ Subgroup.center G) (z : Subgroup.center G),
      π (centralRep G q * z) = q := by
    intro q z
    rw [map_mul, hrep]
    have hz : π z = 1 := (QuotientGroup.eq_one_iff _).mpr z.property
    rw [hz, mul_one]
  let e : commTuples G r ≃ goodCentralTuples G r × (Fin r → Subgroup.center G) :=
    { toFun := fun f =>
        (⟨fun i => π (f.val i), fun i j =>
          (commute_iff_of_central_cosets G (hrep _) (hrep _)).mpr (f.property i j)⟩,
          fun i => ⟨(centralRep G (π (f.val i)))⁻¹ * f.val i, hmem _⟩)
      invFun := fun p =>
        ⟨fun i => centralRep G (p.1.val i) * p.2 i, fun i j =>
          (commute_iff_of_central_cosets G
            ((hrep _).trans (hproj _ _).symm)
            ((hrep _).trans (hproj _ _).symm)).mp (p.1.property i j)⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        exact mul_inv_cancel_left _ _
      right_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          funext i
          exact hproj _ _
        · funext i
          apply Subtype.ext
          change (centralRep G (π (centralRep G (p.1.val i) * p.2 i)))⁻¹ *
            (centralRep G (p.1.val i) * p.2 i) = p.2 i
          rw [hproj, inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_prod, card_funFin]

/-- A derived-subgroup commutator is the identity exactly when its inputs commute. -/
theorem cmap_eq_one_iff (G : Type*) [Group G] (x y : G) :
    cmap G x y = 1 ↔ Commute x y := by
  rw [Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

/-- The good central-coset tuple count is invariant under isoclinism. -/
theorem card_goodCentralTuples_eq_of_isoclinic
    (G H : Type*) [Group G] [Group H] (h : Isoclinic G H) (r : ℕ) :
    Nat.card (goodCentralTuples G r) = Nat.card (goodCentralTuples H r) := by
  obtain ⟨φ, ψ, hcompat⟩ := h.exists_iso
  have hcomm : ∀ (q t : G ⧸ Subgroup.center G),
      Commute (centralRep G q) (centralRep G t) ↔
        Commute (centralRep H (φ q)) (centralRep H (φ t)) := by
    intro q t
    have hc := hcompat (centralRep G q) (centralRep G t)
      (centralRep H (φ q)) (centralRep H (φ t))
      (by rw [centralRep_mk, centralRep_mk])
      (by rw [centralRep_mk, centralRep_mk])
    rw [← cmap_eq_one_iff, ← cmap_eq_one_iff, ← hc, ψ.map_eq_one_iff]
  let e : (Fin r → G ⧸ Subgroup.center G) ≃ (Fin r → H ⧸ Subgroup.center H) :=
    Equiv.piCongrRight (fun _ => φ.toEquiv)
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e (fun q => by
    change (∀ i j, Commute (centralRep G (q i)) (centralRep G (q j))) ↔
      (∀ i j, Commute (centralRep H (φ (q i))) (centralRep H (φ (q j))))
    simp_rw [hcomm])

/-- Dividing the exact lift count cancels the positive center factor. -/
theorem higherCommProb_eq_good_div_quotient (G : Type*) [Group G] [Finite G] (r : ℕ) :
    higherCommProb G r = (Nat.card (goodCentralTuples G r) : ℚ) /
      (Nat.card (G ⧸ Subgroup.center G) : ℚ) ^ r := by
  have hz : (Nat.card (Subgroup.center G) : ℚ) ≠ 0 := by
    exact_mod_cast (Finite.card_pos (α := Subgroup.center G)).ne'
  rw [higherCommProb_def, card_commTuples_eq_good_mul_center,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)]
  push_cast
  rw [mul_pow, mul_div_mul_right _ _ (pow_ne_zero r hz)]

end IsoclinismHigherCommProb

/-- **Isoclinism invariance of higher commuting probability**, for `2 ≤ r`.
Compatible quotient and derived-subgroup isomorphisms transport the identity
commutator fiber; the central lift multiplicities cancel in the probability. -/
theorem higherCommProb_eq_of_isoclinic (G H : Type*) [Group G] [Group H]
    [Finite G] [Finite H] (h : IsoclinismInvariants.Isoclinic G H)
    (r : ℕ) (hr : 2 ≤ r) : higherCommProb G r = higherCommProb H r := by
  letI : Nonempty (Fin r) := ⟨⟨0, lt_of_lt_of_le (by decide : 0 < 2) hr⟩⟩
  obtain ⟨φ, ψ, hcompat⟩ := h.exists_iso
  have hquot : Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) :=
    Nat.card_congr φ.toEquiv
  rw [IsoclinismHigherCommProb.higherCommProb_eq_good_div_quotient,
    IsoclinismHigherCommProb.higherCommProb_eq_good_div_quotient,
    IsoclinismHigherCommProb.card_goodCentralTuples_eq_of_isoclinic G H h r, hquot]

example : Isoclinic (DihedralGroup 4) (DihedralGroup 4) ∧ 2 ≤ (2 : ℕ) := by
  constructor
  · refine ⟨MulEquiv.refl _, MulEquiv.refl _, ?_⟩
    intro x y x' y' hx hy
    apply Subtype.ext
    exact (commutatorElement_eq_of_quotient_eq hx hy).symm
  · decide
