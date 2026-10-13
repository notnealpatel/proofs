import GroupTPP.CharDegreesComm
import GroupTPP.CharDegreesMul
import GroupTPP.BCGPUBarrier
import GroupTPP.IsoclinismInvariants

set_option autoImplicit false

namespace GroupTPP.CharDegrees

/-- Taking a direct product with a finite abelian group preserves the smallest
character degree greater than one, including the zero default for empty support. -/
theorem minNontrivIrrepDim_prod_comm (G A : Type*)
    [Group G] [Fintype G] [CommGroup A] [Fintype A] :
    minNontrivIrrepDim (G × A) = minNontrivIrrepDim G := by
  classical
  have hcard : Fintype.card A ≠ 0 := Fintype.card_pos.ne'
  have hmem (d : ℕ) : d ∈ charDegrees (G × A) ↔ d ∈ charDegrees G := by
    rw [CharDegreesMul.charDegrees_prod, CharDegreesComm.charDegrees_of_commGroup]
    simp [Multiset.mem_bind, Multiset.mem_replicate, hcard]
  have hsupport :
      ((charDegrees (G × A)).filter (fun d => 1 < d)).toFinset =
        ((charDegrees G).filter (fun d => 1 < d)).toFinset := by
    ext d
    simp [hmem]
  unfold minNontrivIrrepDim
  rw [hsupport]

/-- A finite abelian group has no character degree greater than one, so its
minimum nontrivial irreducible degree uses the zero default. -/
theorem minNontrivIrrepDim_eq_zero_of_commGroup (G : Type*)
    [CommGroup G] [Fintype G] : minNontrivIrrepDim G = 0 := by
  classical
  unfold minNontrivIrrepDim
  rw [CharDegreesComm.charDegrees_of_commGroup]
  simp

open scoped IsMulCommutative

/-- For any finite group, the minimum nontrivial irreducible degree is zero
exactly when the number of noncentral conjugacy classes is zero. Both detect
commutativity, with the degree minimum using zero for empty support. -/
theorem minNontrivIrrepDim_eq_zero_iff_nc_eq_zero (G : Type*)
    [Group G] [Fintype G] :
    minNontrivIrrepDim G = 0 ↔ IsoclinismInvariants.nc G = 0 := by
  classical
  by_cases hcomm : IsMulCommutative G
  · letI : IsMulCommutative G := hcomm
    have hdim : minNontrivIrrepDim G = 0 :=
      minNontrivIrrepDim_eq_zero_of_commGroup G
    have hempty : IsEmpty (ConjClasses.noncenter G) := by
      refine ⟨fun c => ?_⟩
      obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c.val
      have hc := c.property
      rw [← hg, ConjClasses.mem_noncenter] at hc
      obtain ⟨a, ha, b, hb, hab⟩ := hc
      have hag : a = g := by
        simpa only [ConjClasses.mem_carrier_iff_mk_eq,
          ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] using ha
      have hbg : b = g := by
        simpa only [ConjClasses.mem_carrier_iff_mk_eq,
          ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] using hb
      exact hab (hag.trans hbg.symm)
    have hnc : IsoclinismInvariants.nc G = 0 := by
      letI := hempty
      exact Nat.card_eq_zero.mpr (Or.inl hempty)
    exact ⟨fun _ => hnc, fun _ => hdim⟩
  · have hnc : 0 < IsoclinismInvariants.nc G :=
      IsoclinismInvariants.nc_pos_of_not_commutative hcomm
    have hnoncomm : ∃ a b : G, a * b ≠ b * a := by
      simpa only [isMulCommutative_iff, not_forall] using hcomm
    have hdim : 2 ≤ minNontrivIrrepDim G :=
      BCGPUBarrier.two_le_minNontrivIrrepDim hnoncomm
    constructor
    · intro hzero
      omega
    · intro hzero
      omega

example : Nonempty (Multiplicative (ZMod 2)) := ⟨1⟩

example : minNontrivIrrepDim
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
      minNontrivIrrepDim (Multiplicative (ZMod 2)) :=
  minNontrivIrrepDim_prod_comm _ _

example : minNontrivIrrepDim (Multiplicative (ZMod 2)) = 0 ∧
    IsoclinismInvariants.nc (Multiplicative (ZMod 2)) = 0 := by
  have hdim := minNontrivIrrepDim_eq_zero_of_commGroup (Multiplicative (ZMod 2))
  exact ⟨hdim, (minNontrivIrrepDim_eq_zero_iff_nc_eq_zero _).mp hdim⟩

end GroupTPP.CharDegrees
