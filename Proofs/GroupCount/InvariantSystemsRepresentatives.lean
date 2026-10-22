/-
# Invariant systems of representatives

A. A. Klyachko and N. M. Luneva, *Invariant systems of representatives,
or The cost of symmetry*, arXiv:1908.03315, Main theorem (Introduction)
and Section 3.

For an arbitrary group acting on `U`, a finite hitting set `X` for an
invariant family of finite subsets of size at most `m` yields an invariant
finite hitting set `Y` with `|Y| ≤ m · |X|`. The unordered family is represented
by `Set (Finset U)`; `m` is any uniform bound, rather than a chosen maximum.

`costSet` consists of points with finite orbit satisfying
`|Gy| ≤ m · |Gy ∩ X|`. The proof uses B. H. Neumann's coset-covering inequality
([Neu54], Proposition 4.5, as cited in Section 3), via Mathlib's
`Subgroup.one_le_sum_inv_index_of_leftCoset_cover` and
`MulAction.index_stabilizer`. Infinite indices and their rational inverses
contribute zero, matching the paper's convention. Double counting the orbit
weights gives the cardinality bound.
-/
import Mathlib

set_option autoImplicit false

open MulAction
open scoped Pointwise

namespace Candidates.InvariantSystemsRepresentatives

/-- The paper's invariant system of representatives (Section 3):
`Y = {y ∈ U | |Gy ∩ X| ⩾ |Gy| / m}`, which contains no point with an infinite orbit.  It is
written here as: the orbit `Gy` is finite and `|Gy| ≤ m · |Gy ∩ X|`. -/
def costSet (G : Type*) {U : Type*} [Group G] [MulAction G U] (X : Finset U) (m : ℕ) : Set U :=
  {y | (orbit G y).Finite ∧ (orbit G y).ncard ≤ m * (orbit G y ∩ (X : Set U)).ncard}

section Main

variable {G U : Type*} [Group G] [MulAction G U]

/-- Neumann step (Section 3): if every translate `g • s` meets `X`, then the cosets
`g_x · St(f)` (`f ∈ s`, `x ∈ X ∩ Gf`) cover `G`, and B. H. Neumann's inequality gives
`1 ≤ ∑_{f ∈ s} |Gf ∩ X| / |Gf|` (an infinite orbit contributes `0`). -/
theorem neumann_step (s X : Finset U)
    (hcov : ∀ g : G, ∃ f ∈ s, g • f ∈ X) :
    (1 : ℚ) ≤ ∑ f ∈ s, ((orbit G f ∩ (X : Set U)).ncard : ℚ) / (orbit G f).ncard := by
  classical
  let t : Finset (U × U) := (s ×ˢ X).filter (fun p => p.2 ∈ orbit G p.1)
  let g : U × U → G := fun p => if h : p.2 ∈ orbit G p.1 then (mem_orbit_iff.mp h).choose else 1
  let H : U × U → Subgroup G := fun p => stabilizer G p.1
  have hcovers : ⋃ i ∈ t, g i • (H i : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨f, hf, hfX⟩ := hcov a
    have hmem : a • f ∈ orbit G f := mem_orbit f a
    refine Set.mem_iUnion₂.mpr ⟨(f, a • f), ?_, ?_⟩
    · simp only [t, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hf, hfX⟩, hmem⟩
    · rw [mem_leftCoset_iff]
      have hspec := (mem_orbit_iff.mp hmem).choose_spec
      simp only [g, H, dif_pos hmem, SetLike.mem_coe, mem_stabilizer_iff, mul_smul]
      exact inv_smul_eq_iff.mpr hspec.symm
  have hN := Subgroup.one_le_sum_inv_index_of_leftCoset_cover hcovers
  refine hN.trans (le_of_eq ?_)
  simp only [t, H, index_stabilizer]
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hset : ((X.filter (fun x => x ∈ orbit G f) : Finset U) : Set U) =
      orbit G f ∩ (X : Set U) := by
    ext x
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe]
    exact and_comm
  rw [← hset, Set.ncard_coe_finset]

/-- The set `Y` is `G`-invariant: `g • y` has the same orbit as `y`. -/
theorem smul_mem_costSet {X : Finset U} {m : ℕ} {y : U} (g : G) (hy : y ∈ costSet G X m) :
    g • y ∈ costSet G X m := by
  simpa only [costSet, Set.mem_ofPred_eq, orbit_smul] using hy

/-- The set `Y` is finite: it is contained in the union of the finite orbits meeting `X`. -/
theorem costSet_finite (X : Finset U) (m : ℕ) : (costSet G X m).Finite := by
  have hsub : costSet G X m ⊆ ⋃ x ∈ (X : Set U), orbit G x ∩ costSet G X m := by
    intro y hy
    have hpos : 0 < (orbit G y).ncard := (Set.ncard_pos hy.1).mpr ⟨y, mem_orbit_self y⟩
    have hne : (orbit G y ∩ (X : Set U)).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have h2 := hy.2
      rw [hcon, Set.ncard_empty, mul_zero] at h2
      omega
    obtain ⟨x, hxo, hxX⟩ := hne
    exact Set.mem_iUnion₂.mpr ⟨x, hxX, mem_orbit_symm.mp hxo, hy⟩
  refine Set.Finite.subset (Set.Finite.biUnion X.finite_toSet fun x _ => ?_) hsub
  by_cases hne : (orbit G x ∩ costSet G X m).Nonempty
  · obtain ⟨y, hyo, hy⟩ := hne
    have heq : orbit G y = orbit G x := orbit_eq_iff.mpr hyo
    exact (heq ▸ hy.1).subset Set.inter_subset_left
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

open Classical in
/-- `|Gy ∩ X|` as a sum of indicators over `X`. -/
theorem ncard_orbit_inter_eq_sum (X : Finset U) (y : U) :
    ((orbit G y ∩ (X : Set U)).ncard : ℚ) = ∑ x ∈ X, if x ∈ orbit G y then (1 : ℚ) else 0 := by
  have hset : ((X.filter (fun x => x ∈ orbit G y) : Finset U) : Set U) =
      orbit G y ∩ (X : Set U) := by
    ext x
    simp only [Finset.coe_filter, Set.mem_inter_iff, Finset.mem_coe]
    exact and_comm
  rw [← hset, Set.ncard_coe_finset, Finset.sum_boole]

open Classical in
/-- For a finite set `T` of points with finite orbits and any point `x`,
`∑_{y ∈ T, x ∈ Gy} 1/|Gy| ≤ 1`, since those `y` all lie in the orbit `Gx`. -/
theorem sum_inv_ncard_le_one (T : Finset U) (hT : ∀ y ∈ T, (orbit G y).Finite) (x : U) :
    ∑ y ∈ T, (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) ≤ 1 := by
  have hterm : ∀ y ∈ T, (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) =
      if y ∈ orbit G x then ((orbit G x).ncard : ℚ)⁻¹ else 0 := by
    intro y _
    by_cases hxy : x ∈ orbit G y
    · have heq : orbit G x = orbit G y := orbit_eq_iff.mpr hxy
      rw [if_pos hxy, if_pos (mem_orbit_symm.mp hxy), heq]
    · rw [if_neg hxy, if_neg (fun h => hxy (mem_orbit_symm.mp h))]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hne : (T.filter (fun y => y ∈ orbit G x)).Nonempty
  · obtain ⟨y, hy⟩ := hne
    rw [Finset.mem_filter] at hy
    have hfin : (orbit G x).Finite := (orbit_eq_iff.mpr hy.2 : orbit G y = orbit G x) ▸ hT y hy.1
    have hpos : 0 < (orbit G x).ncard := (Set.ncard_pos hfin).mpr ⟨x, mem_orbit_self x⟩
    have hcard : (T.filter (fun y => y ∈ orbit G x)).card ≤ (orbit G x).ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun z hz => ?_) hfin
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
    rw [← div_eq_mul_inv, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact zero_le_one

/-- The bound `|Y| ≤ m · |X|` (Section 3), by double counting
`∑_{y ∈ Y} ∑_{x ∈ X ∩ Gy} 1/|Gy|`. -/
theorem card_costSet_le (X : Finset U) (m : ℕ) :
    (costSet_finite (G := G) X m).toFinset.card ≤ m * X.card := by
  classical
  set T := (costSet_finite (G := G) X m).toFinset with hTdef
  have hmemT : ∀ y ∈ T, y ∈ costSet G X m := fun y hy => (Set.Finite.mem_toFinset _).mp hy
  have hT : ∀ y ∈ T, (orbit G y).Finite := fun y hy => (hmemT y hy).1
  have hone : ∀ y ∈ T, (1 : ℚ) ≤
      m * ∑ x ∈ X, (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) := by
    intro y hy
    have hyY := hmemT y hy
    have hpos : 0 < (orbit G y).ncard := (Set.ncard_pos hyY.1).mpr ⟨y, mem_orbit_self y⟩
    have hsum : ∑ x ∈ X, (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) =
        (∑ x ∈ X, if x ∈ orbit G y then (1 : ℚ) else 0) * ((orbit G y).ncard : ℚ)⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [hsum, ← ncard_orbit_inter_eq_sum, ← mul_assoc, ← div_eq_mul_inv,
      le_div_iff₀ (by exact_mod_cast hpos), one_mul]
    exact_mod_cast hyY.2
  have hq : (T.card : ℚ) ≤ m * X.card := by
    calc (T.card : ℚ) = ∑ _y ∈ T, (1 : ℚ) := by simp
      _ ≤ ∑ y ∈ T, (m : ℚ) *
            ∑ x ∈ X, (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) :=
          Finset.sum_le_sum hone
      _ = m * ∑ x ∈ X, ∑ y ∈ T,
            (if x ∈ orbit G y then ((orbit G y).ncard : ℚ)⁻¹ else 0) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ m * ∑ _x ∈ X, (1 : ℚ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => sum_inv_ncard_le_one T hT x)
            (Nat.cast_nonneg m)
      _ = m * X.card := by simp
  exact_mod_cast hq

/-- A point outside `Y` has `m · |Gf ∩ X| / |Gf| < 1`. -/
theorem mul_ratio_lt_one_of_notMem {X : Finset U} {m : ℕ} {f : U}
    (hf : f ∉ costSet G X m) :
    (m : ℚ) * (((orbit G f ∩ (X : Set U)).ncard : ℚ) / (orbit G f).ncard) < 1 := by
  by_cases hfin : (orbit G f).Finite
  · have hlt : m * (orbit G f ∩ (X : Set U)).ncard < (orbit G f).ncard := by
      by_contra hcon
      exact hf ⟨hfin, not_lt.mp hcon⟩
    have hpos : (0 : ℚ) < (orbit G f).ncard := by
      exact_mod_cast (Set.ncard_pos hfin).mpr ⟨f, mem_orbit_self f⟩
    rw [← mul_div_assoc, div_lt_one hpos]
    exact_mod_cast hlt
  · rw [Set.Infinite.ncard hfin, Nat.cast_zero, div_zero, mul_zero]
    exact zero_lt_one

variable [DecidableEq U]

/-- **Main theorem** (Klyachko–Luneva, arXiv:1908.03315).  Let a group `G` act on `U`, let
`F` be a `G`-invariant family of finite subsets of `U` of cardinality at most `m`, and let `X`
be a finite system of representatives for `F` (`X` meets every member of `F`).  Then there is
a `G`-invariant system of representatives `Y` with `|Y| ≤ m · |X|`. -/
theorem exists_invariant_systemOfRepresentatives (F : Set (Finset U))
    (hF : ∀ g : G, ∀ s ∈ F, s.image (g • ·) ∈ F)
    (m : ℕ) (hm : ∀ s ∈ F, s.card ≤ m) (X : Finset U) (hX : ∀ s ∈ F, (s ∩ X).Nonempty) :
    ∃ Y : Finset U, (∀ g : G, Y.image (g • ·) = Y) ∧ (∀ s ∈ F, (s ∩ Y).Nonempty) ∧
      Y.card ≤ m * X.card := by
  refine ⟨(costSet_finite (G := G) X m).toFinset, fun g => ?_, fun s hs => ?_,
    card_costSet_le X m⟩
  · ext z
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact smul_mem_costSet g hy
    · intro hz
      exact ⟨g⁻¹ • z, smul_mem_costSet g⁻¹ hz, smul_inv_smul g z⟩
  · have hcov : ∀ g : G, ∃ f ∈ s, g • f ∈ X := by
      intro g
      obtain ⟨z, hz⟩ := hX _ (hF g s hs)
      rw [Finset.mem_inter, Finset.mem_image] at hz
      obtain ⟨⟨f, hf, rfl⟩, hzX⟩ := hz
      exact ⟨f, hf, hzX⟩
    have hN := neumann_step (G := G) s X hcov
    by_contra hcon
    have hnot : ∀ f ∈ s, f ∉ costSet G X m := by
      intro f hf hfY
      exact hcon ⟨f, Finset.mem_inter.mpr ⟨hf, (Set.Finite.mem_toFinset _).mpr hfY⟩⟩
    have hsne : s.Nonempty := (hX s hs).mono Finset.inter_subset_left
    have hlt : (m : ℚ) * ∑ f ∈ s, ((orbit G f ∩ (X : Set U)).ncard : ℚ) / (orbit G f).ncard <
        s.card := by
      rw [Finset.mul_sum]
      calc ∑ f ∈ s, (m : ℚ) * (((orbit G f ∩ (X : Set U)).ncard : ℚ) / (orbit G f).ncard)
          < ∑ _f ∈ s, (1 : ℚ) :=
            Finset.sum_lt_sum_of_nonempty hsne fun f hf => mul_ratio_lt_one_of_notMem (hnot f hf)
        _ = s.card := by simp
    have hsm : (s.card : ℚ) ≤ m := by exact_mod_cast hm s hs
    have hge : (m : ℚ) * 1 ≤
        m * ∑ f ∈ s, ((orbit G f ∩ (X : Set U)).ncard : ℚ) / (orbit G f).ncard :=
      mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg m)
    linarith


/-- Paper alias for the Main theorem of arXiv:1908.03315. -/
theorem main_theorem (F : Set (Finset U)) (hF : ∀ g : G, ∀ s ∈ F, s.image (g • ·) ∈ F)
    (m : ℕ) (hm : ∀ s ∈ F, s.card ≤ m) (X : Finset U) (hX : ∀ s ∈ F, (s ∩ X).Nonempty) :
    ∃ Y : Finset U, (∀ g : G, Y.image (g • ·) = Y) ∧ (∀ s ∈ F, (s ∩ Y).Nonempty) ∧
      Y.card ≤ m * X.card :=
  exists_invariant_systemOfRepresentatives F hF m hm X hX

end Main

/-! ## Examples -/

/-- For `costSet`, with `S₂` acting on `Fin 2` and `X = {0}`, the single orbit
has size `2` and meets `X` once, so with `m = 2` both points lie in `Y`. -/
example : (0 : Fin 2) ∈ costSet (Equiv.Perm (Fin 2)) {0} 2 ∧
    (1 : Fin 2) ∈ costSet (Equiv.Perm (Fin 2)) {0} 2 := by
  have horb : ∀ y : Fin 2, orbit (Equiv.Perm (Fin 2)) y = Set.univ := fun y => orbit_eq_univ _ y
  have hinter : (Set.univ ∩ ((({0} : Finset (Fin 2))) : Set (Fin 2))) = {0} := by simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [horb, hinter, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_singleton, Set.finite_univ, mul_one, le_refl]

/-- For `costSet`, with `m = 1` the same instance has `|Gy| = 2 > 1 · 1`, so
`Y` is empty. -/
example : (0 : Fin 2) ∉ costSet (Equiv.Perm (Fin 2)) {0} 1 := by
  have horb : orbit (Equiv.Perm (Fin 2)) (0 : Fin 2) = Set.univ := orbit_eq_univ _ _
  have hinter : (Set.univ ∩ ((({0} : Finset (Fin 2))) : Set (Fin 2))) = {0} := by simp
  rintro ⟨-, h⟩
  simp only [horb, hinter, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Set.ncard_singleton] at h
  omega

/-- The hypotheses of the main theorem hold jointly for `S₃` acting on
`Fin 3`, `F` the family of all `2`-element subsets, `m = 2`, and `X = {0, 1}`. -/
example : (∀ g : Equiv.Perm (Fin 3), ∀ s ∈ {s : Finset (Fin 3) | s.card = 2},
      s.image (g • ·) ∈ {s : Finset (Fin 3) | s.card = 2}) ∧
    (∀ s ∈ {s : Finset (Fin 3) | s.card = 2}, s.card ≤ 2) ∧
    (∀ s ∈ {s : Finset (Fin 3) | s.card = 2}, (s ∩ {0, 1}).Nonempty) := by
  refine ⟨fun g s hs => ?_, fun s hs => le_of_eq hs, fun s hs => ?_⟩
  · rw [Set.mem_ofPred_eq] at hs ⊢
    rw [Finset.card_image_of_injective _ (MulAction.injective g), hs]
  · rw [Set.mem_ofPred_eq] at hs
    revert s
    decide

end Candidates.InvariantSystemsRepresentatives
