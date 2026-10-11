import Combinatorics.NoncommutingDenseWindow
import Mathlib.Data.Finset.Prod

/-!
# Density transport to marked unequal-overlap rectangles

This is the geometric input to the dense-box halo argument, not a proof of the
halo estimate. The same finite hole set `E` appears before and after enlargement;
points outside its support contribute zero. In particular holes are not enlarged.
-/

set_option autoImplicit false

namespace NoncommutingDense

/-- Enlarging each side by a factor at most `κ` changes a one-third-density
rectangle into a rectangle satisfying the density inequality at `1/(3κ²)`.
The hole set remains exactly `E`. The denominator-free conclusion also makes
sense at empty rectangles; nonempty windows are certified separately below. -/
theorem rectangle_density_transport (E : Finset (ℤ × ℤ))
    (I J U V : Finset ℤ) (κ : ℝ) (hκ : 1 ≤ κ)
    (hI : I ⊆ U) (hJ : J ⊆ V)
    (hU : (U.card : ℝ) ≤ κ * I.card) (hV : (V.card : ℝ) ≤ κ * J.card)
    (hdensity : ((I ×ˢ J).card : ℝ) ≤ 3 * (E ∩ (I ×ˢ J)).card) :
    ((U ×ˢ V).card : ℝ) ≤ 3 * κ ^ 2 * (E ∩ (U ×ˢ V)).card := by
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have harea : ((U ×ˢ V).card : ℝ) ≤ κ ^ 2 * (I ×ˢ J).card := by
    simp only [Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ (κ * I.card) * (κ * J.card) :=
        mul_le_mul hU hV (Nat.cast_nonneg _) (mul_nonneg hκ0 (Nat.cast_nonneg _))
      _ = _ := by ring
  have hcount : ((E ∩ (I ×ˢ J)).card : ℝ) ≤ (E ∩ (U ×ˢ V)).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter (Finset.Subset.refl E) (Finset.product_subset_product hI hJ))
  calc
    _ ≤ κ ^ 2 * (I ×ˢ J).card := harea
    _ ≤ κ ^ 2 * (3 * (E ∩ (I ×ˢ J)).card) :=
      mul_le_mul_of_nonneg_left hdensity (sq_nonneg κ)
    _ ≤ κ ^ 2 * (3 * (E ∩ (U ×ˢ V)).card) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount (by norm_num))
        (sq_nonneg κ)
    _ = _ := by ring

/-- A dense normalized overlap rectangle has a nonempty enlarged window,
a marked point inside it, and the required transported density. Both windows
lie in their fixed expanded grids; the hole set is unchanged. -/
theorem overlapRectangle_certificate (E : Finset (ℤ × ℤ))
    (u v t u' v' t' : ℤ) (κ : ℝ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 0 ≤ t) (htop : t ≤ u + v - 2)
    (hu' : 1 ≤ u') (hv' : 1 ≤ v') (ht' : 0 ≤ t') (htop' : t' ≤ u' + v' - 2)
    (hκ : 1 ≤ κ) (hvu : (v : ℝ) ≤ κ * u) (hvu' : (v' : ℝ) ≤ κ * u')
    (hdensity : ((overlap u v t ×ˢ overlap u' v' t').card : ℝ) ≤
      3 * (E ∩ (overlap u v t ×ˢ overlap u' v' t')).card) :
    (overlapWindow u v t ×ˢ overlapWindow u' v' t').Nonempty ∧
    (overlapMark u v t, overlapMark u' v' t') ∈
      overlapWindow u v t ×ˢ overlapWindow u' v' t' ∧
    overlapWindow u v t ×ˢ overlapWindow u' v' t' ⊆
      Finset.Icc 0 (max u v - 1) ×ˢ Finset.Icc 0 (max u' v' - 1) ∧
    ((overlapWindow u v t ×ˢ overlapWindow u' v' t').card : ℝ) ≤
      3 * κ ^ 2 * (E ∩ (overlapWindow u v t ×ˢ overlapWindow u' v' t')).card := by
  obtain ⟨hsub, hmark, hgrid⟩ := overlapWindow_geometry u v t hu hv ht htop
  obtain ⟨hsub', hmark', hgrid'⟩ := overlapWindow_geometry u' v' t' hu' hv' ht' htop'
  have hpair : (overlapMark u v t, overlapMark u' v' t') ∈
      overlapWindow u v t ×ˢ overlapWindow u' v' t' :=
    Finset.mem_product.mpr ⟨hmark, hmark'⟩
  refine ⟨⟨_, hpair⟩, hpair, Finset.product_subset_product hgrid hgrid', ?_⟩
  exact rectangle_density_transport E _ _ _ _ κ hκ hsub hsub'
    (overlapWindow_card_le u v t κ hu hv ht htop hκ hvu)
    (overlapWindow_card_le u' v' t' κ hu' hv' ht' htop' hκ hvu') hdensity

/-- For fixed side pairs, the two-coordinate mark has at most four preimages
in any finite source set, without any extra reflection factor. -/
theorem card_overlapMark_pair_fiber_le_four (u v u' v' q q' : ℤ)
    (T : Finset (ℤ × ℤ)) :
    (T.filter (fun p => overlapMark u v p.1 = q ∧ overlapMark u' v' p.2 = q')).card ≤ 4 := by
  have hsub : T.filter (fun p => overlapMark u v p.1 = q ∧
      overlapMark u' v' p.2 = q') ⊆ {q, q + v - 1} ×ˢ {q', q' + v' - 1} := by
    intro p hp
    obtain ⟨hfirst, hsecond⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_product.mpr
    constructor
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        overlapMark_sources u v p.1 q hfirst
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        overlapMark_sources u' v' p.2 q' hsecond
  have hfirst : ({q, q + v - 1} : Finset ℤ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hsecond : ({q', q' + v' - 1} : Finset ℤ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  calc
    _ ≤ (({q, q + v - 1} : Finset ℤ) ×ˢ ({q', q' + v' - 1} : Finset ℤ)).card := Finset.card_le_card hsub
    _ = ({q, q + v - 1} : Finset ℤ).card * ({q', q' + v' - 1} : Finset ℤ).card :=
      Finset.card_product _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hfirst hsecond
    _ = 4 := rfl

example : ((overlap 1 1 0 ×ˢ overlap 1 1 0).card : ℝ) ≤
    3 * (({(0,0)} : Finset (ℤ × ℤ)) ∩ (overlap 1 1 0 ×ˢ overlap 1 1 0)).card := by
  norm_num [overlap, Int.card_Icc]

example : ((overlapWindow 1 1 0 ×ˢ overlapWindow 1 1 0).card : ℝ) ≤
    3 * (1 : ℝ) ^ 2 *
      (({(0,0)} : Finset (ℤ × ℤ)) ∩ (overlapWindow 1 1 0 ×ˢ overlapWindow 1 1 0)).card := by
  have h := overlapRectangle_certificate {(0,0)} 1 1 0 1 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [overlap])
  exact h.2.2.2

example : ((overlapWindow 2 4 2 ×ˢ overlapWindow 2 4 2).card : ℝ) ≤
    3 * (2 : ℝ) ^ 2 *
      (({(0,0),(0,1),(1,0),(1,1)} : Finset (ℤ × ℤ)) ∩
        (overlapWindow 2 4 2 ×ˢ overlapWindow 2 4 2)).card := by
  have h := overlapRectangle_certificate {(0,0),(0,1),(1,0),(1,1)} 2 4 2 2 4 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      have hside : (overlap 2 4 2).card = 2 := by decide
      have hholes : (({(0,0),(0,1),(1,0),(1,1)} : Finset (ℤ × ℤ)) ∩
          (overlap 2 4 2 ×ˢ overlap 2 4 2)).card = 4 := by decide
      norm_num [Finset.card_product, hside, hholes])
  exact h.2.2.2

end NoncommutingDense
