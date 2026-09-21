/-
  Erdős Problem #142 — flat-vector slices of the torus product.

  This module turns the `EnergySlicing` subtype bin of `TorusProductPoint` into
  an ambient slice of the flat grid `Fin (2*k) → ZMod q`, transports the product
  torus separation theorem across a modular three-term arithmetic progression
  inside one slice, and concludes that the flat endpoint difference lies in the
  concrete signed short box `shortBox R q (2*k)`.

  The slice width is `Δ = (R:ℝ)^2 / (2 * (q:ℝ)^2)`, matching both the
  `EnergySlicing` handoff and `torusF_product_slice_separation_sq`.

  The pipeline is:

  * `torusProductSlice e q k R j` — the ambient half-open energy slice;
  * `torusProductSlice_eq_map_energyBin` / `card_torusProductSlice_eq_energyBin`
    — the subtype bin maps onto the ambient slice with equal cardinality;
  * `exists_torusProductSlice_card_mul_le_41` — the quantitative slice-count
    consumer at `ε = e⁻¹`, in the coefficient `41` shape;
  * `torusProductSlice_separation_sq` — modular 3-AP separation inside one slice
    via `torusF_product_slice_separation_sq`;
  * `sub_mem_shortBox_of_block_sq_lt` / `sub_mem_shortBox_of_torusProductSlice_AP`
    — the endpoint signed-box bridge via `sub_mem_shortSignedSet_of_lift_sq_lt`.

  This module stops immediately before proving affine preimages AP-free; it
  performs no affine averaging, avoidance choice, or final transfer inequality.
-/

import Erdos.Erdos142.TorusProduct
import Erdos.Erdos142.TorusTransferArithmetic
import Erdos.Erdos142.EnergySlicing

set_option autoImplicit false

namespace Erdos142

/-- **Ambient flat-vector slice.**  The points of the flat torus-grid product
`torusGridProduct e⁻¹ q k` whose total energy `torusProductEnergy e⁻¹ q k` lies
in the half-open band `[j*Δ, j*Δ + Δ)`, where `Δ = (R:ℝ)^2/(2*(q:ℝ)^2)`. -/
noncomputable def torusProductSlice (e : ℝ) (q k R j : ℕ) [NeZero q] :
    Finset (Fin (2 * k) → ZMod q) :=
  (torusGridProduct e⁻¹ q k).filter fun x =>
    (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ≤ torusProductEnergy e⁻¹ q k x ∧
      torusProductEnergy e⁻¹ q k x <
        (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) +
          ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2))

/-- **Membership in an ambient slice.**  It is exactly product membership plus
the two half-open band inequalities. -/
@[simp]
theorem mem_torusProductSlice {e : ℝ} {q k R j : ℕ} [NeZero q]
    {x : Fin (2 * k) → ZMod q} :
    x ∈ torusProductSlice e q k R j ↔
      x ∈ torusGridProduct e⁻¹ q k ∧
        (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ≤ torusProductEnergy e⁻¹ q k x ∧
          torusProductEnergy e⁻¹ q k x <
            (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) +
              ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) := by
  simp [torusProductSlice]

/-- Every ambient slice is contained in the flat torus-grid product. -/
theorem torusProductSlice_subset (e : ℝ) (q k R j : ℕ) [NeZero q] :
    torusProductSlice e q k R j ⊆ torusGridProduct e⁻¹ q k :=
  Finset.filter_subset _ _

/-- **Subtype-bin bridge.**  Mapping the `EnergySlicing` bin of the subtype
`TorusProductPoint e⁻¹ q k` through the subtype-value embedding gives exactly
the ambient slice `torusProductSlice e q k R j`. -/
theorem torusProductSlice_eq_map_energyBin {e : ℝ} {q k R : ℕ} [NeZero q] (j : ℕ) :
    torusProductSlice e q k R j =
      (energyBin (torusProductPointEnergy e⁻¹ q k)
          ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) j).map
        (Function.Embedding.subtype
          (fun x : Fin (2 * k) → ZMod q => x ∈ torusGridProduct e⁻¹ q k)) := by
  ext x
  rw [mem_torusProductSlice, Finset.mem_map]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨x, hx⟩, by rw [mem_energyBin]; exact ⟨h1, h2⟩, rfl⟩
  · rintro ⟨X, hX, hval⟩
    rw [mem_energyBin] at hX
    rw [← hval]
    exact ⟨X.2, by simpa [torusProductPointEnergy] using hX⟩

/-- **Cardinality of the ambient slice.**  The ambient slice has the same
cardinality as the corresponding subtype energy bin. -/
theorem card_torusProductSlice_eq_energyBin {e : ℝ} {q k R : ℕ} [NeZero q] (j : ℕ) :
    (torusProductSlice e q k R j).card =
      (energyBin (torusProductPointEnergy e⁻¹ q k)
        ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) j).card := by
  rw [torusProductSlice_eq_map_energyBin, Finset.card_map]

/-- **Cardinality of the subtype.**  The subtype of flat-product points has
`(torusGrid ε q).card ^ k` elements, matching `card_torusGridProduct`. -/
theorem card_torusProductPoint (ε : ℝ) (q k : ℕ) [NeZero q] :
    Fintype.card (TorusProductPoint ε q k) = (torusGrid ε q).card ^ k := by
  rw [← card_torusGridProduct ε q k]
  exact Fintype.card_coe (torusGridProduct ε q k)

/-- **Quantitative ambient-slice existence.**  For `6 ≤ e`, positive `q` and
positive `R`, some slice index `j` (with the pigeonhole bound
`j < ⌊M/Δ⌋ + 1`, `M = (2921/144) k e²`, `Δ = R²/(2q²)`) satisfies

  `((torusGrid e⁻¹ q).card ^ k : ℝ) * R² ≤
     (41 * k * e² * q² + R²) * (torusProductSlice e q k R j).card`,

by transporting `exists_energyBin_card_mul_le_41` along the subtype bridge. -/
theorem exists_torusProductSlice_card_mul_le_41 {e : ℝ} {q k R : ℕ} [NeZero q]
    (he : 6 ≤ e) (hq : 0 < q) (hR : 0 < R) :
    ∃ j : ℕ,
      j < Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
            ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2))) + 1 ∧
        (((torusGrid e⁻¹ q).card ^ k : ℕ) : ℝ) * (R : ℝ) ^ 2 ≤
          (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
            ((torusProductSlice e q k R j).card : ℝ) := by
  obtain ⟨j, hjlt, hjcard⟩ :=
    exists_energyBin_card_mul_le_41
      (P := TorusProductPoint e⁻¹ q k) (E := torusProductPointEnergy e⁻¹ q k)
      (k := k) (e := e) (q := (q : ℝ)) (R := (R : ℝ))
      (by exact_mod_cast hq) (by exact_mod_cast hR)
      (torusProductPointEnergy_nonneg_inv he) (torusProductPointEnergy_le_inv he)
  refine ⟨j, hjlt, ?_⟩
  rw [card_torusProductPoint, ← card_torusProductSlice_eq_energyBin] at hjcard
  exact hjcard

/-- **Modular 3-AP separation inside one ambient slice.**  If flat vectors
`X, Y, Z` all lie in the same slice and satisfy `X + Z = 2 • Y`, then in every
block both lift-coordinate endpoint squares are strictly below `2*Δ` with
`Δ = (R:ℝ)^2/(2*(q:ℝ)^2)`.  This is `torusF_product_slice_separation_sq`
applied to the block lifts, with the integer wraps coming from `torusLift_wrap`
on the block-wise progression. -/
theorem torusProductSlice_separation_sq {e : ℝ} {q k R j : ℕ} [NeZero q]
    (he : 6 ≤ e) {X Y Z : Fin (2 * k) → ZMod q}
    (hX : X ∈ torusProductSlice e q k R j)
    (hY : Y ∈ torusProductSlice e q k R j)
    (hZ : Z ∈ torusProductSlice e q k R j)
    (hAP : X + Z = 2 • Y) :
    ∀ i : Fin k,
      ((torusLift q (blockPair q k X i)).1 -
          (torusLift q (blockPair q k Z i)).1) ^ 2 <
        2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ∧
      ((torusLift q (blockPair q k X i)).2 -
          (torusLift q (blockPair q k Z i)).2) ^ 2 <
        2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) := by
  have he0 : (0 : ℝ) < e := by linarith
  have hε : (0 : ℝ) < e⁻¹ := inv_pos.mpr he0
  have hεle : e⁻¹ ≤ 1 / 6 := by
    rw [show (1 / 6 : ℝ) = 6⁻¹ by norm_num, inv_le_inv₀ he0 (by norm_num)]
    exact he
  have hT : ∀ (x : Fin (2 * k) → ZMod q), x ∈ torusProductSlice e q k R j →
      ∀ i, torusT e⁻¹ (torusLift q (blockPair q k x i)) := fun x hx i =>
    mem_torusGridProduct_iff.mp (mem_torusProductSlice.mp hx).1 i
  have hAPblock : ∀ i, blockPair q k X i + blockPair q k Z i =
      2 • blockPair q k Y i := fun i => by
    have h := congrFun (congrArg (blockPair q k) hAP) i
    simpa using h
  have hwrap : ∀ i : Fin k, ∃ w₁ w₂ : ℤ,
      (torusLift q (blockPair q k X i)).1 + (torusLift q (blockPair q k Z i)).1 -
          2 * (torusLift q (blockPair q k Y i)).1 = (w₁ : ℝ) ∧
        (torusLift q (blockPair q k X i)).2 + (torusLift q (blockPair q k Z i)).2 -
          2 * (torusLift q (blockPair q k Y i)).2 = (w₂ : ℝ) :=
    fun i => torusLift_wrap (hAPblock i)
  choose w₁ w₂ hw₁ hw₂ using hwrap
  have hXband : (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k X i)) ∧
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k X i)) <
        (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) +
          ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) := by
    have h := (mem_torusProductSlice.mp hX).2
    simpa only [torusProductEnergy] using h
  have hYband : (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k Y i)) ∧
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k Y i)) <
        (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) +
          ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) := by
    have h := (mem_torusProductSlice.mp hY).2
    simpa only [torusProductEnergy] using h
  have hZband : (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k Z i)) ∧
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
          torusF e⁻¹ (torusLift q (blockPair q k Z i)) <
        (j : ℝ) * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) +
          ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) := by
    have h := (mem_torusProductSlice.mp hZ).2
    simpa only [torusProductEnergy] using h
  have hsep := torusF_product_slice_separation_sq hε hεle
    (Finset.univ : Finset (Fin k))
    (fun i => torusLift q (blockPair q k X i))
    (fun i => torusLift q (blockPair q k Y i))
    (fun i => torusLift q (blockPair q k Z i))
    (fun i _ => hT X hX i) (fun i _ => hT Y hY i) (fun i _ => hT Z hZ i)
    w₁ w₂ (fun i _ => hw₁ i) (fun i _ => hw₂ i)
    hXband hYband hZband
  intro i
  exact hsep i (Finset.mem_univ i)

/-- **Blockwise signed-box bridge.**  If in every block both lift-coordinate
endpoint squares are below `2*Δ`, then `X - Z` lies in the concrete signed box
`shortBox R q (2*k)`.  The coordinates of `X - Z` are recovered from their
`(Fin 2, Fin k)` block addresses via `mem_shortBox`, and each one is discharged
by `sub_mem_shortSignedSet_of_lift_sq_lt`. -/
theorem sub_mem_shortBox_of_block_sq_lt {q k R : ℕ} [NeZero q]
    (hq : 0 < q) (hR : 1 ≤ R) {X Z : Fin (2 * k) → ZMod q}
    (h : ∀ i : Fin k,
      ((torusLift q (blockPair q k X i)).1 -
          (torusLift q (blockPair q k Z i)).1) ^ 2 <
        2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) ∧
      ((torusLift q (blockPair q k X i)).2 -
          (torusLift q (blockPair q k Z i)).2) ^ 2 <
        2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2))) :
    X - Z ∈ shortBox R q (2 * k) := by
  rw [mem_shortBox]
  intro jj
  rw [Pi.sub_apply]
  set p := (finProdFinEquiv (m := 2) (n := k)).symm jj with hp
  have hjj : finProdFinEquiv (m := 2) (n := k) p = jj := by
    rw [hp, Equiv.apply_symm_apply]
  by_cases hr : p.1 = 0
  · have hjj' : jj = finProdFinEquiv (m := 2) (n := k) (0, p.2) := by
      rw [← hjj]
      congr 1
      exact Prod.ext hr rfl
    rw [hjj']
    simp only [← blockPair_fst]
    exact sub_mem_shortSignedSet_of_lift_sq_lt hq hR
      (by simpa [torusLift] using (h p.2).1)
  · have hr1 : p.1 = 1 := by
      have hlt : (p.1).val < 2 := (p.1).isLt
      have hne : (p.1).val ≠ 0 := fun h0 => hr (Fin.ext (by simpa using h0))
      have hv : (p.1).val = 1 := by omega
      exact Fin.ext (by simpa using hv)
    have hjj' : jj = finProdFinEquiv (m := 2) (n := k) (1, p.2) := by
      rw [← hjj]
      congr 1
      exact Prod.ext hr1 rfl
    rw [hjj']
    simp only [← blockPair_snd]
    exact sub_mem_shortSignedSet_of_lift_sq_lt hq hR
      (by simpa [torusLift] using (h p.2).2)

/-- **Endpoint signed-box bridge for modular 3-APs in one slice.**  If
`X + Z = 2 • Y` and `X, Y, Z` all lie in the same ambient slice, then the flat
endpoint difference `X - Z` (this orientation, matching
`sub_mem_shortSignedSet_of_lift_sq_lt`) belongs to the concrete signed box
`shortBox R q (2*k)`. -/
theorem sub_mem_shortBox_of_torusProductSlice_AP {e : ℝ} {q k R j : ℕ} [NeZero q]
    (he : 6 ≤ e) (hq : 0 < q) (hR : 1 ≤ R)
    {X Y Z : Fin (2 * k) → ZMod q}
    (hX : X ∈ torusProductSlice e q k R j)
    (hY : Y ∈ torusProductSlice e q k R j)
    (hZ : Z ∈ torusProductSlice e q k R j)
    (hAP : X + Z = 2 • Y) :
    X - Z ∈ shortBox R q (2 * k) :=
  sub_mem_shortBox_of_block_sq_lt hq hR (torusProductSlice_separation_sq he hX hY hZ hAP)

-- Degenerate ground-truth checks.

/-- Every ambient slice sits inside the flat torus-grid product, at every `k`. -/
example (e : ℝ) (q R j k : ℕ) [NeZero q] :
    torusProductSlice e q k R j ⊆ torusGridProduct e⁻¹ q k :=
  torusProductSlice_subset e q k R j

/-- At `k = 0` the flat group is a subsingleton, so any slice has at most one
point (and the bridge `sub_mem_shortBox_of_torusProductSlice_AP` applies
vacuously). -/
example (e : ℝ) (q R j : ℕ) [NeZero q] : (torusProductSlice e q 0 R j).card ≤ 1 :=
  Finset.card_le_one.mpr fun a _ b _ => by
    funext j
    exact Fin.elim0 j

#print axioms mem_torusProductSlice
#print axioms torusProductSlice_eq_map_energyBin
#print axioms card_torusProductSlice_eq_energyBin
#print axioms card_torusProductPoint
#print axioms exists_torusProductSlice_card_mul_le_41
#print axioms torusProductSlice_separation_sq
#print axioms sub_mem_shortBox_of_block_sq_lt
#print axioms sub_mem_shortBox_of_torusProductSlice_AP

end Erdos142