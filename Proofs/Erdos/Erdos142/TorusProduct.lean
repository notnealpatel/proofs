/-
  Erdős Problem #142 — flat product of the torus grid.

  The transfer of the Ehps argument runs on the residue grid
  `Fin (2*k) → ZMod q`, which is the `k`-fold product of the torus square
  `ZMod q × ZMod q` in the two-coordinate block order supplied by
  `finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2*k)`.  This module makes that
  identification explicit and computes the resulting finite products:

  * `flatBlockEquiv q k : (Fin (2*k) → ZMod q) ≃ (Fin k → ZMod q × ZMod q)`
    with forward map `blockPair`, whose block `i` consists of the entries at
    `finProdFinEquiv (0, i)` and `finProdFinEquiv (1, i)`;
  * `torusGridProduct ε q k`, the flat product of the torus grid under the
    embedding `(flatBlockEquiv q k).symm.toEmbedding`, with an exact
    membership characterisation and cardinality `(torusGrid ε q).card ^ k`;
  * `torusProductEnergy ε q k x = ∑ i, torusF ε (torusLift q (blockPair q k x i))`,
    together with its membership-dependent nonnegativity and the audited upper
    bound `(k : ℝ) * ((2921/144)/ε^2)`;
  * the reciprocal-parameter forms at `ε = e⁻¹`, for `6 ≤ e`, in the exact
    syntactic shape `(2921/144 : ℝ) * (k : ℝ) * e^2` consumed by
    `Erdos.Erdos142.EnergySlicing`;
  * the subtype `TorusProductPoint ε q k` of grid points and its energy, ready
    for the ambient energy-bin argument (not proved here).

  No affine or AP-free transfer is attempted; this module only sets up the flat
  product and its energy interface.
-/

import Erdos.Erdos142.TorusGrid
import Erdos.Erdos142.TorusEnergyBounds

set_option autoImplicit false

namespace Erdos142

/-- The forward **block projection**: reading a flat grid vector
`x : Fin (2*k) → ZMod q` as a `k`-indexed family of torus-square points.  Block
`i` collects the entries at `finProdFinEquiv (0, i)` and `finProdFinEquiv (1, i)`. -/
def blockPair (q k : ℕ) (x : Fin (2 * k) → ZMod q) : Fin k → ZMod q × ZMod q :=
  fun i => (x (finProdFinEquiv (0, i)), x (finProdFinEquiv (1, i)))

/-- The inverse of `blockPair`: reading a `k`-indexed family `y` of torus-square
points as a flat grid vector.  The address `finProdFinEquiv.symm j` decides
whether the entry of `j` is the first coordinate (block index `0`) or the second
coordinate (block index `1`) of the corresponding block. -/
def blockUnpair (q k : ℕ) (y : Fin k → ZMod q × ZMod q) : Fin (2 * k) → ZMod q :=
  fun j =>
    let p := (finProdFinEquiv (m := 2) (n := k)).symm j
    if p.1 = 0 then (y p.2).1 else (y p.2).2

/-- **Flat block equivalence.**  The ambient group `Fin (2*k) → ZMod q` is
identified with `Fin k → (ZMod q × ZMod q)` by grouping the two coordinates of
each block.  The forward map is `blockPair`, projecting the entries at
`finProdFinEquiv (0, i)` and `finProdFinEquiv (1, i)`; the inverse `blockUnpair`
inspects `finProdFinEquiv.symm`. -/
def flatBlockEquiv (q k : ℕ) :
    (Fin (2 * k) → ZMod q) ≃ (Fin k → ZMod q × ZMod q) where
  toFun := blockPair q k
  invFun := blockUnpair q k
  left_inv x := by
    funext j
    generalize hp : (finProdFinEquiv (m := 2) (n := k)).symm j = p
    obtain ⟨r, i⟩ := p
    have hfst : ((finProdFinEquiv (m := 2) (n := k)).symm j).1 = r := by rw [hp]
    have hsnd : ((finProdFinEquiv (m := 2) (n := k)).symm j).2 = i := by rw [hp]
    have hji : finProdFinEquiv (m := 2) (n := k) (r, i) = j := by
      rw [← hp, Equiv.apply_symm_apply]
    fin_cases r
    · simp only [blockUnpair, blockPair, hfst, hsnd]
      exact congrArg x hji
    · simp only [blockUnpair, blockPair, hfst, hsnd]
      exact congrArg x hji
  right_inv y := by
    funext i
    ext <;> simp [blockUnpair, blockPair]

/-- The forward map of `flatBlockEquiv` is `blockPair`. -/
@[simp]
theorem flatBlockEquiv_apply (q k : ℕ) (x : Fin (2 * k) → ZMod q) :
    flatBlockEquiv q k x = blockPair q k x := rfl

/-- The inverse map of `flatBlockEquiv` is `blockUnpair`. -/
@[simp]
theorem flatBlockEquiv_symm_apply (q k : ℕ) (y : Fin k → ZMod q × ZMod q) :
    (flatBlockEquiv q k).symm y = blockUnpair q k y := rfl

/-- Definitional unfolding of `blockPair` at a block index. -/
@[simp]
theorem blockPair_apply (q k : ℕ) (x : Fin (2 * k) → ZMod q) (i : Fin k) :
    blockPair q k x i = (x (finProdFinEquiv (0, i)), x (finProdFinEquiv (1, i))) := rfl

/-- The first coordinate of block `i` is the entry at `finProdFinEquiv (0, i)`. -/
@[simp]
theorem blockPair_fst (q k : ℕ) (x : Fin (2 * k) → ZMod q) (i : Fin k) :
    (blockPair q k x i).1 = x (finProdFinEquiv (0, i)) := rfl

/-- The second coordinate of block `i` is the entry at `finProdFinEquiv (1, i)`. -/
@[simp]
theorem blockPair_snd (q k : ℕ) (x : Fin (2 * k) → ZMod q) (i : Fin k) :
    (blockPair q k x i).2 = x (finProdFinEquiv (1, i)) := rfl

/-- `blockPair` preserves the zero vector. -/
@[simp]
theorem blockPair_zero (q k : ℕ) :
    blockPair q k (0 : Fin (2 * k) → ZMod q) = 0 := by
  funext i
  ext <;> simp

/-- `blockPair` preserves negation. -/
@[simp]
theorem blockPair_neg (q k : ℕ) (x : Fin (2 * k) → ZMod q) :
    blockPair q k (-x) = -blockPair q k x := by
  funext i
  ext <;> simp

/-- `blockPair` preserves addition. -/
@[simp]
theorem blockPair_add (q k : ℕ) (x y : Fin (2 * k) → ZMod q) :
    blockPair q k (x + y) = blockPair q k x + blockPair q k y := by
  funext i
  ext <;> simp

/-- `blockPair` preserves natural scalar multiplication. -/
@[simp]
theorem blockPair_nsmul (q k : ℕ) (n : ℕ) (x : Fin (2 * k) → ZMod q) :
    blockPair q k (n • x) = n • blockPair q k x := by
  funext i
  ext <;> simp

/-- The flat product of the torus grid: the `k`-fold product of `torusGrid ε q`
transported to the ambient group `Fin (2*k) → ZMod q` by the block embedding. -/
noncomputable def torusGridProduct (ε : ℝ) (q k : ℕ) [NeZero q] :
    Finset (Fin (2 * k) → ZMod q) :=
  (Fintype.piFinset fun _ : Fin k => torusGrid ε q).map
    (flatBlockEquiv q k).symm.toEmbedding

/-- **Membership in the flat product.**  A flat grid vector lies in
`torusGridProduct ε q k` exactly when every projected block lies in the torus
grid. -/
@[simp]
theorem mem_torusGridProduct {ε : ℝ} {q k : ℕ} [NeZero q]
    {x : Fin (2 * k) → ZMod q} :
    x ∈ torusGridProduct ε q k ↔ ∀ i, blockPair q k x i ∈ torusGrid ε q := by
  rw [torusGridProduct, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Fintype.mem_piFinset] at ha
    intro i
    change blockPair q k ((flatBlockEquiv q k).symm a) i ∈ torusGrid ε q
    have hba : blockPair q k ((flatBlockEquiv q k).symm a) = a := by
      show flatBlockEquiv q k ((flatBlockEquiv q k).symm a) = a
      exact Equiv.apply_symm_apply _ _
    rw [hba]
    exact ha i
  · intro h
    exact ⟨blockPair q k x, Fintype.mem_piFinset.mpr h,
      Equiv.symm_apply_apply (flatBlockEquiv q k) x⟩

/-- **Membership through the torus predicate.**  The flat product consists
exactly of the grid vectors whose every projected block lift lies in
`torusT ε`. -/
theorem mem_torusGridProduct_iff {ε : ℝ} {q k : ℕ} [NeZero q]
    {x : Fin (2 * k) → ZMod q} :
    x ∈ torusGridProduct ε q k ↔
      ∀ i, torusT ε (torusLift q (blockPair q k x i)) := by
  rw [mem_torusGridProduct]
  exact forall_congr' fun i => mem_torusGrid

/-- **Exact cardinality of the flat product.**  It is the `k`-th power of the
single-block torus grid cardinality. -/
@[simp]
theorem card_torusGridProduct (ε : ℝ) (q k : ℕ) [NeZero q] :
    (torusGridProduct ε q k).card = (torusGrid ε q).card ^ k := by
  rw [torusGridProduct, Finset.card_map, Fintype.card_piFinset_const]

/-- The total product energy: the sum of the audited block weights
`torusF ε (torusLift q ·)` over the `k` blocks of the flat vector. -/
noncomputable def torusProductEnergy (ε : ℝ) (q k : ℕ) [NeZero q]
    (x : Fin (2 * k) → ZMod q) : ℝ :=
  ∑ i : Fin k, torusF ε (torusLift q (blockPair q k x i))

/-- **Membership-dependent nonnegativity.**  Every point of the flat product has
nonnegative total energy. -/
theorem torusProductEnergy_nonneg {ε : ℝ} {q k : ℕ} [NeZero q] (hε : 0 < ε)
    {x : Fin (2 * k) → ZMod q} (hx : x ∈ torusGridProduct ε q k) :
    0 ≤ torusProductEnergy ε q k x := by
  rw [torusProductEnergy]
  exact Finset.sum_nonneg fun i _ =>
    torusF_nonneg hε (mem_torusGrid.mp ((mem_torusGridProduct.mp hx) i))

/-- **Membership-dependent upper bound.**  For `0 < ε ≤ 1/6`, every point of the
flat product has total energy at most `k * ((2921/144)/ε^2)`. -/
theorem torusProductEnergy_le {ε : ℝ} {q k : ℕ} [NeZero q] (hε : 0 < ε)
    (hεle : ε ≤ 1 / 6) {x : Fin (2 * k) → ZMod q}
    (hx : x ∈ torusGridProduct ε q k) :
    torusProductEnergy ε q k x ≤ (k : ℝ) * ((2921 / 144 : ℝ) / ε ^ 2) := by
  rw [torusProductEnergy]
  exact torusF_sum_le hε hεle fun i =>
    mem_torusGrid.mp ((mem_torusGridProduct.mp hx) i)

/-- **Reciprocal-parameter nonnegativity.**  At `ε = e⁻¹` with `6 ≤ e`, every
point of the flat product has nonnegative total energy. -/
theorem torusProductEnergy_nonneg_inv {e : ℝ} {q k : ℕ} [NeZero q]
    (he : 6 ≤ e) {x : Fin (2 * k) → ZMod q} (hx : x ∈ torusGridProduct e⁻¹ q k) :
    0 ≤ torusProductEnergy e⁻¹ q k x :=
  torusProductEnergy_nonneg (inv_pos.mpr (by linarith)) hx

/-- **Reciprocal-parameter upper bound.**  At `ε = e⁻¹` with `6 ≤ e`, every
point of the flat product satisfies

  `torusProductEnergy e⁻¹ q k x ≤ (2921 / 144 : ℝ) * (k : ℝ) * e^2`,

the exact syntactic shape required by `EnergySlicing`. -/
theorem torusProductEnergy_le_inv {e : ℝ} {q k : ℕ} [NeZero q] (he : 6 ≤ e)
    {x : Fin (2 * k) → ZMod q} (hx : x ∈ torusGridProduct e⁻¹ q k) :
    torusProductEnergy e⁻¹ q k x ≤ (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2 := by
  have he0 : (0 : ℝ) < e := by linarith
  have hε : (0 : ℝ) < e⁻¹ := inv_pos.mpr he0
  have hεle : e⁻¹ ≤ 1 / 6 := by
    rw [show (1 / 6 : ℝ) = 6⁻¹ by norm_num, inv_le_inv₀ he0 (by norm_num)]
    exact he
  calc torusProductEnergy e⁻¹ q k x
      ≤ (k : ℝ) * ((2921 / 144 : ℝ) / e⁻¹ ^ 2) := torusProductEnergy_le hε hεle hx
    _ = (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2 := by
        rw [inv_pow, div_inv_eq_mul]
        ring

/-- A point of the flat product, as a subtype carrying its membership proof.
This is the finite type on which the ambient energy-bin argument runs. -/
abbrev TorusProductPoint (ε : ℝ) (q k : ℕ) [NeZero q] : Type :=
  {x : Fin (2 * k) → ZMod q // x ∈ torusGridProduct ε q k}

/-- The product energy restricted to the subtype of flat-product points. -/
noncomputable def torusProductPointEnergy (ε : ℝ) (q k : ℕ) [NeZero q]
    (X : TorusProductPoint ε q k) : ℝ :=
  torusProductEnergy ε q k X.1

/-- Nonnegativity of the product energy on the subtype, in the `∀ X` shape used
by `EnergySlicing`. -/
theorem torusProductPointEnergy_nonneg_inv {e : ℝ} {q k : ℕ} [NeZero q]
    (he : 6 ≤ e) (X : TorusProductPoint e⁻¹ q k) :
    0 ≤ torusProductPointEnergy e⁻¹ q k X :=
  torusProductEnergy_nonneg_inv he X.2

/-- Upper bound `(2921/144) * k * e²` for the product energy on the subtype, in
the `∀ X` shape used by `EnergySlicing`. -/
theorem torusProductPointEnergy_le_inv {e : ℝ} {q k : ℕ} [NeZero q]
    (he : 6 ≤ e) (X : TorusProductPoint e⁻¹ q k) :
    torusProductPointEnergy e⁻¹ q k X ≤ (2921 / 144 : ℝ) * (k : ℝ) * e ^ 2 :=
  torusProductEnergy_le_inv he X.2

-- Ground-truth checks protecting the block coordinate order and cardinality.

/-- Coordinate-order check: for `q = 5`, `k = 2`, the flat vector
`![1,2,3,4]` groups as `(x 0, x 2) = (1, 3)` and `(x 1, x 3) = (2, 4)`. -/
example :
    blockPair 5 2 ![(1 : ZMod 5), 2, 3, 4] (0 : Fin 2) = ((1 : ZMod 5), 3) ∧
      blockPair 5 2 ![(1 : ZMod 5), 2, 3, 4] (1 : Fin 2) = ((2 : ZMod 5), 4) := by
  constructor <;> decide

/-- Inverse check on the same data: ungrouping `(1,3), (2,4)` recovers
`![1,2,3,4]`. -/
example :
    (flatBlockEquiv 5 2).symm
        ![((1 : ZMod 5), (3 : ZMod 5)), ((2 : ZMod 5), (4 : ZMod 5))] =
      ![(1 : ZMod 5), 2, 3, 4] := by
  funext j
  fin_cases j <;> decide

/-- Degenerate cardinality check: for `k = 0` the flat product is a singleton,
consistently with `(torusGrid ε q).card ^ 0 = 1`. -/
example (ε : ℝ) (q : ℕ) [NeZero q] : (torusGridProduct ε q 0).card = 1 := by
  rw [card_torusGridProduct]
  simp

#print axioms blockPair
#print axioms blockPair_zero
#print axioms blockPair_neg
#print axioms blockPair_add
#print axioms blockPair_nsmul
#print axioms flatBlockEquiv
#print axioms mem_torusGridProduct
#print axioms mem_torusGridProduct_iff
#print axioms card_torusGridProduct
#print axioms torusProductEnergy_nonneg
#print axioms torusProductEnergy_le
#print axioms torusProductEnergy_nonneg_inv
#print axioms torusProductEnergy_le_inv
#print axioms torusProductPointEnergy_nonneg_inv
#print axioms torusProductPointEnergy_le_inv

end Erdos142
