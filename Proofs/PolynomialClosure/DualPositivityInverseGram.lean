/-
# Dual positivity: the inverse Gram matrix of a positive-definite tree lattice

## Source

* arXiv:2610.27095 — Joshua Evan Greene, Ahmad Issa, Duncan McCoy,
  *Tree Lattices and the Neumann-Zagier conjecture*.
* Location: Section 2 ("Preparation"), Lemma 2.1 (`lem:dual_positivity`).
* Setup (Introduction): a finite weighted tree `T` with vertex set `V`, edge
  set `E` and weight `wt : V → ℤ` determines the tree lattice `L(T)`, the free
  abelian group on `V` with `u · v = wt(u)` if `u = v`, `-1` if `(u,v) ∈ E`,
  and `0` otherwise.
* Verbatim claim:
  "Let $L(T)$ be a positive definite tree lattice. Let
   $v^*=\sum_{x\in V} \nu_x x$ be the dual to a vertex $v$. Then $\nu_x>0$ for
   all $x \in V$."
* Date recorded: 2026-10-21.
* Status: proved in the paper (sign-splitting argument); it is also the
  classical fact that the inverse of an irreducible nonsingular M-matrix
  (Stieltjes matrix) is entrywise positive (Berman-Plemmons; Varga).

## Formalization

The dual vector `v^*` has coefficient vector `ν` characterised by
`x · v^* = δ_{xv}`, i.e. `A *ᵥ ν = Pi.single v 1` where `A` is the Gram
matrix; equivalently `ν x = A⁻¹ x v`.  We prove the general statement for a
positive-definite real matrix with nonpositive off-diagonal entries that are
strictly negative along the edges of a connected graph, following the paper's
proof (which uses only these properties), and specialise to `treeForm`.
-/
import Mathlib

set_option autoImplicit false

namespace DualPositivityInverseGram

open Matrix

variable {V : Type*} [Fintype V]

/-- The Gram matrix of the graph lattice of a weighted graph `G` with weights
`wt : V → ℤ`: `wt u` on the diagonal, `-1` on edges, `0` on non-adjacent
distinct pairs.  For a tree `G` this is the tree-lattice pairing of
arXiv:2610.27095, Section 1. -/
def treeForm [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℤ) :
    Matrix V V ℝ :=
  fun u v => if u = v then (wt u : ℝ) else if G.Adj u v then -1 else 0

open scoped Classical in
/-- Ground truth: the path on two vertices with weights `2` has diagonal `2`. -/
example : treeForm (SimpleGraph.pathGraph 2) (fun _ => 2) 0 0 = 2 := by
  simp [treeForm]

open scoped Classical in
/-- Ground truth: the path on two vertices has off-diagonal entry `-1`. -/
example : treeForm (SimpleGraph.pathGraph 2) (fun _ => 2) 0 1 = -1 := by
  simp [treeForm, SimpleGraph.pathGraph_adj]

open scoped Classical in
/-- Ground truth: non-adjacent distinct vertices (ends of the path on three
vertices) pair to `0`. -/
example : treeForm (SimpleGraph.pathGraph 3) (fun _ => 2) 0 2 = 0 := by
  simp [treeForm, SimpleGraph.pathGraph_adj]

/-- First half of the paper's argument: if `A` is positive definite (only the
strict positivity of the quadratic form is used) with nonpositive off-diagonal
entries, and `A *ᵥ ν` is entrywise nonnegative, then `ν` is entrywise
nonnegative (the negative part `n` of `ν` must vanish). -/
theorem nonneg_of_mulVec_nonneg {A : Matrix V V ℝ}
    (hA : ∀ x : V → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
    (hoff : ∀ u v, u ≠ v → A u v ≤ 0) {ν : V → ℝ}
    (hν : ∀ x, 0 ≤ (A *ᵥ ν) x) : ∀ x, 0 ≤ ν x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  set n : V → ℝ := fun y => min (ν y) 0 with hn_def
  set p : V → ℝ := fun y => max (ν y) 0 with hp_def
  have hsplit : ν = p + n := by
    funext y
    simp only [Pi.add_apply, hp_def, hn_def]
    rcases le_total (ν y) 0 with h | h
    · rw [max_eq_right h, min_eq_left h, zero_add]
    · rw [max_eq_left h, min_eq_right h, add_zero]
  have hn_ne : n ≠ 0 := by
    intro h
    have h0 : n x₀ = 0 := by rw [h]; rfl
    simp only [hn_def, min_eq_left hx₀.le] at h0
    linarith
  have hquad : 0 < n ⬝ᵥ (A *ᵥ n) := hA n hn_ne
  -- some term of the quadratic form is positive
  obtain ⟨x, hx⟩ : ∃ x, 0 < n x * (A *ᵥ n) x := by
    by_contra hall
    push Not at hall
    have hle : n ⬝ᵥ (A *ᵥ n) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hall i
    linarith
  have hnx_le : n x ≤ 0 := min_le_right _ _
  have hnx : n x < 0 := by
    rcases hnx_le.lt_or_eq with h | h
    · exact h
    · rw [h, zero_mul] at hx; exact absurd hx (lt_irrefl 0)
  have hAn : (A *ᵥ n) x < 0 := by
    by_contra h
    push Not at h
    have hprod := mul_nonpos_of_nonpos_of_nonneg hnx_le h
    linarith
  have hνx : ν x < 0 := by
    by_contra h
    push Not at h
    have hn0 : n x = 0 := min_eq_right h
    linarith
  have hpx : p x = 0 := max_eq_right hνx.le
  have hAp : (A *ᵥ p) x ≤ 0 := by
    change ∑ y, A x y * p y ≤ 0
    refine Finset.sum_nonpos fun y _ => ?_
    by_cases hy : x = y
    · subst hy; rw [hpx, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff x y hy) (le_max_right _ _)
  have hsum : (A *ᵥ ν) x = (A *ᵥ p) x + (A *ᵥ n) x := by
    rw [hsplit, mulVec_add, Pi.add_apply]
  have hνx' := hν x
  linarith

/-- Second half of the paper's argument: if `ν ≥ 0`, `A *ᵥ ν ≥ 0`, the
off-diagonal entries of `A` are nonpositive and `A y x < 0`, then `ν x > 0`
forces `ν y > 0`. -/
theorem pos_of_pos_of_entry_neg {A : Matrix V V ℝ}
    (hoff : ∀ u v, u ≠ v → A u v ≤ 0) {ν : V → ℝ}
    (hν0 : ∀ x, 0 ≤ ν x) (hν : ∀ x, 0 ≤ (A *ᵥ ν) x) {x y : V}
    (hyx : A y x < 0) (hx : 0 < ν x) : 0 < ν y := by
  classical
  rcases (hν0 y).lt_or_eq with h | h
  · exact h
  exfalso
  have hxy : x ≠ y := by
    rintro rfl
    linarith
  have hrest : ∑ z ∈ Finset.univ.erase x, A y z * ν z ≤ 0 := by
    refine Finset.sum_nonpos fun z _ => ?_
    by_cases hz : y = z
    · subst hz; rw [← h, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff y z hz) (hν0 z)
  have hexpand : (A *ᵥ ν) y = A y x * ν x + ∑ z ∈ Finset.univ.erase x, A y z * ν z :=
    (Finset.add_sum_erase Finset.univ (fun z => A y z * ν z) (Finset.mem_univ x)).symm
  have hneg : A y x * ν x < 0 := mul_neg_of_neg_of_pos hyx hx
  have hνy := hν y
  linarith

/-- Dual positivity in vector form (Lemma 2.1 of arXiv:2610.27095, general
version): let `G` be a connected graph and `A` a positive-definite real matrix
with `A u v ≤ 0` for `u ≠ v` and `A u v < 0` on edges of `G`.  If `ν` solves
`A *ᵥ ν = e_v` (so `ν` is the coefficient vector of the dual element `v^*`),
then every coefficient `ν x` is strictly positive. -/
theorem dual_pos_of_posDef {G : SimpleGraph V} (hG : G.Connected) {A : Matrix V V ℝ}
    (hA : A.PosDef) (hoff : ∀ u v, u ≠ v → A u v ≤ 0)
    (hadj : ∀ u v, G.Adj u v → A u v < 0) [DecidableEq V] (v : V) {ν : V → ℝ}
    (hν : A *ᵥ ν = Pi.single v 1) : ∀ x, 0 < ν x := by
  have hquad : ∀ x : V → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := fun x hx => by
    simpa using hA.dotProduct_mulVec_pos hx
  have hAν : ∀ x, 0 ≤ (A *ᵥ ν) x := fun x => by
    rw [hν]
    by_cases hx : x = v
    · subst hx; simp
    · simp [hx]
  have hν0 := nonneg_of_mulVec_nonneg hquad hoff hAν
  -- `ν v > 0`: otherwise `(A *ᵥ ν) v ≤ 0`
  have hνv : 0 < ν v := by
    rcases (hν0 v).lt_or_eq with h | h
    · exact h
    exfalso
    have hle : (A *ᵥ ν) v ≤ 0 := by
      change ∑ y, A v y * ν y ≤ 0
      refine Finset.sum_nonpos fun y _ => ?_
      by_cases hy : v = y
      · subst hy; rw [← h, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff v y hy) (hν0 y)
    rw [hν] at hle
    simp only [Pi.single_eq_same] at hle
    linarith
  -- propagate positivity along a walk to `v`
  have hwalk : ∀ y z : V, G.Walk y z → 0 < ν z → 0 < ν y := by
    intro y z w hz
    induction w with
    | nil => exact hz
    | cons hadj' _ ih =>
      exact pos_of_pos_of_entry_neg hoff hν0 hAν (hadj _ _ hadj') (ih hz)
  intro x
  obtain ⟨w⟩ := hG.preconnected x v
  exact hwalk x v w hνv

/-- Dual positivity in matrix form: under the hypotheses of
`dual_pos_of_posDef`, every entry of the inverse Gram matrix `A⁻¹` is strictly
positive (the classical positivity of the inverse of an irreducible Stieltjes
matrix). -/
theorem inv_pos_of_posDef [DecidableEq V] {G : SimpleGraph V} (hG : G.Connected)
    {A : Matrix V V ℝ} (hA : A.PosDef) (hoff : ∀ u v, u ≠ v → A u v ≤ 0)
    (hadj : ∀ u v, G.Adj u v → A u v < 0) (u v : V) : 0 < A⁻¹ u v := by
  have hdet : IsUnit A.det := (hA.det_pos).ne'.isUnit
  have hν : A *ᵥ (A⁻¹ *ᵥ Pi.single v 1) = Pi.single v 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  have hpos := dual_pos_of_posDef hG hA hoff hadj v hν u
  rwa [mulVec_single_one] at hpos

/-- Lemma 2.1 (`lem:dual_positivity`) of arXiv:2610.27095: if `T` is a
weighted tree whose tree lattice `L(T)` is positive definite, and
`v^* = ∑ ν_x x` is the dual to a vertex `v` (i.e. `x · v^* = δ_{xv}`), then
`ν_x > 0` for all vertices `x`. -/
theorem lem_2_1 [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj] (hT : T.IsTree)
    (wt : V → ℤ) (hpd : (treeForm T wt).PosDef) (v : V) {ν : V → ℝ}
    (hν : treeForm T wt *ᵥ ν = Pi.single v 1) : ∀ x, 0 < ν x := by
  refine dual_pos_of_posDef hT.connected hpd ?_ ?_ v hν
  · intro u w huw
    simp only [treeForm, if_neg huw]
    split_ifs <;> norm_num
  · intro u w huw
    simp only [treeForm, if_neg (T.ne_of_adj huw), if_pos huw]
    norm_num

/-- Matrix form of Lemma 2.1 of arXiv:2610.27095: the inverse Gram matrix of a
positive-definite tree lattice is entrywise strictly positive. -/
theorem treeForm_inv_pos [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (wt : V → ℤ) (hpd : (treeForm T wt).PosDef) (u v : V) :
    0 < (treeForm T wt)⁻¹ u v := by
  refine inv_pos_of_posDef hT.connected hpd ?_ ?_ u v
  · intro a b hab
    simp only [treeForm, if_neg hab]
    split_ifs <;> norm_num
  · intro a b hab
    simp only [treeForm, if_neg (T.ne_of_adj hab), if_pos hab]
    norm_num

/-! ## Non-vacuity: the two-vertex path with weights `2` (the `A₂` lattice) -/

/-- The path on two vertices is a tree. -/
theorem pathGraph_two_isTree : (SimpleGraph.pathGraph 2).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.pathGraph_connected 1, ?_⟩
  rw [SimpleGraph.pathGraph_two_eq_top, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

open scoped Classical in
/-- The tree lattice of the two-vertex path with weights `2` (the root
lattice `A₂`) is positive definite: `2a² - 2ab + 2b² = a² + b² + (a - b)²`. -/
theorem treeForm_pathGraph_two_posDef :
    (treeForm (SimpleGraph.pathGraph 2) (fun _ => 2)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [treeForm, SimpleGraph.pathGraph_adj]
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [dotProduct, Pi.star_apply, star_trivial, mulVec, treeForm, Int.cast_ofNat,
      SimpleGraph.pathGraph_adj, ite_mul, neg_mul, one_mul, zero_mul, Fin.sum_univ_two,
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff,
      one_ne_zero, and_false, zero_add, false_or, Nat.mod_succ, Nat.add_eq_right, Nat.reduceAdd,
      ↓reduceIte, zero_ne_one, OfNat.ofNat_ne_zero, or_false, gt_iff_lt]
    rcases hx' with h | h
    · have hsq := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1)]
    · have hsq := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0)]

open scoped Classical in
/-- Ground truth for the dual characterisation: in `A₂`, the dual of vertex `0`
is `0^* = (2/3)·0 + (1/3)·1`, i.e. `A *ᵥ (2/3, 1/3) = e₀`. -/
example : treeForm (SimpleGraph.pathGraph 2) (fun _ => 2) *ᵥ ![2/3, 1/3] =
    Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, treeForm,
    SimpleGraph.pathGraph_adj] <;> norm_num

open scoped Classical in
/-- Non-vacuity of `treeForm_inv_pos`: all hypotheses hold jointly for the
two-vertex path with weights `2`. -/
example (u v : Fin 2) : 0 < (treeForm (SimpleGraph.pathGraph 2) (fun _ => 2))⁻¹ u v :=
  treeForm_inv_pos pathGraph_two_isTree _ treeForm_pathGraph_two_posDef u v

end DualPositivityInverseGram

