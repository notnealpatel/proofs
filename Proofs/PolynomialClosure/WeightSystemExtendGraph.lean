/-
# Vertex-deletion recurrence for the `c = 3/8` extension `φ`

D. Fomichev, M. Karev, F. Pavutnitskiy, S. Usanov,
"`sl(2)`-weight system does not extend to a graph 4-invariant", arXiv:2607.24217,
Section 3, Conjecture `conj:del-vert-2d`.  The function `φ` is defined in
Section 2, after Proposition `proposition:lando`.  The source states the
recurrence as a conjecture and proves the degree-two case; degree one is the
leaf relation.  `conj_del_vert_2d` gives the recurrence for every positive degree.
This is not a formalization of the whole weight-system or nonextendability
theorem.

A graph is a symmetric zero-diagonal `M : Matrix V V (ZMod 2)` on an ambient
`Fintype V`, restricted to a finite vertex set `S`.  The recurrence requires
`x ∈ S` and a chosen neighbour `a₁ ∈ A = nbhd M S x`, so `k = |A|` is positive.
Deleting a vertex is `S.erase`.  The function `phi` uses the source's formula
`2^{-2|S|} ∑_{U ⊆ S} (-1/2)^{|S \ U|} 2^{η(G|_U)}`, where `η` is the corank
of the induced adjacency matrix over `𝔽₂`.

With the conventions of Theorem `theorem:del-vert-3d`, `G_x` deletes `x`;
`Ḡ_x` also toggles every edge inside `A`.  The graphs `G_x^{a₁}` and
`Ḡ_x^{a₁}` apply the 2T transforms for `(a₁, aᵢ)`, `i = 2, …, k`, then delete
`a₁`.  A single 2T transform adds `a₁`'s row to `aᵢ`'s row and then its column
to `aᵢ`'s column.  The operations `compl` and `twoTs` preserve zero diagonals
for symmetric matrices, so no framing appears.  The simultaneous congruence
`twoTs = E M Eᵀ` agrees with iterated `twoT` by `twoTs_insert`.

## Proof outline

`phi_eq_stateSum` turns `φ` into `8^{-n} ∑_{v ∈ 𝔽₂^S} ∏_i wt(v_i, (Mv)_i)` by
rank–nullity and `Finset.prod_add`.  All five state sums are expanded over
states on `S \ {x, a₁}` and the two extra coordinates.  Edge complementation
is absorbed by the framing-flip identity
`wt v (u + v) = -(-1)^v wt v (u + 1)` (`prod_flip`), and the 2T transforms become
explicit shifts (`twoTs_mulVec`).  The remaining four-term identity at each
fixed outer state is `pointwise`.
-/
import Mathlib

set_option autoImplicit false

/-! Namespace for the formalization of Conjecture `conj:del-vert-2d` of arXiv:2607.24217. -/
namespace WeightSystemExtendGraph

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Per-vertex weight of the state sum: `wt v u` is `1, 2, -1, 0` at
`(v,u) = (0,0), (1,0), (0,1), (1,1)`;
it equals `2 * ([u = 0] - (1/2) [v = 0])`, see `wt_half`. -/
def wt (v u : ZMod 2) : ℤ :=
  if u = 0 then (if v = 0 then 1 else 2) else (if v = 0 then -1 else 0)

/-- The character `(-1)^t` of `ZMod 2`, valued in `ℤ`. -/
def sgn (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

/-- Indicator of a finset, valued in `ZMod 2`. -/
def ind (C : Finset V) (i : V) : ZMod 2 := if i ∈ C then 1 else 0

/-- Vectors over `ZMod 2` supported in `S` (the space `𝔽₂^S` inside `𝔽₂^V`). -/
def vecs (S : Finset V) : Finset (V → ZMod 2) :=
  univ.filter fun v => ∀ i, i ∉ S → v i = 0

/-- Integer state sum `F(M,S) = ∑_{v ∈ 𝔽₂^S} ∏_{i ∈ S} wt(v_i, (Mv)_i)`; `phi M S = 8^{-|S|} F(M,S)`
(`phi_eq_stateSum`). -/
def stateSum (M : Matrix V V (ZMod 2)) (S : Finset V) : ℤ :=
  ∑ v ∈ vecs S, ∏ i ∈ S, wt (v i) ((M *ᵥ v) i)

/-- Membership in `vecs S`. -/
lemma mem_vecs {S : Finset V} {v : V → ZMod 2} : v ∈ vecs S ↔ ∀ i, i ∉ S → v i = 0 := by
  simp [vecs]

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  exacts [Or.inl rfl, Or.inr rfl]

/-- Framing flip at one vertex: `wt v (u + v) = -(-1)^v * wt v (u + 1)`. -/
lemma wt_add_self (v u : ZMod 2) : wt v (u + v) = -sgn v * wt v (u + 1) := by
  fin_cases v <;> fin_cases u <;> decide

/-- `sgn` is a character. -/
lemma sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  fin_cases s <;> fin_cases t <;> decide

omit [Fintype V] in
/-- Product of signs is the sign of the sum. -/
lemma prod_sgn (C : Finset V) (y : V → ZMod 2) : ∏ i ∈ C, sgn (y i) = sgn (∑ i ∈ C, y i) := by
  induction C using Finset.induction_on with
  | empty => simp [sgn]
  | insert j C hj ih => rw [prod_insert hj, sum_insert hj, ih, sgn_add]

/-- Effect of adding `t e_j` on `M *ᵥ v`. -/
lemma mulVec_add_single (M : Matrix V V (ZMod 2)) (v : V → ZMod 2) (j : V) (t : ZMod 2) (i : V) :
    (M *ᵥ (v + Pi.single j t)) i = (M *ᵥ v) i + M i j * t := by
  simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Pi.single_apply]

/-- Splitting a sum over `𝔽₂^S` at a coordinate `x ∈ S`. -/
lemma sum_vecs_split {β : Type*} [AddCommMonoid β] (S : Finset V) (x : V) (hx : x ∈ S)
    (g : (V → ZMod 2) → β) :
    ∑ v ∈ vecs S, g v = ∑ v ∈ vecs (S.erase x), ∑ t : ZMod 2, g (v + Pi.single x t) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => p.1 + Pi.single x p.2) (fun v => (Function.update v x 0, v x))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨v, t⟩ hp
    simp only [mem_product, mem_vecs, mem_erase] at hp
    rw [mem_vecs]
    intro i hi
    have hix : i ≠ x := fun h => hi (h ▸ hx)
    simp [hix, hp.1 i (fun h => hi h.2)]
  · intro v hv
    rw [mem_vecs] at hv
    simp only [mem_product, mem_vecs, mem_erase, mem_univ, and_true]
    intro i hi
    by_cases hix : i = x
    · simp [hix]
    · simp [hix, hv i (fun h => hi ⟨hix, h⟩)]
  · rintro ⟨v, t⟩ hp
    simp only [mem_product, mem_vecs, mem_erase] at hp
    have hvx : v x = 0 := hp.1 x (fun h => h.1 rfl)
    ext i
    · by_cases hix : i = x
      · subst hix; simp [hvx]
      · simp [hix]
    · simp [hvx]
  · intro v _
    ext i
    by_cases hix : i = x
    · subst hix; simp
    · simp [hix]
  · intro p _; rfl


/-- Neighbourhood `A = {j ∈ S | M x j = 1}` of `x` in the graph `M|_S`. -/
def nbhd (M : Matrix V V (ZMod 2)) (S : Finset V) (x : V) : Finset V := S.filter fun j => M x j = 1

/-- `compl M A`: invert all edges inside `A` (off-diagonal entries of `A × A` are toggled).
For `A` the neighbourhood of `x`, `compl M A` restricted to `S \ {x}` is the paper's `Ḡ_x`. -/
def compl (M : Matrix V V (ZMod 2)) (A : Finset V) : Matrix V V (ZMod 2) :=
  Matrix.of fun i j => if i ∈ A ∧ j ∈ A ∧ i ≠ j then M i j + 1 else M i j

/-- Simultaneous 2T transforms for all pairs `(a, c)`, `c ∈ C`: the congruence `E M Eᵀ` where
`E` adds row `a` to every row in `C`. It is the iterate of the paper's single 2T transform
`twoT` (see `twoTs_empty`, `twoTs_insert`). -/
def twoTs (M : Matrix V V (ZMod 2)) (a : V) (C : Finset V) : Matrix V V (ZMod 2) :=
  Matrix.of fun i j => M i j + (if i ∈ C then M a j else 0) + (if j ∈ C then M i a else 0)
    + (if i ∈ C ∧ j ∈ C then M a a else 0)

/-- Characteristic two. -/
lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> rfl

/-- `compl M A *ᵥ v` in terms of `M *ᵥ v`. -/
lemma compl_mulVec (M : Matrix V V (ZMod 2)) (A : Finset V) (v : V → ZMod 2) (i : V) :
    (compl M A *ᵥ v) i = (M *ᵥ v) i + ind A i * (∑ j ∈ A, v j + v i) := by
  have hsplit : (compl M A *ᵥ v) i
      = (M *ᵥ v) i + ∑ j, (if i ∈ A ∧ j ∈ A ∧ i ≠ j then v j else 0) := by
    simp only [mulVec, dotProduct, compl, Matrix.of_apply, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  congr 1
  by_cases hi : i ∈ A
  · have hfilt : ∑ j, (if i ∈ A ∧ j ∈ A ∧ i ≠ j then v j else 0) = ∑ j ∈ A.erase i, v j := by
      rw [← sum_filter]
      congr 1
      ext j
      simp [hi, and_comm, eq_comm]
    have hadd := add_sum_erase A v hi
    rw [hfilt]
    simp only [ind, if_pos hi, one_mul]
    rw [← hadd, add_comm (v i), add_assoc, zmod2_add_self, add_zero]
  · simp [ind, hi]

/-- `twoTs N a C *ᵥ y` in terms of `N *ᵥ y`. -/
lemma twoTs_mulVec (N : Matrix V V (ZMod 2)) (a : V) (C : Finset V) (y : V → ZMod 2) (i : V) :
    (twoTs N a C *ᵥ y) i = (N *ᵥ y) i + ind C i * (N *ᵥ y) a + N i a * ∑ j ∈ C, y j
      + ind C i * N a a * ∑ j ∈ C, y j := by
  simp only [mulVec, dotProduct, twoTs, Matrix.of_apply, add_mul, sum_add_distrib]
  by_cases hi : i ∈ C
  · simp [hi, ind, ite_mul, sum_ite_mem, mul_sum]
  · simp [hi, ind, ite_mul, sum_ite_mem, mul_sum]


/-- Sum over `ZMod 2`. -/
lemma sum_zmod2 {β : Type*} [AddCommMonoid β] (f : ZMod 2 → β) : ∑ t : ZMod 2, f t = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- Core four-term identity at fixed outer state `y`, for arbitrary values `R s t`;
here `e = (-1)^(k-1)`. -/
lemma pointwise (R : ZMod 2 → ZMod 2 → ℤ) (α β : ZMod 2) (e : ℤ) (he : e = 1 ∨ e = -1) :
    ∑ s : ZMod 2, ∑ t : ZMod 2, wt t (β + s) * (wt s (α + t) * R s t)
      + 5 * ∑ s : ZMod 2, wt s α * R s 0
      + 4 * (-e) * ∑ s : ZMod 2, wt s (α + β) * (e * sgn β * R s (β + s + 1))
    = 6 * R β α + 6 * (-e) * (e * sgn β * R β (α + β + 1)) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  simp only [sum_zmod2]
  rcases he with rfl | rfl <;> rcases zmod2_cases α with rfl | rfl <;>
    rcases zmod2_cases β with rfl | rfl <;>
    simp only [wt, sgn, h11, add_zero, zero_add, mul_neg, mul_one, mul_zero, neg_mul, neg_neg,
      neg_zero, one_mul, one_ne_zero, zero_mul, ↓reduceIte, Int.reduceNeg] <;> ring


/-- Product over `S₂ = S \ {x, a}` with the two possible shifts of the outer state `y`. -/
def rprod (M : Matrix V V (ZMod 2)) (a : V) (C S₂ : Finset V) (y : V → ZMod 2) (s t : ZMod 2) : ℤ :=
  ∏ i ∈ S₂, wt (y i) ((M *ᵥ y) i + s * M i a + ind C i * t)

omit [Fintype V] in
/-- Removing the toggled framings on `C` costs the sign `(-1)^|C| (-1)^{∑_C y}`. -/
lemma prod_flip (S₂ C : Finset V) (hC : C ⊆ S₂) (y u : V → ZMod 2) (c : ZMod 2) :
    ∏ i ∈ S₂, wt (y i) (u i + ind C i * (c + y i))
      = (-1) ^ C.card * sgn (∑ i ∈ C, y i) * ∏ i ∈ S₂, wt (y i) (u i + ind C i * (c + 1)) := by
  have hfac : ∀ i ∈ S₂, wt (y i) (u i + ind C i * (c + y i))
      = (if i ∈ C then -sgn (y i) else 1) * wt (y i) (u i + ind C i * (c + 1)) := by
    intro i _
    by_cases hi : i ∈ C
    · simp only [ind, hi, if_true, one_mul]
      rw [← add_assoc, wt_add_self, add_assoc]
    · simp [ind, hi]
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_ite_mem, inter_eq_right.mpr hC, prod_neg,
    prod_sgn]

omit [Fintype V] [DecidableEq V] in
/-- Membership in the neighbourhood. -/
lemma mem_nbhd {M : Matrix V V (ZMod 2)} {S : Finset V} {x j : V} :
    j ∈ nbhd M S x ↔ j ∈ S ∧ M x j = 1 := mem_filter

omit [Fintype V] [DecidableEq V] in
/-- A neighbour of `x` differs from `x` (zero diagonal). -/
lemma ne_of_mem_nbhd {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0) {S : Finset V} {x j : V}
    (hj : j ∈ nbhd M S x) : j ≠ x := by
  rintro rfl
  rw [mem_nbhd, hdiag] at hj
  exact zero_ne_one hj.2

omit [Fintype V] in
/-- `A \ {a} ⊆ S \ {x, a}`. -/
lemma erase_nbhd_subset {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0) (S : Finset V)
    (x a : V) : (nbhd M S x).erase a ⊆ (S.erase x).erase a := by
  intro j hj
  rw [mem_erase] at hj ⊢
  exact ⟨hj.1, mem_erase.mpr ⟨ne_of_mem_nbhd hdiag hj.2, (mem_nbhd.mp hj.2).1⟩⟩

omit [Fintype V] in
/-- On `S \ {x, a}`, row `x` of `M` is the indicator of `A \ {a}`. -/
lemma entry_x_eq_ind {M : Matrix V V (ZMod 2)} {S : Finset V} {x a i : V}
    (hi : i ∈ (S.erase x).erase a) : M x i = ind ((nbhd M S x).erase a) i := by
  rw [mem_erase, mem_erase] at hi
  by_cases h : M x i = 1
  · rw [h, ind, if_pos (mem_erase.mpr ⟨hi.1, mem_nbhd.mpr ⟨hi.2.2, h⟩⟩)]
  · rw [ind, if_neg (fun hm => h (mem_nbhd.mp (mem_erase.mp hm).2).2)]
    exact (zmod2_cases _).resolve_right h

/-- For `y` supported in `S \ {x, a}`, `(M y)_x = ∑_{j ∈ A \ {a}} y_j`. -/
lemma mulVec_x_eq_sum {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0) {S : Finset V} {x a : V}
    {y : V → ZMod 2} (hy : y ∈ vecs ((S.erase x).erase a)) :
    (M *ᵥ y) x = ∑ j ∈ (nbhd M S x).erase a, y j := by
  rw [mem_vecs] at hy
  have h1 : (M *ᵥ y) x = ∑ j ∈ (S.erase x).erase a, M x j * y j := by
    simp only [mulVec, dotProduct]
    symm
    refine sum_subset (subset_univ _) fun j _ hj => ?_
    rw [hy j hj, mul_zero]
  rw [h1, ← sum_subset (erase_nbhd_subset hdiag S x a) (fun j hj hjC => ?_)]
  · refine sum_congr rfl fun j hj => ?_
    rw [entry_x_eq_ind (M := M) (erase_nbhd_subset hdiag S x a hj), ind, if_pos hj, one_mul]
  · rw [entry_x_eq_ind (M := M) hj, ind, if_neg hjC, zero_mul]


/-- Expansion of `F(G)` over the states on `S \ {x, a}`. -/
lemma stateSum_expand {M : Matrix V V (ZMod 2)} (hsymm : M.IsSymm) (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (hx : x ∈ S) (ha : a ∈ nbhd M S x) :
    stateSum M S = ∑ y ∈ vecs ((S.erase x).erase a), ∑ s : ZMod 2, ∑ t : ZMod 2,
      wt t ((M *ᵥ y) x + s) * (wt s ((M *ᵥ y) a + t)
        * rprod M a ((nbhd M S x).erase a) ((S.erase x).erase a) y s t) := by
  have hax : a ≠ x := ne_of_mem_nbhd hdiag ha
  have haS : a ∈ S := (mem_nbhd.mp ha).1
  have hxa : M x a = 1 := (mem_nbhd.mp ha).2
  have hax' : M a x = 1 := by rw [hsymm.apply x a]; exact hxa
  have haS' : a ∈ S.erase x := mem_erase.mpr ⟨hax, haS⟩
  unfold stateSum
  rw [sum_vecs_split S x hx, sum_vecs_split (S.erase x) a haS']
  refine sum_congr rfl fun y hy => sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  have hyv := mem_vecs.mp hy
  have hyx : y x = 0 := hyv x (by simp)
  have hya : y a = 0 := hyv a (by simp)
  have hmv : ∀ i, (M *ᵥ (y + Pi.single a s + Pi.single x t)) i
      = (M *ᵥ y) i + M i a * s + M i x * t := by
    intro i
    rw [mulVec_add_single, mulVec_add_single]
  rw [← mul_prod_erase S _ hx, ← mul_prod_erase (S.erase x) _ haS']
  congr 1
  · simp [hmv, hyx, hax.symm, hxa, hdiag]
  · congr 1
    · simp [hmv, hya, hax, hax', hdiag]
    · refine prod_congr rfl fun i hi => ?_
      have hi' := hi
      rw [mem_erase, mem_erase] at hi'
      rw [hmv, hsymm.apply x i, entry_x_eq_ind (M := M) hi, mul_comm (M i a)]
      simp [hi'.1, hi'.2.1]


/-- Expansion of `F(G_x)`. -/
lemma stateSum_erase_expand {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (ha : a ∈ nbhd M S x) :
    stateSum M (S.erase x) = ∑ y ∈ vecs ((S.erase x).erase a), ∑ s : ZMod 2,
      wt s ((M *ᵥ y) a) * rprod M a ((nbhd M S x).erase a) ((S.erase x).erase a) y s 0 := by
  have hax : a ≠ x := ne_of_mem_nbhd hdiag ha
  have haS' : a ∈ S.erase x := mem_erase.mpr ⟨hax, (mem_nbhd.mp ha).1⟩
  unfold stateSum
  rw [sum_vecs_split (S.erase x) a haS']
  refine sum_congr rfl fun y hy => sum_congr rfl fun s _ => ?_
  have hya : y a = 0 := mem_vecs.mp hy a (by simp)
  rw [← mul_prod_erase (S.erase x) _ haS']
  congr 1
  · simp [mulVec_add_single, hya, hdiag]
  · refine prod_congr rfl fun i hi => ?_
    have hi' := hi
    rw [mem_erase] at hi'
    rw [mulVec_add_single, mul_comm (M i a)]
    simp [hi'.1]

/-- Expansion of `F(Ḡ_x)`. -/
lemma stateSum_compl_expand {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (ha : a ∈ nbhd M S x) :
    stateSum (compl M (nbhd M S x)) (S.erase x) = ∑ y ∈ vecs ((S.erase x).erase a),
      ∑ s : ZMod 2, wt s ((M *ᵥ y) a + ∑ j ∈ (nbhd M S x).erase a, y j)
        * ((-1) ^ ((nbhd M S x).erase a).card * sgn (∑ j ∈ (nbhd M S x).erase a, y j)
          * rprod M a ((nbhd M S x).erase a) ((S.erase x).erase a) y s
              (∑ j ∈ (nbhd M S x).erase a, y j + s + 1)) := by
  set A := nbhd M S x with hA
  set C := A.erase a with hC
  have hax : a ≠ x := ne_of_mem_nbhd hdiag ha
  have haS' : a ∈ S.erase x := mem_erase.mpr ⟨hax, (mem_nbhd.mp ha).1⟩
  unfold stateSum
  rw [sum_vecs_split (S.erase x) a haS']
  refine sum_congr rfl fun y hy => sum_congr rfl fun s _ => ?_
  have hya : y a = 0 := mem_vecs.mp hy a (by simp)
  have hsumA : ∑ j ∈ A, (y + Pi.single a s : V → ZMod 2) j = ∑ j ∈ C, y j + s := by
    simp only [Pi.add_apply]
    rw [sum_add_distrib, Finset.sum_pi_single' a s A, if_pos ha, ← add_sum_erase A y ha, hya,
      zero_add]
  rw [← mul_prod_erase (S.erase x) _ haS']
  congr 1
  · rw [compl_mulVec, hsumA, mulVec_add_single, hdiag, ind, if_pos ha]
    simp only [Pi.add_apply, Pi.single_eq_same, hya, zero_add, zero_mul, add_zero, one_mul]
    rw [add_assoc (∑ j ∈ C, y j), zmod2_add_self, add_zero]
  · have hfl := prod_flip ((S.erase x).erase a) C (erase_nbhd_subset hdiag S x a) y
      (fun i => (M *ᵥ y) i + s * M i a) (∑ j ∈ C, y j + s)
    rw [rprod, ← hfl]
    refine prod_congr rfl fun i hi => ?_
    have hi' := hi
    rw [mem_erase] at hi'
    have hindA : ind A i = ind C i := by
      simp [hC, ind, hi'.1]
    rw [compl_mulVec, hsumA, mulVec_add_single, hindA, mul_comm (M i a)]
    simp [hi'.1]

/-- Expansion of `F(G_x^{a})`. -/
lemma stateSum_twoTs_expand {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} :
    stateSum (twoTs M a ((nbhd M S x).erase a)) ((S.erase x).erase a)
      = ∑ y ∈ vecs ((S.erase x).erase a), rprod M a ((nbhd M S x).erase a) ((S.erase x).erase a) y
          (∑ j ∈ (nbhd M S x).erase a, y j) ((M *ᵥ y) a) := by
  unfold stateSum rprod
  refine sum_congr rfl fun y _ => prod_congr rfl fun i _ => ?_
  rw [twoTs_mulVec, hdiag]
  congr 1
  ring

/-- Expansion of `F(Ḡ_x^{a})`. -/
lemma stateSum_twoTs_compl_expand {M : Matrix V V (ZMod 2)} (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (ha : a ∈ nbhd M S x) :
    stateSum (twoTs (compl M (nbhd M S x)) a ((nbhd M S x).erase a)) ((S.erase x).erase a)
      = ∑ y ∈ vecs ((S.erase x).erase a),
        (-1) ^ ((nbhd M S x).erase a).card * sgn (∑ j ∈ (nbhd M S x).erase a, y j)
          * rprod M a ((nbhd M S x).erase a) ((S.erase x).erase a) y
              (∑ j ∈ (nbhd M S x).erase a, y j)
              ((M *ᵥ y) a + ∑ j ∈ (nbhd M S x).erase a, y j + 1) := by
  set A := nbhd M S x with hA
  set C := A.erase a with hC
  unfold stateSum
  refine sum_congr rfl fun y hy => ?_
  have hya : y a = 0 := mem_vecs.mp hy a (by simp)
  have hsumA : ∑ j ∈ A, y j = ∑ j ∈ C, y j := by
    rw [← add_sum_erase A y ha, hya, zero_add]
  have hfl := prod_flip ((S.erase x).erase a) C (erase_nbhd_subset hdiag S x a) y
      (fun i => (M *ᵥ y) i + (∑ j ∈ C, y j) * M i a) ((M *ᵥ y) a + ∑ j ∈ C, y j)
  rw [rprod, ← hfl]
  refine prod_congr rfl fun i hi => ?_
  have hi' := hi
  rw [mem_erase] at hi'
  have hindA : ind A i = ind C i := by
    simp [hC, ind, hi'.1]
  have hcaa : compl M A a a = M a a := by simp [compl]
  have hcia : compl M A i a = M i a + ind C i := by
    by_cases hiC : i ∈ C
    · have hiA : i ∈ A := (mem_erase.mp hiC).2
      simp [compl, ind, hiC, hiA, ha, hi'.1]
    · have hiA : i ∉ A := fun h => hiC (mem_erase.mpr ⟨hi'.1, h⟩)
      simp [compl, ind, hiC, hiA]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hindAa : ind A a = 1 := if_pos ha
  rw [twoTs_mulVec, compl_mulVec, compl_mulVec, hcaa, hdiag, hcia, hindA, hsumA, hya, hindAa]
  congr 1
  linear_combination (ind C i * ∑ j ∈ C, y j) * h2


/-- Integer form of the conjecture:
`F(G) + 5 F(G_x) + 4 (-1)^k F(Ḡ_x) = 6 F(G_x^{a}) + 6 (-1)^k F(Ḡ_x^{a})`. -/
theorem stateSum_identity {M : Matrix V V (ZMod 2)} (hsymm : M.IsSymm) (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (hx : x ∈ S) (ha : a ∈ nbhd M S x) :
    stateSum M S + 5 * stateSum M (S.erase x)
        + 4 * (-1) ^ (nbhd M S x).card * stateSum (compl M (nbhd M S x)) (S.erase x)
      = 6 * stateSum (twoTs M a ((nbhd M S x).erase a)) ((S.erase x).erase a)
        + 6 * (-1) ^ (nbhd M S x).card
          * stateSum (twoTs (compl M (nbhd M S x)) a ((nbhd M S x).erase a))
              ((S.erase x).erase a) := by
  set C := (nbhd M S x).erase a with hC
  set e : ℤ := (-1) ^ C.card with he
  have hk : (-1 : ℤ) ^ (nbhd M S x).card = -e := by
    rw [← card_erase_add_one ha, pow_succ, he, mul_neg_one]
  rw [stateSum_expand hsymm hdiag hx ha, stateSum_erase_expand hdiag ha,
    stateSum_compl_expand hdiag ha, stateSum_twoTs_expand hdiag,
    stateSum_twoTs_compl_expand hdiag ha, hk, mul_sum, mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y hy => ?_
  rw [mulVec_x_eq_sum hdiag hy]
  exact pointwise _ _ _ e (neg_one_pow_eq_or ℤ _)


/-- Corank `η(G|_U) = |U| - rank_{𝔽₂}(M|_{U×U})` of the adjacency matrix of the induced subgraph
(`rank ≤ |U|`, so the natural subtraction is exact). -/
noncomputable def eta (M : Matrix V V (ZMod 2)) (U : Finset V) : ℕ :=
  U.card - (M.submatrix (fun i : U => (i : V)) (fun i : U => (i : V))).rank

/-- The paper's extension `φ(G) = 2^{-2|V|} ∑_{U ⊆ V} (-1/2)^{|V \ U|} 2^{η(G|_U)}` of the
`sl(2)` weight system at `c = 3/8`, for the graph `M|_S` (vertex set `S`). -/
noncomputable def phi (M : Matrix V V (ZMod 2)) (S : Finset V) : ℚ :=
  (1 / 4 : ℚ) ^ S.card * ∑ U ∈ S.powerset, (-1 / 2 : ℚ) ^ (S \ U).card * 2 ^ eta M U

/-- For `v` supported in `U`, `M *ᵥ v` only sees the columns in `U`. -/
lemma mulVec_eq_sum_coe (M : Matrix V V (ZMod 2)) {U : Finset V} {v : V → ZMod 2}
    (hv : v ∈ vecs U) (i : V) : (M *ᵥ v) i = ∑ j : U, M i j * v j := by
  rw [mem_vecs] at hv
  simp only [mulVec, dotProduct]
  rw [sum_coe_sort U (fun j => M i j * v j)]
  symm
  exact sum_subset (subset_univ _) fun j _ hj => by rw [hv j hj, mul_zero]

/-- The kernel of `M|_{U×U}` is in bijection with the vectors of `𝔽₂^U` killed by `M` on `U`. -/
lemma card_ker_eq (M : Matrix V V (ZMod 2)) (U : Finset V) :
    Nat.card (LinearMap.ker (M.submatrix (fun i : U => (i : V)) (fun i : U => (i : V))).mulVecLin)
      = ((vecs U).filter fun v => ∀ i ∈ U, (M *ᵥ v) i = 0).card := by
  classical
  set N := M.submatrix (fun i : U => (i : V)) (fun i : U => (i : V)) with hN
  have h1 : Nat.card (LinearMap.ker N.mulVecLin) = Nat.card {w : U → ZMod 2 // N *ᵥ w = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp [LinearMap.mem_ker])
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  let ext : (U → ZMod 2) → V → ZMod 2 := fun w j => if h : j ∈ U then w ⟨j, h⟩ else 0
  have hext : ∀ w, ext w ∈ vecs U := fun w => mem_vecs.mpr fun j hj => dif_neg hj
  have hNw : ∀ (w : U → ZMod 2) (i : U), (N *ᵥ w) i = (M *ᵥ ext w) i := by
    intro w i
    rw [mulVec_eq_sum_coe M (hext w)]
    simp only [mulVec, dotProduct, hN, Matrix.submatrix_apply, ext]
    exact sum_congr rfl fun j _ => by rw [dif_pos j.2]
  refine card_nbij' ext (fun v i => v i) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨hext w, fun i hi => ?_⟩
    rw [← hNw w ⟨i, hi⟩, hw, Pi.zero_apply]
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    funext i
    rw [Pi.zero_apply, ← hv.2 i i.2, mulVec_eq_sum_coe M hv.1]
    simp only [mulVec, dotProduct, hN, Matrix.submatrix_apply]
  · intro w _
    funext i
    simp [ext]
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv
    funext j
    by_cases hj : j ∈ U
    · simp [ext, hj]
    · simp [ext, hj, mem_vecs.mp hv.1 j hj]

/-- `2^{η(G|_U)}` counts the kernel vectors (rank–nullity). -/
lemma two_pow_eta (M : Matrix V V (ZMod 2)) (U : Finset V) :
    2 ^ eta M U = ((vecs U).filter fun v => ∀ i ∈ U, (M *ᵥ v) i = 0).card := by
  set N := M.submatrix (fun i : U => (i : V)) (fun i : U => (i : V)) with hN
  have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrk
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker N.mulVecLin)
  rw [card_ker_eq, Nat.card_zmod] at hcard
  rw [hcard, eta, ← hN, Matrix.rank]
  congr 1
  omega


/-- `[u = 0] - (1/2)[v = 0] = (1/2) wt v u`. -/
lemma wt_half (v u : ZMod 2) :
    ((if u = 0 then 1 else 0 : ℚ) + (-1 / 2) * (if v = 0 then 1 else 0))
      = (1 / 2) * (wt v u : ℚ) := by
  rcases zmod2_cases v with rfl | rfl <;> rcases zmod2_cases u with rfl | rfl <;> norm_num [wt]

/-- One summand of `φ` written as a sum over `𝔽₂^S`. -/
lemma term_eq_sum (M : Matrix V V (ZMod 2)) {S U : Finset V} (hU : U ⊆ S) :
    (-1 / 2 : ℚ) ^ (S \ U).card * 2 ^ eta M U
      = ∑ v ∈ vecs S, (∏ i ∈ U, (if (M *ᵥ v) i = 0 then (1 : ℚ) else 0))
          * ∏ i ∈ S \ U, ((-1 / 2) * (if v i = 0 then (1 : ℚ) else 0)) := by
  have hcast : (2 : ℚ) ^ eta M U = (((2 : ℕ) ^ eta M U : ℕ) : ℚ) := by push_cast; rfl
  have hfilt : ((vecs U).filter fun v => ∀ i ∈ U, (M *ᵥ v) i = 0)
      = (vecs S).filter fun v => (∀ i ∈ S \ U, v i = 0) ∧ ∀ i ∈ U, (M *ᵥ v) i = 0 := by
    ext v
    simp only [mem_filter, mem_vecs, mem_sdiff]
    constructor
    · rintro ⟨hv, hM⟩
      exact ⟨fun i hi => hv i (fun h => hi (hU h)), fun i hi => hv i hi.2, hM⟩
    · rintro ⟨hv, hS, hM⟩
      refine ⟨fun i hi => ?_, hM⟩
      by_cases hiS : i ∈ S
      · exact hS i ⟨hiS, hi⟩
      · exact hv i hiS
  rw [hcast, two_pow_eta, hfilt, card_filter, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_mul_distrib, prod_const, prod_boole, prod_boole]
  split_ifs <;> simp_all

/-- State-sum formula: `φ(G) = 8^{-|S|} ∑_{v} ∏_{i} wt(v_i, (Mv)_i)`, equivalently
`8^{-n} ∑_{v : v_i (Mv)_i = 0} 2^{|v|} (-1)^{|Mv|}`. -/
theorem phi_eq_stateSum (M : Matrix V V (ZMod 2)) (S : Finset V) :
    phi M S = (1 / 8 : ℚ) ^ S.card * stateSum M S := by
  rw [phi, sum_congr rfl fun U hU => term_eq_sum M (mem_powerset.mp hU), sum_comm]
  have hprod : ∀ v ∈ vecs S, ∑ U ∈ S.powerset, (∏ i ∈ U, (if (M *ᵥ v) i = 0 then (1 : ℚ) else 0))
      * ∏ i ∈ S \ U, ((-1 / 2) * (if v i = 0 then (1 : ℚ) else 0))
      = (1 / 2 : ℚ) ^ S.card * ∏ i ∈ S, (wt (v i) ((M *ᵥ v) i) : ℚ) := by
    intro v _
    rw [← prod_add, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => wt_half _ _
  rw [sum_congr rfl hprod, ← mul_sum, ← mul_assoc, ← mul_pow, stateSum]
  push_cast
  norm_num


/-- **Conjecture `conj:del-vert-2d` of arXiv:2607.24217 (Fomichev–Karev–Pavutnitskiy–Usanov),
proved for all `k ≥ 1`.**  Let `G = M|_S` be a simple graph (`M` symmetric over `𝔽₂` with zero
diagonal), `x ∈ S` a vertex with neighbourhood `A = nbhd M S x` of size `k`, and `a = a₁ ∈ A`.  Then
`φ(G) = (3/8 - 1) φ(G_x) + (-1)^{k+1}/2 φ(Ḡ_x) + (-1)^k/4 · 3/8 φ(Ḡ_x^{a₁})
  + 1/4 · 3/8 φ(G_x^{a₁})`,
where `G_x = M|_{S \ x}`, `Ḡ_x = (compl M A)|_{S \ x}`, and `G_x^{a₁}`, `Ḡ_x^{a₁}` are the 2T
transforms for all pairs `(a₁, aᵢ)` followed by deletion of `x` and `a₁`. -/
theorem conj_del_vert_2d {M : Matrix V V (ZMod 2)} (hsymm : M.IsSymm) (hdiag : ∀ i, M i i = 0)
    {S : Finset V} {x a : V} (hx : x ∈ S) (ha : a ∈ nbhd M S x) :
    phi M S = (3 / 8 - 1) * phi M (S.erase x)
      + (-1) ^ ((nbhd M S x).card + 1) / 2 * phi (compl M (nbhd M S x)) (S.erase x)
      + (-1) ^ (nbhd M S x).card / 4 * (3 / 8)
          * phi (twoTs (compl M (nbhd M S x)) a ((nbhd M S x).erase a)) ((S.erase x).erase a)
      + 1 / 4 * (3 / 8) * phi (twoTs M a ((nbhd M S x).erase a)) ((S.erase x).erase a) := by
  have hax : a ≠ x := ne_of_mem_nbhd hdiag ha
  have haS' : a ∈ S.erase x := mem_erase.mpr ⟨hax, (mem_nbhd.mp ha).1⟩
  have hc1 : (S.erase x).card = ((S.erase x).erase a).card + 1 := (card_erase_add_one haS').symm
  have hc0 : S.card = (S.erase x).card + 1 := (card_erase_add_one hx).symm
  have hI := congrArg (fun z : ℤ => (z : ℚ)) (stateSum_identity hsymm hdiag hx ha)
  push_cast at hI
  simp only [phi_eq_stateSum]
  rw [hc0, hc1]
  set q : ℚ := (1 / 8) ^ ((S.erase x).erase a).card
  rw [pow_succ, pow_succ]
  linear_combination (q / 64) * hI


/-- The paper's 2T transform for the pair `(a, b)`: add row `a` to row `b`, then column `a` to
column `b`. -/
def twoT (M : Matrix V V (ZMod 2)) (a b : V) : Matrix V V (ZMod 2) :=
  let R : Matrix V V (ZMod 2) := Matrix.of fun i j => if i = b then M i j + M a j else M i j
  Matrix.of fun i j => if j = b then R i j + R i a else R i j

omit [Fintype V] in
/-- No 2T transforms. -/
lemma twoTs_empty (M : Matrix V V (ZMod 2)) (a : V) : twoTs M a ∅ = M := by
  ext i j
  simp [twoTs]

omit [Fintype V] in
/-- `twoTs` is the iterate of single 2T transforms `(a, c)`, so it is the paper's
"apply the 2T transform to all pairs `(a₁, aᵢ)`". -/
lemma twoTs_insert (M : Matrix V V (ZMod 2)) {a b : V} {C : Finset V} (hb : b ∉ C)
    (ha : a ∉ C) : twoTs M a (insert b C) = twoT (twoTs M a C) a b := by
  ext i j
  simp only [twoT, twoTs, Matrix.of_apply, mem_insert]
  by_cases hi : i = b <;> by_cases hj : j = b
  · subst hi; subst hj
    simp only [hb, or_false, ↓reduceIte, and_self, add_zero, ha]
    ring
  · subst hi
    have hjb : j ≠ i := hj
    by_cases hjC : j ∈ C
    · simp only [hb, or_false, ↓reduceIte, hjb, hjC, or_true, and_self, add_zero, and_true, ha]
      ring
    · simp [hb, ha, hjb, hjC]
  · subst hj
    have hib : i ≠ j := hi
    by_cases hiC : i ∈ C
    · simp only [hib, hiC, or_true, ↓reduceIte, hb, or_false, and_self, add_zero, and_false, ha]
      ring
    · simp [hb, ha, hib, hiC]
  · by_cases hiC : i ∈ C <;> by_cases hjC : j ∈ C <;> simp [hi, hj, hiC, hjC]

/-! ## Examples -/

/-- The adjacency matrix of `K₂`. -/
def k2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

/-- The adjacency matrix of the path `0 - 1 - 2`. -/
def p3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- A single vertex has `φ = 3/8 = c`, the Casimir value. -/
example : phi k2 {0} = 3 / 8 := by
  rw [phi_eq_stateSum, show stateSum k2 {0} = 3 by decide]
  norm_num

/-- `φ(K₂) = c² - c/2` at `c = 3/8`, the `sl(2)` weight of one pair of crossing chords. -/
example : phi k2 univ = -3 / 64 := by
  rw [phi_eq_stateSum, show stateSum k2 univ = -3 by decide]
  norm_num

/-- The middle vertex of `P₃` has neighbourhood `{0, 2}`. -/
example : nbhd p3 univ 1 = {0, 2} := by decide

/-- `Ḡ_x` for the middle vertex of `P₃` adds the edge `0 - 2`. -/
example : compl p3 {0, 2} 0 2 = 1 ∧ compl p3 {0, 2} 0 0 = 0 := by decide

/-- The 2T transform `(0, 2)` on `P₃` removes the edge `2 - 1` (row `0` added to row `2`). -/
example : twoTs p3 0 {2} 2 1 = 0 ∧ twoT p3 0 2 = twoTs p3 0 {2} := by decide

/-- The hypotheses of `conj_del_vert_2d` hold jointly for `P₃`, `x = 1`, `a₁ = 0`. -/
example : p3.IsSymm ∧ (∀ i, p3 i i = 0) ∧ (1 : Fin 3) ∈ (univ : Finset (Fin 3)) ∧
    (0 : Fin 3) ∈ nbhd p3 univ 1 := by
  refine ⟨Matrix.IsSymm.ext fun i j => ?_, ?_, mem_univ _, by decide⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · decide

/-- Direct evaluation of the integer form of the recurrence on `P₃` at `x = 1`, `a₁ = 0`. -/
example : stateSum p3 univ + 5 * stateSum p3 (univ.erase 1)
      + 4 * (-1) ^ 2 * stateSum (compl p3 {0, 2}) (univ.erase 1)
    = 6 * stateSum (twoTs p3 0 {2}) ((univ.erase 1).erase 0)
      + 6 * (-1) ^ 2 * stateSum (twoTs (compl p3 {0, 2}) 0 {2}) ((univ.erase 1).erase 0) := by
  decide

end WeightSystemExtendGraph
