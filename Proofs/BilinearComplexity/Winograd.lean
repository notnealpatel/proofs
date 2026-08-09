/-
  BilinearComplexity/Winograd — the rank lower bound R⟨2,2,2⟩ ≥ 7
  (Hopcroft–Kerr 1971 / Winograd 1971), formalized over F₂ = ZMod 2 and
  transferred to ℤ. Card Pf11.

  Combined with `rank_matMulTensor_le_seven` (Strassen, `Strassen.lean`)
  this gives the exact value R⟨2,2,2⟩ = 7 over ℤ.

  ROUTE (following arXiv:2603-07280 App. D, worked over F₂ where every
  step is a finite check):

  1. Base change (`rank_matMulTensor_hom_le`, `KroneckerMatMul.lean`):
     it suffices to prove `7 ≤ rank (matMulTensor (ZMod 2) 2 2 2)`.
  2. Substitution / drop (`rankLE_contract₁_drop`): a rank-(r+1)
     decomposition one of whose A-vectors is killed by a contraction `M`
     yields a rank-r decomposition of `contract₁ M T`.
  3. Orbit 4 (`six_le_rank_T4`, the Hopcroft–Kerr forced product): the
     2×4×4 tensor `T4 = contract₁ P_base ⟨2,2,2⟩` has rank ≥ 6.
  4. Top level (`key_step`): for every nonzero A-vector `z`, there is a
     contraction `M` killing `z` with `contract₁ M ⟨2,2,2⟩` GL-equivalent
     to `T4`, hence of rank ≥ 6; picking a nonzero triad of an optimal
     decomposition and dropping it gives `7 ≤ r`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import BilinearComplexity.Basic
import BilinearComplexity.RankCalculus
import BilinearComplexity.Flattening
import BilinearComplexity.Strassen
import BilinearComplexity.KroneckerMatMul

namespace BilinearComplexity

/-! ## 1. The substitution (drop) lemma -/

/-- Substitution / drop lemma: given an `(r+1)`-triad decomposition whose
`s₀`-th A-vector is annihilated by the contraction `M` (`M · u_{s₀} = 0`),
the contracted tensor `contract₁ M T` has an `r`-triad decomposition —
drop the dead triad by reindexing `Fin (r+1)` along `s₀.succAbove`. -/
theorem rankLE_contract₁_drop {k : Type*} [CommSemiring k] {a a' b c r : ℕ}
    (M : Matrix (Fin a') (Fin a) k)
    (u : Fin (r + 1) → Fin a → k) (v : Fin (r + 1) → Fin b → k)
    (w : Fin (r + 1) → Fin c → k) (s₀ : Fin (r + 1))
    (hkill : ∀ i', ∑ i, M i' i * u s₀ i = 0) :
    RankLE (contract₁ M (fun i j l => ∑ s, u s i * v s j * w s l)) r := by
  refine ⟨fun s i' => ∑ i, M i' i * u (s₀.succAbove s) i,
          fun s j => v (s₀.succAbove s) j,
          fun s l => w (s₀.succAbove s) l, ?_⟩
  funext i' j l
  have step1 : contract₁ M (fun i j l => ∑ s, u s i * v s j * w s l) i' j l
      = ∑ s : Fin (r + 1), (∑ i, M i' i * u s i) * v s j * w s l := by
    simp only [contract₁, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  rw [step1, Fin.sum_univ_succAbove _ s₀, hkill i', zero_mul, zero_mul, zero_add]

/-! ## 2. The forced-product core: R(T4) ≥ 6 -/

/-- The base contraction `P_base : Fin 2 → Fin 4`, identifying the surviving
A-coordinates of orbit 4 (`a₀₀ = 0`, `a₀₁ = a₁₀`): row 0 collapses `a₀₁`
and `a₁₀`, row 1 keeps `a₁₁`. -/
def P_base : Matrix (Fin 2) (Fin 4) (ZMod 2) := !![0, 1, 1, 0; 0, 0, 0, 1]

/-- The orbit-4 tensor `T4 : Tensor F₂ 2 4 4`, the contraction of `⟨2,2,2⟩`
by `P_base`. Support `(i,j,l)`:
`(0,0,1),(0,1,3),(0,2,0),(0,3,2),(1,2,1),(1,3,3)`. -/
def T4 : Tensor (ZMod 2) 2 4 4 :=
  ![![![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 0, 1, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]]

/-- `T4` is literally the `P_base`-contraction of the matrix multiplication
tensor. -/
theorem T4_eq_contract : T4 = contract₁ P_base (matMulTensor (ZMod 2) 2 2 2) := by
  decide

/-- **Single forced-product swap (Hopcroft–Kerr exchange, one step).** In a
decomposition `∑ u_s ⊗ v_s ⊗ w_s` whose slice at a fixed C-coordinate `z₀`
is the single product `p ⊗ q`, any term `s₀` with `w_{s₀}(z₀) = 1` can be
exchanged so that term `s₀` becomes literally `p ⊗ q ⊗ w_{s₀}`, keeping the
same number of terms and leaving every other term's `A,B` parts unchanged. -/
theorem swap_forced {k : Type*} [CommRing k] {a b c r : ℕ}
    (u : Fin r → Fin a → k) (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (z₀ : Fin c) (p : Fin a → k) (q : Fin b → k)
    (hslice : ∀ i j, ∑ s, u s i * v s j * w s z₀ = p i * q j)
    (s₀ : Fin r) (hs₀ : w s₀ z₀ = 1) :
    ∃ (u' : Fin r → Fin a → k) (v' : Fin r → Fin b → k) (w' : Fin r → Fin c → k),
      (∀ i j l, ∑ s, u' s i * v' s j * w' s l = ∑ s, u s i * v s j * w s l) ∧
      u' s₀ = p ∧ v' s₀ = q ∧ (∀ s, s ≠ s₀ → u' s = u s ∧ v' s = v s) := by
  refine ⟨fun s => if s = s₀ then p else u s,
          fun s => if s = s₀ then q else v s,
          fun s => if s = s₀ then w s₀ else fun l => w s l - w s z₀ * w s₀ l,
          ?_, by simp, by simp, ?_⟩
  · intro i j l
    have key : ∀ s, (if s = s₀ then p else u s) i * (if s = s₀ then q else v s) j *
          (if s = s₀ then w s₀ else fun l => w s l - w s z₀ * w s₀ l) l
        = u s i * v s j * w s l +
          (if s = s₀ then p i * q j - u s₀ i * v s₀ j
            else -(u s i * v s j * w s z₀)) * w s₀ l := by
      intro s
      by_cases hs : s = s₀
      · subst hs; simp only [↓reduceIte]; ring
      · simp only [if_neg hs]; ring
    have hzero : (∑ s, if s = s₀ then p i * q j - u s₀ i * v s₀ j
        else -(u s i * v s j * w s z₀)) = 0 := by
      have h1 : (∑ s, ((if s = s₀ then p i * q j - u s₀ i * v s₀ j
            else -(u s i * v s j * w s z₀)) + u s i * v s j * w s z₀))
          = ∑ s, (if s = s₀ then p i * q j else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s = s₀
        · subst hs; simp only [↓reduceIte, hs₀, mul_one]; ring
        · simp only [if_neg hs]; ring
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ s₀ (fun _ => p i * q j)] at h1
      simp only [Finset.mem_univ, if_true] at h1
      rw [hslice i j] at h1
      exact add_right_cancel (h1.trans (zero_add _).symm)
    trans (∑ s, (u s i * v s j * w s l +
        (if s = s₀ then p i * q j - u s₀ i * v s₀ j
          else -(u s i * v s j * w s z₀)) * w s₀ l))
    · exact Finset.sum_congr rfl (fun s _ => key s)
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, hzero, zero_mul, add_zero]
  · intro s hs
    exact ⟨if_neg hs, if_neg hs⟩

/-- A-vector `a₀₁` (the surviving first A-coordinate of orbit 4). -/
def p0 : Fin 2 → ZMod 2 := ![1, 0]
/-- B-vector `b₁₀` — the B-part of the forced product at slice `c₀₀`. -/
def q0 : Fin 4 → ZMod 2 := ![0, 0, 1, 0]
/-- B-vector `b₁₁` — the B-part of the forced product at slice `c₁₀`. -/
def q1 : Fin 4 → ZMod 2 := ![0, 0, 0, 1]

/-- The forced-product residual: `T4` with the two forced products
`a₀₁⊗b₁₀⊗W0` (slice `c₀₀`) and `a₀₁⊗b₁₁⊗W1` (slice `c₁₀`) stripped, for
arbitrary C-completions `W0, W1`. -/
def Xres (W0 W1 : Fin 4 → ZMod 2) : Tensor (ZMod 2) 2 4 4 :=
  fun i j l => T4 i j l - p0 i * q0 j * W0 l - p0 i * q1 j * W1 l

/-- Column selection `(l,i)` picking the four B-flattening columns
`{(c₀₁,a₀₁),(c₁₁,a₀₁),(c₀₁,a₁₁),(c₁₁,a₁₁)}` (the odd-C columns) that carry an
invertible submatrix of the residual, uniformly in `W0,W1`. -/
def colsel : Fin 4 → Fin 4 × Fin 2 := ![(1, 0), (3, 0), (1, 1), (3, 1)]

/-- The invertible witness: the residual's B-flattening restricted to
`colsel` is block-unitriangular (`W`-dependent lower-left block, identity
blocks on the diagonal), hence an involution over `F₂`. -/
def Msub (W0 W1 : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; W0 1, W0 3, 1, 0; W1 1, W1 3, 0, 1]

/-- **Residual flattening bound.** For every completion `W0, W1`, the
B-flattening `flattening (cyc (Xres W0 W1))` has rank ≥ 4: its `colsel`
submatrix is `Msub W0 W1`, an involution (`Msub² = 1` over `F₂`), hence a
unit of full rank 4, and `rank_submatrix_le` transfers the bound. -/
theorem resid_flat_rank (W0 W1 : Fin 4 → ZMod 2) :
    4 ≤ (flattening (cyc (Xres W0 W1))).rank := by
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  have hadd : ∀ x : ZMod 2, x + x = 0 := by decide
  have hsub : (flattening (cyc (Xres W0 W1))).submatrix id colsel = Msub W0 W1 := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [flattening, cyc, Xres, Msub, colsel, T4, p0, q0, q1, hneg]
  have hinv : Msub W0 W1 * Msub W0 W1 = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Msub, hadd]
  have hU : IsUnit (Msub W0 W1) := IsUnit.of_mul_eq_one _ hinv
  calc (4 : ℕ) = Fintype.card (Fin 4) := (Fintype.card_fin 4).symm
    _ = (Msub W0 W1).rank := (Matrix.rank_of_isUnit _ hU).symm
    _ = ((flattening (cyc (Xres W0 W1))).submatrix id colsel).rank := by rw [hsub]
    _ ≤ (flattening (cyc (Xres W0 W1))).rank := Matrix.rank_submatrix_le _ _ _

/-- A tensor written as a triad sum over a `Finset` `S` of term indices has
`RankLE` at most `S.card` — reindex `S` by `S.equivFin`. -/
theorem rankLE_of_finset_sum {k : Type*} [CommSemiring k] {a b c r : ℕ}
    (S : Finset (Fin r)) (u : Fin r → Fin a → k) (v : Fin r → Fin b → k)
    (w : Fin r → Fin c → k) :
    RankLE (fun i j l => ∑ s ∈ S, u s i * v s j * w s l) S.card := by
  refine ⟨fun t i => u (S.equivFin.symm t) i, fun t j => v (S.equivFin.symm t) j,
          fun t l => w (S.equivFin.symm t) l, ?_⟩
  funext i j l
  rw [← Finset.sum_coe_sort S (fun s => u s i * v s j * w s l)]
  exact (Equiv.sum_comp S.equivFin.symm (fun s => u s i * v s j * w s l)).symm

/-- **Hopcroft–Kerr forced product (orbit 4).** The 2×4×4 tensor `T4` has
rank at least 6. This is the hard core: the two rank-1 C-slices at `c₀₀`
and `c₁₀` are single products that any decomposition may be assumed to
compute literally, using up two terms; the residual flattens to rank ≥ 4
for every completion. -/
theorem six_le_rank_T4 : 6 ≤ rank T4 := by
  suffices h : ∀ (r : ℕ) (u : Fin r → Fin 2 → ZMod 2) (v : Fin r → Fin 4 → ZMod 2)
      (w : Fin r → Fin 4 → ZMod 2),
      (T4 = fun i j l => ∑ s, u s i * v s j * w s l) → 6 ≤ r by
    obtain ⟨u, v, w, hT⟩ := rankLE_rank T4
    exact h _ u v w hT
  intro r u v w hT
  have zne1 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
  -- The C-slice at c₀₀ is the single product a₀₁ ⊗ b₁₀ = p0 ⊗ q0.
  have h0 : ∀ (i : Fin 2) (j : Fin 4), T4 i j 0 = p0 i * q0 j := by decide
  have hslice0 : ∀ (i : Fin 2) (j : Fin 4), ∑ s, u s i * v s j * w s 0 = p0 i * q0 j := by
    intro i j
    have e : T4 i j 0 = ∑ s, u s i * v s j * w s 0 := by rw [hT]
    rw [← e]; exact h0 i j
  -- Some term carries the c₀₀ slice, else the slice would vanish.
  obtain ⟨s0, hs0⟩ : ∃ s0, w s0 0 = 1 := by
    by_contra hcon
    simp only [not_exists] at hcon
    have hz : ∀ s, w s 0 = 0 := fun s => zne1 _ (hcon s)
    have hbad : (p0 0 : ZMod 2) * q0 2 = 0 := by
      rw [← hslice0 0 2]
      exact Finset.sum_eq_zero fun s _ => by rw [hz s]; ring
    revert hbad; decide
  -- Swap 1: force term s0 to be a₀₁ ⊗ b₁₀ ⊗ w_{s0}.
  obtain ⟨u1, v1, w1, hsum1, hu1, hv1, hunch1⟩ := swap_forced u v w 0 p0 q0 hslice0 s0 hs0
  have hT1 : T4 = fun i j l => ∑ s, u1 s i * v1 s j * w1 s l := by
    funext i j l; rw [hT]; exact (hsum1 i j l).symm
  -- The C-slice at c₁₀ is the single product a₀₁ ⊗ b₁₁ = p0 ⊗ q1.
  have h2 : ∀ (i : Fin 2) (j : Fin 4), T4 i j 2 = p0 i * q1 j := by decide
  have hslice1 : ∀ (i : Fin 2) (j : Fin 4), ∑ s, u1 s i * v1 s j * w1 s 2 = p0 i * q1 j := by
    intro i j
    have e : T4 i j 2 = ∑ s, u1 s i * v1 s j * w1 s 2 := by rw [hT1]
    rw [← e]; exact h2 i j
  -- A different term carries the c₁₀ slice: else it would be a multiple of
  -- the c₀₀ product a₀₁⊗b₁₀, impossible since a₀₁⊗b₁₁ is independent of it.
  obtain ⟨s1, hs1ne, hs1⟩ : ∃ s1, s1 ≠ s0 ∧ w1 s1 2 = 1 := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hz : ∀ s, s ≠ s0 → w1 s 2 = 0 := fun s h => zne1 _ (hcon s h)
    have key : ∑ s, u1 s 0 * v1 s 3 * w1 s 2 = p0 0 * q0 3 * w1 s0 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s0),
        Finset.sum_eq_zero fun s hs => by rw [hz s (Finset.ne_of_mem_erase hs)]; ring,
        hu1, hv1]
      ring
    rw [hslice1 0 3] at key
    simp only [p0, q0, q1, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three, mul_zero, zero_mul, mul_one] at key
    exact one_ne_zero key
  -- Swap 2: force term s1 to be a₀₁ ⊗ b₁₁ ⊗ w1_{s1}; term s0 keeps its A,B parts.
  obtain ⟨u2, v2, w2, hsum2, hu2s1, hv2s1, hunch2⟩ := swap_forced u1 v1 w1 2 p0 q1 hslice1 s1 hs1
  have hT2 : T4 = fun i j l => ∑ s, u2 s i * v2 s j * w2 s l := by
    funext i j l; rw [hT1]; exact (hsum2 i j l).symm
  have hu2s0 : u2 s0 = p0 := (hunch2 s0 (Ne.symm hs1ne)).1.trans hu1
  have hv2s0 : v2 s0 = q0 := (hunch2 s0 (Ne.symm hs1ne)).2.trans hv1
  -- Strip the two forced terms: the residual is `Xres (w2 s0) (w2 s1)`.
  set S := (Finset.univ.erase s0).erase s1 with hS
  have hXeq : Xres (w2 s0) (w2 s1) = fun i j l => ∑ s ∈ S, u2 s i * v2 s j * w2 s l := by
    funext i j l
    have strip : (∑ s ∈ S, u2 s i * v2 s j * w2 s l)
        = (∑ s, u2 s i * v2 s j * w2 s l) - u2 s0 i * v2 s0 j * w2 s0 l
          - u2 s1 i * v2 s1 j * w2 s1 l := by
      have e1 : (∑ s, u2 s i * v2 s j * w2 s l)
          = u2 s0 i * v2 s0 j * w2 s0 l
            + ∑ s ∈ Finset.univ.erase s0, u2 s i * v2 s j * w2 s l :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ s0)).symm
      have e2 : (∑ s ∈ Finset.univ.erase s0, u2 s i * v2 s j * w2 s l)
          = u2 s1 i * v2 s1 j * w2 s1 l + ∑ s ∈ S, u2 s i * v2 s j * w2 s l :=
        (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hs1ne, Finset.mem_univ s1⟩)).symm
      rw [e1, e2]; ring
    have hT2v : (∑ s, u2 s i * v2 s j * w2 s l) = T4 i j l := by rw [hT2]
    rw [strip, hT2v, hu2s0, hv2s0, hu2s1, hv2s1]
    simp only [Xres]
  have hRank : RankLE (Xres (w2 s0) (w2 s1)) S.card := by
    rw [hXeq]; exact rankLE_of_finset_sum S u2 v2 w2
  have hScard : S.card = r - 2 := by
    have h1 : s1 ∈ Finset.univ.erase s0 := Finset.mem_erase.mpr ⟨hs1ne, Finset.mem_univ s1⟩
    have e := Finset.card_erase_of_mem h1
    rw [Finset.card_erase_of_mem (Finset.mem_univ s0), Finset.card_univ, Fintype.card_fin] at e
    omega
  have hflat : (flattening (cyc (Xres (w2 s0) (w2 s1)))).rank ≤ S.card :=
    hRank.cyc.rank_flattening_le
  have hge := resid_flat_rank (w2 s0) (w2 s1)
  omega

/-! ## 3. Top-level per-orbit key step

For every nonzero A-vector `z`, a rank-3 contraction moves the hyperplane
`{z = 0}` onto orbit 4. We tabulate, indexed by `zidx z ∈ {1,…,15}`, the
2×4 contraction `Pz z` (`P_base` composed with the matmul symmetry), and the
invertible 4×4 witnesses `gBz z`, `gCz z` (with inverses `gBinvz`, `gCinvz`)
certifying `contract₁ (Pz z) ⟨2,2,2⟩` is GL-equivalent to `T4`. All the data
was generated by an exhaustive search over the symmetry group
`GL₂(F₂)³` (see `References/arXiv-2603-07280`); the three defining
properties are then finite `decide` checks. -/

/-- Index of an A-vector `z : Fin 4 → F₂` as a bit pattern in `{0,…,15}`. -/
def zidx (z : Fin 4 → ZMod 2) : ℕ :=
  (z 0).val + 2 * (z 1).val + 4 * (z 2).val + 8 * (z 3).val

/-- The 2×4 contraction moving `{z = 0}` onto orbit 4, keyed by `zidx`. -/
def PzT : ℕ → Matrix (Fin 2) (Fin 4) (ZMod 2)
  | 1 => !![0, 1, 1, 0; 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 1; 0, 0, 1, 0]
  | 3 => !![1, 1, 1, 0; 0, 0, 1, 1]
  | 4 => !![1, 0, 0, 1; 0, 1, 0, 0]
  | 5 => !![1, 0, 1, 1; 0, 1, 0, 1]
  | 6 => !![0, 1, 1, 0; 1, 0, 0, 0]
  | 7 => !![1, 0, 1, 1; 1, 1, 0, 0]
  | 8 => !![0, 1, 1, 0; 1, 0, 0, 0]
  | 9 => !![1, 0, 0, 1; 0, 1, 0, 0]
  | 10 => !![0, 1, 1, 1; 1, 0, 1, 0]
  | 11 => !![1, 0, 1, 1; 1, 1, 0, 0]
  | 12 => !![1, 0, 1, 1; 1, 1, 0, 0]
  | 13 => !![1, 0, 0, 1; 0, 1, 0, 0]
  | 14 => !![0, 1, 1, 0; 1, 0, 0, 0]
  | 15 => !![1, 0, 0, 1; 1, 1, 1, 1]
  | _ => 0

/-- Invertible B-mode witness of the GL-equivalence `contract₁ (Pz z) ⟨2,2,2⟩ ≅ T4`. -/
def gBT : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 1 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 2 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 3 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 4 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 5 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 6 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 7 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 8 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 9 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 10 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 11 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 12 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 13 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 14 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 15 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | _ => 1

/-- Invertible C-mode witness of the GL-equivalence. -/
def gCT : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 1 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 2 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 3 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 4 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 5 => !![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0]
  | 6 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 7 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 8 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 9 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 10 => !![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0]
  | 11 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 12 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 13 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 14 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 15 => !![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0]
  | _ => 1

/-- Inverse of `gBT`. -/
def gBinvT : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 1 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 2 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 3 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 4 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 5 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 6 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 7 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 8 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 9 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 10 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 11 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 12 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 13 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 14 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 15 => !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | _ => 1

/-- Inverse of `gCT`. -/
def gCinvT : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 1 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 2 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 3 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 4 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 5 => !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0]
  | 6 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 7 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 8 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 9 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 10 => !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0]
  | 11 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 12 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 13 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 14 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  | 15 => !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0]
  | _ => 1

/-- The per-`z` data as functions of the vector `z`, via `zidx`. -/
def Pz (z : Fin 4 → ZMod 2) : Matrix (Fin 2) (Fin 4) (ZMod 2) := PzT (zidx z)
def gBz (z : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) := gBT (zidx z)
def gCz (z : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) := gCT (zidx z)
def gBinvz (z : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) := gBinvT (zidx z)
def gCinvz (z : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) := gCinvT (zidx z)

/-- `Pz z` annihilates `z` (finite check over all 16 vectors). -/
theorem Pz_kill : ∀ z : Fin 4 → ZMod 2, ∀ α, ∑ i, (Pz z) α i * z i = 0 := by decide

/-- The GL-equivalence identity: for every nonzero `z`, applying the
invertible B/C witnesses to `contract₁ (Pz z) ⟨2,2,2⟩` recovers `T4`. -/
theorem key_id : ∀ z : Fin 4 → ZMod 2, z ≠ 0 →
    contract₂ (gBz z) (contract₃ (gCz z)
        (contract₁ (Pz z) (matMulTensor (ZMod 2) 2 2 2))) = T4 := by
  decide

/-- `gBinvz z` is a two-sided inverse of `gBz z` (nonzero `z`). -/
theorem gBz_inv : ∀ z : Fin 4 → ZMod 2, z ≠ 0 →
    gBz z * gBinvz z = 1 ∧ gBinvz z * gBz z = 1 := by decide

/-- `gCinvz z` is a two-sided inverse of `gCz z` (nonzero `z`). -/
theorem gCz_inv : ∀ z : Fin 4 → ZMod 2, z ≠ 0 →
    gCz z * gCinvz z = 1 ∧ gCinvz z * gCz z = 1 := by decide

/-- **Key step.** For every nonzero A-vector `z`, the tabulated contraction
`Pz z` annihilates `z` and its contracted tensor `contract₁ (Pz z) ⟨2,2,2⟩`
is GL-equivalent to `T4`, hence has rank ≥ 6. -/
theorem key_step (z : Fin 4 → ZMod 2) (hz : z ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 4) (ZMod 2),
      (∀ α, ∑ i, M α i * z i = 0) ∧
      6 ≤ rank (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) := by
  refine ⟨Pz z, Pz_kill z, ?_⟩
  obtain ⟨hB1, hB2⟩ := gBz_inv z hz
  obtain ⟨hC1, hC2⟩ := gCz_inv z hz
  letI : Invertible (gBz z) := ⟨gBinvz z, hB2, hB1⟩
  letI : Invertible (gCz z) := ⟨gCinvz z, hC2, hC1⟩
  calc 6 ≤ rank T4 := six_le_rank_T4
    _ = rank (contract₂ (gBz z) (contract₃ (gCz z)
          (contract₁ (Pz z) (matMulTensor (ZMod 2) 2 2 2)))) := by rw [key_id z hz]
    _ = rank (contract₃ (gCz z) (contract₁ (Pz z) (matMulTensor (ZMod 2) 2 2 2))) :=
        rank_contract₂_of_invertible _ _
    _ = rank (contract₁ (Pz z) (matMulTensor (ZMod 2) 2 2 2)) :=
        rank_contract₃_of_invertible _ _

/-! ## 4. Assembly -/

/-- `⟨2,2,2⟩` over `F₂` has rank ≥ 7: from an optimal decomposition pick a
nonzero A-triad, drop it via `key_step`'s contraction, and land on a
rank-≥6 tensor — impossible if the rank were ≤ 6. -/
theorem seven_le_rank_matMulTensor_zmod :
    7 ≤ rank (matMulTensor (ZMod 2) 2 2 2) := by
  by_contra hlt
  rw [not_le] at hlt
  have hle : rank (matMulTensor (ZMod 2) 2 2 2) ≤ 6 := by omega
  obtain ⟨u, v, w, hT⟩ := rankLE_of_rank_le hle
  -- some A-vector is nonzero, else the tensor is 0
  have hex : ∃ s₀ : Fin 6, u s₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hzero : matMulTensor (ZMod 2) 2 2 2 = 0 := by
      rw [hT]; funext i j l; simp [h]
    exact (by decide : matMulTensor (ZMod 2) 2 2 2 ≠ 0) hzero
  obtain ⟨s₀, hs₀⟩ := hex
  obtain ⟨M, hkill, hrank⟩ := key_step (u s₀) (by simpa using hs₀)
  have hdrop : RankLE (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) 5 := by
    rw [hT]
    exact rankLE_contract₁_drop M u v w s₀ hkill
  have : rank (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) ≤ 5 :=
    rank_le_of_rankLE hdrop
  omega

/-- **Winograd / Hopcroft–Kerr (1971).** The 2×2 matrix multiplication
tensor over ℤ has rank at least 7. Transferred from `F₂` along
`Int.castRingHom (ZMod 2)`: rank cannot increase under a ring hom, so the
F₂ lower bound lifts to ℤ. Together with Strassen's `≤ 7` this pins the
rank at exactly 7. -/
theorem seven_le_rank_matMulTensor : 7 ≤ rank (matMulTensor ℤ 2 2 2) :=
  le_trans seven_le_rank_matMulTensor_zmod
    (rank_matMulTensor_hom_le ℤ (ZMod 2) (Int.castRingHom (ZMod 2)) 2 2 2)

/-- **The rank of `2×2` matrix multiplication is exactly 7** (Strassen 1969
upper bound, `rank_matMulTensor_le_seven`; Hopcroft–Kerr / Winograd 1971
lower bound, `seven_le_rank_matMulTensor`). -/
theorem rank_matMulTensor_eq_seven : rank (matMulTensor ℤ 2 2 2) = 7 :=
  le_antisymm rank_matMulTensor_le_seven seven_le_rank_matMulTensor

end BilinearComplexity
