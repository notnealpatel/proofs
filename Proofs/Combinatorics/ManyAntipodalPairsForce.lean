/-
# Many antipodal pairs force many neighbouring pairs: the spectral core

## Source

arXiv 2608.02605v1, Gábor Damásdi, Laurențiu Ploscaru et al.,
"Many Antipodal Pairs Force Many Neighboring Pairs".
Section 2, Prop. 2.1 (`vector-test-criterion`, Collatz-Wielandt bound);
Section 4, Lemma 4.3 (`lem:tails`) and Prop. 4.4 (`prop:sqrt-control`).
Recorded 2026-10-21.

## Informal claim (combinatorial engine of Prop. 4.4)

Lemma 4.3 supplies, for the box graph, the tail estimate
"for every vertex `k` and integer `t ≥ 1`,
`|{j ∼ k : d_j ≥ t}| ≤ c₀ (N/t) (ε₂/ε₁)²`", and Prop. 4.4 deduces
`λ₁(G) ≤ 6 ε₂ ε₁⁻¹ √(c₀ N)` via the test vector `(√d_i)` and a dyadic
decomposition. Abstracted: for a finite simple graph `G` and real `M` with
`t · #{j ∈ N(k) : t ≤ deg j} ≤ M` for all `k` and all naturals `t ≥ 1`,
`λ₁(G) ≤ C √M`. The paper proves `C = 6`.

## Status

Proved in the paper with constant `6`. This file proves the sharper
constant `2`, stated as the quadratic-form bound
`v ⬝ (A_G v) ≤ 2 √M (v ⬝ v)` for all real `v` (equivalent to
`λ₁(A_G) ≤ 2√M`). The sharpening replaces the dyadic decomposition by
a sorting argument: removing the neighbour of least degree `d₀` from
a neighbourhood of size `n` gives `d₀ n ≤ M`, and
`√(M/n) + 2√(M(n-1)) ≤ 2√(Mn)`.
-/
import Mathlib

set_option autoImplicit false

open Matrix

namespace ManyAntipodalPairsForce


/-- Weighted AM-GM: for positive weights `x, y`,
`2ab ≤ a² y / x + b² x / y`. -/
theorem amgm_ratio (a b x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 * (a * b) ≤ a ^ 2 * y / x + b ^ 2 * x / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', le_div_iff₀ (mul_pos hx hy)]
  nlinarith [sq_nonneg (a * y - b * x)]

/-- **Schur test / Collatz-Wielandt bound** (cf. arXiv 2608.02605, Prop. 2.1).
If `A` is a real symmetric matrix with nonnegative entries and `x` is a
strictly positive vector with `(A x)_i ≤ λ x_i` for every `i`, then the
quadratic form of `A` satisfies `v ⬝ (A v) ≤ λ (v ⬝ v)` for every `v`;
equivalently `λ₁(A) ≤ λ`. Proved directly, without Perron-Frobenius. -/
theorem dotProduct_mulVec_le_of_pos_supersolution {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (x : n → ℝ) (hx : ∀ i, 0 < x i) (lam : ℝ)
    (h : ∀ i, (A *ᵥ x) i ≤ lam * x i) (v : n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ lam * (v ⬝ᵥ v) := by
  set T : n → n → ℝ := fun i j => A i j * v i ^ 2 * x j / x i with hT
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    simpa using congrFun (congrFun hA i) j
  have hpt : ∀ i j, v i * (A i j * v j) ≤ (T i j + T j i) / 2 := by
    intro i j
    have h2 := amgm_ratio (v i) (v j) (x i) (x j) (hx i) (hx j)
    have hT1 : T i j + T j i = A i j * (v i ^ 2 * x j / x i + v j ^ 2 * x i / x j) := by
      simp only [hT, hsymm]; ring
    rw [hT1]
    nlinarith [hnn i j]
  have hrow : ∀ i, ∑ j, T i j ≤ lam * v i ^ 2 := by
    intro i
    have hsum : ∑ j, T i j = v i ^ 2 / x i * (A *ᵥ x) i := by
      simp only [hT, mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    calc v i ^ 2 / x i * (A *ᵥ x) i ≤ v i ^ 2 / x i * (lam * x i) :=
          mul_le_mul_of_nonneg_left (h i) (div_nonneg (sq_nonneg _) (hx i).le)
      _ = lam * v i ^ 2 := by field_simp [(hx i).ne']
  calc v ⬝ᵥ (A *ᵥ v) = ∑ i, ∑ j, v i * (A i j * v j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, (T i j + T j i) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = ∑ i, ∑ j, T i j := by
        have hswap : ∑ i, ∑ j, T j i = ∑ i, ∑ j, T i j := Finset.sum_comm
        simp only [← Finset.sum_div, Finset.sum_add_distrib, hswap]
        ring
    _ ≤ ∑ i, lam * v i ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = lam * (v ⬝ᵥ v) := by
        simp only [dotProduct, Finset.mul_sum, sq]

/-- The induction step of the local sum bound: if `d₀ n ≤ M` with `n ≥ 1`,
then `√d₀ + 2√(M(n-1)) ≤ 2√(Mn)`. -/
theorem step_ineq (d0 n M : ℝ) (hd0 : 0 ≤ d0) (hn : 1 ≤ n) (h : d0 * n ≤ M) :
    √d0 + 2 * √(M * (n - 1)) ≤ 2 * √(M * n) := by
  have hM : 0 ≤ M := le_trans (mul_nonneg hd0 (by linarith)) h
  set a := √d0 with ha
  set s := √n with hs
  set r := √(n - 1) with hr
  set m := √M with hm
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hn
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hrr : r ^ 2 = n - 1 := Real.sq_sqrt (by linarith)
  have hmm : m ^ 2 = M := Real.sq_sqrt hM
  have haa : a ^ 2 = d0 := Real.sq_sqrt hd0
  have has : a * s ≤ m := by
    have h2 : (a * s) ^ 2 ≤ m ^ 2 := by rw [mul_pow, haa, hss, hmm]; exact h
    exact (pow_le_pow_iff_left₀ (mul_nonneg ha0 (by linarith)) hm0 two_ne_zero).mp h2
  have hrs : 2 * (r * s) ≤ 2 * s ^ 2 - 1 := by nlinarith [sq_nonneg (s - r)]
  rw [Real.sqrt_mul hM, Real.sqrt_mul hM, ← hm, ← hs, ← hr]
  have key : (a + 2 * (m * r)) * s ≤ 2 * (m * s) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hrs hm0]
  exact le_of_mul_le_mul_right key (by linarith)

/-- **Local square-root sum.** If a finite family of positive naturals `d`
indexed by `s` satisfies the tail bound `t · #{j ∈ s : t ≤ d j} ≤ M` for
every integer `t ≥ 1`, then `∑_{j ∈ s} √(d j) ≤ 2 √(M · #s)`. -/
theorem sum_sqrt_le_of_tail {ι : Type*} (d : ι → ℕ) (M : ℝ) (s : Finset ι)
    (hpos : ∀ j ∈ s, 1 ≤ d j)
    (h : ∀ t : ℕ, 1 ≤ t → (t : ℝ) * ((s.filter (fun j => t ≤ d j)).card : ℝ) ≤ M) :
    ∑ j ∈ s, √(d j : ℝ) ≤ 2 * √(M * s.card) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp
    obtain ⟨j0, hj0, hmin⟩ := s.exists_min_image d hs
    have hsub : s.erase j0 ⊂ s := Finset.erase_ssubset hj0
    have h' : ∀ t : ℕ, 1 ≤ t →
        (t : ℝ) * (((s.erase j0).filter (fun j => t ≤ d j)).card : ℝ) ≤ M := by
      intro t ht
      have hle : (((s.erase j0).filter (fun j => t ≤ d j)).card : ℝ) ≤
          ((s.filter (fun j => t ≤ d j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.erase_subset j0 s))
      exact le_trans (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg t)) (h t ht)
    have ih' := ih (s.erase j0) hsub (fun j hj => hpos j (Finset.mem_of_mem_erase hj)) h'
    have hfilt : s.filter (fun j => d j0 ≤ d j) = s :=
      Finset.filter_true_of_mem fun j hj => hmin j hj
    have htail : (d j0 : ℝ) * (s.card : ℝ) ≤ M := by
      have := h (d j0) (hpos j0 hj0)
      rwa [hfilt] at this
    have hcard : ((s.erase j0).card : ℝ) = (s.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hj0, Nat.cast_sub (Finset.card_pos.mpr hs), Nat.cast_one]
    have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr hs
    rw [← Finset.add_sum_erase s _ hj0]
    calc √(d j0 : ℝ) + ∑ j ∈ s.erase j0, √(d j : ℝ)
        ≤ √(d j0 : ℝ) + 2 * √(M * ((s.card : ℝ) - 1)) := by
          rw [← hcard]; exact add_le_add_right ih' _
      _ ≤ 2 * √(M * s.card) := step_ineq _ _ _ (Nat.cast_nonneg _) hn htail

/-- The degree tail of `k`: `#{j ∼ k : t ≤ deg j}`, the quantity
`|{j ∼ k : d_j ≥ t}|` bounded in Lemma 4.3 of arXiv 2608.02605. -/
def tailCount {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : V) (t : ℕ) : ℕ :=
  ((G.neighborFinset k).filter (fun j => t ≤ G.degree j)).card

/-- Ground truth: in the triangle `K₃` every vertex has two neighbours of
degree `2`, so the tail at `t = 2` is `2` and at `t = 3` is `0`. -/
example : tailCount (⊤ : SimpleGraph (Fin 3)) 0 2 = 2 := by decide

example : tailCount (⊤ : SimpleGraph (Fin 3)) 0 3 = 0 := by decide

/-- Ground truth on the path `0 - 1 - 2`: the leaf `0` has the single
neighbour `1` of degree `2`; the centre `1` has two neighbours of
degree `1`. -/
example : tailCount (SimpleGraph.fromRel (fun a b : Fin 3 => b.val = a.val + 1)) 0 2 = 1 := by
  decide

example : tailCount (SimpleGraph.fromRel (fun a b : Fin 3 => b.val = a.val + 1)) 1 2 = 0 := by
  decide

/-- Non-vacuity of the degree-tail hypothesis: every finite simple graph
satisfies it with `M = |V|²`. -/
theorem tail_le_card_sq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : V) (t : ℕ) :
    (t : ℝ) * (tailCount G k t : ℝ) ≤ ((Fintype.card V : ℝ)) ^ 2 := by
  have hcard : tailCount G k t ≤ Fintype.card V := by
    unfold tailCount
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_univ _)
  rcases Nat.eq_zero_or_pos (tailCount G k t) with h0 | hpos
  · rw [h0]; simp
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have htj : t ≤ Fintype.card V :=
    ((Finset.mem_filter.mp hj).2).trans (G.degree_lt_card_verts j).le
  rw [sq]
  exact_mod_cast Nat.mul_le_mul htj hcard

/-- **Spectral core of arXiv 2608.02605 (Prop. 4.4 with Lemma 4.3), with
constant `2`.** Let `G` be a finite simple graph and `M` a real number such
that for every vertex `k` and every natural `t ≥ 1`,
`t · #{j ∼ k : t ≤ deg j} ≤ M`. Then for every real vector `v`,
`v ⬝ (A_G v) ≤ 2 √M (v ⬝ v)`, i.e. `λ₁(G) ≤ 2 √M`. The paper proves the
same with constant `6`. -/
theorem dotProduct_adjMatrix_le_of_degree_tail {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℝ)
    (hM : ∀ k : V, ∀ t : ℕ, 1 ≤ t → (t : ℝ) * (tailCount G k t : ℝ) ≤ M)
    (v : V → ℝ) :
    v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) ≤ 2 * √M * (v ⬝ᵥ v) := by
  set x : V → ℝ := fun i => √((max (G.degree i) 1 : ℕ) : ℝ) with hx
  have hxpos : ∀ i, 0 < x i := fun i => Real.sqrt_pos.mpr (by
    have : 1 ≤ max (G.degree i) 1 := le_max_right _ _
    exact_mod_cast this)
  refine dotProduct_mulVec_le_of_pos_supersolution _ (G.isSymm_adjMatrix)
    (fun i j => by rw [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num)
    x hxpos _ (fun i => ?_) v
  have hnb : ∀ j ∈ G.neighborFinset i, x j = √(G.degree j : ℝ) := by
    intro j hj
    have hdeg : 1 ≤ G.degree j := G.degree_pos_iff_exists_adj j |>.mpr
      ⟨i, (G.mem_neighborFinset i j).mp hj |>.symm⟩
    simp only [hx, max_eq_left hdeg]
  have hloc := sum_sqrt_le_of_tail (fun j => G.degree j) M (G.neighborFinset i)
    (fun j hj => G.degree_pos_iff_exists_adj j |>.mpr
      ⟨i, (G.mem_neighborFinset i j).mp hj |>.symm⟩)
    (fun t ht => by unfold tailCount at hM; exact hM i t ht)
  rw [SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_congr rfl hnb]
  refine hloc.trans ?_
  rw [G.card_neighborFinset_eq_degree, Real.sqrt_mul' _ (Nat.cast_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    zero_le_two
  exact Real.sqrt_le_sqrt (by exact_mod_cast le_max_left _ _)

/-- Satisfiability witness: the hypothesis of
`dotProduct_adjMatrix_le_of_degree_tail` holds for `K₃` with `M = 9`,
so the theorem applies and gives `v ⬝ (A v) ≤ 6 (v ⬝ v)` there. -/
example (v : Fin 3 → ℝ) :
    v ⬝ᵥ ((⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ *ᵥ v) ≤ 2 * √9 * (v ⬝ᵥ v) :=
  dotProduct_adjMatrix_le_of_degree_tail _ 9
    (fun k t _ => by
      have h := tail_le_card_sq (⊤ : SimpleGraph (Fin 3)) k t
      norm_num at h ⊢
      linarith) v

end ManyAntipodalPairsForce
