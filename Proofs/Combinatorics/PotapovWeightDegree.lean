/-
# Potapov: weight-degree inequality for Boolean functions

## Source

Vladimir N. Potapov, "On the Fourier Entropy–Influence Conjecture for Boolean
Plateaued Functions", arXiv:2609.21563.  Abstract, inequality (1) (`feie1`),
and Section "Proof of the Main Inequality": Lemma 1 (`lemIA1`), Lemma 2
(`lemIA2`), Theorem 3 (`ThAI3`); the dual form is Proposition `feie11`.

Theorem 3:

  Let $f:\mathbb{F}_2^n\rightarrow \mathbb{F}_2$ be a Boolean function then
  $$2\sum_{x\in \mathbb{F}_2^n}f(x)\wt(x)\geq \wt(f)(n-\deg_{alg}(f)).$$

Here `wt(x)` is the Hamming weight, `wt(f) = ∑ₓ f(x)` is the support size, and
`deg_alg(f) = max_{M_f(y)=1} wt(y)` with Möbius transform
`M_f(y) = ⊕_{x ≤ y} f(x)` (paper, equation `eqMob`).

The author credits ChatGPT assistance for the main inequality.

## Translation

A vector `x ∈ 𝔽₂ⁿ` is identified with its support `x : Finset (Fin n)`; then
`wt(x) = x.card` and the order `x ≤ y` is `x ⊆ y`.  A Boolean function `f` is
identified with its support `S : Finset (Finset (Fin n))`, so `wt(f) = S.card`
and `∑ₓ f(x) wt(x) = ∑ x ∈ S, x.card`.  The Möbius coefficient `M_f(y)` is the
parity of `#{x ∈ S | x ⊆ y}`, and `anfDeg S` is the largest `y.card` with odd
coefficient (`0` for the zero function, where the inequality is trivial).

## Proof route

* Lemma 1 (`exists_perm_odd_common_superset`): the containment matrix
  `Z y t = [y ⊆ t]` on `S` is block triangular with identity diagonal blocks,
  so `det (Z Zᵀ) = 1` over `ZMod 2`, and a nonzero term of the Leibniz
  expansion gives the permutation.
* Lemma 2 (`even_card_superset_of_lt`): proved here by a parity count instead
  of the paper's ANF-product degree bound: for `T ⊆ w`, the coefficient at
  `univ \ T` vanishes, and summing these over `T ⊆ w` counts `x ∈ S` with
  multiplicity `2 ^ #(w \ x)`, which is odd exactly when `w ⊆ x`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.PotapovWeightDegree

open Finset

/-- The algebraic (ANF) degree of the Boolean function with support
`S ⊆ 𝔽₂ⁿ` (vectors encoded by their supports `Finset (Fin n)`): the largest
`y.card` such that the Möbius coefficient `M_f(y) = ⊕_{x ⊆ y} f(x)`, i.e. the
parity of `#{x ∈ S | x ⊆ y}`, is `1`.  It is `0` when `S = ∅`. -/
def anfDeg {n : ℕ} (S : Finset (Finset (Fin n))) : ℕ :=
  ({y | Odd #{x ∈ S | x ⊆ y}} : Finset (Finset (Fin n))).sup Finset.card

/-! ### Examples for `anfDeg` -/

/-- The constant function `1` on `𝔽₂²` has degree `0`. -/
example : anfDeg (univ : Finset (Finset (Fin 2))) = 0 := by decide

/-- The monomial `x₁x₂` (support `{(1,1)}`) has degree `2`. -/
example : anfDeg ({univ} : Finset (Finset (Fin 2))) = 2 := by decide

/-- The coordinate function `x₁` on `𝔽₂³` has degree `1`. -/
example : anfDeg ({x | (0 : Fin 3) ∈ x} : Finset (Finset (Fin 3))) = 1 := by decide

/-- The zero function has degree `0`. -/
example : anfDeg (∅ : Finset (Finset (Fin 3))) = 0 := by decide

/-- `x₁ + x₂` on `𝔽₂³` has degree `1`. -/
example : anfDeg ({x | xor (decide ((0 : Fin 3) ∈ x)) (decide ((1 : Fin 3) ∈ x)) = true} :
    Finset (Finset (Fin 3))) = 1 := by decide

/-- `x₁x₂ + x₃` on `𝔽₂³` has degree `2`. -/
example : anfDeg ({x | xor (decide ((0 : Fin 3) ∈ x ∧ (1 : Fin 3) ∈ x))
    (decide ((2 : Fin 3) ∈ x)) = true} : Finset (Finset (Fin 3))) = 2 := by decide

/-- The ANF degree never exceeds `n`. -/
theorem anfDeg_le {n : ℕ} (S : Finset (Finset (Fin n))) : anfDeg S ≤ n := by
  refine Finset.sup_le fun y _ => ?_
  simpa using card_le_univ y

/-! ### Lemma 2: parity of superset counts -/

/-- If `n - #T` exceeds the degree, the Möbius coefficient at `univ \ T`
vanishes: `#{x ∈ S | x ⊆ univ \ T}` is even. -/
theorem even_card_subset_compl_of_lt {n : ℕ} (S : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (h : anfDeg S < n - T.card) :
    Even #{x ∈ S | x ⊆ univ \ T} := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hle : (univ \ T).card ≤ anfDeg S :=
    Finset.le_sup (f := Finset.card) (by simpa using hodd)
  rw [card_univ_sdiff, Fintype.card_fin] at hle
  omega

/-- Double counting: summing the coefficients `#{x ∈ S | x ⊆ univ \ T}` over
`T ⊆ w` counts each `x ∈ S` exactly `2 ^ #(w \ x)` times. -/
theorem sum_card_subset_compl {n : ℕ} (S : Finset (Finset (Fin n)))
    (w : Finset (Fin n)) :
    ∑ T ∈ w.powerset, #{x ∈ S | x ⊆ univ \ T} = ∑ x ∈ S, 2 ^ #(w \ x) := by
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter, ← card_powerset]
  congr 1
  ext T
  simp only [mem_filter, mem_powerset, subset_sdiff, subset_univ, true_and]
  exact ⟨fun hT => ⟨hT.1, hT.2.symm⟩, fun hT => ⟨hT.1, hT.2.symm⟩⟩

/-- Potapov's Lemma 2 (`lemIA2`), contrapositive form: if
`#w + deg S < n` then the number of `x ∈ S` with `w ⊆ x` is even.  (With
`w = u ∪ v`, an odd `|T_S(u,v)|` forces `wt u + wt v ≥ n - deg`.) -/
theorem even_card_superset_of_lt {n : ℕ} (S : Finset (Finset (Fin n)))
    (w : Finset (Fin n)) (h : w.card + anfDeg S < n) :
    Even #{x ∈ S | w ⊆ x} := by
  have hsum : Even (∑ x ∈ S, 2 ^ #(w \ x)) := by
    rw [← sum_card_subset_compl]
    refine Finset.even_sum _ fun T hT => even_card_subset_compl_of_lt S T ?_
    have hTw := card_le_card (mem_powerset.mp hT)
    omega
  rw [← ZMod.natCast_eq_zero_iff_even] at hsum ⊢
  rw [← hsum, Nat.cast_sum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hwx : w ⊆ x
  · simp [hwx, sdiff_eq_empty_iff_subset.mpr hwx]
  · have hne : #(w \ x) ≠ 0 := by
      rw [Ne, card_eq_zero, sdiff_eq_empty_iff_subset]
      exact hwx
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [if_neg hwx, hk, Nat.cast_pow, h2, zero_pow (Nat.succ_ne_zero k), Nat.cast_zero]

/-! ### Lemma 1: a permutation with odd common-superset counts -/

/-- The containment matrix of `S` over `𝔽₂`: `Z y t = 1` iff `y ⊆ t`. -/
def inclMatrix {n : ℕ} (S : Finset (Finset (Fin n))) : Matrix S S (ZMod 2) :=
  fun y t => if (y : Finset (Fin n)) ⊆ t then 1 else 0

/-- Entry formula for `inclMatrix`. -/
theorem inclMatrix_apply {n : ℕ} (S : Finset (Finset (Fin n))) (y t : S) :
    inclMatrix S y t = if (y : Finset (Fin n)) ⊆ t then 1 else 0 := rfl

/-- The containment matrix is unitriangular: it is block triangular with
respect to cardinality and its diagonal blocks are identity matrices, so its
determinant is `1`. -/
theorem det_inclMatrix {n : ℕ} (S : Finset (Finset (Fin n))) :
    (inclMatrix S).det = 1 := by
  have hbt : (inclMatrix S).BlockTriangular fun y => (y : Finset (Fin n)).card := by
    intro y t hlt
    have hlt' : (t : Finset (Fin n)).card < (y : Finset (Fin n)).card := hlt
    have hns : ¬ (y : Finset (Fin n)) ⊆ t := fun hsub =>
      absurd (card_le_card hsub) (by omega)
    simp [inclMatrix_apply, hns]
  rw [hbt.det]
  refine prod_eq_one fun k _ => ?_
  have hblock :
      (inclMatrix S).toSquareBlock (fun y => (y : Finset (Fin n)).card) k = 1 := by
    ext i j
    change inclMatrix S i.1 j.1 = (1 : Matrix _ _ (ZMod 2)) i j
    rw [inclMatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hns : ¬ ((i : S) : Finset (Fin n)) ⊆ (j : S) := by
        intro hsub
        apply hij
        apply Subtype.ext
        apply Subtype.ext
        exact eq_of_subset_of_card_le hsub (by rw [i.2, j.2])
      simp [hns, hij]
  rw [hblock, Matrix.det_one]

/-- Over `ZMod 2`, a matrix with nonzero determinant has a permutation `σ`
with all entries `A (σ i) i` nonzero (a nonzero Leibniz term). -/
theorem exists_perm_ne_zero_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hA : A.det ≠ 0) :
    ∃ σ : Equiv.Perm ι, ∀ i, A (σ i) i ≠ 0 := by
  rw [Matrix.det_apply] at hA
  obtain ⟨σ, -, hσ⟩ := exists_ne_zero_of_sum_ne_zero hA
  have hprod : ∏ i, A (σ i) i ≠ 0 := fun h0 => hσ (by rw [h0, smul_zero])
  exact ⟨σ, fun i => (prod_ne_zero_iff.mp hprod) i (mem_univ i)⟩

/-- A nonzero `ZMod 2` cast of a natural number is the cast of an odd number. -/
theorem odd_of_natCast_ne_zero {m : ℕ} (h : (m : ZMod 2) ≠ 0) : Odd m := by
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even]
  exact h

/-- Potapov's Lemma 1 (`lemIA1`): there is a permutation `σ` of `S` such that
for every `y ∈ S` the number `|T_S(y, σ y)|` of `t ∈ S` containing both `y`
and `σ y` is odd. -/
theorem exists_perm_odd_common_superset {n : ℕ} (S : Finset (Finset (Fin n))) :
    ∃ σ : Equiv.Perm S, ∀ y : S,
      Odd #{t ∈ S | (y : Finset (Fin n)) ⊆ t ∧ ((σ y : S) : Finset (Fin n)) ⊆ t} := by
  set Z := inclMatrix S with hZ
  have hG : (Z * Z.transpose).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose, det_inclMatrix, one_mul]
    exact one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det_ne_zero _ hG
  refine ⟨σ, fun y => odd_of_natCast_ne_zero ?_⟩
  convert hσ y using 1
  rw [Matrix.mul_apply, card_filter, Nat.cast_sum, ← sum_coe_sort S]
  refine sum_congr rfl fun t _ => ?_
  simp only [hZ, inclMatrix_apply, Matrix.transpose_apply]
  by_cases h1 : ((σ y : S) : Finset (Fin n)) ⊆ t <;>
    by_cases h2 : (y : Finset (Fin n)) ⊆ t <;> simp [h1, h2]

/-- Dual of Lemma 1: there is a permutation `σ` of `S` such that for every
`y ∈ S` the number of `t ∈ S` contained in both `y` and `σ y` is odd. -/
theorem exists_perm_odd_common_subset {n : ℕ} (S : Finset (Finset (Fin n))) :
    ∃ σ : Equiv.Perm S, ∀ y : S,
      Odd #{t ∈ S | t ⊆ (y : Finset (Fin n)) ∧ t ⊆ ((σ y : S) : Finset (Fin n))} := by
  set Z := inclMatrix S with hZ
  have hG : (Z.transpose * Z).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose, det_inclMatrix, one_mul]
    exact one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det_ne_zero _ hG
  refine ⟨σ, fun y => odd_of_natCast_ne_zero ?_⟩
  convert hσ y using 1
  rw [Matrix.mul_apply, card_filter, Nat.cast_sum, ← sum_coe_sort S]
  refine sum_congr rfl fun t _ => ?_
  simp only [hZ, inclMatrix_apply, Matrix.transpose_apply]
  by_cases h1 : (t : Finset (Fin n)) ⊆ (σ y : S) <;>
    by_cases h2 : (t : Finset (Fin n)) ⊆ y <;> simp [h1, h2]

/-! ### Theorem 3 -/

/-- Potapov, arXiv:2609.21563, Theorem 3 (`ThAI3`), inequality (1): for every
Boolean function `f : 𝔽₂ⁿ → 𝔽₂` with support `S`,
`2 ∑ₓ f(x) wt(x) ≥ wt(f) (n - deg_alg f)`, i.e.
`|S| (n - deg S) ≤ 2 ∑_{x ∈ S} |x|`.  Stated in `ℤ`; no truncation occurs
since `anfDeg S ≤ n` (`anfDeg_le`). -/
theorem potapov_weight_degree {n : ℕ} (S : Finset (Finset (Fin n))) :
    (#S : ℤ) * ((n : ℤ) - anfDeg S) ≤ 2 * ∑ x ∈ S, (#x : ℤ) := by
  obtain ⟨σ, hσ⟩ := exists_perm_odd_common_superset S
  have hpt : ∀ y : S, (n : ℤ) - anfDeg S ≤
      (#(y : Finset (Fin n)) : ℤ) + #((σ y : S) : Finset (Fin n)) := by
    intro y
    have hle : n ≤ #((y : Finset (Fin n)) ∪ (σ y : S)) + anfDeg S := by
      by_contra hlt
      have heven := even_card_superset_of_lt S _ (Nat.lt_of_not_le hlt)
      simp only [union_subset_iff] at heven
      exact (Nat.not_even_iff_odd.mpr (hσ y)) heven
    have hu := card_union_le (y : Finset (Fin n)) (σ y : S)
    omega
  have hsum := sum_le_sum fun (y : S) (_ : y ∈ univ) => hpt y
  rw [sum_const, card_univ, Fintype.card_coe, sum_add_distrib,
    Equiv.sum_comp σ (fun y : S => (#(y : Finset (Fin n)) : ℤ)),
    sum_coe_sort S (fun x => (#x : ℤ)), nsmul_eq_mul] at hsum
  linarith

/-- Potapov, arXiv:2609.21563, Theorem 3 in the truncated natural-number form
`wt(f) (n - deg f) ≤ 2 ∑_{x ∈ S} wt(x)`; the subtraction is exact because
`anfDeg S ≤ n`. -/
theorem potapov_weight_degree_nat {n : ℕ} (S : Finset (Finset (Fin n))) :
    #S * (n - anfDeg S) ≤ 2 * ∑ x ∈ S, #x := by
  have h := potapov_weight_degree S
  have hd := anfDeg_le S
  zify [hd]
  exact h

/-- Potapov, arXiv:2609.21563, Proposition `feie11` (dual form of
inequality (1)): `2 ∑ₓ f(x) wt(x) ≤ wt(f) (n + deg_alg f)`. -/
theorem potapov_weight_degree_dual {n : ℕ} (S : Finset (Finset (Fin n))) :
    2 * ∑ x ∈ S, #x ≤ #S * (n + anfDeg S) := by
  obtain ⟨σ, hσ⟩ := exists_perm_odd_common_subset S
  have hpt : ∀ y : S,
      #(y : Finset (Fin n)) + #((σ y : S) : Finset (Fin n)) ≤ n + anfDeg S := by
    intro y
    have hinter : #((y : Finset (Fin n)) ∩ (σ y : S)) ≤ anfDeg S := by
      refine Finset.le_sup (f := Finset.card) ?_
      simpa only [mem_filter, mem_univ, true_and, subset_inter_iff] using hσ y
    have hunion : #((y : Finset (Fin n)) ∪ (σ y : S)) ≤ n := by
      simpa using card_le_univ ((y : Finset (Fin n)) ∪ (σ y : S))
    have hui := card_union_add_card_inter (y : Finset (Fin n)) (σ y : S)
    omega
  have hsum := sum_le_sum fun (y : S) (_ : y ∈ univ) => hpt y
  rw [sum_const, card_univ, Fintype.card_coe, sum_add_distrib,
    Equiv.sum_comp σ (fun y : S => #(y : Finset (Fin n))),
    sum_coe_sort S (fun x => #x), smul_eq_mul] at hsum
  omega

/-- Non-vacuity and sharpness: for `f = 1` on `𝔽₂²` (support all of the
cube, degree `0`) Theorem 3 holds with equality `4 · 2 = 2 · 4`. -/
example : (#(univ : Finset (Finset (Fin 2))) : ℤ) *
    ((2 : ℕ) - anfDeg (univ : Finset (Finset (Fin 2)))) =
      2 * ∑ x ∈ (univ : Finset (Finset (Fin 2))), (#x : ℤ) := by decide

end Candidates.PotapovWeightDegree
