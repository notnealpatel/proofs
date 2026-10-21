/-
# Chow–Rimanić function-field lonely runner conjecture fails: `C_3(2) ≤ 13`

## Source

* arXiv:2608.18818, Xiyu Hu, "Lonely Runners over Function Fields: Quantized
  Phase–Riesz product".
* Conjecture 1.1 (`conj:CR`, Chow–Rimanić), Theorem 1.2
  (`thm:counterexample-intro`), Lemma 2.1 (`lem:covering`), Section 3 and
  Proposition 3.1 (`prop:certificate`).
* Recorded 2026-10-21.  Status: **proved in the paper** (by an exhaustive check of
  `2^7 = 128` vectors); this module re-proves the certificate in Lean.

## Verbatim informal claims

Conjecture 1.1 (Chow–Rimanić): "If `|F| < Q_k(q)`, then `δ(F) ≥ q^{-k}`", where
`Q_k(q) := 1 + q + ⋯ + q^k` and
`δ(F) := sup_{α ∈ T^{-1} F_q[[T^{-1}]]} min_{f ∈ F} ‖α f‖`.

Theorem 1.2: "There is a family `F_* ⊂ F_2[T]` of thirteen monic polynomials
satisfying `δ(F_*) = 2^{-4}`.  Consequently, `C_3(2) ≤ 13 < 15 = Q_3(2)`."

Section 3: `F_* := {1, T^2+T, T^2+T+1, T^3, T^3+T^2+1, T^3+T+1, T^3+T^2+T+1,
T^4+T^2, T^4+T, T^4+T^3+1, T^4+T^2+1, T^4+T+1, T^4+T^3+T^2+T+1}`.

## Formal reading

Write `α = ∑_{j ≥ 1} α_j T^{-j}`.  For `f = ∑ a_i T^i`, the coefficient of
`T^{-s}` in `α f` (for `s ≥ 1`) is `∑_i a_i α_{i+s}` (proof of Lemma 2.1), and
`‖α f‖ < q^{-k}` holds exactly when these coefficients vanish for `1 ≤ s ≤ k`.

* `fracCoeff f α s` is this coefficient in sequence form; `laurentInv f` is
  `f(T)` written in Mathlib's `LaurentSeries` variable `X = T^{-1}`, and
  `coeff_laurentInv_mul` proves that `fracCoeff` is the genuine coefficient of
  `X^s = T^{-s}` in the product `f · α`.
* `exists_mem_familyStar_coeff_eq_zero` is the covering statement
  (`δ(F_*) < 2^{-3}`, i.e. `δ(F_*) ≤ 2^{-4}`) for every Laurent series `α`.
* `coeff_laurentInv_mul_single_four_ne_zero` is the reverse witness `α = T^{-4}`
  (`δ(F_*) ≥ 2^{-4}`).
* `DeltaLtPow F k` is `δ(F) < q^{-k}` in coefficient form (times `α` range over
  `T^{-1} F_q[[T^{-1}]]`); `ChowRimanicConjectureF2 k` is Conjecture 1.1 at
  `q = 2`.
* `thm_1_2` packages: `F_*` consists of 13 monic polynomials, `13 < Q_3(2) = 15`,
  `DeltaLtPow F_* 3` and `¬ DeltaLtPow F_* 4` (i.e. `δ(F_*) = 2^{-4}`).
* `exists_card_le_thirteen_deltaLtPow_three` is `C_3(2) ≤ 13`, and
  `not_chowRimanicConjectureF2_three` refutes Conjecture 1.1 at `(q, k) = (2, 3)`.

The real-valued norm `‖·‖` and the supremum `δ` are not introduced; the
statements are made at the level of the coefficients that define them.
-/
import Mathlib

set_option autoImplicit false

namespace ChowRimanicLonelyRunner

open Polynomial

/-! ## Definitions -/

/-- `Q_k(q) = 1 + q + ⋯ + q^k`, the size of the standard family of all monic
polynomials of degree at most `k` over `F_q`. -/
def projThreshold (k q : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), q ^ i

example : projThreshold 3 2 = 15 := by decide
example : projThreshold 2 3 = 13 := by decide

/-- Sequence form of the coefficient of `T^{-s}` in `α f`, where
`α = ∑_{j ≥ 1} α j T^{-j}` and `f = ∑ a_i T^i`: it is `∑_i a_i α_{i+s}`
(equation (2.4) of the source).  For `s ≥ 1` the value `α 0` is never used. -/
noncomputable def fracCoeff {R : Type*} [Semiring R] (f : R[X]) (α : ℕ → R) (s : ℕ) : R :=
  f.sum fun i a => a * α (i + s)

/-- The polynomial `f(T)` viewed as a Laurent series in the variable `X = T^{-1}`:
`∑ a_i T^i ↦ ∑ a_i X^{-i}`. -/
noncomputable def laurentInv {R : Type*} [Semiring R] (f : R[X]) : LaurentSeries R :=
  f.sum fun i a => HahnSeries.single (-(i : ℤ)) a

/-- The polynomial with coefficient vector `v = (a_0, …, a_4)`. -/
noncomputable def ofCoeffs (v : Fin 5 → ZMod 2) : (ZMod 2)[X] :=
  ∑ i : Fin 5, C (v i) * X ^ (i : ℕ)

/-- The coefficient vectors `(a_0, …, a_4)` of the thirteen members of `F_*`. -/
def coeffVecs : List (Fin 5 → ZMod 2) :=
  [![1, 0, 0, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 1, 1, 0],
   ![1, 1, 0, 1, 0], ![1, 1, 1, 1, 0], ![0, 0, 1, 0, 1], ![0, 1, 0, 0, 1], ![1, 0, 0, 1, 1],
   ![1, 0, 1, 0, 1], ![1, 1, 0, 0, 1], ![1, 1, 1, 1, 1]]

/-- The paper's thirteen-element family `F_* ⊂ F_2[T]` (Section 3). -/
noncomputable def familyStar : Finset (ZMod 2)[X] :=
  {1, X ^ 2 + X, X ^ 2 + X + 1, X ^ 3, X ^ 3 + X ^ 2 + 1, X ^ 3 + X + 1,
    X ^ 3 + X ^ 2 + X + 1, X ^ 4 + X ^ 2, X ^ 4 + X, X ^ 4 + X ^ 3 + 1, X ^ 4 + X ^ 2 + 1,
    X ^ 4 + X + 1, X ^ 4 + X ^ 3 + X ^ 2 + X + 1}

/-! ## Coefficient computations -/

/-- Coefficients of `ofCoeffs v`: `v n` below degree five, zero above. -/
theorem coeff_ofCoeffs (v : Fin 5 → ZMod 2) (n : ℕ) :
    (ofCoeffs v).coeff n = if h : n < 5 then v ⟨n, h⟩ else 0 := by
  simp only [ofCoeffs, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hn
      exact hb (Fin.ext hn.symm)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hn
    exact h (hn ▸ i.isLt)

/-- `ofCoeffs v` has degree at most four. -/
theorem natDegree_ofCoeffs_lt (v : Fin 5 → ZMod 2) : (ofCoeffs v).natDegree < 5 := by
  have hle : (ofCoeffs v).natDegree ≤ 4 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_ofCoeffs, dif_neg]
    omega
  omega

/-- The sequence-form coefficient for `ofCoeffs v` is the partial-circulant row
`∑_{i<5} a_i α_{i+s}` of equation (3.1). -/
theorem fracCoeff_ofCoeffs (v : Fin 5 → ZMod 2) (α : ℕ → ZMod 2) (s : ℕ) :
    fracCoeff (ofCoeffs v) α s =
      v 0 * α s + v 1 * α (s + 1) + v 2 * α (s + 2) + v 3 * α (s + 3) + v 4 * α (s + 4) := by
  rw [fracCoeff, sum_over_range' _ (fun n => zero_mul (α (n + s))) 5 (natDegree_ofCoeffs_lt v)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_ofCoeffs]
  simp only [Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, dif_pos, zero_add]
  rw [Nat.add_comm 1 s, Nat.add_comm 2 s, Nat.add_comm 3 s, Nat.add_comm 4 s]
  rfl


/-- Bridge to the genuine product (Lemma 2.1, equation (2.4)): for a polynomial
`f(T)` and a Laurent series `α` in `X = T^{-1}`, the coefficient of
`X^s = T^{-s}` in `f · α` is `fracCoeff f (α.coeff ·) s = ∑_i a_i α_{i+s}`. -/
theorem coeff_laurentInv_mul {R : Type*} [Semiring R] (f : R[X]) (α : LaurentSeries R)
    (s : ℕ) : (laurentInv f * α).coeff (s : ℤ) = fracCoeff f (fun j => α.coeff (j : ℤ)) s := by
  rw [laurentInv, fracCoeff, sum_def, sum_def, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hidx : (s : ℤ) = ((i + s : ℕ) : ℤ) + -(i : ℤ) := by push_cast; ring
  rw [hidx, HahnSeries.coeff_single_mul_add]

/- Ground truth: `T` becomes `X^{-1}`. -/
example : laurentInv (X : (ZMod 2)[X]) = HahnSeries.single (-1 : ℤ) 1 := by
  simp [laurentInv]

/- Ground truth: `ofCoeffs (1, 0, 1, 1, 0) = 1 + T^2 + T^3`. -/
example : ofCoeffs ![1, 0, 1, 1, 0] = X ^ 3 + X ^ 2 + 1 := by
  simp only [ofCoeffs, Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, map_one, map_zero,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, mul_one, Matrix.cons_val_one, Nat.one_mod,
      pow_one, zero_mul, add_zero, Matrix.cons_val, Nat.reduceMod, one_mul, Nat.mod_succ]
  ring

/- Ground truth: the `T^{-1}` coefficient of `α (T^3 + T^2 + 1)` is `α_1 + α_3 + α_4`. -/
example (α : ℕ → ZMod 2) : fracCoeff (ofCoeffs ![1, 0, 1, 1, 0]) α 1 = α 1 + α 3 + α 4 := by
  rw [fracCoeff_ofCoeffs]
  simp

/-! ## The family `F_*` -/

/-- The paper's display of `F_*` is the image of the coefficient vectors
`coeffVecs` under `ofCoeffs`. -/
theorem familyStar_eq : familyStar = (coeffVecs.map ofCoeffs).toFinset := by
  have hmap : coeffVecs.map ofCoeffs =
      [1, X ^ 2 + X, X ^ 2 + X + 1, X ^ 3, X ^ 3 + X ^ 2 + 1, X ^ 3 + X + 1,
        X ^ 3 + X ^ 2 + X + 1, X ^ 4 + X ^ 2, X ^ 4 + X, X ^ 4 + X ^ 3 + 1, X ^ 4 + X ^ 2 + 1,
        X ^ 4 + X + 1, X ^ 4 + X ^ 3 + X ^ 2 + X + 1] := by
    simp only [coeffVecs, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ofCoeffs, Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, map_one, map_zero,
          Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, mul_one, Matrix.cons_val_one, Nat.one_mod,
          pow_one, zero_mul, add_zero, Matrix.cons_val, Nat.reduceMod, one_mul, zero_add, Nat.mod_succ] <;>
      ring
  rw [hmap]
  simp [familyStar]

/-- `ofCoeffs` is injective: the vector is recovered from the coefficients. -/
theorem ofCoeffs_injective : Function.Injective ofCoeffs := by
  intro v w hvw
  funext i
  have hv := coeff_ofCoeffs v i
  have hw := coeff_ofCoeffs w i
  rw [hvw, hw, dif_pos i.isLt] at hv
  rw [dif_pos i.isLt] at hv
  exact hv.symm

/-- `F_*` has exactly thirteen members. -/
theorem card_familyStar : familyStar.card = 13 := by
  rw [familyStar_eq, List.toFinset_card_of_nodup]
  · simp [coeffVecs]
  · exact (List.nodup_map_iff ofCoeffs_injective).mpr (by decide)

/-- Every member of `F_*` is monic (in particular nonzero). -/
theorem monic_of_mem_familyStar {f : (ZMod 2)[X]} (hf : f ∈ familyStar) : f.Monic := by
  simp only [familyStar, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    monicity!


/-! ## The certificate (Proposition 3.1) -/

/-- The partial-circulant row `∑_{i<5} a_i α_{i+s}` for a coefficient vector. -/
def circRow (v : Fin 5 → ZMod 2) (α : ℕ → ZMod 2) (s : ℕ) : ZMod 2 :=
  v 0 * α s + v 1 * α (s + 1) + v 2 * α (s + 2) + v 3 * α (s + 3) + v 4 * α (s + 4)

/-- The sequence `0, x₁, …, x₇, 0, 0, …` carrying the seven relevant coefficients. -/
def seq7 (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ZMod 2) (j : ℕ) : ZMod 2 :=
  [0, x₁, x₂, x₃, x₄, x₅, x₆, x₇].getD j 0

example : seq7 1 0 0 1 0 0 1 4 = 1 := by decide
example : seq7 1 1 1 1 1 1 1 8 = 0 := by decide
/- `T^3 + T^2 + 1` against `α = T^{-1}`: the `T^{-1}` coefficient of `α f` is the
`T^0`-coefficient of `f`, namely `1`. -/
example : circRow ![1, 0, 1, 1, 0] (seq7 1 0 0 0 0 0 0) 1 = 1 := by decide

/-- Proposition 3.1 (exhaustive check over `F_2^7`): the thirteen kernels cover
`F_2^7`, i.e. every vector satisfies the three kernel equations of some member. -/
theorem kernels_cover : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ZMod 2,
    ∃ v ∈ coeffVecs, ∀ s ∈ [1, 2, 3], circRow v (seq7 x₁ x₂ x₃ x₄ x₅ x₆ x₇) s = 0 := by
  decide

/-- Only `α_1, …, α_7` enter the rows `s = 1, 2, 3`. -/
theorem circRow_eq_seq7 (v : Fin 5 → ZMod 2) (α : ℕ → ZMod 2) {s : ℕ} (hs : s ∈ [1, 2, 3]) :
    circRow v α s = circRow v (seq7 (α 1) (α 2) (α 3) (α 4) (α 5) (α 6) (α 7)) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> rfl

/-- Sequence form of the covering: for every coefficient sequence `α`, some
`f ∈ F_*` has vanishing coefficients of `T^{-1}, T^{-2}, T^{-3}` in `α f`. -/
theorem exists_mem_familyStar_fracCoeff_eq_zero (α : ℕ → ZMod 2) :
    ∃ f ∈ familyStar, ∀ s ∈ Finset.Icc 1 3, fracCoeff f α s = 0 := by
  obtain ⟨v, hv, hrow⟩ := kernels_cover (α 1) (α 2) (α 3) (α 4) (α 5) (α 6) (α 7)
  refine ⟨ofCoeffs v, ?_, fun s hs => ?_⟩
  · rw [familyStar_eq, List.mem_toFinset]
    exact List.mem_map_of_mem hv
  · have hs' : s ∈ [1, 2, 3] := by
      simp only [Finset.mem_Icc] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [fracCoeff_ofCoeffs]
    exact (circRow_eq_seq7 v α hs').trans (hrow s hs')

/-- **Covering (`δ(F_*) ≤ 2^{-4}`).**  For every Laurent series `α` in
`X = T^{-1}`, some `f ∈ F_*` has `f · α` with vanishing coefficients of
`T^{-1}, T^{-2}, T^{-3}`, i.e. `‖α f‖ < 2^{-3}`. -/
theorem exists_mem_familyStar_coeff_eq_zero (α : LaurentSeries (ZMod 2)) :
    ∃ f ∈ familyStar, ∀ s ∈ Finset.Icc (1 : ℕ) 3, (laurentInv f * α).coeff (s : ℤ) = 0 := by
  obtain ⟨f, hf, hzero⟩ := exists_mem_familyStar_fracCoeff_eq_zero fun j => α.coeff (j : ℤ)
  exact ⟨f, hf, fun s hs => (coeff_laurentInv_mul f α s).trans (hzero s hs)⟩

/-- Finite check behind the witness `α = T^{-4}`. -/
theorem circRow_single_four_ne_zero :
    ∀ v ∈ coeffVecs, ∃ s ∈ [1, 2, 3, 4], circRow v (fun j => if j = 4 then 1 else 0) s ≠ 0 := by
  decide

/-- **Witness (`δ(F_*) ≥ 2^{-4}`).**  For `α = T^{-4}` (the Laurent series
`X^4`), every `f ∈ F_*` has a nonzero coefficient of some `T^{-s}`, `1 ≤ s ≤ 4`,
in `f · α`, i.e. `‖α f‖ ≥ 2^{-4}`. -/
theorem coeff_laurentInv_mul_single_four_ne_zero {f : (ZMod 2)[X]} (hf : f ∈ familyStar) :
    ∃ s ∈ Finset.Icc (1 : ℕ) 4,
      (laurentInv f * HahnSeries.single (4 : ℤ) (1 : ZMod 2)).coeff (s : ℤ) ≠ 0 := by
  rw [familyStar_eq, List.mem_toFinset, List.mem_map] at hf
  obtain ⟨v, hv, rfl⟩ := hf
  obtain ⟨s, hs, hne⟩ := circRow_single_four_ne_zero v hv
  refine ⟨s, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [Finset.mem_Icc]
    omega
  · rw [coeff_laurentInv_mul, fracCoeff_ofCoeffs]
    have hcast : ∀ n : ℕ, (n : ℤ) = 4 ↔ n = 4 := fun n => by omega
    simpa only [circRow, HahnSeries.coeff_single, hcast] using hne


/-! ## Loneliness thresholds and the refutation -/

/-- `δ(F) < q^{-k}` in coefficient form: for every time `α ∈ T^{-1} F_q[[T^{-1}]]`
(a Laurent series in `X = T^{-1}` with no coefficients in degrees `≤ 0`), some
speed `f ∈ F` makes the coefficients of `T^{-1}, …, T^{-k}` in `α f` vanish,
i.e. `‖α f‖ < q^{-k}`.  (The norm takes values in `{0, q^{-1}, q^{-2}, …}`, so
the supremum defining `δ` is attained and `δ(F) < q^{-k}` is this statement.) -/
def DeltaLtPow {K : Type*} [Semiring K] (F : Finset K[X]) (k : ℕ) : Prop :=
  ∀ α : LaurentSeries K, (∀ j : ℤ, j ≤ 0 → α.coeff j = 0) →
    ∃ f ∈ F, ∀ s ∈ Finset.Icc (1 : ℕ) k, (laurentInv f * α).coeff (s : ℤ) = 0

/-- The Chow–Rimanić conjecture (Conjecture 1.1) over `F_2` at level `k`: every
family `F` of nonzero polynomials with `|F| < Q_k(2)` has `δ(F) ≥ 2^{-k}`. -/
def ChowRimanicConjectureF2 (k : ℕ) : Prop :=
  ∀ F : Finset (ZMod 2)[X], (∀ f ∈ F, f ≠ 0) → F.card < projThreshold k 2 → ¬ DeltaLtPow F k

/-- `δ(F_*) < 2^{-3}`. -/
theorem deltaLtPow_familyStar_three : DeltaLtPow familyStar 3 := fun α _ =>
  exists_mem_familyStar_coeff_eq_zero α

/-- `δ(F_*) ≥ 2^{-4}`, witnessed by `α = T^{-4}`. -/
theorem not_deltaLtPow_familyStar_four : ¬ DeltaLtPow familyStar 4 := by
  intro hδ
  have htorus : ∀ j : ℤ, j ≤ 0 → (HahnSeries.single (4 : ℤ) (1 : ZMod 2)).coeff j = 0 := by
    intro j hj
    rw [HahnSeries.coeff_single, if_neg (by omega)]
  obtain ⟨f, hf, hzero⟩ := hδ _ htorus
  obtain ⟨s, hs, hne⟩ := coeff_laurentInv_mul_single_four_ne_zero hf
  exact hne (hzero s hs)

/-- **Theorem 1.2.** `F_*` is a family of thirteen monic polynomials over `F_2`
with `δ(F_*) = 2^{-4}` (that is, `δ(F_*) < 2^{-3}` and `δ(F_*) ≥ 2^{-4}`), and
`13 < 15 = Q_3(2)`. -/
theorem thm_1_2 :
    familyStar.card = 13 ∧ (∀ f ∈ familyStar, f.Monic) ∧ DeltaLtPow familyStar 3 ∧
      ¬ DeltaLtPow familyStar 4 ∧ 13 < projThreshold 3 2 :=
  ⟨card_familyStar, fun _ hf => monic_of_mem_familyStar hf, deltaLtPow_familyStar_three,
    not_deltaLtPow_familyStar_four, by decide⟩

/-- `C_3(2) ≤ 13`: some family of at most thirteen nonzero polynomials over `F_2`
has `δ < 2^{-3}`. -/
theorem exists_card_le_thirteen_deltaLtPow_three :
    ∃ F : Finset (ZMod 2)[X], (∀ f ∈ F, f ≠ 0) ∧ F.card ≤ 13 ∧ DeltaLtPow F 3 :=
  ⟨familyStar, fun _ hf => (monic_of_mem_familyStar hf).ne_zero, card_familyStar.le,
    deltaLtPow_familyStar_three⟩

/-- **The Chow–Rimanić conjecture fails for `(q, k) = (2, 3)`.** -/
theorem not_chowRimanicConjectureF2_three : ¬ ChowRimanicConjectureF2 3 := by
  intro hconj
  refine hconj familyStar (fun _ hf => (monic_of_mem_familyStar hf).ne_zero) ?_
    deltaLtPow_familyStar_three
  rw [card_familyStar]
  decide

end ChowRimanicLonelyRunner
