/-
  BilinearComplexity/Omega — the matrix multiplication exponent ω and the
  elementary bounds 2 ≤ ω ≤ 3.

  Capstone of the tensor-rank calculus campaign (roadmap priority 3). It
  defines the exponent of matrix multiplication on top of the sorry-free
  rank calculus (`Basic.lean`, `Flattening.lean`) and proves the two
  classical elementary bounds:

    · `omegaSet`   — the set of admissible exponents `x` such that the
                     rank of the ⟨n,n,n⟩ tensor is eventually bounded by
                     `nˣ` (`Real.rpow`): `∀ᶠ n, R⟨n,n,n⟩ ≤ nˣ`.
    · `omega`      — the exponent `ω := sInf omegaSet`.
    · `three_mem_omegaSet` — `3 ∈ omegaSet`, from the trivial cubic
                     decomposition `R⟨n,n,n⟩ ≤ n·n·n = n³`
                     (`rank_matMulTensor_le`).
    · `two_le_of_mem_omegaSet` — every admissible exponent is `≥ 2`, from
                     the flattening lower bound `n² ≤ R⟨n,n,n⟩`
                     (`sq_le_rank_matMulTensor`): at any `n ≥ 2` one has
                     `n² ≤ nˣ` with base `n > 1`, so `2 ≤ x`.
    · `bddBelow_omegaSet` — `omegaSet` is bounded below (by `2`).
    · `two_le_omega`, `omega_le_three` — the payoff `2 ≤ ω ≤ 3`, packaging
                     the membership lemmas through the `csInf` order API.

  The bound `ω ≤ 3` is the trivial algorithm; `2 ≤ ω` is the flattening
  (a.k.a. Strassen substitution / border-rank) lower bound. Both are the
  textbook first facts about ω; the deep content (`ω < 3`, and whether
  `ω = 2`) lives in later cards.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Proofs.BilinearComplexity.Basic
import Proofs.BilinearComplexity.Flattening

namespace BilinearComplexity

/-! ## 1. The admissible-exponent set and its membership bounds -/

/-- The set of admissible exponents: `x` such that the rank of the
matrix multiplication tensor `⟨n,n,n⟩` is eventually bounded by `nˣ`.
Here `matMulTensor ℝ n n n : Tensor ℝ (n*n) (n*n) (n*n)` is the ⟨n,n,n⟩
tensor and `(n : ℝ) ^ x` is `Real.rpow`. The exponent of matrix
multiplication is the infimum of this set. -/
def omegaSet : Set ℝ :=
  {x : ℝ | ∀ᶠ n : ℕ in Filter.atTop,
    (rank (matMulTensor ℝ n n n) : ℝ) ≤ (n : ℝ) ^ x}

/-- `3` is an admissible exponent: the standard cubic decomposition gives
`R⟨n,n,n⟩ ≤ n·n·n = n³` for every `n` (`rank_matMulTensor_le`), so the
eventual bound holds outright. The cast `((n·n·n : ℕ) : ℝ) = (n:ℝ)^(3:ℝ)`
routes through `Real.rpow_natCast`, covering the `n = 0` case
(`(0:ℝ)^(3:ℝ) = 0`) uniformly. -/
theorem three_mem_omegaSet : (3 : ℝ) ∈ omegaSet := by
  show ∀ᶠ n : ℕ in Filter.atTop,
    (rank (matMulTensor ℝ n n n) : ℝ) ≤ (n : ℝ) ^ (3 : ℝ)
  filter_upwards with n
  have h : rank (matMulTensor ℝ n n n) ≤ n * n * n := rank_matMulTensor_le ℝ n n n
  have hcast : (n : ℝ) ^ (3 : ℝ) = ((n * n * n : ℕ) : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    ring
  rw [hcast]
  exact_mod_cast h

/-- Every admissible exponent is at least `2`: the flattening lower bound
`n² ≤ R⟨n,n,n⟩` (`sq_le_rank_matMulTensor`) combined with `x ∈ omegaSet`
forces `n² ≤ nˣ` at some `n ≥ 2`; since the base `n > 1`, monotonicity of
`Real.rpow` in the exponent (`Real.rpow_le_rpow_left_iff`) yields `2 ≤ x`. -/
theorem two_le_of_mem_omegaSet {x : ℝ} (hx : x ∈ omegaSet) : 2 ≤ x := by
  have hx' : ∀ᶠ n : ℕ in Filter.atTop,
      (rank (matMulTensor ℝ n n n) : ℝ) ≤ (n : ℝ) ^ x := hx
  obtain ⟨n, hbound, hn2⟩ := (hx'.and (Filter.eventually_ge_atTop 2)).exists
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := by omega
    exact_mod_cast this
  have hsq : n ^ 2 ≤ rank (matMulTensor ℝ n n n) := sq_le_rank_matMulTensor ℝ n
  have hcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ (2 : ℝ) := by
    rw [Nat.cast_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hchain : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ x := by
    rw [← hcast]
    calc ((n ^ 2 : ℕ) : ℝ) ≤ (rank (matMulTensor ℝ n n n) : ℝ) := by exact_mod_cast hsq
      _ ≤ (n : ℝ) ^ x := hbound
  exact (Real.rpow_le_rpow_left_iff hn1).mp hchain

/-- `omegaSet` is bounded below: `2` is a lower bound by
`two_le_of_mem_omegaSet`. This makes `sInf omegaSet` a genuine infimum. -/
theorem bddBelow_omegaSet : BddBelow omegaSet :=
  ⟨2, fun _ hx => two_le_of_mem_omegaSet hx⟩

/-! ## 2. The matrix multiplication exponent ω -/

/-- The exponent of matrix multiplication `ω := sInf omegaSet`. The set is
nonempty (`three_mem_omegaSet`) and bounded below by `2`
(`bddBelow_omegaSet`), so this is a genuine infimum bracketed by
`2 ≤ ω ≤ 3`. -/
noncomputable def omega : ℝ := sInf omegaSet

/-- The lower bound `2 ≤ ω`: `2` bounds every admissible exponent below
(`two_le_of_mem_omegaSet`) and `omegaSet` is nonempty
(`three_mem_omegaSet`), so `2 ≤ sInf omegaSet`. -/
theorem two_le_omega : 2 ≤ omega :=
  le_csInf ⟨3, three_mem_omegaSet⟩ (fun _ hx => two_le_of_mem_omegaSet hx)

/-- The upper bound `ω ≤ 3`: `3` is an admissible exponent
(`three_mem_omegaSet`) and `omegaSet` is bounded below
(`bddBelow_omegaSet`), so `sInf omegaSet ≤ 3`. -/
theorem omega_le_three : omega ≤ 3 :=
  csInf_le bddBelow_omegaSet three_mem_omegaSet

end BilinearComplexity
