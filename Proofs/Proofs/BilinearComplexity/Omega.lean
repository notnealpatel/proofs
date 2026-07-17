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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Proofs.BilinearComplexity.Basic
import Proofs.BilinearComplexity.Flattening
import Proofs.BilinearComplexity.KroneckerMatMul
import Proofs.BilinearComplexity.MatMulMono

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

/-! ## 3. The Strassen exponent bound `ω ≤ log_n R⟨n,n,n⟩` -/

/-- **Padding membership.** For every base `n ≥ 2` and every `ε > 0`, the
shifted exponent `α + ε` — with `α := log_n R⟨n,n,n⟩` — is admissible.

This is the analytic heart of the Strassen bound. The exponent `α` itself
is generally *not* in `omegaSet`: recursively padding an `m×m×m` product up
to the next power `n^t ≥ m` costs a bounded but nonzero constant factor
`≤ R⟨n,n,n⟩`, which only washes out in the limit. Concretely, writing
`r := R⟨n,n,n⟩`, `s := Nat.log n m` and `t := s + 1`, so that
`n^s ≤ m < n^t` (`Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`),
monotonicity (Om3, `rank_matMulTensor_mono_cube`) and submultiplicativity
(Om2, `rank_matMulTensor_pow_le`) give

  R⟨m,m,m⟩ ≤ R⟨nᵗ,nᵗ,nᵗ⟩ ≤ rᵗ = rˢ · r.

Since `(n:ℝ)^α = r` (`Real.rpow_logb`; `r ≥ n² ≥ 4 > 0`) and `α ≥ 0`
(`Real.logb_nonneg`), we get `rˢ = ((n:ℝ)ˢ)^α ≤ (m:ℝ)^α`
(`Real.rpow_le_rpow` with `nˢ ≤ m`), whence `R⟨m,m,m⟩ ≤ (m:ℝ)^α · r`.
Finally `r ≤ (m:ℝ)^ε` eventually (`tendsto_rpow_atTop`), so
`R⟨m,m,m⟩ ≤ (m:ℝ)^(α+ε)` eventually — i.e. `α + ε ∈ omegaSet`. -/
theorem logb_rank_add_mem_omegaSet {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    Real.logb n (rank (matMulTensor ℝ n n n)) + ε ∈ omegaSet := by
  have hn1 : 1 < n := by omega
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnR0 : (0 : ℝ) < (n : ℝ) := lt_trans one_pos hnR
  have hnR_ne1 : (n : ℝ) ≠ 1 := ne_of_gt hnR
  set r := rank (matMulTensor ℝ n n n) with hr
  set α := Real.logb (n : ℝ) (r : ℝ) with hα
  have hsq : n ^ 2 ≤ r := by rw [hr]; exact sq_le_rank_matMulTensor ℝ n
  have hr4 : 4 ≤ r := by
    have h4 : (4 : ℕ) ≤ n ^ 2 := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    exact le_trans h4 hsq
  have hr0 : 0 < r := by omega
  have hrR0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hα_eq : (n : ℝ) ^ α = (r : ℝ) := by
    rw [hα]; exact Real.rpow_logb hnR0 hnR_ne1 hrR0
  have hα0 : 0 ≤ α := by rw [hα]; exact Real.logb_nonneg hnR hr1R
  -- `r ≤ m^ε` holds for all sufficiently large `m` since `ε > 0`.
  have hev : ∀ᶠ m : ℕ in Filter.atTop, (r : ℝ) ≤ (m : ℝ) ^ ε := by
    have htend : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ ε) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop (r : ℝ)
  show ∀ᶠ m : ℕ in Filter.atTop,
      (rank (matMulTensor ℝ m m m) : ℝ) ≤ (m : ℝ) ^ (α + ε)
  filter_upwards [Filter.eventually_ge_atTop 1, hev] with m hm1 hmr
  have hm0 : m ≠ 0 := by omega
  have hmR0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  set s := Nat.log n m with hs
  -- `n^s ≤ m < n^(s+1)` bracket `m` between consecutive powers of `n`.
  have hmt : m < n ^ (s + 1) := by rw [hs]; exact Nat.lt_pow_succ_log_self hn1 m
  have hmle : m ≤ n ^ (s + 1) := le_of_lt hmt
  have hlog : n ^ s ≤ m := by rw [hs]; exact Nat.pow_log_le_self n hm0
  -- ℕ chain: pad up to `n^(s+1)`, then use submultiplicativity.
  have hNat : rank (matMulTensor ℝ m m m) ≤ r ^ (s + 1) := by
    calc rank (matMulTensor ℝ m m m)
        ≤ rank (matMulTensor ℝ (n ^ (s + 1)) (n ^ (s + 1)) (n ^ (s + 1))) :=
          rank_matMulTensor_mono_cube ℝ hmle
      _ ≤ rank (matMulTensor ℝ n n n) ^ (s + 1) := rank_matMulTensor_pow_le ℝ n (s + 1)
      _ = r ^ (s + 1) := by rw [← hr]
  have hNatR : (rank (matMulTensor ℝ m m m) : ℝ) ≤ (r : ℝ) ^ (s + 1) := by
    exact_mod_cast hNat
  -- `rˢ = ((n:ℝ)ˢ)^α` via `r = (n:ℝ)^α` and commuting the two exponents.
  have hswap : (r : ℝ) ^ s = ((n : ℝ) ^ s) ^ α := by
    rw [← hα_eq, ← Real.rpow_natCast_mul hnR0.le, ← Real.rpow_mul_natCast hnR0.le,
      mul_comm α (s : ℝ)]
  have hbase : (n : ℝ) ^ s ≤ (m : ℝ) := by exact_mod_cast hlog
  have hstep : ((n : ℝ) ^ s) ^ α ≤ (m : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) hbase hα0
  have hrs : (r : ℝ) ^ s ≤ (m : ℝ) ^ α := by rw [hswap]; exact hstep
  calc (rank (matMulTensor ℝ m m m) : ℝ)
      ≤ (r : ℝ) ^ (s + 1) := hNatR
    _ = (r : ℝ) ^ s * (r : ℝ) := by rw [pow_succ]
    _ ≤ (m : ℝ) ^ α * (r : ℝ) := mul_le_mul_of_nonneg_right hrs hrR0.le
    _ ≤ (m : ℝ) ^ α * (m : ℝ) ^ ε := mul_le_mul_of_nonneg_left hmr (by positivity)
    _ = (m : ℝ) ^ (α + ε) := by rw [← Real.rpow_add hmR0]

/-- **Any single rank bound gives a Strassen exponent bound.** For `n ≥ 2`,
`ω ≤ log_n R⟨n,n,n⟩`. The padding membership `logb_rank_add_mem_omegaSet`
puts `α + ε` in `omegaSet` for every `ε > 0`, so `ω = sInf omegaSet ≤ α + ε`
(`csInf_le bddBelow_omegaSet`); letting `ε → 0` gives `ω ≤ α`. -/
theorem omega_le_logb {n : ℕ} (hn : 2 ≤ n) :
    omega ≤ Real.logb n (rank (matMulTensor ℝ n n n)) := by
  have key : ∀ ε : ℝ, 0 < ε →
      omega ≤ Real.logb n (rank (matMulTensor ℝ n n n)) + ε :=
    fun ε hε => csInf_le bddBelow_omegaSet (logb_rank_add_mem_omegaSet hn hε)
  by_contra hcon
  rw [not_le] at hcon
  have hε : (0 : ℝ) < (omega - Real.logb n (rank (matMulTensor ℝ n n n))) / 2 := by
    linarith
  have := key _ hε
  linarith

/-- **Strassen's exponent bound** `ω ≤ log₂ 7`. Instantiate `omega_le_logb`
at `n = 2` and bound `log₂ R⟨2,2,2⟩ ≤ log₂ 7` by monotonicity of `log₂`
(base `1 < 2`), using Strassen's `R⟨2,2,2⟩ ≤ 7`
(`rank_matMulTensor_le_seven_real`, Om2) and `0 < R⟨2,2,2⟩` (from
`4 ≤ R⟨2,2,2⟩`). -/
theorem omega_le_logb_two_seven : omega ≤ Real.logb 2 7 := by
  have h1 := omega_le_logb (n := 2) (by norm_num)
  simp only [Nat.cast_ofNat] at h1
  have hpos : (0 : ℝ) < (rank (matMulTensor ℝ 2 2 2) : ℝ) := by
    have h4 := sq_le_rank_matMulTensor ℝ 2
    norm_num at h4
    exact_mod_cast (show 0 < rank (matMulTensor ℝ 2 2 2) by omega)
  have hle7 : (rank (matMulTensor ℝ 2 2 2) : ℝ) ≤ (7 : ℝ) := by
    exact_mod_cast rank_matMulTensor_le_seven_real
  have h2 : Real.logb 2 (rank (matMulTensor ℝ 2 2 2) : ℝ) ≤ Real.logb 2 7 :=
    Real.logb_le_logb_of_le (by norm_num) hpos hle7
  exact le_trans h1 h2

/-- **`ω < 3`.** The Strassen bound `ω ≤ log₂ 7` is strictly below `3`
because `7 < 2³ = 8` (`Real.logb_lt_iff_lt_rpow`; `norm_num` closes the
arithmetic after `Real.rpow_natCast`). -/
theorem omega_lt_three : omega < 3 := by
  have h37 : Real.logb 2 7 < 3 := by
    have hlt : (7 : ℝ) < (2 : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)).mpr hlt
  exact lt_of_le_of_lt omega_le_logb_two_seven h37

/-! ## 4. Asymptotic upper bound R(k,k,k) ≤ C · k^(ω+ε) -/

/-- **Asymptotic upper bound.** For every `ε > 0` there exists `C > 0` such
that for all `k ≥ 1`, `R⟨k,k,k⟩ ≤ C · k^(ω+ε)` (where `^` is `Real.rpow`).

Since `ω = sInf omegaSet` and `ε > 0`, there is an admissible exponent
`x ∈ omegaSet` with `x < ω + ε` (by `Real.lt_sInf_add_pos`). From
`x ∈ omegaSet`, the bound `R⟨k,k,k⟩ ≤ k^x` holds for all `k` above some
threshold `n₀`. Since `x ≤ ω + ε` and `k ≥ 1` entails `k^x ≤ k^(ω+ε)`,
the bound holds for `k ≥ n₀` with `C = 1`. For the finitely many
`k ∈ {1, …, n₀-1}`, each `R⟨k,k,k⟩ ≤ R(k) · 1 ≤ R(k) · k^(ω+ε)` (since
`k^(ω+ε) ≥ 1`), so taking `C` to be the max over these ranks (floored at 1)
handles all cases uniformly. -/
theorem exists_rank_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      (rank (matMulTensor ℝ k k k) : ℝ) ≤ C * (k : ℝ) ^ (omega + ε) := by
  -- Step 1: extract an admissible exponent x < omega + ε from omegaSet.
  obtain ⟨x, hx_mem, hx_lt⟩ :=
    Real.lt_sInf_add_pos ⟨3, three_mem_omegaSet⟩ hε
  -- Step 2: from x ∈ omegaSet, extract threshold n₀ such that the bound
  -- holds for all k ≥ n₀.
  have hx_ev : ∀ᶠ k : ℕ in Filter.atTop,
      (rank (matMulTensor ℝ k k k) : ℝ) ≤ (k : ℝ) ^ x := hx_mem
  obtain ⟨n₀, hn₀⟩ :=
    (Filter.eventually_forall_ge_atTop.mpr hx_ev).exists
  -- hn₀ : ∀ k ≥ n₀, R(k,k,k) ≤ k^x
  -- The exponent x is at most omega + ε (strictly less, but ≤ suffices).
  have hx_le : x ≤ omega + ε := le_of_lt hx_lt
  -- Step 3: define C as the max of 1 and all ranks for k < n₀.
  -- We use Finset.sup over Finset.range n₀ with ⊥ = 0 in ℕ, then cast.
  set M : ℕ := (Finset.range n₀).sup (fun k => rank (matMulTensor ℝ k k k))
  set C : ℝ := max 1 (M : ℝ) with hC_def
  refine ⟨C, lt_of_lt_of_le one_pos (le_max_left 1 (M : ℝ)), fun k hk => ?_⟩
  -- omega + ε > 0 (since omega ≥ 2 and ε > 0)
  have hωε : 0 < omega + ε := by linarith [two_le_omega]
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpow1 : (1 : ℝ) ≤ (k : ℝ) ^ (omega + ε) := Real.one_le_rpow hk1 hωε.le
  by_cases hkn : n₀ ≤ k
  · -- Large case: k ≥ n₀. Use the eventually bound + exponent monotonicity.
    have h1 : (rank (matMulTensor ℝ k k k) : ℝ) ≤ (k : ℝ) ^ x := hn₀ k hkn
    have h2 : (k : ℝ) ^ x ≤ (k : ℝ) ^ (omega + ε) :=
      Real.rpow_le_rpow_of_exponent_le hk1 hx_le
    calc (rank (matMulTensor ℝ k k k) : ℝ)
        ≤ (k : ℝ) ^ (omega + ε) := le_trans h1 h2
      _ = 1 * (k : ℝ) ^ (omega + ε) := (one_mul _).symm
      _ ≤ C * (k : ℝ) ^ (omega + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left 1 (M : ℝ)) (by positivity)
  · -- Small case: k < n₀. Use the finite max bound.
    push Not at hkn
    have hk_range : k ∈ Finset.range n₀ := Finset.mem_range.mpr hkn
    have hM : rank (matMulTensor ℝ k k k) ≤ M :=
      Finset.le_sup (f := fun k => rank (matMulTensor ℝ k k k)) hk_range
    calc (rank (matMulTensor ℝ k k k) : ℝ)
        ≤ (M : ℝ) := by exact_mod_cast hM
      _ ≤ C := le_max_right 1 (M : ℝ)
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (k : ℝ) ^ (omega + ε) :=
          mul_le_mul_of_nonneg_left hkpow1 (lt_of_lt_of_le one_pos (le_max_left 1 _)).le

/-- **Complex corollary.** The same asymptotic upper bound holds over `ℂ`:
for every `ε > 0` there exists `C > 0` such that for all `k ≥ 1`,
`R_ℂ⟨k,k,k⟩ ≤ C · k^(ω+ε)`. Since `R_ℂ⟨k,k,k⟩ ≤ R_ℝ⟨k,k,k⟩`
(by `rank_matMulTensor_hom_le` along `algebraMap ℝ ℂ`), the real bound
transfers immediately. -/
theorem exists_rank_le_rpow_complex (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      (rank (matMulTensor ℂ k k k) : ℝ) ≤ C * (k : ℝ) ^ (omega + ε) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := exists_rank_le_rpow ε hε
  refine ⟨C, hC_pos, fun k hk => ?_⟩
  have htransfer : rank (matMulTensor ℂ k k k) ≤ rank (matMulTensor ℝ k k k) :=
    rank_matMulTensor_hom_le ℝ ℂ (algebraMap ℝ ℂ) k k k
  calc (rank (matMulTensor ℂ k k k) : ℝ)
      ≤ (rank (matMulTensor ℝ k k k) : ℝ) := by exact_mod_cast htransfer
    _ ≤ C * (k : ℝ) ^ (omega + ε) := hC_bound k hk

end BilinearComplexity
