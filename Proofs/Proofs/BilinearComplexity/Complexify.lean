/-
  BilinearComplexity/Complexify — the complexification rank bound
  `R_ℝ(T) ≤ 4·R_ℂ(Tℂ)` and the complex-rank Strassen bounds for ω.

  The exponent `ω` (`Omega.lean`) is defined through ranks of
  `matMulTensor ℝ n n n`, but decompositions arising from Wedderburn
  theory (the Cohn–Umans chain) live over ℂ. The hom-transfer of
  `KroneckerMatMul.lean` only gives `R_ℂ ≤ R_ℝ`; this file supplies the
  reverse comparison, at the standard factor `4`, and feeds it through
  the Strassen padding argument:

    · `RankLE.add`         — pointwise-sum subadditivity of `RankLE`
                             (concatenate triad families with
                             `Fin.append`), with the rank corollary
                             `rank_add_le`.
    · `RankLE.of_map_complex` — an `r`-triad ℂ-decomposition of the
                             entrywise complexification
                             `fun i j l => algebraMap ℝ ℂ (T i j l)`
                             yields `4r` real triads for `T`: taking
                             real parts, each complex triad `u⊗v⊗w`
                             contributes
                             `Re(uvw) = Re u·Re v·Re w − Im u·Im v·Re w
                             − Re u·Im v·Im w − Im u·Re v·Im w`,
                             i.e. four real triads (signs absorbed into
                             the first vector).
    · `rank_le_four_mul_rank_map_complex` — the payoff
                             `R_ℝ(T) ≤ 4·R_ℂ(Tℂ)`, and its matMul
                             instance `rank_matMulTensor_le_four_mul_complex`
                             (`R_ℝ⟨a,b,c⟩ ≤ 4·R_ℂ⟨a,b,c⟩` via
                             `matMulTensor_map`).
    · `logb_rank_complex_add_mem_omegaSet` — the padding membership of
                             `Omega.lean` rerun against `r := R_ℂ⟨n,n,n⟩`:
                             `R_ℝ⟨m,m,m⟩ ≤ R_ℝ⟨n^(s+1)⟩ ≤ 4·R_ℂ⟨n^(s+1)⟩
                             ≤ 4·r^(s+1)`, the constant `4·r` being
                             absorbed by the `ε`-slack `r·4 ≤ m^ε`
                             eventually; the flattening lower bound
                             `n² ≤ R_ℂ⟨n,n,n⟩` (valid over any nontrivial
                             commutative ring) supplies the positivity
                             side conditions.
    · `omega_le_logb_complex`, `rpow_omega_le_rank_complex` — the
                             consumable Strassen bounds over ℂ: for
                             `n ≥ 2`, `ω ≤ log_n R_ℂ⟨n,n,n⟩` and
                             `n^ω ≤ R_ℂ⟨n,n,n⟩` (`Real.rpow`).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Proofs.BilinearComplexity.Basic
import Proofs.BilinearComplexity.Flattening
import Proofs.BilinearComplexity.KroneckerMatMul
import Proofs.BilinearComplexity.MatMulMono
import Proofs.BilinearComplexity.Omega

namespace BilinearComplexity

/-! ## 1. Pointwise-sum subadditivity of rank -/

section Add

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- `RankLE` is subadditive under pointwise sums: concatenate the two
triad families with `Fin.append` (same mechanism as `RankLE.mono`, which
pads with zeros; here both halves carry content). -/
theorem RankLE.add {T T' : Tensor k a b c} {r r' : ℕ}
    (h : RankLE T r) (h' : RankLE T' r') : RankLE (T + T') (r + r') := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨u', v', w', rfl⟩ := h'
  refine ⟨Fin.append u u', Fin.append v v', Fin.append w w', ?_⟩
  funext i j l
  simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- Tensor rank is subadditive: `rank (T + T') ≤ rank T + rank T'`. -/
theorem rank_add_le (T T' : Tensor k a b c) :
    rank (T + T') ≤ rank T + rank T' :=
  rank_le_of_rankLE ((rankLE_rank T).add (rankLE_rank T'))

end Add

/-! ## 2. The 4× complexification bound -/

section Complexify

variable {a b c : ℕ}

/-- **The 4× real/imaginary split.** An `r`-triad decomposition over ℂ of
the entrywise complexification of a real tensor yields a `4r`-triad real
decomposition of the tensor itself. Taking real parts of
`Tℂ = ∑ₛ uₛ ⊗ vₛ ⊗ wₛ` and expanding by `Complex.mul_re`/`mul_im`, each
complex triad contributes the four real triads
`Re u ⊗ Re v ⊗ Re w`, `(−Im u) ⊗ Im v ⊗ Re w`, `(−Re u) ⊗ Im v ⊗ Im w`,
`(−Im u) ⊗ Re v ⊗ Im w`, which are summed with `RankLE.add`. -/
theorem RankLE.of_map_complex {T : Tensor ℝ a b c} {r : ℕ}
    (h : RankLE (fun i j l => algebraMap ℝ ℂ (T i j l)) r) :
    RankLE T (4 * r) := by
  obtain ⟨u, v, w, hT⟩ := h
  have h₁ : RankLE
      (fun i j l => ∑ s, (u s i).re * (v s j).re * (w s l).re) r :=
    ⟨fun s i => (u s i).re, fun s j => (v s j).re, fun s l => (w s l).re, rfl⟩
  have h₂ : RankLE
      (fun i j l => ∑ s, (-(u s i).im) * (v s j).im * (w s l).re) r :=
    ⟨fun s i => -(u s i).im, fun s j => (v s j).im, fun s l => (w s l).re, rfl⟩
  have h₃ : RankLE
      (fun i j l => ∑ s, (-(u s i).re) * (v s j).im * (w s l).im) r :=
    ⟨fun s i => -(u s i).re, fun s j => (v s j).im, fun s l => (w s l).im, rfl⟩
  have h₄ : RankLE
      (fun i j l => ∑ s, (-(u s i).im) * (v s j).re * (w s l).im) r :=
    ⟨fun s i => -(u s i).im, fun s j => (v s j).re, fun s l => (w s l).im, rfl⟩
  have hsplit : T =
      (fun i j l => ∑ s, (u s i).re * (v s j).re * (w s l).re)
      + (fun i j l => ∑ s, (-(u s i).im) * (v s j).im * (w s l).re)
      + (fun i j l => ∑ s, (-(u s i).re) * (v s j).im * (w s l).im)
      + (fun i j l => ∑ s, (-(u s i).im) * (v s j).re * (w s l).im) := by
    funext i j l
    have h0 : algebraMap ℝ ℂ (T i j l) = ∑ s, u s i * v s j * w s l :=
      congrFun (congrFun (congrFun hT i) j) l
    have h1 : (algebraMap ℝ ℂ (T i j l)).re = T i j l := by
      simp [Complex.coe_algebraMap]
    have hre : T i j l = ∑ s, (u s i * v s j * w s l).re := by
      rw [← h1, h0, Complex.re_sum]
    simp only [Pi.add_apply]
    rw [hre, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [show 4 * r = r + r + r + r by ring, hsplit]
  exact ((h₁.add h₂).add h₃).add h₄

/-- **Complexification rank bound.** The real rank of a real tensor is at
most four times the complex rank of its entrywise complexification:
`R_ℝ(T) ≤ 4·R_ℂ(Tℂ)`. Apply `RankLE.of_map_complex` to an optimal
complex decomposition (`rankLE_rank`). -/
theorem rank_le_four_mul_rank_map_complex (T : Tensor ℝ a b c) :
    rank T ≤ 4 * rank (fun i j l => algebraMap ℝ ℂ (T i j l)) :=
  rank_le_of_rankLE
    (RankLE.of_map_complex (rankLE_rank (fun i j l => algebraMap ℝ ℂ (T i j l))))

end Complexify

/-- The matrix multiplication instance of the complexification bound:
`R_ℝ⟨a,b,c⟩ ≤ 4·R_ℂ⟨a,b,c⟩`. The complexified matMul tensor IS the
complex matMul tensor (`matMulTensor_map`, entries are `0`/`1`). Together
with `rank_matMulTensor_hom_le` this sandwiches the two ranks:
`R_ℂ ≤ R_ℝ ≤ 4·R_ℂ`. -/
theorem rank_matMulTensor_le_four_mul_complex (a b c : ℕ) :
    rank (matMulTensor ℝ a b c) ≤ 4 * rank (matMulTensor ℂ a b c) := by
  have h := rank_le_four_mul_rank_map_complex (matMulTensor ℝ a b c)
  rwa [matMulTensor_map ℝ ℂ (algebraMap ℝ ℂ) a b c] at h

/-! ## 3. ω against the complex rank of ⟨n,n,n⟩ -/

/-- **Padding membership against the complex rank.** For every base
`n ≥ 2` and every `ε > 0`, the exponent `log_n R_ℂ⟨n,n,n⟩ + ε` is
admissible for `ω`. This is `logb_rank_add_mem_omegaSet` (Omega.lean)
rerun with `r := R_ℂ⟨n,n,n⟩`: bracketing `n^s ≤ m < n^(s+1)`,
monotonicity over ℝ, the complexification bound, and
submultiplicativity over ℂ give

  `R_ℝ⟨m,m,m⟩ ≤ R_ℝ⟨n^(s+1)⟩ ≤ 4·R_ℂ⟨n^(s+1)⟩ ≤ 4·r^(s+1)`,

and with `(n:ℝ)^α = r` for `α := log_n r` (the flattening bound
`n² ≤ R_ℂ⟨n,n,n⟩`, valid over the nontrivial commutative ring ℂ,
supplies `r ≥ 4 > 0`), `r^s ≤ (m:ℝ)^α`, so
`R_ℝ⟨m,m,m⟩ ≤ (m:ℝ)^α · (4r) ≤ (m:ℝ)^(α+ε)` once `4r ≤ (m:ℝ)^ε` —
which holds eventually since `ε > 0`. The extra constant `4` is thus
absorbed exactly like the single padding factor `r` in the real proof. -/
theorem logb_rank_complex_add_mem_omegaSet {n : ℕ} (hn : 2 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    Real.logb n (rank (matMulTensor ℂ n n n)) + ε ∈ omegaSet := by
  have hn1 : 1 < n := by omega
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnR0 : (0 : ℝ) < (n : ℝ) := lt_trans one_pos hnR
  have hnR_ne1 : (n : ℝ) ≠ 1 := ne_of_gt hnR
  set r := rank (matMulTensor ℂ n n n) with hr
  set α := Real.logb (n : ℝ) (r : ℝ) with hα
  have hsq : n ^ 2 ≤ r := by rw [hr]; exact sq_le_rank_matMulTensor ℂ n
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
  -- `4·r ≤ m^ε` holds for all sufficiently large `m` since `ε > 0`.
  have hev : ∀ᶠ m : ℕ in Filter.atTop, 4 * (r : ℝ) ≤ (m : ℝ) ^ ε := by
    have htend : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ ε)
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop (4 * (r : ℝ))
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
  -- ℕ chain: pad up over ℝ, complexify, then use submultiplicativity over ℂ.
  have hNat : rank (matMulTensor ℝ m m m) ≤ 4 * r ^ (s + 1) := by
    calc rank (matMulTensor ℝ m m m)
        ≤ rank (matMulTensor ℝ (n ^ (s + 1)) (n ^ (s + 1)) (n ^ (s + 1))) :=
          rank_matMulTensor_mono_cube ℝ hmle
      _ ≤ 4 * rank (matMulTensor ℂ (n ^ (s + 1)) (n ^ (s + 1)) (n ^ (s + 1))) :=
          rank_matMulTensor_le_four_mul_complex (n ^ (s + 1)) (n ^ (s + 1))
            (n ^ (s + 1))
      _ ≤ 4 * rank (matMulTensor ℂ n n n) ^ (s + 1) :=
          Nat.mul_le_mul (le_refl 4) (rank_matMulTensor_pow_le ℂ n (s + 1))
      _ = 4 * r ^ (s + 1) := by rw [← hr]
  have hNatR : (rank (matMulTensor ℝ m m m) : ℝ) ≤ 4 * (r : ℝ) ^ (s + 1) := by
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
      ≤ 4 * (r : ℝ) ^ (s + 1) := hNatR
    _ = (r : ℝ) ^ s * (4 * (r : ℝ)) := by rw [pow_succ]; ring
    _ ≤ (m : ℝ) ^ α * (4 * (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hrs (by positivity)
    _ ≤ (m : ℝ) ^ α * (m : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hmr (by positivity)
    _ = (m : ℝ) ^ (α + ε) := by rw [← Real.rpow_add hmR0]

/-- **The Strassen exponent bound against the complex rank.** For `n ≥ 2`,
`ω ≤ log_n R_ℂ⟨n,n,n⟩`. The padding membership
`logb_rank_complex_add_mem_omegaSet` puts `α + ε` in `omegaSet` for every
`ε > 0`, so `ω = sInf omegaSet ≤ α + ε`; letting `ε → 0` gives `ω ≤ α`.
This is the lower-bound-side transfer needed to run the Cohn–Umans chain,
whose decompositions live over ℂ, against the real-rank definition of ω. -/
theorem omega_le_logb_complex {n : ℕ} (hn : 2 ≤ n) :
    omega ≤ Real.logb n (rank (matMulTensor ℂ n n n)) := by
  have key : ∀ ε : ℝ, 0 < ε →
      omega ≤ Real.logb n (rank (matMulTensor ℂ n n n)) + ε :=
    fun ε hε => csInf_le bddBelow_omegaSet (logb_rank_complex_add_mem_omegaSet hn hε)
  by_contra hcon
  rw [not_le] at hcon
  have hε : (0 : ℝ) < (omega - Real.logb n (rank (matMulTensor ℂ n n n))) / 2 := by
    linarith
  have := key _ hε
  linarith

/-- **Exponentiated form**: `n^ω ≤ R_ℂ⟨n,n,n⟩` for `n ≥ 2` (`^` is
`Real.rpow`). From `ω ≤ log_n R_ℂ⟨n,n,n⟩` by monotonicity of `rpow` in
the exponent (base `n > 1`) and `Real.rpow_logb` (the flattening bound
over ℂ gives `R_ℂ⟨n,n,n⟩ ≥ n² > 0`). -/
theorem rpow_omega_le_rank_complex {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ omega ≤ (rank (matMulTensor ℂ n n n) : ℝ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr0 : 0 < rank (matMulTensor ℂ n n n) :=
    lt_of_lt_of_le (pow_pos (show 0 < n by omega) 2) (sq_le_rank_matMulTensor ℂ n)
  have hrR0 : (0 : ℝ) < (rank (matMulTensor ℂ n n n) : ℝ) := by exact_mod_cast hr0
  calc (n : ℝ) ^ omega
      ≤ (n : ℝ) ^ Real.logb n (rank (matMulTensor ℂ n n n)) :=
        Real.rpow_le_rpow_of_exponent_le hn1.le (omega_le_logb_complex hn)
    _ = (rank (matMulTensor ℂ n n n) : ℝ) :=
        Real.rpow_logb (lt_trans one_pos hn1) (ne_of_gt hn1) hrR0

end BilinearComplexity
