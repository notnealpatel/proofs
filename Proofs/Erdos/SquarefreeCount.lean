/-
# Counting squarefree integers: `Q(N) = (6/π²) N + O(√N)`

## Classical source

* L. Gegenbauer, *Asymptotische Gesetze der Zahlentheorie*, Denkschriften
  der Akademie der Wissenschaften Wien 49 (1885), 37–80.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of
  Numbers*, Theorem 333 (§18.6): the number `Q(x)` of squarefree
  ("quadratfrei") numbers not exceeding `x` satisfies
  `Q(x) = 6x/π² + O(√x)`.

## Informal statement (target spec, verbatim)

  "There is C such that for all N >= 1,
   |#{n <= N : n squarefree} - 6N/pi^2| <= C sqrt N."

Date: 2026-10-21.

## Mathlib absence check

`leandoc` searches ("squarefree count density asymptotic", "squarefree
moebius sum divisors square squarefree indicator") and a grep of Mathlib
for `Squarefree` together with `card`/`tendsto`/`density`/`π ^ 2` find no
counting result; Mathlib supplies only the ingredients used below.

## Proof (Hardy–Wright route)

1. `[n squarefree] = ∑_{d² ∣ n} μ(d)` (write `n = b² a` with `a`
   squarefree; then `d² ∣ n ↔ d ∣ b`, and `∑_{d ∣ b} μ(d) = [b = 1]`).
2. Swapping sums, `Q(N) = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`.
3. Replacing `⌊N/d²⌋` by `N/d²` costs at most `⌊√N⌋ + 1`.
4. `∑_d μ(d)/d² = 6/π²` (from `L(ζ, 2) · L(μ, 2) = 1` and
   `ζ(2) = π²/6`), and the tail beyond `⌊√N⌋` is at most `2/(⌊√N⌋+1)`,
   so `N` times it is at most `2√N`.

Together: `|Q(N) - 6N/π²| ≤ 4√N` for `N ≥ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Erdos.SquarefreeCount

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Ground truth for the counted set

`Q(10) = 7` (the squarefree numbers `1, 2, 3, 5, 6, 7, 10`), and
`Q(1) = 1`. -/

/-- For `n ≠ 0`, `n` is squarefree iff no `x` with `2 ≤ x ≤ n` has `x * x ∣ n`.
A bounded, kernel-decidable reformulation of `Squarefree` used only for the
ground-truth checks below (Mathlib's `Nat.minSqFac` instance does not reduce
in the kernel). -/
lemma squarefree_iff_forall_Icc {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ x ∈ Icc 2 n, ¬ x * x ∣ n := by
  constructor
  · intro h x hx hdvd
    have hx1 := Nat.isUnit_iff.mp (h x hdvd)
    simp only [mem_Icc] at hx
    omega
  · intro h x hdvd
    rw [Nat.isUnit_iff]
    by_contra hx1
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp only [mul_zero, zero_dvd_iff] at hdvd
      exact hn hdvd
    have hxn : x ≤ n := (Nat.le_mul_self x).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
    exact h x (mem_Icc.mpr ⟨by omega, hxn⟩) hdvd

example : ((Icc 1 10).filter Squarefree).card = 7 := by
  rw [filter_congr (q := fun n => ∀ x ∈ Icc 2 n, ¬ x * x ∣ n)
    (fun n hn => squarefree_iff_forall_Icc (by simp only [mem_Icc] at hn; omega))]
  decide

example : ((Icc 1 30).filter Squarefree).card = 19 := by
  rw [filter_congr (q := fun n => ∀ x ∈ Icc 2 n, ¬ x * x ∣ n)
    (fun n hn => squarefree_iff_forall_Icc (by simp only [mem_Icc] at hn; omega))]
  decide

/-! ## Arithmetic layer -/


/-- If `a` is squarefree, `b ≠ 0`, and `d² ∣ b² a`, then `d ∣ b`
(compare `p`-adic valuations: `2 v_p(d) ≤ 2 v_p(b) + v_p(a)` with `v_p(a) ≤ 1`). -/
lemma dvd_of_sq_dvd_sq_mul {d b a : ℕ} (hb : b ≠ 0) (ha : Squarefree a)
    (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hd : d ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_dvd_iff,
      mul_eq_zero, pow_eq_zero_iff, hb, ha0, or_self] at h
  rw [← Nat.factorization_le_iff_dvd hd hb]
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) (mul_ne_zero (pow_ne_zero 2 hb) ha0)] at h
  intro p
  have hp := h p
  have h1 := ha.natFactorization_le_one p
  simp only [Nat.factorization_mul (pow_ne_zero 2 hb) ha0, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
  omega

/-- Möbius inversion of the constant `1`: `∑_{d ∣ b} μ(d) = [b = 1]`. -/
lemma sum_moebius_divisors (b : ℕ) :
    ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f b) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  exact h

/-- `∑_{d ≥ 1} μ(d)/d² = 6/π²` (the `d = 0` term is `0/0 = 0`), from
`L(ζ, 2) · L(μ, 2) = 1` and `ζ(2) = π²/6`. -/
lemma hasSum_moebius_div_sq :
    HasSum (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hsum := (LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have hval : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have h1 := LSeries_zeta_mul_Lseries_moebius hs
    rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp at h1 ⊢
    linear_combination h1
  rw [hval] at hsum
  refine Complex.hasSum_ofReal.mp ?_
  unfold LSeriesHasSum at hsum
  convert hsum using 1
  funext n
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.cpow_ofNat]
    push_cast
    rfl


/-- If `n = b² a` with `a` squarefree and `0 < n ≤ N`, then the `d ∈ [1, N]`
with `d² ∣ n` are exactly the divisors of `b`. -/
lemma filter_sq_dvd_eq_divisors {N n a b : ℕ} (hnN : n ≤ N) (hab : b ^ 2 * a = n)
    (ha : Squarefree a) (hn : n ≠ 0) :
    (Icc 1 N).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hab
    exact hn hab.symm
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors, ne_eq, hb, not_false_eq_true, and_true]
  constructor
  · rintro ⟨-, hd⟩
    exact dvd_of_sq_dvd_sq_mul hb ha (hab ▸ hd)
  · intro hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hb)
    have hdb : d ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hd
    have hbn : b ≤ n := by
      rw [← hab]
      have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
      calc b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
        _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ ha0
    refine ⟨⟨hd0, by omega⟩, ?_⟩
    rw [← hab]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd 2) a

/-- The squarefree indicator: for `1 ≤ n ≤ N`,
`[n squarefree] = ∑_{d ∈ [1, N], d² ∣ n} μ(d)`. -/
lemma squarefree_indicator_eq_sum {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (if Squarefree n then 1 else 0 : ℤ) =
      ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) := by
  have hn : n ≠ 0 := by omega
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  rw [filter_sq_dvd_eq_divisors hnN hab ha hn, sum_moebius_divisors]
  have hiff : Squarefree n ↔ b = 1 := by
    constructor
    · intro hsq
      have hbb : b * b ∣ n := ⟨a, by rw [← hab]; ring⟩
      exact Nat.isUnit_iff.mp (hsq b hbb)
    · rintro rfl
      simpa [← hab] using ha
  simp only [hiff]

/-- `Q(N) = ∑_{d ∈ [1, N]} μ(d) ⌊N/d²⌋` (in `ℤ`). -/
lemma card_squarefree_eq_sum (N : ℕ) :
    (((Icc 1 N).filter Squarefree).card : ℤ) = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
  calc (((Icc 1 N).filter Squarefree).card : ℤ)
      = ∑ n ∈ Icc 1 N, (if Squarefree n then 1 else 0 : ℤ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) := by
        refine sum_congr rfl fun n hn => ?_
        rw [mem_Icc] at hn
        exact squarefree_indicator_eq_sum hn.1 hn.2
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if d ^ 2 ∣ n then (μ d : ℤ) else 0) := by
        simp_rw [sum_filter]
        exact sum_comm
    _ = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
        refine sum_congr rfl fun d _ => ?_
        have hI : Icc 1 N = Ioc 0 N := by
          ext m
          simp only [mem_Icc, mem_Ioc]
          omega
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, hI,
          Nat.Ioc_filter_dvd_card_eq_div]

/-- Tail bound: `|6/π² - ∑_{d ≤ K} μ(d)/d²| ≤ 2/(K + 1)`. -/
lemma abs_sub_partial_sum_le (K : ℕ) :
    |6 / Real.pi ^ 2 - ∑ d ∈ range (K + 1), (μ d : ℝ) / (d : ℝ) ^ 2| ≤ 2 / ((K : ℝ) + 1) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2 with hf
  have hlim := (hasSum_moebius_div_sq.tendsto_sum_nat).sub_const
    (∑ d ∈ range (K + 1), f d) |>.abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop (K + 1)] with M hM
  rw [← sum_range_add_sum_Ico f hM, add_sub_cancel_left]
  have hIco : Ico (K + 1) M = Ioo K M := by
    ext m
    simp only [mem_Ico, mem_Ioo]
    omega
  rw [hIco]
  calc |∑ d ∈ Ioo K M, f d| ≤ ∑ d ∈ Ioo K M, |f d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioo K M, ((d : ℝ) ^ 2)⁻¹ := by
        refine sum_le_sum fun d _ => ?_
        rw [hf, abs_div, abs_of_nonneg (sq_nonneg (d : ℝ)), div_eq_mul_inv]
        have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have hinv : 0 ≤ ((d : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
        calc |(μ d : ℝ)| * ((d : ℝ) ^ 2)⁻¹ ≤ 1 * ((d : ℝ) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hμ hinv
          _ = ((d : ℝ) ^ 2)⁻¹ := one_mul _
    _ ≤ 2 / ((K : ℝ) + 1) := sum_Ioo_inv_sq_le K M

/-- Floor error: `|∑_{d ≤ K} μ(d) ⌊N/d²⌋ - N ∑_{d ≤ K} μ(d)/d²| ≤ K + 1`. -/
lemma abs_floor_sum_sub_le (N K : ℕ) :
    |∑ d ∈ range (K + 1), (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) -
        (N : ℝ) * ∑ d ∈ range (K + 1), (μ d : ℝ) / (d : ℝ) ^ 2| ≤ (K : ℝ) + 1 := by
  have hterm : ∀ q : ℕ, |((N / q : ℕ) : ℝ) - (N : ℝ) / q| ≤ 1 := by
    intro q
    rw [← Nat.floor_div_eq_div (K := ℝ) N q]
    have hnn : 0 ≤ (N : ℝ) / q := by positivity
    have h1 := Nat.floor_le hnn
    have h2 := Nat.sub_one_lt_floor ((N : ℝ) / q)
    rw [abs_le]
    constructor <;> linarith
  rw [mul_sum, ← sum_sub_distrib]
  calc |∑ d ∈ range (K + 1), ((μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2))|
      ≤ ∑ d ∈ range (K + 1), |(μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ range (K + 1), (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have he : (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2)
            = (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d ^ 2 : ℕ) : ℝ)) := by
          push_cast; ring
        rw [he, abs_mul]
        calc |(μ d : ℝ)| * |((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / ((d ^ 2 : ℕ) : ℝ)| ≤ 1 * 1 :=
              mul_le_mul hμ (hterm _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (K : ℝ) + 1 := by simp

/-- `Q(N) = ∑_{d ≤ ⌊√N⌋} μ(d) ⌊N/d²⌋` (in `ℝ`); terms with `d > ⌊√N⌋`
vanish because then `N < d²`. -/
lemma card_squarefree_eq_sum_range (N : ℕ) :
    (((Icc 1 N).filter Squarefree).card : ℝ) =
      ∑ d ∈ range (Nat.sqrt N + 1), (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
  set g : ℕ → ℤ := fun d => (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) with hg
  have h1 : ∑ d ∈ Icc 1 N, g d = ∑ d ∈ range (N + 1), g d := by
    refine sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
    · simp only [mem_Icc] at hd
      simp only [mem_range]
      omega
    · have hd0 : d = 0 := by
        simp only [mem_Icc, not_and, not_le] at hd
        by_contra hne
        have := hd (by omega)
        simp only [mem_range] at *
        omega
      simp [hg, hd0]
  have h2 : ∑ d ∈ range (Nat.sqrt N + 1), g d = ∑ d ∈ range (N + 1), g d := by
    refine sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
    · simp only [mem_range] at hd ⊢
      have := Nat.sqrt_le_self N
      omega
    · simp only [mem_range, not_lt] at hd
      have hlt : N < d ^ 2 := by
        rw [sq]
        exact Nat.sqrt_lt.mp (by omega)
      show (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) = 0
      rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]
  have hZ : (((Icc 1 N).filter Squarefree).card : ℤ) =
      ∑ d ∈ range (Nat.sqrt N + 1), g d := by
    rw [card_squarefree_eq_sum, h2, ← h1]
  have hR := congrArg (fun z : ℤ => (z : ℝ)) hZ
  simp only [hg, Int.cast_natCast, Int.cast_sum, Int.cast_mul] at hR
  exact hR

/-! ## Main theorem -/

/-- **Gegenbauer (1885); Hardy–Wright Theorem 333**, explicit form: for every
`N ≥ 1`, the number `Q(N)` of squarefree `n ∈ [1, N]` satisfies
`|Q(N) - (6/π²) N| ≤ 4 √N`. -/
theorem abs_card_squarefree_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(((Icc 1 N).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * N| ≤ 4 * Real.sqrt N := by
  set K := Nat.sqrt N with hK
  set T := ∑ d ∈ range (K + 1), (μ d : ℝ) / (d : ℝ) ^ 2 with hT
  have hA := abs_floor_sum_sub_le N K
  have hB := abs_sub_partial_sum_le K
  rw [card_squarefree_eq_sum_range]
  have hsqrt1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  have hKle : (K : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hKlt : Real.sqrt N < (K : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
  have htail : (N : ℝ) * |6 / Real.pi ^ 2 - T| ≤ 2 * Real.sqrt N := by
    calc (N : ℝ) * |6 / Real.pi ^ 2 - T| ≤ (N : ℝ) * (2 / ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg N)
      _ ≤ 2 * Real.sqrt N := by
          rw [mul_div_assoc', div_le_iff₀ hK1]
          have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
          have hmul := mul_le_mul_of_nonneg_left hKlt.le hs0
          linarith
  have hsplit : ∑ d ∈ range (K + 1), (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - 6 / Real.pi ^ 2 * N =
      (∑ d ∈ range (K + 1), (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) * T) -
        (N : ℝ) * (6 / Real.pi ^ 2 - T) := by ring
  rw [hsplit]
  calc _ ≤ |∑ d ∈ range (K + 1), (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) * T| +
        |(N : ℝ) * (6 / Real.pi ^ 2 - T)| := abs_sub _ _
    _ ≤ ((K : ℝ) + 1) + 2 * Real.sqrt N := by
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [abs_mul, abs_of_nonneg hN0]
        exact add_le_add hA htail
    _ ≤ 4 * Real.sqrt N := by linarith

/-- **Counting squarefree integers (Gegenbauer 1885; Hardy–Wright Thm 333).**
There is a constant `C` such that for all `N ≥ 1`,
`|#{n ≤ N : n squarefree} - 6N/π²| ≤ C √N`; i.e. `Q(N) = (6/π²) N + O(√N)`.
Witness `C = 4`. -/
theorem exists_abs_card_squarefree_sub_le :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(((Icc 1 N).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * N| ≤ C * Real.sqrt N :=
  ⟨4, abs_card_squarefree_sub_le⟩

/-! Non-vacuity: the hypothesis `1 ≤ N` is satisfiable, so the bound is a
genuine statement at `N = 1` (and every larger `N`). -/
example : |(((Icc 1 1).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * (1 : ℕ)| ≤
    4 * Real.sqrt (1 : ℕ) :=
  abs_card_squarefree_sub_le 1 le_rfl

end Erdos.SquarefreeCount
