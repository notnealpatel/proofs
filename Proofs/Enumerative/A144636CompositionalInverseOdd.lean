/-
Integrality and parity of the rescaled A144636 e.g.f.
(Peter Bala, Feb 16 2026; OEIS reversion characterization).

For the unique A∈ℚ⟦X⟧ with A(0)=0 and A+A²/2+A³/6=X, set a(n)=n! [X^n]A.
For n≥1, 6^(n-1)a(n)/n! is integral and odd iff n is a power of 2.
Existence of the inverse is proved, and the result holds for every such A.
The triangle A144633 is not reconstructed; the e.g.f. characterization
(Bala; earlier algebraic formula by Vladeta Jovovic, Jan 24 2009) defines a.
Rescaling gives y+3y²+6y³=X; modulo 2 this is y+y²=X.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A144636CompositionalInverseOdd

open Finset PowerSeries

/-! ## The integral series `y = (1/6) A(6x)` -/

/-- One step of the coefficient recursion for `y = x - 3 y^2 - 6 y^3`:
given the coefficients `g` (intended to vanish from index `n` on), returns
`[x^n] (x - 3 G^2 - 6 G^3)` with `G = Σ g i x^i`, written with explicit
antidiagonal convolutions so that it is computable. -/
def step (n : ℕ) (g : ℕ → ℤ) : ℤ :=
  (if n = 1 then 1 else 0) - 3 * ∑ p ∈ antidiagonal n, g p.1 * g p.2
    - 6 * ∑ p ∈ antidiagonal n, g p.1 * ∑ q ∈ antidiagonal p.2, g q.1 * g q.2

/-- The list `[b 0, …, b (n-1)]` of the first `n` coefficients of
`y = (1/6) A(6x)`, built by the recursion `step`. -/
def bs : ℕ → List ℤ
  | 0 => []
  | n + 1 => let l := bs n; l ++ [step n (fun i => l.getD i 0)]

/-- `b n = [x^n] y` where `y = (1/6) A(6x)` is the unique series with `y(0) = 0`
and `y + 3 y^2 + 6 y^3 = x` (see `Y_eq`); for `n ≥ 1`, `b n = 6^(n-1) a(n)/n!`
(see `conjecture`). -/
def b (n : ℕ) : ℤ := (bs (n + 1)).getD n 0

/-- Bala's printed expansion through `x^8`, followed by four further
coefficients of the same recurrence. -/
theorem b_values : (List.range 13).map b =
    [0, 1, -3, 12, -45, 108, 378, -8424, 82863, -623700, 3822390, -17816760, 37055070] := by
  decide

/-- The list `bs n` has length `n`. -/
theorem bs_length (n : ℕ) : (bs n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bs, ih]

/-- Extending `bs n` by one entry does not change earlier entries. -/
theorem getD_bs_succ {i n : ℕ} (h : i < n) : (bs (n + 1)).getD i 0 = (bs n).getD i 0 := by
  simp only [bs]
  rw [List.getD_append _ _ _ _ (by rw [bs_length]; exact h)]

/-- The `i`-th entry of `bs n` (for `i < n`) is `b i`. -/
theorem getD_bs {i n : ℕ} (h : i < n) : (bs n).getD i 0 = b i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [getD_bs_succ h', ih h']
    · rfl

/-- Recursion: `b n` is `step n` applied to the coefficients `b i`, `i < n`
(truncated to zero from index `n` on). -/
theorem b_eq_step (n : ℕ) : b n = step n (fun i => if i < n then b i else 0) := by
  have hg : (fun i => (bs n).getD i 0) = (fun i => if i < n then b i else 0) := by
    funext i
    split_ifs with h
    · exact getD_bs h
    · rw [List.getD_eq_default _ _ (by rw [bs_length]; omega)]
  show (bs n ++ [step n (fun i => (bs n).getD i 0)]).getD n 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [bs_length]), bs_length, Nat.sub_self, hg]
  rfl

/-- `step n g` is the `n`-th coefficient of `X - 3 G^2 - 6 G^3`, `G = mk g`. -/
theorem step_eq_coeff (n : ℕ) (g : ℕ → ℤ) :
    step n g = coeff n (X - C 3 * (PowerSeries.mk g) ^ 2 - C 6 * (PowerSeries.mk g) ^ 3) := by
  rw [map_sub, map_sub, coeff_C_mul, coeff_C_mul]
  simp only [step, coeff_X, pow_two, pow_three, coeff_mul, coeff_mk]

/-- `y(0) = 0`. -/
theorem b_zero : b 0 = 0 := by decide

/-- The integral series `Y = Σ b n x^n = (1/6) A(6x)` over `ℤ`. -/
def Y : ℤ⟦X⟧ := PowerSeries.mk b

/-- The `n`-th coefficient of `3 Y^2 + 6 Y^3` only depends on the coefficients
of `Y` below `n` (using `Y(0) = 0`). -/
theorem coeff_truncation_eq (n : ℕ) :
    coeff n (C 3 * Y ^ 2 + C 6 * Y ^ 3) =
      coeff n (C 3 * (PowerSeries.mk fun i => if i < n then b i else 0) ^ 2
        + C 6 * (PowerSeries.mk fun i => if i < n then b i else 0) ^ 3) := by
  set P : ℤ⟦X⟧ := PowerSeries.mk fun i => if i < n then b i else 0 with hP
  have hdiff : X ^ n ∣ Y - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [Y, hP, hm]
  have hY0 : constantCoeff Y = 0 := by simp [Y, ← coeff_zero_eq_constantCoeff_apply, b_zero]
  have hP0 : constantCoeff P = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hP, ← coeff_zero_eq_constantCoeff_apply]
    · simp [hP, ← coeff_zero_eq_constantCoeff_apply, hn, b_zero]
  have hsum : X ∣ Y + P := by rw [X_dvd_iff]; simp [hY0, hP0]
  have hsq : X ∣ Y ^ 2 + Y * P + P ^ 2 := by rw [X_dvd_iff]; simp [hY0, hP0]
  obtain ⟨T, hT⟩ := hdiff
  obtain ⟨U, hU⟩ := hsum
  obtain ⟨V, hV⟩ := hsq
  have key : C 3 * Y ^ 2 + C 6 * Y ^ 3 - (C 3 * P ^ 2 + C 6 * P ^ 3) =
      X ^ (n + 1) * (T * (C 3 * U + C 6 * V)) := by
    have e1 : C 3 * Y ^ 2 + C 6 * Y ^ 3 - (C 3 * P ^ 2 + C 6 * P ^ 3) =
        (Y - P) * (C 3 * (Y + P) + C 6 * (Y ^ 2 + Y * P + P ^ 2)) := by ring
    rw [e1, hT, hU, hV]; ring
  have hz : coeff n (C 3 * Y ^ 2 + C 6 * Y ^ 3 - (C 3 * P ^ 2 + C 6 * P ^ 3)) = 0 := by
    rw [key]
    exact (X_pow_dvd_iff.mp (dvd_mul_right _ _)) n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **Integrality (Bala).** `Y = Σ b n x^n ∈ ℤ⟦X⟧` satisfies `Y + 3Y^2 + 6Y^3 = X`. -/
theorem Y_eq : Y + C 3 * Y ^ 2 + C 6 * Y ^ 3 = X := by
  ext n
  have h1 : coeff n Y = coeff n X - coeff n (C 3 * Y ^ 2 + C 6 * Y ^ 3) := by
    rw [coeff_truncation_eq n, ← map_sub]
    simp only [Y, coeff_mk]
    rw [b_eq_step, step_eq_coeff]
    congr 1
    ring
  rw [add_assoc, map_add, h1]
  ring

/-- Characteristic-2 squaring: `[x^n] G^2 = [n even] (g (n/2))^2` over `ZMod 2`,
written as an antidiagonal convolution. -/
theorem sum_antidiagonal_mul_zmod_two (g : ℕ → ZMod 2) (n : ℕ) :
    ∑ p ∈ antidiagonal n, g p.1 * g p.2 = if Even n then g (n / 2) ^ 2 else 0 := by
  rw [← sum_filter_add_sum_filter_not (antidiagonal n) (fun p => p.1 = p.2)]
  have hoff : ∑ p ∈ (antidiagonal n).filter (fun p => ¬ p.1 = p.2), g p.1 * g p.2 = 0 := by
    refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      rw [Prod.fst_swap, Prod.snd_swap, mul_comm (g p.2), CharTwo.add_self_eq_zero]
    · intro p hp _
      rw [mem_filter] at hp
      intro h
      exact hp.2 (congrArg Prod.snd h)
    · intro p hp
      rw [mem_filter, HasAntidiagonal.mem_antidiagonal] at hp ⊢
      rw [Prod.fst_swap, Prod.snd_swap]
      exact ⟨by omega, fun h => hp.2 h.symm⟩
    · intro p _
      exact Prod.swap_swap p
  rw [hoff, add_zero]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hset : (antidiagonal (m + m)).filter (fun p => p.1 = p.2) = {(m, m)} := by
      ext ⟨i, j⟩
      simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, mem_singleton, Prod.mk.injEq]
      omega
    rw [hset, sum_singleton, if_pos ⟨m, rfl⟩, show (m + m) / 2 = m by omega, sq]
  · have hset : (antidiagonal (2 * m + 1)).filter (fun p => p.1 = p.2) = ∅ := by
      ext ⟨i, j⟩
      simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, Finset.notMem_empty, iff_false, not_and]
      omega
    rw [hset, sum_empty, if_neg (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩)]

/-- Every element of `ZMod 2` is idempotent. -/
theorem zmod_two_sq (x : ZMod 2) : x ^ 2 = x := by
  fin_cases x <;> rfl

/-- Parity recursion from `Y + 3Y^2 + 6Y^3 = X` mod 2:
`b n + [n even] b (n/2) ≡ [n = 1] (mod 2)`. -/
theorem parity_rec (n : ℕ) :
    (b n : ZMod 2) + (if Even n then (b (n / 2) : ZMod 2) else 0) = if n = 1 then 1 else 0 := by
  have h := congrArg (coeff n) Y_eq
  rw [map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_X, pow_two, coeff_mul] at h
  have h2 := congrArg (Int.cast : ℤ → ZMod 2) h
  push_cast at h2
  simp only [Y, coeff_mk] at h2
  rw [sum_antidiagonal_mul_zmod_two (fun i => (b i : ZMod 2)) n] at h2
  have h3 : (3 : ZMod 2) = 1 := rfl
  have h6 : (6 : ZMod 2) = 0 := rfl
  rw [h3, h6, one_mul, zero_mul, add_zero] at h2
  split_ifs at h2 ⊢ <;> simp_all

/-- `2m` is a power of two iff `m` is. -/
theorem exists_two_pow_double_iff (m : ℕ) :
    (∃ k, 2 * m = 2 ^ k) ↔ ∃ k, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by rw [pow_succ]; ring⟩

/-- Mod-2 form of the parity claim: for `n ≥ 1`, `b n ≡ 1 (mod 2)` iff `n = 2^k`. -/
theorem b_cast_eq_one_iff (n : ℕ) (hn : 1 ≤ n) :
    (b n : ZMod 2) = 1 ↔ ∃ k, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec := parity_rec n
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : 1 ≤ m := by omega
      have hne : m + m ≠ 1 := by omega
      rw [if_pos ⟨m, rfl⟩, if_neg hne, show (m + m) / 2 = m by omega] at hrec
      have hbm : (b (m + m) : ZMod 2) = b m := by
        rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]; exact hrec
      rw [hbm, ih m (by omega) hm, ← two_mul, exists_two_pow_double_iff]
    · rw [if_neg (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩), add_zero] at hrec
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [mul_zero, zero_add, if_true] at hrec
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => hrec⟩
      · rw [if_neg (by omega)] at hrec
        rw [hrec]
        constructor
        · intro h; exact absurd h zero_ne_one
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · omega
          · rw [pow_succ] at hk; omega

/-- **Parity (Bala's conjecture, in terms of `b`).** For `n ≥ 1`, `b n` is odd
iff `n` is a power of 2. -/
theorem odd_b_iff (n : ℕ) (hn : 1 ≤ n) : Odd (b n) ↔ ∃ k, n = 2 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd, b_cast_eq_one_iff n hn]

/-- `f(x) = x + x^2/2! + x^3/3!`, whose series reversion is the e.g.f. of A144636. -/
noncomputable def f : Polynomial ℚ :=
  Polynomial.X + Polynomial.C (1 / 2) * Polynomial.X ^ 2 + Polynomial.C (1 / 6) * Polynomial.X ^ 3

/-- Evaluating `f` at a power series `A`. -/
theorem aeval_f (A : ℚ⟦X⟧) : Polynomial.aeval A f = A + C (1 / 2) * A ^ 2 + C (1 / 6) * A ^ 3 := by
  simp [f]

/-- Uniqueness of the series reversion of `f`: two series with zero constant
term and `f(g) = f(h) = X` coincide. -/
theorem unique (g h : ℚ⟦X⟧) (hg0 : constantCoeff g = 0) (hh0 : constantCoeff h = 0)
    (hg : Polynomial.aeval g f = X) (hh : Polynomial.aeval h f = X) : g = h := by
  rw [aeval_f] at hg hh
  have hfac : (g - h) * (1 + C (1 / 2) * (g + h) + C (1 / 6) * (g ^ 2 + g * h + h ^ 2)) = 0 := by
    linear_combination hg - hh
  have hne : (1 + C (1 / 2) * (g + h) + C (1 / 6) * (g ^ 2 + g * h + h ^ 2) : ℚ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hg0, hh0] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne)

/-- The explicit reversion `A₀(x) = 6 y(x/6)`, built from the integral series `Y`. -/
noncomputable def A₀ : ℚ⟦X⟧ := C 6 * rescale (1 / 6) (PowerSeries.map (Int.castRingHom ℚ) Y)

/-- Coefficients of `A₀`: `[x^n] A₀ = 6 · 6^(-n) · b n`. -/
theorem coeff_A₀ (n : ℕ) : coeff n A₀ = 6 * (1 / 6) ^ n * b n := by
  simp only [A₀, coeff_C_mul, coeff_rescale, coeff_map, Y, coeff_mk, eq_intCast]
  ring

/-- `rescale` fixes constants. -/
theorem rescale_C_eq (a c : ℚ) : rescale a (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

/-- `A₀` is the series reversion of `f`: `A₀(0) = 0` and `f(A₀) = X`. -/
theorem A₀_spec : constantCoeff A₀ = 0 ∧ Polynomial.aeval A₀ f = X := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_A₀, b_zero]; simp
  · rw [aeval_f]
    have hY := congrArg (rescale (1 / 6 : ℚ)) (congrArg (PowerSeries.map (Int.castRingHom ℚ)) Y_eq)
    simp only [map_add, map_mul, map_pow, map_C, map_X, rescale_X, rescale_C_eq] at hY
    simp only [eq_intCast, Int.cast_ofNat] at hY
    set R := rescale (1 / 6 : ℚ) (PowerSeries.map (Int.castRingHom ℚ) Y) with hR
    have e1 : C (6 : ℚ) * C (1 / 6) = 1 := by rw [← map_mul]; norm_num
    have e2 : C (1 / 2 : ℚ) * C 6 ^ 2 = C 6 * C 3 := by rw [← map_pow, ← map_mul, ← map_mul]; norm_num
    have e3 : C (1 / 6 : ℚ) * C 6 ^ 3 = C 6 * C 6 := by rw [← map_pow, ← map_mul, ← map_mul]; norm_num
    rw [A₀, ← hR]
    linear_combination C 6 * hY + R ^ 2 * e2 + R ^ 3 * e3 + X * e1

/-- The series reversion of `f = x + x^2/2! + x^3/3!` exists. -/
theorem exists_compInverse : ∃ A : ℚ⟦X⟧, constantCoeff A = 0 ∧ Polynomial.aeval A f = X :=
  ⟨A₀, A₀_spec⟩

/-- `a A n = n! [x^n] A`: the sequence with e.g.f. `A`; A144636 is `a A` for `A`
the series reversion of `f`. -/
noncomputable def a (A : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n A

/-- Coefficients of the series reversion in terms of `b`. -/
theorem a_eq (A : ℚ⟦X⟧) (hA0 : constantCoeff A = 0) (hA : Polynomial.aeval A f = X) (n : ℕ) :
    a A n = (n.factorial : ℚ) * (6 * (1 / 6) ^ n * b n) := by
  rw [a, unique A A₀ hA0 A₀_spec.1 hA A₀_spec.2, coeff_A₀]

/-- The e.g.f. coefficients of the reversion of `x + x^2/2! + x^3/3!`
reproduce the first ten listed terms of A144636. -/
theorem a_values (A : ℚ⟦X⟧) (hA0 : constantCoeff A = 0) (hA : Polynomial.aeval A f = X) :
    (List.range 10).map (a A) = [0, 1, -1, 2, -5, 10, 35, -910, 11935, -134750] := by
  rw [List.map_congr_left (fun n _ => a_eq A hA0 hA n)]
  have hb := b_values
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true] at hb ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hb
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, Nat.factorial]
  norm_num

/-- For any zero-constant reversion `A` of `X+X²/2+X³/6` and `n≥1`,
`6^(n-1) a(n)/n!` is integral and odd iff `n` is a power of two. -/
theorem conjecture (A : ℚ⟦X⟧) (hA0 : constantCoeff A = 0) (hA : Polynomial.aeval A f = X)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℤ, (m : ℚ) = 6 ^ (n - 1) * a A n / n.factorial ∧ (Odd m ↔ ∃ k, n = 2 ^ k) := by
  refine ⟨b n, ?_, odd_b_iff n hn⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a_eq A hA0 hA, Nat.add_sub_cancel]
  have hfac : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  have h6 : (6 : ℚ) ^ k * (6 * (1 / 6) ^ (k + 1)) = 1 := by
    rw [one_div, inv_pow, pow_succ]
    field_simp
  linear_combination (-(b (k + 1) : ℚ)) * h6

/-- Bala's equivalent form: `y = A(6x)/6` has integer coefficients `b n` and
satisfies `y + 3y^2 + 6y^3 = x`; precisely `rescale 6 A = 6 · Y` with `Y ∈ ℤ⟦X⟧`. -/
theorem rescale_six_eq (A : ℚ⟦X⟧) (hA0 : constantCoeff A = 0) (hA : Polynomial.aeval A f = X) :
    rescale 6 A = C 6 * PowerSeries.map (Int.castRingHom ℚ) Y := by
  rw [unique A A₀ hA0 A₀_spec.1 hA A₀_spec.2]
  ext n
  rw [coeff_rescale, coeff_A₀, coeff_C_mul, coeff_map]
  simp only [Y, coeff_mk, eq_intCast]
  rw [one_div, inv_pow]
  field_simp

end Candidates.A144636CompositionalInverseOdd
