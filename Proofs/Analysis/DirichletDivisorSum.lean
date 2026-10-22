/-
# Dirichlet's divisor-sum estimate

For every natural `N ≥ 1`,
`|∑_{n=1}^N d(n) - N log N - (2γ-1)N| ≤ 8√N`,
where `γ` is the Euler–Mascheroni constant.

References: P. G. L. Dirichlet, "Über die Bestimmung der mittleren Werte in
der Zahlentheorie" (1849); Hardy and Wright, *An Introduction to the Theory
of Numbers*, Theorem 320; Apostol, *Introduction to Analytic Number Theory*,
Theorem 3.3. This is the classical `O(√N)` estimate, not an optimal-exponent
solution of the Dirichlet divisor problem.

With `s = ⌊√N⌋`, the hyperbola identity is
`∑_{n≤N} d(n) + s² = 2∑_{a≤s} ⌊N/a⌋`. Removing floors, bounding
`H_s-log s-γ` by `1/s`, and comparing `log N` with `2 log s` give the
explicit error bound.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.DirichletDivisorSum

open Finset Real

/-! ## Examples

No new definitions are introduced: `d(n)` is Mathlib's `n.divisors.card`
(equal to `ArithmeticFunction.sigma 0 n` by `ArithmeticFunction.sigma_zero_apply`),
`γ` is `Real.eulerMascheroniConstant`, and `H_s` is Mathlib's `harmonic s`. -/

/-- `d(1) + ⋯ + d(10) = 1+2+2+3+2+4+2+4+3+4 = 27`. -/
example : ∑ n ∈ Icc 1 10, n.divisors.card = 27 := by decide

/-- The hyperbola identity at `N = 10`, `s = 3`: `27 + 9 = 2 (10 + 5 + 3)`. -/
example : ∑ n ∈ Icc 1 10, n.divisors.card + Nat.sqrt 10 * Nat.sqrt 10
    = 2 * ∑ a ∈ Icc 1 (Nat.sqrt 10), 10 / a := by
  have h3 : Nat.sqrt 10 = 3 := (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm
  rw [h3]
  decide

/-! ## Step 1: the hyperbola identity -/

/-- The number of lattice points `(a, b)` with `1 ≤ a ≤ c`, `1 ≤ b ≤ N`, and
`a b ≤ N` equals `∑_{a = 1}^{c} ⌊N / a⌋`. -/
theorem card_filter_mul_le (N c : ℕ) :
    ((Icc 1 c ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)).card
      = ∑ a ∈ Icc 1 c, N / a := by
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun a ha => ?_)
  have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
  rw [← card_filter]
  have hset : (Icc 1 N).filter (fun b => a * b ≤ N) = Icc 1 (N / a) := by
    ext b
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega)]
    constructor
    · rintro ⟨⟨hb1, _⟩, hab⟩
      exact ⟨hb1, by rw [mul_comm]; exact hab⟩
    · rintro ⟨hb1, hba⟩
      refine ⟨⟨hb1, ?_⟩, by rw [mul_comm]; exact hba⟩
      calc b ≤ b * a := Nat.le_mul_of_pos_right b (by omega)
        _ ≤ N := hba
  rw [hset, Nat.card_Icc]
  exact Nat.add_sub_cancel _ _

/-- **Dirichlet's hyperbola identity.**  With `s = ⌊√N⌋`,
`∑_{n = 1}^{N} d(n) + s² = 2 ∑_{a = 1}^{s} ⌊N / a⌋`. -/
theorem sum_card_divisors_add_sqrt_mul_sqrt (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card + N.sqrt * N.sqrt
      = 2 * ∑ a ∈ Icc 1 N.sqrt, N / a := by
  set s := N.sqrt with hs
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hsle : s ≤ N := by nlinarith
  have hD : ∑ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, N / a := by
    have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N
    simp only [ArithmeticFunction.sigma_zero_apply] at h
    have hI : Ioc 0 N = Icc 1 N := by ext x; simp only [mem_Ioc, mem_Icc]; omega
    rw [hI] at h
    exact h
  let A := (Icc 1 s ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  let B := (Icc 1 N ×ˢ Icc 1 s).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  let P := (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  have hA : A.card = ∑ a ∈ Icc 1 s, N / a := card_filter_mul_le N s
  have hP : P.card = ∑ a ∈ Icc 1 N, N / a := card_filter_mul_le N N
  have hB : B.card = A.card := by
    refine card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [B, A, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hp ⊢
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [mul_comm]; exact hp.2⟩
    · intro p hp
      simp only [B, A, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hp ⊢
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [mul_comm]; exact hp.2⟩
    · intro p _; simp
    · intro p _; simp
  have hU : A ∪ B = P := by
    ext ⟨a, b⟩
    simp only [A, B, P, mem_union, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro (⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ | ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩)
      · exact ⟨⟨⟨h1, by omega⟩, h3, h4⟩, h5⟩
      · exact ⟨⟨⟨h1, h2⟩, h3, by omega⟩, h5⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      by_cases ha : a ≤ s
      · exact Or.inl ⟨⟨⟨h1, ha⟩, h3, h4⟩, h5⟩
      · by_cases hb : b ≤ s
        · exact Or.inr ⟨⟨⟨h1, h2⟩, h3, hb⟩, h5⟩
        · exfalso
          have : (s + 1) * (s + 1) ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
          omega
  have hI : A ∩ B = Icc 1 s ×ˢ Icc 1 s := by
    ext ⟨a, b⟩
    simp only [A, B, mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, _, _⟩, _⟩, ⟨⟨_, _⟩, h3, h4⟩, _⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have hab : a * b ≤ N := le_trans (Nat.mul_le_mul h2 h4) hsN
      exact ⟨⟨⟨⟨h1, h2⟩, h3, by omega⟩, hab⟩, ⟨⟨h1, by omega⟩, h3, h4⟩, hab⟩
  have hcard := card_union_add_card_inter A B
  rw [hU, hI, card_product, Nat.card_Icc, hB, hA, hP] at hcard
  rw [hD]
  simp only [Nat.add_sub_cancel] at hcard
  omega

/-! ## Step 2: removing the floors -/

/-- For every `s`, `N H_s - s ≤ ∑_{a = 1}^{s} ⌊N / a⌋ ≤ N H_s`, where
`H_s = ∑_{a = 1}^{s} 1 / a` is the harmonic number. -/
theorem floor_sum_bounds (N s : ℕ) :
    (N : ℝ) * (harmonic s : ℝ) - s ≤ ∑ a ∈ Icc 1 s, ((N / a : ℕ) : ℝ) ∧
      ∑ a ∈ Icc 1 s, ((N / a : ℕ) : ℝ) ≤ (N : ℝ) * (harmonic s : ℝ) := by
  have hH : (N : ℝ) * (harmonic s : ℝ) = ∑ a ∈ Icc 1 s, (N : ℝ) / a := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    rfl
  rw [hH]
  constructor
  · have hcs : (s : ℝ) = ∑ a ∈ Icc 1 s, (1 : ℝ) := by simp
    rw [hcs, ← sum_sub_distrib]
    refine sum_le_sum (fun a ha => ?_)
    have ha1 : 0 < a := by have := (mem_Icc.mp ha).1; omega
    have hlt : N < a * (N / a + 1) := Nat.lt_mul_div_succ N ha1
    have hlt' : (N : ℝ) < a * (((N / a : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
    rw [sub_le_iff_le_add, div_le_iff₀ hapos]
    linarith
  · exact sum_le_sum (fun a _ => Nat.cast_div_le)

/-! ## Step 3: the Euler–Mascheroni sandwich -/

/-- For `s ≥ 1`, `0 < H_s - log s - γ` and `s (H_s - log s - γ) ≤ 1`,
i.e. `H_s - log s - γ ∈ (0, 1 / s]`. -/
theorem harmonic_sub_log_sub_gamma_bounds (s : ℕ) (hs : 1 ≤ s) :
    0 < (harmonic s : ℝ) - log s - eulerMascheroniConstant ∧
      (s : ℝ) * ((harmonic s : ℝ) - log s - eulerMascheroniConstant) ≤ 1 := by
  have hs0 : s ≠ 0 := by omega
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
  have hup := eulerMascheroniConstant_lt_eulerMascheroniSeq' s
  have hlo := eulerMascheroniSeq_lt_eulerMascheroniConstant s
  simp only [eulerMascheroniSeq', hs0, if_false] at hup
  simp only [eulerMascheroniSeq] at hlo
  refine ⟨by linarith, ?_⟩
  have hlog : log ((s : ℝ) + 1) - log s ≤ 1 / s := by
    rw [← log_div (by positivity) hspos.ne']
    have h := log_le_sub_one_of_pos (x := ((s : ℝ) + 1) / s) (by positivity)
    have he : ((s : ℝ) + 1) / s - 1 = 1 / s := by field_simp; ring
    linarith
  have hlog' : (s : ℝ) * (log ((s : ℝ) + 1) - log s) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlog hspos.le
    rwa [mul_one_div_cancel hspos.ne'] at this
  nlinarith

/-! ## Step 4: `log N` versus `2 log ⌊√N⌋` -/

/-- For `N ≥ 1` and `s = ⌊√N⌋`, `0 ≤ log N - 2 log s` and
`s (log N - 2 log s) ≤ 2`, i.e. `log N - 2 log s ∈ [0, 2 / s]`. -/
theorem log_sub_two_log_sqrt_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ log N - 2 * log (N.sqrt : ℝ) ∧
      (N.sqrt : ℝ) * (log N - 2 * log (N.sqrt : ℝ)) ≤ 2 := by
  set s := N.sqrt with hs
  have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hsN' : (s : ℝ) * s ≤ N := by exact_mod_cast hsN
  have hNs' : (N : ℝ) ≤ s * s + 2 * s := by
    have : N ≤ s * s + 2 * s := by nlinarith
    exact_mod_cast this
  have hss : (0 : ℝ) < s * s := by positivity
  have heq : log N - 2 * log (s : ℝ) = log (N / (s * s)) := by
    rw [log_div (by positivity) hss.ne', log_mul hspos.ne' hspos.ne']
    ring
  rw [heq]
  constructor
  · apply log_nonneg
    rw [le_div_iff₀ hss]
    linarith
  · have h := log_le_sub_one_of_pos (x := (N : ℝ) / (s * s)) (by positivity)
    have h2 : (N : ℝ) / (s * s) - 1 ≤ 2 / s := by
      rw [div_sub_one hss.ne', div_le_div_iff₀ hss hspos]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left (h.trans h2) hspos.le
    rwa [mul_div_cancel₀ (2 : ℝ) hspos.ne'] at h3

/-! ## Main theorem -/

/-- **Dirichlet's divisor theorem with explicit constant.**  For every `N ≥ 1`,
`|∑_{n = 1}^{N} d(n) - (N log N + (2γ - 1) N)| ≤ 8 √N`,
where `d(n)` is the number of divisors of `n` and `γ` is the
Euler–Mascheroni constant. -/
theorem abs_sum_card_divisors_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)
        - (N * log N + (2 * eulerMascheroniConstant - 1) * N)| ≤ 8 * √(N : ℝ) := by
  set s := N.sqrt with hs
  have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hsN' : (s : ℝ) * s ≤ N := by exact_mod_cast hsN
  have hNs' : (N : ℝ) ≤ s * s + 2 * s := by
    have : N ≤ s * s + 2 * s := by nlinarith
    exact_mod_cast this
  have hsqrt : (s : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  -- the hyperbola identity, cast to ℝ
  have hD : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)
      = 2 * ∑ a ∈ Icc 1 s, ((N / a : ℕ) : ℝ) - (s : ℝ) * s := by
    have h := sum_card_divisors_add_sqrt_mul_sqrt N
    rw [← hs] at h
    have h' : ((∑ n ∈ Icc 1 N, n.divisors.card + s * s : ℕ) : ℝ)
        = ((2 * ∑ a ∈ Icc 1 s, N / a : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  obtain ⟨hS1, hS2⟩ := floor_sum_bounds N s
  obtain ⟨hε0, hε1⟩ := harmonic_sub_log_sub_gamma_bounds s hs1
  obtain ⟨hδ0, hδ1⟩ := log_sub_two_log_sqrt_bounds N hN
  rw [← hs] at hδ0 hδ1
  set S := ∑ a ∈ Icc 1 s, ((N / a : ℕ) : ℝ)
  set H := (harmonic s : ℝ)
  set γ := eulerMascheroniConstant
  set ε := H - log s - γ with hε
  set δ := log N - 2 * log (s : ℝ) with hδ
  have hNε : (N : ℝ) * ε ≤ s + 2 := by
    calc (N : ℝ) * ε ≤ (s * s + 2 * s) * ε := mul_le_mul_of_nonneg_right hNs' hε0.le
      _ = (s + 2) * (s * ε) := by ring
      _ ≤ (s + 2) * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
      _ = s + 2 := by ring
  have hNδ : (N : ℝ) * δ ≤ 2 * (s + 2) := by
    calc (N : ℝ) * δ ≤ (s * s + 2 * s) * δ := mul_le_mul_of_nonneg_right hNs' hδ0
      _ = (s + 2) * (s * δ) := by ring
      _ ≤ (s + 2) * 2 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = 2 * (s + 2) := by ring
  have hNε0 : 0 ≤ (N : ℝ) * ε := mul_nonneg (by positivity) hε0.le
  have hNδ0 : 0 ≤ (N : ℝ) * δ := mul_nonneg (by positivity) hδ0
  have hlogN : log (N : ℝ) = 2 * log (s : ℝ) + δ := by rw [hδ]; ring
  have hHe : H = log s + γ + ε := by rw [hε]; ring
  have hE : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)
      - (N * log N + (2 * γ - 1) * N)
      = 2 * (S - N * H) + 2 * (N * ε) - N * δ + (N - s * s) := by
    rw [hD, hlogN, hHe]; ring
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  rw [hE, abs_le]
  constructor <;> linarith

/-- **Dirichlet divisor problem (1849), `O(√N)` form.**  There is a constant `C`
such that for all `N ≥ 1`,
`|∑_{n = 1}^{N} d(n) - N log N - (2γ - 1) N| ≤ C √N`,
where `d(n)` is the number of divisors of `n` and `γ` is the
Euler–Mascheroni constant.  (One may take `C = 8`.) -/
theorem sum_card_divisors_asymp : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)
      - (N * log N + (2 * eulerMascheroniConstant - 1) * N)| ≤ C * √(N : ℝ) :=
  ⟨8, abs_sum_card_divisors_sub_le⟩

end Candidates.DirichletDivisorSum
