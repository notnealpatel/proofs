/-
# A295458 — Bala: both `a(n/2)` and `a(n/3)` are integers

Peter Bala's conjecture in OEIS A295458 (July 29, 2026) asserts that
both `a(n/2)` and `a(n/3)` are integers for every natural `n`, where
`a(n) = (30n)! (5n)! (4n)! / ((15n)! (10n)! (8n)! (6n)!)`
and fractional factorials mean `x! = Γ(x+1)`.

* Half index, odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k` gives
  `a(n/2) = 2^(10n) ⌊15n/2⌋! (2n)! / (⌊5n/2⌋! (4n)! (3n)!)`, and Landau's
  criterion (step `⌊5x/2⌋ + ⌊4x⌋ + ⌊3x⌋ ≤ ⌊15x/2⌋ + ⌊2x⌋`, period check in
  `j = ⌊60x⌋`) shows the factorial quotient is already integral.
* Third index, every `n`: pairing `Γ(8n/3 + 1) = Γ(5n/3 + 1) ∏_{i<n} (5n/3 + 1 + i)`
  and `Γ(10n/3 + 1) = Γ(4n/3 + 1) ∏_{i<2n} (4n/3 + 1 + i)` gives
  `a(n/3) = 3^(3n) (10n)! / ((5n)! (2n)! ∏_{i<n} (5n + 3(i+1)) ∏_{i<2n} (4n + 3(i+1)))`.
  For `3 ∤ n` and a prime power `q = p^k` with `p ≠ 3`, the quotients of the
  multiples of `q` in each progression lie in a fixed residue class mod `3`
  (classes `3 - s` and `s` with `s ≡ nq (mod 3)`), and an exact residue count
  reduces the claim to a step inequality checked over one period `j < 120`
  of `j = ⌊40x⌋`, for both `s ∈ {1, 2}`. The power `3^(3n)` is not needed.
* `n = 2m` and `n = 3m`: the ratios equal `a(m)` (`halfRatio_two_mul`,
  `thirdRatio_three_mul`).
-/
import Mathlib
import Combinatorics.A295431BalaGamma
import Combinatorics.A295470Bala
import Combinatorics.A295437BalaJunBoth

set_option autoImplicit false

namespace Candidates.A295458BalaBoth

open Finset
open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)
open Candidates.A295437BalaJunBoth (apProd factorization_apProd card_eq_zero_of_dvd gamma_add_nat
  apProd_real factorial_mul_prod_succ apProd_mul_left)

/-! ## Definition layer -/

/-- The OEIS sequence A295458:
`a(n) = (30n)! (5n)! (4n)! / ((15n)! (10n)! (8n)! (6n)!)`. The truncating `Nat`
division is exact; see `a295458_mul`. -/
def a295458 (n : ℕ) : ℕ :=
  (30 * n).factorial * (5 * n).factorial * (4 * n).factorial /
    ((15 * n).factorial * (10 * n).factorial * (8 * n).factorial * (6 * n).factorial)

/-- Bala's half-index value
`a(n/2) = (15n)! (5n/2)! (2n)! / ((15n/2)! (5n)! (4n)! (3n)!)`, with
`x! := Γ(x + 1)`. The denominator is positive (`halfRatio_denom_pos`), so the
real division never takes its junk value. -/
noncomputable def halfRatio (n : ℕ) : ℝ :=
  ((15 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ) /
    (Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) *
      ((3 * n).factorial : ℝ))

/-- Bala's third-index value
`a(n/3) = (10n)! (5n/3)! (4n/3)! / ((5n)! (10n/3)! (8n/3)! (2n)!)`, with
`x! := Γ(x + 1)`. The denominator is positive (`thirdRatio_denom_pos`). -/
noncomputable def thirdRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 3 + 1) * Real.Gamma (4 * (n : ℝ) / 3 + 1) /
    (((5 * n).factorial : ℝ) * Real.Gamma (10 * (n : ℝ) / 3 + 1) *
      Real.Gamma (8 * (n : ℝ) / 3 + 1) * ((2 * n).factorial : ℝ))

/-- The denominator of `halfRatio n` is positive. -/
theorem halfRatio_denom_pos (n : ℕ) :
    0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) *
      ((4 * n).factorial : ℝ) * ((3 * n).factorial : ℝ) := by
  have hG : 0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- The denominator of `thirdRatio n` is positive. -/
theorem thirdRatio_denom_pos (n : ℕ) :
    0 < ((5 * n).factorial : ℝ) * Real.Gamma (10 * (n : ℝ) / 3 + 1) *
      Real.Gamma (8 * (n : ℝ) / 3 + 1) * ((2 * n).factorial : ℝ) := by
  have hG₁ : 0 < Real.Gamma (10 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG₂ : 0 < Real.Gamma (8 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The third index: exact residue counting -/

/-- A finset of naturals in `(A, B]`, all congruent to `c < 3` modulo `3`, has at
most `⌊(B + 3 - c)/3⌋ - ⌊(A + 3 - c)/3⌋` elements. -/
theorem card_le_of_mod_three (S : Finset ℕ) (A B c : ℕ) (hc : c < 3)
    (hS : ∀ y ∈ S, A < y ∧ y ≤ B ∧ y % 3 = c) :
    #S ≤ (B + 3 - c) / 3 - (A + 3 - c) / 3 := by
  have h : #S ≤ #(Ioc ((A + 3 - c) / 3) ((B + 3 - c) / 3)) := by
    apply card_le_card_of_injOn (fun y => (y + 3 - c) / 3)
    · intro y hy
      have hy' := hS y hy
      simp only [coe_Ioc, Set.mem_Ioc]
      omega
    · intro y₁ hy₁ y₂ hy₂ heq
      have h₁ := hS y₁ hy₁
      have h₂ := hS y₂ hy₂
      simp only at heq
      omega
  simpa [Nat.card_Ioc] using h

/-- Exact-residue count of the multiples of `q` in the progression `n + 3(i+1)`,
`i < L`. If every `y` with `q y ≡ n (mod 3)` satisfies `y ≡ c (mod 3)`, then the
quotients lie in `(⌊n/q⌋, ⌊(n+3L)/q⌋]` and are `≡ c (mod 3)`, so there are at
most `⌊(⌊(n+3L)/q⌋ + 3 - c)/3⌋ - ⌊(⌊n/q⌋ + 3 - c)/3⌋` of them. -/
theorem card_ap_dvd_le (n L q c : ℕ) (hq : 0 < q) (hc : c < 3)
    (hres : ∀ y, q * y % 3 = n % 3 → y % 3 = c) :
    #{i ∈ range L | q ∣ n + 3 * (i + 1)} ≤
      ((n + 3 * L) / q + 3 - c) / 3 - (n / q + 3 - c) / 3 := by
  set T := (range L).filter (fun i => q ∣ n + 3 * (i + 1)) with hT
  have hinj : Set.InjOn (fun i => (n + 3 * (i + 1)) / q) (T : Set ℕ) := by
    intro i₁ hi₁ i₂ hi₂ heq
    rw [mem_coe, hT, mem_filter] at hi₁ hi₂
    have e₁ := Nat.div_mul_cancel hi₁.2
    have e₂ := Nat.div_mul_cancel hi₂.2
    simp only at heq
    rw [heq] at e₁
    omega
  rw [← card_image_of_injOn hinj]
  apply card_le_of_mod_three _ _ _ _ hc
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
  rw [hT, mem_filter, mem_range] at hi
  obtain ⟨s, hs⟩ := hi.2
  rw [hs, Nat.mul_div_cancel_left _ hq]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hq, mul_comm s q, ← hs]
    omega
  · rw [Nat.le_div_iff_mul_le hq, mul_comm s q, ← hs]
    omega
  · exact hres s (by rw [← hs]; omega)

/-- The third-index step inequality in `j = ⌊40x⌋`, for the two residue patterns
`s ∈ {1, 2}`:
`⌊5x⌋ + ⌊2x⌋ + (⌊(⌊8x⌋+s)/3⌋ - ⌊(⌊5x⌋+s)/3⌋)
  + (⌊(⌊10x⌋+3-s)/3⌋ - ⌊(⌊4x⌋+3-s)/3⌋) ≤ ⌊10x⌋`. -/
theorem step_third (j s : ℕ) (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) :
    j / 8 + j / 20 + ((j / 5 + s) / 3 - (j / 8 + s) / 3) +
      ((j / 4 + 3 - s) / 3 - (j / 10 + 3 - s) / 3) ≤ j / 4 := by
  have key : ∀ r < 120, ∀ s < 3, 1 ≤ s →
      r / 8 + r / 20 + ((r / 5 + s) / 3 - (r / 8 + s) / 3) +
        ((r / 4 + 3 - s) / 3 - (r / 10 + 3 - s) / 3) ≤ r / 4 := by
    decide
  have hj : j = j % 120 + 120 * (j / 120) := (Nat.mod_add_div j 120).symm
  have hr := key (j % 120) (Nat.mod_lt _ (by norm_num)) s (by omega) hs₁
  generalize j % 120 = r at hj hr
  generalize j / 120 = t at hj
  subst hj
  have e₈ : (r + 120 * t) / 8 = r / 8 + 15 * t := by omega
  have e₂₀ : (r + 120 * t) / 20 = r / 20 + 6 * t := by omega
  have e₅ : (r + 120 * t) / 5 = r / 5 + 24 * t := by omega
  have e₄ : (r + 120 * t) / 4 = r / 4 + 30 * t := by omega
  have e₁₀ : (r + 120 * t) / 10 = r / 10 + 12 * t := by omega
  rw [e₈, e₂₀, e₅, e₄, e₁₀]
  have f₁ : (r / 5 + 24 * t + s) / 3 = (r / 5 + s) / 3 + 8 * t := by omega
  have f₂ : (r / 8 + 15 * t + s) / 3 = (r / 8 + s) / 3 + 5 * t := by omega
  have f₃ : (r / 4 + 30 * t + 3 - s) / 3 = (r / 4 + 3 - s) / 3 + 10 * t := by omega
  have f₄ : (r / 10 + 12 * t + 3 - s) / 3 = (r / 10 + 3 - s) / 3 + 4 * t := by omega
  rw [f₁, f₂, f₃, f₄]
  omega

/-- Landau-type criterion with two extra arithmetic-progression factors of
common difference `d`. Suppose that for every prime `p` and `k ≥ 1`,
`∑_{y ∈ bs} ⌊y/p^k⌋ + #{i < L₁ : p^k ∣ n₁ + d(i+1)} + #{i < L₂ : p^k ∣ n₂ + d(i+1)}`
is at most `∑_{x ∈ as} ⌊x/p^k⌋`. Then
`(∏_{y ∈ bs} y!) · apProd n₁ d L₁ · apProd n₂ d L₂` divides `∏_{x ∈ as} x!`. -/
theorem dvd_of_terms_two (as bs : List ℕ) (n₁ L₁ n₂ L₂ d M : ℕ) (hd : 0 < d)
    (has : ∀ x ∈ as, x ≤ M) (hbs : ∀ x ∈ bs, x ≤ M) (hL₁ : n₁ + d * L₁ ≤ M)
    (hL₂ : n₂ + d * L₂ ≤ M)
    (hterm : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      (bs.map (· / p ^ k)).sum + #{i ∈ range L₁ | p ^ k ∣ n₁ + d * (i + 1)} +
          #{i ∈ range L₂ | p ^ k ∣ n₂ + d * (i + 1)} ≤ (as.map (· / p ^ k)).sum) :
    (bs.map Nat.factorial).prod * apProd n₁ d L₁ * apProd n₂ d L₂ ∣
      (as.map Nat.factorial).prod := by
  have hne : ∀ l : List ℕ, (l.map Nat.factorial).prod ≠ 0 := fun l => by
    simp [Nat.factorial_ne_zero]
  have hpos : ∀ m i : ℕ, 0 < m + d * (i + 1) := fun m i => by positivity
  have hP : ∀ m L : ℕ, apProd m d L ≠ 0 := fun m L =>
    prod_ne_zero_iff.2 fun i _ => (hpos m i).ne'
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (mul_ne_zero (hne bs) (hP n₁ L₁)) (hP n₂ L₂))
    (hne as), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hb : ∀ x ≤ M, Nat.log p x < M + 1 := fun x hx =>
      Nat.lt_succ_of_le ((Nat.log_le_self p x).trans hx)
    have hMp : M < p ^ (M + 1) :=
      (Nat.lt_pow_self hp.one_lt).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self M))
    have hb' : ∀ m L : ℕ, m + d * L ≤ M → ∀ i < L, m + d * (i + 1) < p ^ (M + 1) :=
      fun m L hL i hi =>
        lt_of_le_of_lt ((Nat.add_le_add_left (Nat.mul_le_mul_left d hi) m).trans hL) hMp
    rw [Nat.factorization_mul (mul_ne_zero (hne bs) (hP n₁ L₁)) (hP n₂ L₂),
      Nat.factorization_mul (hne bs) (hP n₁ L₁), Finsupp.add_apply, Finsupp.add_apply,
      Candidates.A295431BalaGamma.factorization_prod_factorial hp (M + 1) bs
        fun x hx => hb x (hbs x hx),
      Candidates.A295431BalaGamma.factorization_prod_factorial hp (M + 1) as
        fun x hx => hb x (has x hx),
      factorization_apProd hp n₁ d L₁ (M + 1) (fun i _ => hpos n₁ i) (hb' n₁ L₁ hL₁),
      factorization_apProd hp n₂ d L₂ (M + 1) (fun i _ => hpos n₂ i) (hb' n₂ L₂ hL₂),
      ← sum_add_distrib, ← sum_add_distrib]
    exact sum_le_sum fun k hk => hterm p k hp (mem_Ico.1 hk).1
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- For `3 ∤ n`,
`(5n)! (2n)! ∏_{i<n} (5n + 3(i+1)) ∏_{i<2n} (4n + 3(i+1))` divides `(10n)!`. -/
theorem third_dvd (n : ℕ) (hn : ¬ 3 ∣ n) :
    (5 * n).factorial * (2 * n).factorial * apProd (5 * n) 3 n * apProd (4 * n) 3 (2 * n) ∣
      (10 * n).factorial := by
  have h5 : ¬ 3 ∣ 5 * n := fun h => hn (by omega)
  have h4 : ¬ 3 ∣ 4 * n := fun h => hn (by omega)
  have h := dvd_of_terms_two [10 * n] [5 * n, 2 * n] (5 * n) n (4 * n) (2 * n) 3 (10 * n)
    (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega) (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp3 : p = 3
      · subst hp3
        rw [card_eq_zero_of_dvd (5 * n) 3 n 3 k hk dvd_rfl h5,
          card_eq_zero_of_dvd (4 * n) 3 (2 * n) 3 k hk dvd_rfl h4, add_zero, add_zero]
        calc 5 * n / 3 ^ k + 2 * n / 3 ^ k ≤ (5 * n + 2 * n) / 3 ^ k :=
              Nat.add_div_le_add_div _ _ _
          _ ≤ 10 * n / 3 ^ k := Nat.div_le_div_right (by omega)
      · set q := p ^ k with hqdef
        have hq : 0 < q := pow_pos hp.pos k
        have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
          have hcop : Nat.Coprime q 3 :=
            Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
          have h0 : q % 3 ≠ 0 := fun h0 =>
            Nat.not_coprime_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero h0) dvd_rfl hcop
          omega
        have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by omega
        obtain ⟨s, hs₁, hs₂, hr₁, hr₂⟩ : ∃ s, 1 ≤ s ∧ s ≤ 2 ∧
            (∀ y, q * y % 3 = 5 * n % 3 → y % 3 = 3 - s) ∧
            (∀ y, q * y % 3 = 4 * n % 3 → y % 3 = s) := by
          rcases hq3 with hq3 | hq3 <;> rcases hn3 with hn3 | hn3 <;>
            first
            | exact ⟨1, le_rfl, by norm_num,
                fun y hy => by rw [Nat.mul_mod, hq3] at hy; omega,
                fun y hy => by rw [Nat.mul_mod, hq3] at hy; omega⟩
            | exact ⟨2, by norm_num, le_rfl,
                fun y hy => by rw [Nat.mul_mod, hq3] at hy; omega,
                fun y hy => by rw [Nat.mul_mod, hq3] at hy; omega⟩
        have hc₁ := card_ap_dvd_le (5 * n) n q (3 - s) hq (by omega) hr₁
        have hc₂ := card_ap_dvd_le (4 * n) (2 * n) q s hq (by omega) hr₂
        rw [show 5 * n + 3 * n = 8 * n by ring] at hc₁
        rw [show 4 * n + 3 * (2 * n) = 10 * n by ring] at hc₂
        have hs := step_third (40 * n / q) s hs₁ hs₂
        rw [div_div_eq_of_mul_eq 40 n q 5 8 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 40 n q 2 20 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 40 n q 8 5 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 40 n q 10 4 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 40 n q 4 10 1 (by norm_num) (by norm_num) (by norm_num)] at hs
        simp only [one_mul] at hs
        omega)
  simpa [mul_assoc] using h

/-! ## The half index -/

set_option maxRecDepth 20000 in
/-- The odd-case step inequality in `j = ⌊60x⌋`:
`⌊j/24⌋ + ⌊j/15⌋ + ⌊j/20⌋ ≤ ⌊j/8⌋ + ⌊j/30⌋`, i.e.
`⌊5x/2⌋ + ⌊4x⌋ + ⌊3x⌋ ≤ ⌊15x/2⌋ + ⌊2x⌋`. -/
theorem step_half_odd (j : ℕ) : j / 24 + j / 15 + j / 20 ≤ j / 8 + j / 30 := by
  have h := Candidates.A295470Bala.step_of_period 120 (by norm_num) [8, 30] [24, 15, 20]
    (by decide) (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

set_option maxRecDepth 20000 in
/-- The step inequality of A295458 itself in `j = ⌊120y⌋`:
`⌊j/8⌋ + ⌊j/12⌋ + ⌊j/15⌋ + ⌊j/20⌋ ≤ ⌊j/4⌋ + ⌊j/24⌋ + ⌊j/30⌋`, i.e.
`⌊15y⌋ + ⌊10y⌋ + ⌊8y⌋ + ⌊6y⌋ ≤ ⌊30y⌋ + ⌊5y⌋ + ⌊4y⌋`. -/
theorem step_a (j : ℕ) : j / 8 + j / 12 + j / 15 + j / 20 ≤ j / 4 + j / 24 + j / 30 := by
  have h := Candidates.A295470Bala.step_of_period 120 (by norm_num) [4, 24, 30]
    [8, 12, 15, 20] (by decide) (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊⌊5n/2⌋/q⌋ + ⌊4n/q⌋ + ⌊3n/q⌋ ≤ ⌊⌊15n/2⌋/q⌋ + ⌊2n/q⌋`. -/
theorem term_half_odd (n q : ℕ) :
    5 * n / 2 / q + 4 * n / q + 3 * n / q ≤ 15 * n / 2 / q + 2 * n / q := by
  have h := step_half_odd (60 * n / q)
  rw [div_div_eq_of_mul_eq 60 n q 5 24 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 4 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 3 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 15 8 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 2 30 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The Landau term inequality of A295458, valid for every `m` and `q`:
`⌊15m/q⌋ + ⌊10m/q⌋ + ⌊8m/q⌋ + ⌊6m/q⌋ ≤ ⌊30m/q⌋ + ⌊5m/q⌋ + ⌊4m/q⌋`. -/
theorem term_a (m q : ℕ) :
    15 * m / q + 10 * m / q + 8 * m / q + 6 * m / q ≤ 30 * m / q + 5 * m / q + 4 * m / q := by
  have h := step_a (120 * m / q)
  rw [div_div_eq_of_mul_eq 120 m q 15 8 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 10 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 8 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 6 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 30 4 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 5 24 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 4 30 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-- For every `n`, `⌊5n/2⌋! (4n)! (3n)!` divides `⌊15n/2⌋! (2n)!`. For odd `n`
this is stronger than needed: the factor `2^(10n)` of Bala's ratio is not used. -/
theorem factorial_dvd_half_odd_form (n : ℕ) :
    (5 * n / 2).factorial * (4 * n).factorial * (3 * n).factorial ∣
      (15 * n / 2).factorial * (2 * n).factorial := by
  have h := landau_list [15 * n / 2, 2 * n] [5 * n / 2, 4 * n, 3 * n] (15 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_half_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295458: `(15m)! (10m)! (8m)! (6m)!` divides `(30m)! (5m)! (4m)!`. -/
theorem factorial_dvd_a295458 (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (8 * m).factorial * (6 * m).factorial ∣
      (30 * m).factorial * (5 * m).factorial * (4 * m).factorial := by
  have h := landau_list [30 * m, 5 * m, 4 * m] [15 * m, 10 * m, 8 * m, 6 * m] (30 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_a m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295458`. -/
theorem a295458_mul (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (8 * m).factorial * (6 * m).factorial *
        a295458 m = (30 * m).factorial * (5 * m).factorial * (4 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295458 m)

/-- For odd `n`, suppose `⌊15n/2⌋! (2n)! = ⌊5n/2⌋! (4n)! (3n)! c`. Then the
half-index ratio equals `2^(10n) c`. -/
theorem halfRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (15 * n / 2).factorial * (2 * n).factorial =
      (5 * n / 2).factorial * (4 * n).factorial * (3 * n).factorial * c) :
    halfRatio n = 2 ^ (10 * n) * (c : ℝ) := by
  have h5 : 5 * (n : ℝ) = ((5 * n : ℕ) : ℝ) := by push_cast; ring
  have h15 : 15 * (n : ℝ) = ((15 * n : ℕ) : ℝ) := by push_cast; ring
  have hG5 := gamma_half_of_odd (Odd.mul (by decide : Odd 5) hn)
  have hG15 := gamma_half_of_odd (Odd.mul (by decide : Odd 15) hn)
  have hcR : ((15 * n / 2).factorial : ℝ) * (2 * n).factorial =
      (5 * n / 2).factorial * (4 * n).factorial * (3 * n).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos5 : (0 : ℝ) < (5 * n / 2).factorial := by positivity
  have hpos15 : (0 : ℝ) < (15 * n / 2).factorial := by positivity
  unfold halfRatio
  rw [h5, h15, hG5, hG15]
  field_simp
  linear_combination (2 ^ (15 * n) : ℝ) * hcR

/-- For even `n = 2m`, the half-index ratio is the sequence term `a(m)`. -/
theorem halfRatio_two_mul (m : ℕ) : halfRatio (2 * m) = (a295458 m : ℝ) := by
  have hG5 : Real.Gamma (5 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((5 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG15 : Real.Gamma (15 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((15 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((15 * m).factorial * (10 * m).factorial * (8 * m).factorial *
      (6 * m).factorial * a295458 m : ℕ) : ℝ) =
      (((30 * m).factorial * (5 * m).factorial * (4 * m).factorial : ℕ) : ℝ) := by
    rw [a295458_mul]
  push_cast at hmul
  unfold halfRatio
  rw [hG5, hG15, show 15 * (2 * m) = 30 * m by ring, show 2 * (2 * m) = 4 * m by ring,
    show 5 * (2 * m) = 10 * m by ring, show 4 * (2 * m) = 8 * m by ring,
    show 3 * (2 * m) = 6 * m by ring]
  have h15 : (0 : ℝ) < (15 * m).factorial := by positivity
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h8 : (0 : ℝ) < (8 * m).factorial := by positivity
  have h6 : (0 : ℝ) < (6 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-- The half-index ratio `a(n/2)` is a natural number for every `n`. -/
theorem halfRatio_integral (n : ℕ) : ∃ k : ℕ, halfRatio n = k := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · exact ⟨a295458 m, by rw [← two_mul, halfRatio_two_mul]⟩
  · obtain ⟨c, hc⟩ := factorial_dvd_half_odd_form n
    refine ⟨2 ^ (10 * n) * c, ?_⟩
    rw [halfRatio_of_odd hn hc]
    push_cast
    ring

/-! ## The third index: Gamma bridge -/

/-- The Gamma bridge for the third index. Suppose
`3^(3n) (10n)! = (5n)! (2n)! ∏_{i<n} (5n + 3(i+1)) ∏_{i<2n} (4n + 3(i+1)) · c`.
Then `a(n/3) = c`. It uses `Γ(8n/3 + 1) = Γ(5n/3 + 1) ∏_{i<n} (5n/3 + 1 + i)` and
`Γ(10n/3 + 1) = Γ(4n/3 + 1) ∏_{i<2n} (4n/3 + 1 + i)`. -/
theorem thirdRatio_eq {n c : ℕ}
    (hc : 3 ^ (3 * n) * (10 * n).factorial =
      (5 * n).factorial * (2 * n).factorial * apProd (5 * n) 3 n * apProd (4 * n) 3 (2 * n) * c) :
    thirdRatio n = c := by
  set Q₁ := ∏ i ∈ range n, (5 * (n : ℝ) / 3 + 1 + i) with hQ₁
  set Q₂ := ∏ i ∈ range (2 * n), (4 * (n : ℝ) / 3 + 1 + i) with hQ₂
  have hQ₁pos : 0 < Q₁ := prod_pos fun i _ => by positivity
  have hQ₂pos : 0 < Q₂ := prod_pos fun i _ => by positivity
  have hΓ₈ : Real.Gamma (8 * (n : ℝ) / 3 + 1) = Real.Gamma (5 * (n : ℝ) / 3 + 1) * Q₁ := by
    rw [show 8 * (n : ℝ) / 3 + 1 = (5 * (n : ℝ) / 3 + 1) + (n : ℝ) by ring,
      gamma_add_nat _ (by positivity)]
  have hΓ₁₀ : Real.Gamma (10 * (n : ℝ) / 3 + 1) = Real.Gamma (4 * (n : ℝ) / 3 + 1) * Q₂ := by
    rw [show 10 * (n : ℝ) / 3 + 1 = (4 * (n : ℝ) / 3 + 1) + ((2 * n : ℕ) : ℝ) by
        push_cast; ring,
      gamma_add_nat _ (by positivity)]
  have hP₁ : (apProd (5 * n) 3 n : ℝ) = 3 ^ n * Q₁ := by
    rw [apProd_real (5 * n) 3 n (by norm_num)]
    push_cast
    rfl
  have hP₂ : (apProd (4 * n) 3 (2 * n) : ℝ) = 3 ^ (2 * n) * Q₂ := by
    rw [apProd_real (4 * n) 3 (2 * n) (by norm_num)]
    push_cast
    rfl
  have hcR : (3 : ℝ) ^ (3 * n) * ((10 * n).factorial : ℝ) =
      ((5 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * (apProd (5 * n) 3 n : ℝ) *
        (apProd (4 * n) 3 (2 * n) : ℝ) * c := by
    exact_mod_cast hc
  rw [hP₁, hP₂] at hcR
  have key : ((10 * n).factorial : ℝ) =
      c * Q₁ * Q₂ * (5 * n).factorial * (2 * n).factorial := by
    have h3 : (3 : ℝ) ^ (3 * n) ≠ 0 := by positivity
    apply mul_left_cancel₀ h3
    linear_combination hcR
  have hG₅ : 0 < Real.Gamma (5 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG₄ : 0 < Real.Gamma (4 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold thirdRatio
  rw [hΓ₈, hΓ₁₀, div_eq_iff (by positivity), key]
  ring

/-- For `n = 3m`:
`3^(3n) (10n)! = (5n)! (2n)! ∏_{i<n} (5n + 3(i+1)) ∏_{i<2n} (4n + 3(i+1)) · a(m)`. -/
theorem third_three_mul_eq (m : ℕ) :
    3 ^ (3 * (3 * m)) * (10 * (3 * m)).factorial =
      (5 * (3 * m)).factorial * (2 * (3 * m)).factorial * apProd (5 * (3 * m)) 3 (3 * m) *
        apProd (4 * (3 * m)) 3 (2 * (3 * m)) * a295458 m := by
  rw [show 5 * (3 * m) = 3 * (5 * m) by ring, show 4 * (3 * m) = 3 * (4 * m) by ring,
    apProd_mul_left, apProd_mul_left, show 3 * (5 * m) = 15 * m by ring,
    show 10 * (3 * m) = 30 * m by ring, show 2 * (3 * m) = 6 * m by ring,
    show 3 * (3 * m) = 9 * m by ring]
  have hX₁ := factorial_mul_prod_succ (5 * m) (3 * m)
  have hX₂ := factorial_mul_prod_succ (4 * m) (6 * m)
  rw [show 5 * m + 3 * m = 8 * m by ring] at hX₁
  rw [show 4 * m + 6 * m = 10 * m by ring] at hX₂
  have ha := a295458_mul m
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (5 * m).factorial_pos (4 * m).factorial_pos)
  calc (5 * m).factorial * (4 * m).factorial * (3 ^ (9 * m) * (30 * m).factorial)
      = 3 ^ (9 * m) * ((30 * m).factorial * (5 * m).factorial * (4 * m).factorial) := by ring
    _ = 3 ^ (9 * m) * ((15 * m).factorial * (10 * m).factorial * (8 * m).factorial *
          (6 * m).factorial * a295458 m) := by rw [ha]
    _ = _ := by rw [← hX₁, ← hX₂]; ring

/-- For every `n`,
`(5n)! (2n)! ∏_{i<n} (5n + 3(i+1)) ∏_{i<2n} (4n + 3(i+1))` divides `3^(3n) (10n)!`. -/
theorem third_exists (n : ℕ) : ∃ c : ℕ,
    3 ^ (3 * n) * (10 * n).factorial =
      (5 * n).factorial * (2 * n).factorial * apProd (5 * n) 3 n * apProd (4 * n) 3 (2 * n) * c := by
  by_cases h3 : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3
    exact ⟨a295458 m, third_three_mul_eq m⟩
  · obtain ⟨c, hc⟩ := third_dvd n h3
    exact ⟨3 ^ (3 * n) * c, by rw [hc]; ring⟩

/-- The third-index ratio `a(n/3)` is a natural number for every `n`. -/
theorem thirdRatio_integral (n : ℕ) : ∃ k : ℕ, thirdRatio n = k := by
  obtain ⟨c, hc⟩ := third_exists n
  exact ⟨c, thirdRatio_eq hc⟩

/-- Consistency with the entry: at `n = 3m` the third-index ratio is `a(m)`. -/
theorem thirdRatio_three_mul (m : ℕ) : thirdRatio (3 * m) = a295458 m :=
  thirdRatio_eq (third_three_mul_eq m)

/-! ## Examples -/

example : a295458 0 = 1 := by decide

example : a295458 1 = 5545451340 := by decide

/-- `a(1/2) = 15! Γ(7/2) 2! / (Γ(17/2) 5! 4! 3!) = 35840`. -/
theorem halfRatio_one : halfRatio 1 = 35840 := by
  rw [halfRatio_of_odd (c := 35) (by decide) (by decide)]
  norm_num

/-- `a(3/2) = 991901222174720`. -/
theorem halfRatio_three : halfRatio 3 = 991901222174720 := by
  rw [halfRatio_of_odd (c := 923780) (by decide) (by decide)]
  norm_num

/-- `a(2/2) = a(1) = 5545451340`. -/
example : halfRatio 2 = 5545451340 := by
  have h := halfRatio_two_mul 1
  rw [show (5545451340 : ℝ) = (a295458 1 : ℝ) by
    norm_num [show a295458 1 = 5545451340 by decide]]
  simpa using h

/-- `a(1/3) = 10! Γ(8/3) Γ(7/3) / (5! Γ(13/3) Γ(11/3) 2!) = 729`. -/
theorem thirdRatio_one : thirdRatio 1 = 729 := thirdRatio_eq (c := 729) (by decide)

/-- `a(2/3) = 1869885`. -/
theorem thirdRatio_two : thirdRatio 2 = 1869885 := thirdRatio_eq (c := 1869885) (by decide)

/-- `a(3/3) = a(1) = 5545451340`. -/
example : thirdRatio 3 = 5545451340 := by
  have h := thirdRatio_three_mul 1
  rw [show (5545451340 : ℝ) = (a295458 1 : ℝ) by
    norm_num [show a295458 1 = 5545451340 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- Bala's conjecture (OEIS A295458, July 29, 2026): both `a(n/2)` and
`a(n/3)` are natural numbers for every natural `n`, interpreting
fractional factorials as `x! = Γ(x+1)`. -/
theorem bala_both (n : ℕ) : (∃ k : ℕ, halfRatio n = k) ∧ (∃ k : ℕ, thirdRatio n = k) :=
  ⟨halfRatio_integral n, thirdRatio_integral n⟩

end Candidates.A295458BalaBoth
