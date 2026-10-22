/-
# A295437 — Bala: both `a(n/2)` and `a(n/3)` are integers

OEIS A295437, Peter Bala (2026): both `a(n/2)` and `a(n/3)` are integers
for every natural `n`, where `a(n) = (18n)! n! / ((9n)! (6n)! (4n)!)` and
fractional factorials mean `x! = Γ(x+1)`.

## Proof outline

* Gamma is removed uniformly by the Pochhammer identity
  `Γ(x + k) = Γ(x) ∏_{i<k} (x + i)`:
  `a(n/2) = 2^(4n) (9n)! / ((3n)! (2n)! ∏_{i<4n} (n + 2(i+1)))` and
  `a(n/3) = 3^n (6n)! / ((3n)! (2n)! ∏_{i<n} (n + 3(i+1)))`.
* `n = 2m` (resp. `n = 3m`): the progression product is a power of `2`
  (resp. `3`) times `(9m)!/m!` (resp. `(4m)!/m!`), and the ratio is `a(m)`.
* `n` odd (resp. `3 ∤ n`): the prime `2` (resp. `3`) divides no term of the
  progression. For every other prime power `q = p^k`, the multiples of `q` among
  the terms have quotients in `(⌊n/q⌋, ⌊(n+dL)/q⌋]` that are pairwise congruent
  modulo `d`. A Legendre count then reduces the claim to the step inequalities
  `⌊3x⌋ + ⌊2x⌋ + ⌈(⌊9x⌋ - ⌊x⌋)/2⌉ ≤ ⌊9x⌋` and
  `⌊3x⌋ + ⌊2x⌋ + ⌈(⌊4x⌋ - ⌊x⌋)/3⌉ ≤ ⌊6x⌋`, closed by `omega` in `j = ⌊18x⌋` and
  `j = ⌊12x⌋`. The powers `2^(4n)` and `3^n` are not needed in these cases.
-/
import Mathlib
import Combinatorics.A295431BalaGamma

set_option autoImplicit false

namespace Candidates.A295437BalaJunBoth

open Finset
open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq)

/-! ## Definition layer -/

/-- The OEIS sequence A295437: `a(n) = (18n)! n! / ((9n)! (6n)! (4n)!)`. The
truncating `Nat` division is exact; see `a295437_mul`. -/
def a295437 (n : ℕ) : ℕ :=
  (18 * n).factorial * n.factorial / ((9 * n).factorial * (6 * n).factorial * (4 * n).factorial)

/-- Bala's half-index value `a(n/2) = (9n)! (n/2)! / ((9n/2)! (3n)! (2n)!)`, with
`x! := Γ(x + 1)`. The denominator is positive (Gamma is positive on `(0, ∞)`), so
the real division never takes its junk value. -/
noncomputable def halfRatio (n : ℕ) : ℝ :=
  ((9 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (Real.Gamma (9 * (n : ℝ) / 2 + 1) * ((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ))

/-- Bala's third-index value `a(n/3) = (6n)! (n/3)! / ((3n)! (2n)! (4n/3)!)`, with
`x! := Γ(x + 1)`. The denominator is positive. -/
noncomputable def thirdRatio (n : ℕ) : ℝ :=
  ((6 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 3 + 1) /
    (((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma (4 * (n : ℝ) / 3 + 1))

/-- The arithmetic-progression product `∏_{i < L} (n + d(i+1))`. -/
def apProd (n d L : ℕ) : ℕ := ∏ i ∈ range L, (n + d * (i + 1))

/-! ## Legendre counting for progression products -/

/-- Legendre's formula for an arithmetic-progression product. If every term
`n + d(i+1)` (`i < L`) is positive and below `p^b`, then
`v_p(apProd n d L) = ∑_{1 ≤ k < b} #{i < L : p^k ∣ n + d(i+1)}`. -/
theorem factorization_apProd {p : ℕ} (hp : p.Prime) (n d L b : ℕ)
    (hpos : ∀ i < L, 0 < n + d * (i + 1)) (hb : ∀ i < L, n + d * (i + 1) < p ^ b) :
    (apProd n d L).factorization p =
      ∑ k ∈ Ico 1 b, #{i ∈ range L | p ^ k ∣ n + d * (i + 1)} := by
  unfold apProd
  rw [Nat.factorization_prod fun i hi => (hpos i (mem_range.1 hi)).ne', Finsupp.finsetSum_apply]
  have hterm : ∀ i ∈ range L, (n + d * (i + 1)).factorization p =
      ∑ k ∈ Ico 1 b, if p ^ k ∣ n + d * (i + 1) then 1 else 0 := by
    intro i hi
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (hpos i (mem_range.1 hi)) (hb i (mem_range.1 hi)),
      card_filter]
  rw [sum_congr rfl hterm, sum_comm]
  exact sum_congr rfl fun k _ => (card_filter _ _).symm

/-- Counting multiples of `q` in the progression `n + d(i+1)`, `i < L`, with `q`
coprime to `d`. Their quotients by `q` lie in `(⌊n/q⌋, ⌊(n+dL)/q⌋]` and are
pairwise congruent modulo `d`. Hence there are at most `⌈(B - A)/d⌉` of them,
where `A = ⌊n/q⌋` and `B = ⌊(n+dL)/q⌋`. -/
theorem card_dvd_le (n d L q : ℕ) (hd : 0 < d) (hq : 0 < q) (hcop : Nat.Coprime q d) :
    #{i ∈ range L | q ∣ n + d * (i + 1)} ≤ ((n + d * L) / q - n / q + d - 1) / d := by
  set T := (range L).filter (fun i => q ∣ n + d * (i + 1)) with hT
  rcases T.eq_empty_or_nonempty with hE | hne
  · rw [hE, card_empty]; exact Nat.zero_le _
  set i0 := T.min' hne
  have hi0 : i0 ∈ T := T.min'_mem hne
  rw [hT, mem_filter, mem_range] at hi0
  obtain ⟨s0, hs0⟩ := hi0.2
  set A := n / q
  set B := (n + d * L) / q
  have hA : A < s0 := by
    have h1 : A * q ≤ n := Nat.div_mul_le_self n q
    by_contra hcon
    have : s0 * q ≤ A * q := Nat.mul_le_mul_right q (not_lt.1 hcon)
    nlinarith
  set N := (B - A - 1) / d
  have hsub : T ⊆ (range (N + 1)).image (fun t => i0 + q * t) := by
    intro i hi
    have hmin : i0 ≤ i := T.min'_le i hi
    rw [hT, mem_filter, mem_range] at hi
    obtain ⟨s, hs⟩ := hi.2
    have hdq : q ∣ d * (i - i0) := by
      have : d * (i - i0) = (n + d * (i + 1)) - (n + d * (i0 + 1)) := by
        have hle : d * i0 ≤ d * i := Nat.mul_le_mul_left d hmin
        rw [Nat.mul_sub, mul_add, mul_add, mul_one]; omega
      rw [this]; exact Nat.dvd_sub hi.2 hi0.2
    obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left hdq
    rw [mem_image]
    refine ⟨t, ?_, by omega⟩
    rw [mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
    have hsB : s ≤ B := by
      rw [Nat.le_div_iff_mul_le hq]
      have : n + d * (i + 1) ≤ n + d * L := by
        have : i + 1 ≤ L := hi.1
        exact Nat.add_le_add_left (Nat.mul_le_mul_left d this) n
      rw [hs] at this; linarith
    have hss : s = s0 + d * t := by
      have hi' : i = i0 + q * t := by omega
      have h1 : q * s = q * (s0 + d * t) := by
        calc q * s = n + d * (i + 1) := hs.symm
          _ = (n + d * (i0 + 1)) + d * (q * t) := by rw [hi']; ring
          _ = q * (s0 + d * t) := by rw [hs0]; ring
      exact Nat.eq_of_mul_eq_mul_left hq h1
    have : d * t ≤ B - A - 1 := by omega
    linarith
  have hcard : T.card ≤ N + 1 := (card_le_card hsub).trans (card_image_le.trans (by simp))
  have hBA : A < B := by
    have : s0 ≤ B := by
      rw [Nat.le_div_iff_mul_le hq]
      have : n + d * (i0 + 1) ≤ n + d * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_left d hi0.1) n
      rw [hs0] at this; linarith
    omega
  have hN : N + 1 = (B - A + d - 1) / d := by
    rw [show B - A + d - 1 = (B - A - 1) + d by omega, Nat.add_div_right _ hd]
  rw [← hN]
  exact hcard

/-- The third-index step inequality in `j = ⌊12x⌋`:
`⌊3x⌋ + ⌊2x⌋ + ⌈(⌊4x⌋ - ⌊x⌋)/3⌉ ≤ ⌊6x⌋`. -/
theorem step_third (j : ℕ) : j / 4 + j / 6 + (j / 3 - j / 12 + 3 - 1) / 3 ≤ j / 2 := by omega

/-- The half-index step inequality in `j = ⌊18x⌋`:
`⌊3x⌋ + ⌊2x⌋ + ⌈(⌊9x⌋ - ⌊x⌋)/2⌉ ≤ ⌊9x⌋`. -/
theorem step_half (j : ℕ) : j / 6 + j / 9 + (j / 2 - j / 18 + 2 - 1) / 2 ≤ j / 2 := by omega

/-- The step inequality for A295437 itself in `j = ⌊36y⌋`:
`⌊9y⌋ + ⌊6y⌋ + ⌊4y⌋ ≤ ⌊18y⌋ + ⌊y⌋`. -/
theorem step_a (j : ℕ) : j / 4 + j / 6 + j / 9 ≤ j / 2 + j / 36 := by omega

/-- Landau-type criterion with an extra arithmetic-progression factor. Let
`∑_{y ∈ bs} ⌊y/p^k⌋ + #{i < L : p^k ∣ n + d(i+1)} ≤ ∑_{x ∈ as} ⌊x/p^k⌋` for every
prime `p` and `k ≥ 1`. Then `(∏_{y ∈ bs} y!) · apProd n d L` divides
`∏_{x ∈ as} x!`. The bound `M` only supplies a common range for Legendre's
formula. -/
theorem dvd_of_terms (as bs : List ℕ) (n d L M : ℕ) (hd : 0 < d) (has : ∀ x ∈ as, x ≤ M)
    (hbs : ∀ x ∈ bs, x ≤ M) (hL : n + d * L ≤ M)
    (hterm : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      (bs.map (· / p ^ k)).sum + #{i ∈ range L | p ^ k ∣ n + d * (i + 1)} ≤
        (as.map (· / p ^ k)).sum) :
    (bs.map Nat.factorial).prod * apProd n d L ∣ (as.map Nat.factorial).prod := by
  have hne : ∀ l : List ℕ, (l.map Nat.factorial).prod ≠ 0 := fun l => by
    simp [Nat.factorial_ne_zero]
  have hpos : ∀ i < L, 0 < n + d * (i + 1) := fun i _ => by positivity
  have hP : apProd n d L ≠ 0 := prod_ne_zero_iff.2 fun i hi => (hpos i (mem_range.1 hi)).ne'
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (hne bs) hP) (hne as), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hb : ∀ x ≤ M, Nat.log p x < M + 1 := fun x hx =>
      Nat.lt_succ_of_le ((Nat.log_le_self p x).trans hx)
    have hMp : M < p ^ (M + 1) :=
      (Nat.lt_pow_self hp.one_lt).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self M))
    have hb' : ∀ i < L, n + d * (i + 1) < p ^ (M + 1) := fun i hi =>
      lt_of_le_of_lt ((Nat.add_le_add_left (Nat.mul_le_mul_left d hi) n).trans hL) hMp
    rw [Nat.factorization_mul (hne bs) hP, Finsupp.add_apply,
      Candidates.A295431BalaGamma.factorization_prod_factorial hp (M + 1) bs
        fun x hx => hb x (hbs x hx),
      Candidates.A295431BalaGamma.factorization_prod_factorial hp (M + 1) as
        fun x hx => hb x (has x hx),
      factorization_apProd hp n d L (M + 1) hpos hb', ← sum_add_distrib]
    exact sum_le_sum fun k hk => hterm p k hp (mem_Ico.1 hk).1
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Pochhammer form of the Gamma recursion: for `x > 0`,
`Γ(x + k) = Γ(x) ∏_{i < k} (x + i)`. -/
theorem gamma_add_nat (x : ℝ) (hx : 0 < x) (k : ℕ) :
    Real.Gamma (x + k) = Real.Gamma x * ∏ i ∈ range k, (x + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [← add_assoc, Real.Gamma_add_one (by positivity), ih, prod_range_succ]
    ring

/-- In `ℝ`, `apProd n d L = d^L ∏_{i < L} (n/d + 1 + i)`. -/
theorem apProd_real (n d L : ℕ) (hd : 0 < d) :
    (apProd n d L : ℝ) = (d : ℝ) ^ L * ∏ i ∈ range L, ((n : ℝ) / d + 1 + i) := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  unfold apProd
  push_cast
  rw [show (d : ℝ) ^ L = ∏ _i ∈ range L, (d : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  field_simp
  ring

/-- `m! ∏_{i < L} (m + i + 1) = (m + L)!`. -/
theorem factorial_mul_prod_succ (m L : ℕ) :
    m.factorial * ∏ i ∈ range L, (m + i + 1) = (m + L).factorial := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ]
    ring

/-- When `d ∣ n`, the progression factors: `apProd (d m) d L = d^L ∏_{i < L} (m + i + 1)`. -/
theorem apProd_mul_left (d m L : ℕ) :
    apProd (d * m) d L = d ^ L * ∏ i ∈ range L, (m + i + 1) := by
  unfold apProd
  rw [show d ^ L = ∏ _i ∈ range L, d by simp, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by ring

/-- Integrality of A295437: `(9m)! (6m)! (4m)!` divides `(18m)! m!`. -/
theorem factorial_dvd_a295437 (m : ℕ) :
    (9 * m).factorial * (6 * m).factorial * (4 * m).factorial ∣
      (18 * m).factorial * m.factorial := by
  have h := landau_list [18 * m, m] [9 * m, 6 * m, 4 * m] (18 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have hs := step_a (36 * m / q)
      rw [div_div_eq_of_mul_eq 36 m q 9 4 1 (by norm_num) (by norm_num) (by norm_num),
        div_div_eq_of_mul_eq 36 m q 6 6 1 (by norm_num) (by norm_num) (by norm_num),
        div_div_eq_of_mul_eq 36 m q 4 9 1 (by norm_num) (by norm_num) (by norm_num),
        div_div_eq_of_mul_eq 36 m q 18 2 1 (by norm_num) (by norm_num) (by norm_num),
        div_div_eq_of_mul_eq 36 m q 1 36 1 (by norm_num) (by norm_num) (by norm_num)] at hs
      simp only [one_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at hs ⊢
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295437`. -/
theorem a295437_mul (m : ℕ) :
    (9 * m).factorial * (6 * m).factorial * (4 * m).factorial * a295437 m =
      (18 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295437 m)

/-- If `r ∣ d` and `r ∤ n`, then no term `n + d(i+1)` is divisible by `r^k` with
`k ≥ 1`. -/
theorem card_eq_zero_of_dvd (n d L r k : ℕ) (hk : 1 ≤ k) (hr : r ∣ d) (hn : ¬ r ∣ n) :
    #{i ∈ range L | r ^ k ∣ n + d * (i + 1)} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i _ hdiv
  have hr' : r ∣ n + d * (i + 1) := (dvd_pow_self r (by omega)).trans hdiv
  exact hn ((Nat.dvd_add_right (hr.mul_right _)).1 (by rwa [add_comm] at hr'))

/-- For odd `n`, `(3n)! (2n)! ∏_{i < 4n} (n + 2(i+1))` divides `(9n)!`. -/
theorem half_odd_dvd (n : ℕ) (hn : ¬ 2 ∣ n) :
    (3 * n).factorial * (2 * n).factorial * apProd n 2 (4 * n) ∣ (9 * n).factorial := by
  have h := dvd_of_terms [9 * n] [3 * n, 2 * n] n 2 (4 * n) (9 * n) (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp2 : p = 2
      · subst hp2
        rw [card_eq_zero_of_dvd n 2 (4 * n) 2 k hk dvd_rfl hn, add_zero]
        calc 3 * n / 2 ^ k + 2 * n / 2 ^ k ≤ (3 * n + 2 * n) / 2 ^ k := Nat.add_div_le_add_div _ _ _
          _ ≤ 9 * n / 2 ^ k := Nat.div_le_div_right (by omega)
      · have hcop : Nat.Coprime (p ^ k) 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
        have hc := card_dvd_le n 2 (4 * n) (p ^ k) (by norm_num) (pow_pos hp.pos k) hcop
        rw [show n + 2 * (4 * n) = 9 * n by ring] at hc
        have hs := step_half (18 * n / p ^ k)
        rw [div_div_eq_of_mul_eq 18 n (p ^ k) 3 6 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 18 n (p ^ k) 2 9 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 18 n (p ^ k) 9 2 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 18 n (p ^ k) 1 18 1 (by norm_num) (by norm_num) (by norm_num)] at hs
        simp only [one_mul] at hs
        omega)
  simpa [mul_assoc] using h

/-- For `3 ∤ n`, `(3n)! (2n)! ∏_{i < n} (n + 3(i+1))` divides `(6n)!`. -/
theorem third_dvd (n : ℕ) (hn : ¬ 3 ∣ n) :
    (3 * n).factorial * (2 * n).factorial * apProd n 3 n ∣ (6 * n).factorial := by
  have h := dvd_of_terms [6 * n] [3 * n, 2 * n] n 3 n (6 * n) (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp3 : p = 3
      · subst hp3
        rw [card_eq_zero_of_dvd n 3 n 3 k hk dvd_rfl hn, add_zero]
        calc 3 * n / 3 ^ k + 2 * n / 3 ^ k ≤ (3 * n + 2 * n) / 3 ^ k := Nat.add_div_le_add_div _ _ _
          _ ≤ 6 * n / 3 ^ k := Nat.div_le_div_right (by omega)
      · have hcop : Nat.Coprime (p ^ k) 3 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
        have hc := card_dvd_le n 3 n (p ^ k) (by norm_num) (pow_pos hp.pos k) hcop
        rw [show n + 3 * n = 4 * n by ring] at hc
        have hs := step_third (12 * n / p ^ k)
        rw [div_div_eq_of_mul_eq 12 n (p ^ k) 3 4 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 12 n (p ^ k) 2 6 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 12 n (p ^ k) 4 3 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 12 n (p ^ k) 1 12 1 (by norm_num) (by norm_num) (by norm_num),
          div_div_eq_of_mul_eq 12 n (p ^ k) 6 2 1 (by norm_num) (by norm_num) (by norm_num)] at hs
        simp only [one_mul] at hs
        omega)
  simpa [mul_assoc] using h

/-- For `n = 2m`: `2^(4n) (9n)! = (3n)! (2n)! ∏_{i<4n} (n + 2(i+1)) · a(m)`. -/
theorem half_even_eq (m : ℕ) :
    2 ^ (4 * (2 * m)) * (9 * (2 * m)).factorial =
      (3 * (2 * m)).factorial * (2 * (2 * m)).factorial * apProd (2 * m) 2 (4 * (2 * m)) *
        a295437 m := by
  rw [apProd_mul_left, show 4 * (2 * m) = 8 * m by ring, show 9 * (2 * m) = 18 * m by ring,
    show 3 * (2 * m) = 6 * m by ring, show 2 * (2 * m) = 4 * m by ring]
  have hX := factorial_mul_prod_succ m (8 * m)
  rw [show m + 8 * m = 9 * m by ring] at hX
  have ha := a295437_mul m
  apply Nat.eq_of_mul_eq_mul_left m.factorial_pos
  calc m.factorial * (2 ^ (8 * m) * (18 * m).factorial)
      = 2 ^ (8 * m) * ((18 * m).factorial * m.factorial) := by ring
    _ = 2 ^ (8 * m) * ((9 * m).factorial * (6 * m).factorial * (4 * m).factorial *
          a295437 m) := by rw [ha]
    _ = _ := by rw [← hX]; ring

/-- For `n = 3m`: `3^n (6n)! = (3n)! (2n)! ∏_{i<n} (n + 3(i+1)) · a(m)`. -/
theorem third_three_mul_eq (m : ℕ) :
    3 ^ (3 * m) * (6 * (3 * m)).factorial =
      (3 * (3 * m)).factorial * (2 * (3 * m)).factorial * apProd (3 * m) 3 (3 * m) *
        a295437 m := by
  rw [apProd_mul_left, show 6 * (3 * m) = 18 * m by ring, show 3 * (3 * m) = 9 * m by ring,
    show 2 * (3 * m) = 6 * m by ring]
  have hX := factorial_mul_prod_succ m (3 * m)
  rw [show m + 3 * m = 4 * m by ring] at hX
  have ha := a295437_mul m
  apply Nat.eq_of_mul_eq_mul_left m.factorial_pos
  calc m.factorial * (3 ^ (3 * m) * (18 * m).factorial)
      = 3 ^ (3 * m) * ((18 * m).factorial * m.factorial) := by ring
    _ = 3 ^ (3 * m) * ((9 * m).factorial * (6 * m).factorial * (4 * m).factorial *
          a295437 m) := by rw [ha]
    _ = _ := by rw [← hX]; ring

/-- For every `n`, `(3n)! (2n)! ∏_{i<4n} (n + 2(i+1))` divides `2^(4n) (9n)!`. -/
theorem half_exists (n : ℕ) : ∃ c : ℕ,
    2 ^ (4 * n) * (9 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 2 (4 * n) * c := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    exact ⟨a295437 m, half_even_eq m⟩
  · obtain ⟨c, hc⟩ := half_odd_dvd n h2
    exact ⟨2 ^ (4 * n) * c, by rw [hc]; ring⟩

/-- For every `n`, `(3n)! (2n)! ∏_{i<n} (n + 3(i+1))` divides `3^n (6n)!`. -/
theorem third_exists (n : ℕ) : ∃ c : ℕ,
    3 ^ n * (6 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 3 n * c := by
  by_cases h3 : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3
    exact ⟨a295437 m, third_three_mul_eq m⟩
  · obtain ⟨c, hc⟩ := third_dvd n h3
    exact ⟨3 ^ n * c, by rw [hc]; ring⟩

/-- The Gamma bridge for the half index. Suppose
`2^(4n) (9n)! = (3n)! (2n)! ∏_{i<4n} (n + 2(i+1)) · c`. Then `a(n/2) = c`. It uses
`Γ(9n/2 + 1) = Γ(n/2 + 1) ∏_{i<4n} (n/2 + 1 + i)`. -/
theorem halfRatio_eq {n c : ℕ}
    (hc : 2 ^ (4 * n) * (9 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 2 (4 * n) * c) :
    halfRatio n = c := by
  set Q := ∏ i ∈ range (4 * n), ((n : ℝ) / 2 + 1 + i) with hQ
  have hQpos : 0 < Q := prod_pos fun i _ => by positivity
  have hΓ : Real.Gamma (9 * (n : ℝ) / 2 + 1) = Real.Gamma ((n : ℝ) / 2 + 1) * Q := by
    rw [show 9 * (n : ℝ) / 2 + 1 = ((n : ℝ) / 2 + 1) + ((4 * n : ℕ) : ℝ) by push_cast; ring,
      gamma_add_nat _ (by positivity)]
  have hP : (apProd n 2 (4 * n) : ℝ) = 2 ^ (4 * n) * Q := by
    rw [apProd_real n 2 (4 * n) (by norm_num)]
    push_cast
    rfl
  have hcR : (2 : ℝ) ^ (4 * n) * ((9 * n).factorial : ℝ) =
      ((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * (apProd n 2 (4 * n) : ℝ) * c := by
    exact_mod_cast hc
  rw [hP] at hcR
  have key : ((9 * n).factorial : ℝ) = c * Q * (3 * n).factorial * (2 * n).factorial := by
    have h2 : (2 : ℝ) ^ (4 * n) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    linear_combination hcR
  have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold halfRatio
  rw [hΓ, div_eq_iff (by positivity), key]
  ring

/-- The Gamma bridge for the third index. Suppose
`3^n (6n)! = (3n)! (2n)! ∏_{i<n} (n + 3(i+1)) · c`. Then `a(n/3) = c`. It uses
`Γ(4n/3 + 1) = Γ(n/3 + 1) ∏_{i<n} (n/3 + 1 + i)`. -/
theorem thirdRatio_eq {n c : ℕ}
    (hc : 3 ^ n * (6 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 3 n * c) :
    thirdRatio n = c := by
  set Q := ∏ i ∈ range n, ((n : ℝ) / 3 + 1 + i) with hQ
  have hQpos : 0 < Q := prod_pos fun i _ => by positivity
  have hΓ : Real.Gamma (4 * (n : ℝ) / 3 + 1) = Real.Gamma ((n : ℝ) / 3 + 1) * Q := by
    rw [show 4 * (n : ℝ) / 3 + 1 = ((n : ℝ) / 3 + 1) + (n : ℝ) by ring,
      gamma_add_nat _ (by positivity)]
  have hP : (apProd n 3 n : ℝ) = 3 ^ n * Q := by
    rw [apProd_real n 3 n (by norm_num)]
    push_cast
    rfl
  have hcR : (3 : ℝ) ^ n * ((6 * n).factorial : ℝ) =
      ((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * (apProd n 3 n : ℝ) * c := by
    exact_mod_cast hc
  rw [hP] at hcR
  have key : ((6 * n).factorial : ℝ) = c * Q * (3 * n).factorial * (2 * n).factorial := by
    have h3 : (3 : ℝ) ^ n ≠ 0 := by positivity
    apply mul_left_cancel₀ h3
    linear_combination hcR
  have hG : 0 < Real.Gamma ((n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold thirdRatio
  rw [hΓ, div_eq_iff (by positivity), key]
  ring

/-- Consistency with the entry: at even `n = 2m` the half-index ratio is `a(m)`. -/
theorem halfRatio_two_mul (m : ℕ) : halfRatio (2 * m) = a295437 m :=
  halfRatio_eq (half_even_eq m)

/-- Consistency with the entry: at `n = 3m` the third-index ratio is `a(m)`. -/
theorem thirdRatio_three_mul (m : ℕ) : thirdRatio (3 * m) = a295437 m :=
  thirdRatio_eq (third_three_mul_eq m)

/-! ## Examples -/

example : a295437 0 = 1 := by decide

example : a295437 1 = 1021020 := by decide

/-- `a(1/2) = 9! Γ(3/2) / (Γ(11/2) 3! 2!) = 512`. -/
theorem halfRatio_one : halfRatio 1 = 512 := halfRatio_eq (c := 512) (by decide)

/-- `a(3/2) = 27! Γ(5/2) / (Γ(29/2) 9! 6!) = 2399141888`. -/
theorem halfRatio_three : halfRatio 3 = 2399141888 :=
  halfRatio_eq (c := 2399141888) (by decide)

/-- `a(2/2) = a(1) = 1021020`. -/
example : halfRatio 2 = 1021020 := by
  have h := halfRatio_two_mul 1
  rw [show (1021020 : ℝ) = (a295437 1 : ℝ) by norm_num [show a295437 1 = 1021020 by decide]]
  simpa using h

/-- `a(1/3) = 6! Γ(4/3) / (3! 2! Γ(7/3)) = 45`. -/
theorem thirdRatio_one : thirdRatio 1 = 45 := thirdRatio_eq (c := 45) (by decide)

/-- `a(2/3) = 12! Γ(5/3) / (6! 4! Γ(11/3)) = 6237`. -/
theorem thirdRatio_two : thirdRatio 2 = 6237 := thirdRatio_eq (c := 6237) (by decide)

/-! ## The conjecture -/

/-- **Bala's conjecture, first half (A295437, Peter Bala, Jun 13 2026).** For every
`n ≥ 0`, `a(n/2) = (9n)! (n/2)! / ((9n/2)! (3n)! (2n)!)` is a natural number,
with `x! := Γ(x + 1)`. -/
theorem halfRatio_integral (n : ℕ) : ∃ k : ℕ, halfRatio n = k := by
  obtain ⟨c, hc⟩ := half_exists n
  exact ⟨c, halfRatio_eq hc⟩

/-- **Bala's conjecture, second half (A295437, Peter Bala, Jun 13 2026).** For every
`n ≥ 0`, `a(n/3) = (6n)! (n/3)! / ((3n)! (2n)! (4n/3)!)` is a natural number,
with `x! := Γ(x + 1)`. -/
theorem thirdRatio_integral (n : ℕ) : ∃ k : ℕ, thirdRatio n = k := by
  obtain ⟨c, hc⟩ := third_exists n
  exact ⟨c, thirdRatio_eq hc⟩

/-- Bala's conjecture (OEIS A295437, Peter Bala, 2026):
for every natural `n`, both `a(n/2)` and `a(n/3)` are natural numbers,
with fractional factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_both (n : ℕ) : (∃ k : ℕ, halfRatio n = k) ∧ (∃ k : ℕ, thirdRatio n = k) :=
  ⟨halfRatio_integral n, thirdRatio_integral n⟩

end Candidates.A295437BalaJunBoth
