/-
# A295456 — Bala: both `a(n/2)` and `a(n/3)` are integers

## OEIS source (retrieved with `oeis show A295456`, 2026-10-21)

```
NAME:     a(n) = (30*n)!*(5*n)!*(4*n)!/((15*n)!*(12*n)!*(10*n)!*(2*n)!).
TERMS:    1,168043980,126694219977836700,109504706026534324525391988,...
FORMULA:  a(n) = binomial(30*n,15*n)*binomial(15*n,3*n)*binomial(3*n,n)/
          (binomial(10*n,5*n)*binomial(5*n,n)). - _Chai Wah Wu_, Feb 15 2026
COMMENT (the conjecture):
  Conjecture: for n >= 0, both a(n/2) = (15*n)!*(5*n/2)!*(2*n)! /
  ((15*n/2)!*(6*n)!*(5*n)!*n!) and a(n/3) = (10*n)!*(5*n/3)!*(4*n/3)! /
  ((5*n)!*(4*n)!*(10*n/3)!*(2*n/3)!) are integers, where fractional
  factorials are defined using the Gamma function; for example
  (5*n/2)! := Gamma(5*n/2 + 1). - _Peter Bala_, Jun 13 2026
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell. Triage evidence: both ratios integral for `n ≤ 300`; re-checked here for
`n ≤ 450` (exact rational arithmetic after removing Gamma, cross-checked against
a multiprecision Gamma evaluation for `n ≤ 3`).

## Result of this module

Both conjectures are proved for every `n`.

* Gamma is removed by the Pochhammer identity `Γ(x + k) = Γ(x) ∏_{i<k} (x + i)`:
  `a(n/2) = 2^(5n) (15n)! (2n)! / ((6n)! (5n)! n! ∏_{i<5n} (5n + 2(i+1)))` and
  `a(n/3) = 3^n (10n)! ∏_{i<n} (2n + 3(i+1)) / ((5n)! (4n)! ∏_{i<2n} (4n + 3(i+1)))`.
* `n = 2m` (resp. `n = 3m`): the ratio is `a(m)` itself, integral by Landau's
  criterion.
* `n` odd (resp. `3 ∤ n`): the prime `2` (resp. `3`) divides no progression term
  in the denominator, and superadditivity of `⌊·/p^k⌋` suffices. For every other
  prime power `q`, choose `ñ` with `dñ ≡ n (mod q)` (`d = 2` or `3`). The number of
  multiples of `q` among the progression terms is an exact Legendre difference in
  `ñ`, and the term inequality becomes Landau's inequality for `a` at `ñ / q`:
  `⌊15y⌋ + ⌊12y⌋ + ⌊10y⌋ + ⌊2y⌋ ≤ ⌊30y⌋ + ⌊5y⌋ + ⌊4y⌋`.
-/
import Mathlib
import Combinatorics.A295437BalaJunBoth

set_option autoImplicit false

namespace Candidates.A295456BalaBoth

open Finset
open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq factorization_prod_factorial)
open Candidates.A295437BalaJunBoth (apProd factorization_apProd gamma_add_nat apProd_real
  factorial_mul_prod_succ apProd_mul_left card_eq_zero_of_dvd)

/-! ## Definition layer -/

/-- The OEIS sequence A295456:
`a(n) = (30n)! (5n)! (4n)! / ((15n)! (12n)! (10n)! (2n)!)`. The truncating `Nat`
division is exact; see `a295456_mul`. -/
def a295456 (n : ℕ) : ℕ :=
  (30 * n).factorial * (5 * n).factorial * (4 * n).factorial /
    ((15 * n).factorial * (12 * n).factorial * (10 * n).factorial * (2 * n).factorial)

/-- Bala's half-index value
`a(n/2) = (15n)! (5n/2)! (2n)! / ((15n/2)! (6n)! (5n)! n!)`, with `x! := Γ(x + 1)`.
The denominator is positive (Gamma is positive on `(0, ∞)`), so the real division
never takes its junk value. -/
noncomputable def halfRatio (n : ℕ) : ℝ :=
  ((15 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ) /
    (Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((6 * n).factorial : ℝ) * ((5 * n).factorial : ℝ) *
      (n.factorial : ℝ))

/-- Bala's third-index value
`a(n/3) = (10n)! (5n/3)! (4n/3)! / ((5n)! (4n)! (10n/3)! (2n/3)!)`, with
`x! := Γ(x + 1)`. The denominator is positive. -/
noncomputable def thirdRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 3 + 1) *
      Real.Gamma (4 * (n : ℝ) / 3 + 1) /
    (((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (10 * (n : ℝ) / 3 + 1) *
      Real.Gamma (2 * (n : ℝ) / 3 + 1))

/-! ## Landau's inequality for A295456 -/

/-- Landau's step inequality for A295456 in `j = ⌊60y⌋`:
`⌊15y⌋ + ⌊12y⌋ + ⌊10y⌋ + ⌊2y⌋ ≤ ⌊30y⌋ + ⌊5y⌋ + ⌊4y⌋`. -/
theorem step_a (j : ℕ) : j / 4 + j / 5 + j / 6 + j / 30 ≤ j / 2 + j / 12 + j / 15 := by
  -- The defect is `60`-periodic; reduce to `j = 60a + r` and check each residue `r`.
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r : ℕ, r < 60 ∧ j = 60 * a + r :=
    ⟨j / 60, j % 60, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 60).symm⟩
  interval_cases r <;> omega

/-- Landau's term inequality for A295456, valid for every `m` and `q`:
`⌊15m/q⌋ + ⌊12m/q⌋ + ⌊10m/q⌋ + ⌊2m/q⌋ ≤ ⌊30m/q⌋ + ⌊5m/q⌋ + ⌊4m/q⌋`. -/
theorem term_a (m q : ℕ) :
    15 * m / q + 12 * m / q + 10 * m / q + 2 * m / q ≤ 30 * m / q + 5 * m / q + 4 * m / q := by
  have hs := step_a (60 * m / q)
  rw [div_div_eq_of_mul_eq 60 m q 15 4 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 12 5 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 10 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 2 30 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 30 2 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 5 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 4 15 1 (by norm_num) (by norm_num) (by norm_num)] at hs
  simpa only [one_mul] using hs

/-- Integrality of A295456: `(15m)! (12m)! (10m)! (2m)!` divides `(30m)! (5m)! (4m)!`. -/
theorem factorial_dvd_a295456 (m : ℕ) :
    (15 * m).factorial * (12 * m).factorial * (10 * m).factorial * (2 * m).factorial ∣
      (30 * m).factorial * (5 * m).factorial * (4 * m).factorial := by
  have h := landau_list [30 * m, 5 * m, 4 * m] [15 * m, 12 * m, 10 * m, 2 * m] (30 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have hs := term_a m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295456`. -/
theorem a295456_mul (m : ℕ) :
    (15 * m).factorial * (12 * m).factorial * (10 * m).factorial * (2 * m).factorial *
        a295456 m =
      (30 * m).factorial * (5 * m).factorial * (4 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295456 m)

/-! ## Exact counting of multiples in progressions -/

/-- The number of multiples of `q` in `(a, a + L]` is `⌊(a+L)/q⌋ - ⌊a/q⌋`. -/
theorem card_dvd_add_succ (a L q : ℕ) :
    #{i ∈ range L | q ∣ a + i + 1} = (a + L) / q - a / q := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [range_add_one, filter_insert]
    have hmono : a / q ≤ (a + L) / q := Nat.div_le_div_right (by omega)
    have hsucc := Nat.succ_div (a := a + L) (b := q)
    rw [show a + (L + 1) = a + L + 1 by ring]
    by_cases hd : q ∣ a + L + 1
    · rw [if_pos hd, card_insert_of_notMem (by simp), ih]
      rw [if_pos hd] at hsucc
      omega
    · rw [if_neg hd, ih]
      rw [if_neg hd] at hsucc
      omega

/-- A lift of `n / d` modulo `q`: for `q` coprime to `d > 0`, there are `ñ, t` with
`d ñ = n + q t`. -/
theorem exists_lift (d n q : ℕ) (hd : 0 < d) (hq : 0 < q) (hcop : Nat.Coprime d q) :
    ∃ ñ t : ℕ, d * ñ = n + q * t := by
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_of_coprime n hcop hq.ne'
  set ñ := u + n * q
  have hle : n ≤ d * ñ := by
    have h1 : n ≤ n * q := Nat.le_mul_of_pos_right n hq
    have h2 : n * q ≤ d * (n * q) := Nat.le_mul_of_pos_left _ hd
    have h3 : d * ñ = d * u + d * (n * q) := by rw [mul_add]
    omega
  have hmod : n ≡ d * ñ [MOD q] := by
    show n % q = (d * (u + n * q)) % q
    rw [show d * (u + n * q) = d * u + q * (d * n) by ring, Nat.add_mul_mod_self_left, hu]
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).1 hmod
  exact ⟨ñ, t, by omega⟩

/-- Exact count of multiples of `q` in the progression `e n + d(i+1)`, `i < L`. If
`q` is coprime to `d` and `d ñ = n + q t`, it equals `⌊(eñ+L)/q⌋ - ⌊eñ/q⌋`. -/
theorem card_ap_eq (d e n q t ñ L : ℕ) (hcop : Nat.Coprime q d) (h : d * ñ = n + q * t) :
    #{i ∈ range L | q ∣ e * n + d * (i + 1)} = (e * ñ + L) / q - e * ñ / q := by
  rw [← card_dvd_add_succ]
  congr 1
  refine filter_congr fun i _ => ?_
  have key : d * (e * ñ + i + 1) = (e * n + d * (i + 1)) + q * (e * t) := by
    calc d * (e * ñ + i + 1) = e * (d * ñ) + d * (i + 1) := by ring
      _ = _ := by rw [h]; ring
  constructor
  · intro hq
    apply hcop.dvd_of_dvd_mul_left
    rw [key]
    exact dvd_add hq (dvd_mul_right _ _)
  · intro hq
    have hdq : q ∣ d * (e * ñ + i + 1) := dvd_mul_of_dvd_right hq _
    rw [key] at hdq
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).1 hdq

/-- `(x + q t)/q = x/q + t`, in the orientation used below. -/
theorem div_eq_of_eq_add_mul {x y q t : ℕ} (hq : 0 < q) (h : y = x + q * t) :
    y / q = x / q + t := by
  rw [h, Nat.add_mul_div_left _ _ hq]

/-! ## Legendre counting with progressions in numerator and denominator -/

/-- Landau-type criterion with an arithmetic-progression factor on each side. Let
`∑_{y ∈ bs} ⌊y/p^k⌋ + #{i < L₂ : p^k ∣ n₂ + d(i+1)}` be at most
`∑_{x ∈ as} ⌊x/p^k⌋ + #{i < L₁ : p^k ∣ n₁ + d(i+1)}` for every prime `p` and
`k ≥ 1`. Then `(∏_{y ∈ bs} y!) · apProd n₂ d L₂` divides
`(∏_{x ∈ as} x!) · apProd n₁ d L₁`. The bound `M` only supplies a common range for
Legendre's formula. -/
theorem dvd_of_terms₂ (as bs : List ℕ) (n₁ L₁ n₂ L₂ d M : ℕ) (hd : 0 < d)
    (has : ∀ x ∈ as, x ≤ M) (hbs : ∀ x ∈ bs, x ≤ M) (hL₁ : n₁ + d * L₁ ≤ M)
    (hL₂ : n₂ + d * L₂ ≤ M)
    (hterm : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      (bs.map (· / p ^ k)).sum + #{i ∈ range L₂ | p ^ k ∣ n₂ + d * (i + 1)} ≤
        (as.map (· / p ^ k)).sum + #{i ∈ range L₁ | p ^ k ∣ n₁ + d * (i + 1)}) :
    (bs.map Nat.factorial).prod * apProd n₂ d L₂ ∣
      (as.map Nat.factorial).prod * apProd n₁ d L₁ := by
  have hne : ∀ l : List ℕ, (l.map Nat.factorial).prod ≠ 0 := fun l => by
    simp [Nat.factorial_ne_zero]
  have hpos : ∀ m L : ℕ, ∀ i < L, 0 < m + d * (i + 1) := fun m L i _ => by positivity
  have hP : ∀ m L : ℕ, apProd m d L ≠ 0 := fun m L =>
    prod_ne_zero_iff.2 fun i hi => (hpos m L i (mem_range.1 hi)).ne'
  rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (hne bs) (hP n₂ L₂))
    (mul_ne_zero (hne as) (hP n₁ L₁)), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hb : ∀ x ≤ M, Nat.log p x < M + 1 := fun x hx =>
      Nat.lt_succ_of_le ((Nat.log_le_self p x).trans hx)
    have hMp : M < p ^ (M + 1) :=
      (Nat.lt_pow_self hp.one_lt).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self M))
    have hb' : ∀ m L : ℕ, m + d * L ≤ M → ∀ i < L, m + d * (i + 1) < p ^ (M + 1) :=
      fun m L hmL i hi =>
        lt_of_le_of_lt ((Nat.add_le_add_left (Nat.mul_le_mul_left d hi) m).trans hmL) hMp
    rw [Nat.factorization_mul (hne bs) (hP n₂ L₂), Nat.factorization_mul (hne as) (hP n₁ L₁),
      Finsupp.add_apply, Finsupp.add_apply,
      factorization_prod_factorial hp (M + 1) bs fun x hx => hb x (hbs x hx),
      factorization_prod_factorial hp (M + 1) as fun x hx => hb x (has x hx),
      factorization_apProd hp n₂ d L₂ (M + 1) (hpos n₂ L₂) (hb' n₂ L₂ hL₂),
      factorization_apProd hp n₁ d L₁ (M + 1) (hpos n₁ L₁) (hb' n₁ L₁ hL₁),
      ← sum_add_distrib, ← sum_add_distrib]
    exact sum_le_sum fun k hk => hterm p k hp (mem_Ico.1 hk).1
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ## The half index -/

/-- For odd `n`, `(6n)! (5n)! n! ∏_{i < 5n} (5n + 2(i+1))` divides `(15n)! (2n)!`. -/
theorem half_odd_dvd (n : ℕ) (hn : ¬ 2 ∣ n) :
    (6 * n).factorial * (5 * n).factorial * n.factorial * apProd (5 * n) 2 (5 * n) ∣
      (15 * n).factorial * (2 * n).factorial := by
  have h := dvd_of_terms₂ [15 * n, 2 * n] [6 * n, 5 * n, n] 0 0 (5 * n) (5 * n) 2 (15 * n)
    (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega) (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        range_zero, filter_empty, card_empty]
      by_cases hp2 : p = 2
      · subst hp2
        rw [card_eq_zero_of_dvd (5 * n) 2 (5 * n) 2 k hk dvd_rfl (by omega), add_zero]
        calc 6 * n / 2 ^ k + (5 * n / 2 ^ k + n / 2 ^ k)
            ≤ 6 * n / 2 ^ k + (5 * n + n) / 2 ^ k :=
              Nat.add_le_add_left (Nat.add_div_le_add_div _ _ _) _
          _ ≤ (6 * n + (5 * n + n)) / 2 ^ k := Nat.add_div_le_add_div _ _ _
          _ ≤ 15 * n / 2 ^ k := Nat.div_le_div_right (by omega)
          _ ≤ 15 * n / 2 ^ k + 2 * n / 2 ^ k := Nat.le_add_right _ _
      · set q := p ^ k with hqdef
        have hq : 0 < q := pow_pos hp.pos k
        have hcop : Nat.Coprime q 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
        obtain ⟨ñ, t, ht⟩ := exists_lift 2 n q (by norm_num) hq hcop.symm
        rw [card_ap_eq 2 5 n q t ñ (5 * n) hcop ht]
        have hmono : 5 * ñ / q ≤ (5 * ñ + 5 * n) / q := Nat.div_le_div_right (by omega)
        have r1 := div_eq_of_eq_add_mul (x := 5 * ñ + 5 * n) (y := 15 * ñ) (t := 5 * t) hq
          (by rw [mul_left_comm q 5 t]; omega)
        have r2 := div_eq_of_eq_add_mul (x := 6 * n) (y := 12 * ñ) (t := 6 * t) hq
          (by rw [mul_left_comm q 6 t]; omega)
        have r3 := div_eq_of_eq_add_mul (x := 5 * n) (y := 10 * ñ) (t := 5 * t) hq
          (by rw [mul_left_comm q 5 t]; omega)
        have r4 := div_eq_of_eq_add_mul (x := n) (y := 2 * ñ) (t := t) hq (by omega)
        have r5 := div_eq_of_eq_add_mul (x := 15 * n) (y := 30 * ñ) (t := 15 * t) hq
          (by rw [mul_left_comm q 15 t]; omega)
        have r6 := div_eq_of_eq_add_mul (x := 2 * n) (y := 4 * ñ) (t := 2 * t) hq
          (by rw [mul_left_comm q 2 t]; omega)
        have hs := term_a ñ q
        omega)
  simpa [mul_assoc, apProd] using h

/-- For `n = 2m`:
`2^(5n) (15n)! (2n)! = (6n)! (5n)! n! ∏_{i<5n} (5n + 2(i+1)) · a(m)`. -/
theorem half_even_eq (m : ℕ) :
    2 ^ (5 * (2 * m)) * (15 * (2 * m)).factorial * (2 * (2 * m)).factorial =
      (6 * (2 * m)).factorial * (5 * (2 * m)).factorial * (2 * m).factorial *
        apProd (5 * (2 * m)) 2 (5 * (2 * m)) * a295456 m := by
  rw [show 5 * (2 * m) = 2 * (5 * m) by ring, apProd_mul_left,
    show 2 * (5 * m) = 10 * m by ring, show 15 * (2 * m) = 30 * m by ring,
    show 2 * (2 * m) = 4 * m by ring, show 6 * (2 * m) = 12 * m by ring]
  have hX := factorial_mul_prod_succ (5 * m) (10 * m)
  rw [show 5 * m + 10 * m = 15 * m by ring] at hX
  have ha := a295456_mul m
  apply Nat.eq_of_mul_eq_mul_left (5 * m).factorial_pos
  calc (5 * m).factorial * (2 ^ (10 * m) * (30 * m).factorial * (4 * m).factorial)
      = 2 ^ (10 * m) * ((30 * m).factorial * (5 * m).factorial * (4 * m).factorial) := by ring
    _ = 2 ^ (10 * m) * ((15 * m).factorial * (12 * m).factorial * (10 * m).factorial *
          (2 * m).factorial * a295456 m) := by rw [ha]
    _ = _ := by rw [← hX]; ring

/-- For every `n`, `(6n)! (5n)! n! ∏_{i<5n} (5n + 2(i+1))` divides `2^(5n) (15n)! (2n)!`. -/
theorem half_exists (n : ℕ) : ∃ c : ℕ,
    2 ^ (5 * n) * (15 * n).factorial * (2 * n).factorial =
      (6 * n).factorial * (5 * n).factorial * n.factorial * apProd (5 * n) 2 (5 * n) * c := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    exact ⟨a295456 m, half_even_eq m⟩
  · obtain ⟨c, hc⟩ := half_odd_dvd n h2
    exact ⟨2 ^ (5 * n) * c, by rw [mul_assoc (2 ^ (5 * n)), hc]; ring⟩

/-- The Gamma bridge for the half index. Suppose
`2^(5n) (15n)! (2n)! = (6n)! (5n)! n! ∏_{i<5n} (5n + 2(i+1)) · c`. Then
`a(n/2) = c`. It uses `Γ(15n/2 + 1) = Γ(5n/2 + 1) ∏_{i<5n} (5n/2 + 1 + i)`. -/
theorem halfRatio_eq {n c : ℕ}
    (hc : 2 ^ (5 * n) * (15 * n).factorial * (2 * n).factorial =
      (6 * n).factorial * (5 * n).factorial * n.factorial * apProd (5 * n) 2 (5 * n) * c) :
    halfRatio n = c := by
  set Q := ∏ i ∈ range (5 * n), (5 * (n : ℝ) / 2 + 1 + i) with hQ
  have hQpos : 0 < Q := prod_pos fun i _ => by positivity
  have hΓ : Real.Gamma (15 * (n : ℝ) / 2 + 1) = Real.Gamma (5 * (n : ℝ) / 2 + 1) * Q := by
    rw [show 15 * (n : ℝ) / 2 + 1 = (5 * (n : ℝ) / 2 + 1) + ((5 * n : ℕ) : ℝ) by
      push_cast; ring, gamma_add_nat _ (by positivity)]
  have hP : (apProd (5 * n) 2 (5 * n) : ℝ) = 2 ^ (5 * n) * Q := by
    rw [apProd_real (5 * n) 2 (5 * n) (by norm_num)]
    push_cast
    rfl
  have hcR : (2 : ℝ) ^ (5 * n) * ((15 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) =
      ((6 * n).factorial : ℝ) * ((5 * n).factorial : ℝ) * (n.factorial : ℝ) *
        (apProd (5 * n) 2 (5 * n) : ℝ) * c := by
    exact_mod_cast hc
  rw [hP] at hcR
  have key : ((15 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) =
      c * Q * (6 * n).factorial * (5 * n).factorial * n.factorial := by
    have h2 : (2 : ℝ) ^ (5 * n) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    linear_combination hcR
  have hG : 0 < Real.Gamma (5 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold halfRatio
  rw [hΓ, div_eq_iff (by positivity),
    show ((15 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ)
      = ((15 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1)
      by ring, key]
  ring

/-! ## The third index -/

/-- For `3 ∤ n`, `(5n)! (4n)! ∏_{i < 2n} (4n + 3(i+1))` divides
`(10n)! ∏_{i < n} (2n + 3(i+1))`. -/
theorem third_dvd (n : ℕ) (hn : ¬ 3 ∣ n) :
    (5 * n).factorial * (4 * n).factorial * apProd (4 * n) 3 (2 * n) ∣
      (10 * n).factorial * apProd (2 * n) 3 n := by
  have h := dvd_of_terms₂ [10 * n] [5 * n, 4 * n] (2 * n) n (4 * n) (2 * n) 3 (10 * n)
    (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega) (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp3 : p = 3
      · subst hp3
        rw [card_eq_zero_of_dvd (4 * n) 3 (2 * n) 3 k hk dvd_rfl (by omega), add_zero]
        calc 5 * n / 3 ^ k + 4 * n / 3 ^ k ≤ (5 * n + 4 * n) / 3 ^ k :=
              Nat.add_div_le_add_div _ _ _
          _ ≤ 10 * n / 3 ^ k := Nat.div_le_div_right (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      · set q := p ^ k with hqdef
        have hq : 0 < q := pow_pos hp.pos k
        have hcop : Nat.Coprime q 3 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
        obtain ⟨ñ, t, ht⟩ := exists_lift 3 n q (by norm_num) hq hcop.symm
        rw [card_ap_eq 3 4 n q t ñ (2 * n) hcop ht, card_ap_eq 3 2 n q t ñ n hcop ht]
        have hmono1 : 4 * ñ / q ≤ (4 * ñ + 2 * n) / q := Nat.div_le_div_right (by omega)
        have hmono2 : 2 * ñ / q ≤ (2 * ñ + n) / q := Nat.div_le_div_right (by omega)
        have r1 := div_eq_of_eq_add_mul (x := 2 * ñ + n) (y := 5 * ñ) (t := t) hq (by omega)
        have r2 := div_eq_of_eq_add_mul (x := 4 * ñ + 2 * n) (y := 10 * ñ) (t := 2 * t) hq
          (by rw [mul_left_comm q 2 t]; omega)
        have r3 := div_eq_of_eq_add_mul (x := 5 * n) (y := 15 * ñ) (t := 5 * t) hq
          (by rw [mul_left_comm q 5 t]; omega)
        have r4 := div_eq_of_eq_add_mul (x := 4 * n) (y := 12 * ñ) (t := 4 * t) hq
          (by rw [mul_left_comm q 4 t]; omega)
        have r5 := div_eq_of_eq_add_mul (x := 10 * n) (y := 30 * ñ) (t := 10 * t) hq
          (by rw [mul_left_comm q 10 t]; omega)
        have hs := term_a ñ q
        omega)
  simpa [mul_assoc] using h

/-- For `n = 3m`:
`3^n (10n)! ∏_{i<n} (2n + 3(i+1)) = (5n)! (4n)! ∏_{i<2n} (4n + 3(i+1)) · a(m)`. -/
theorem third_three_mul_eq (m : ℕ) :
    3 ^ (3 * m) * (10 * (3 * m)).factorial * apProd (2 * (3 * m)) 3 (3 * m) =
      (5 * (3 * m)).factorial * (4 * (3 * m)).factorial *
        apProd (4 * (3 * m)) 3 (2 * (3 * m)) * a295456 m := by
  rw [show 2 * (3 * m) = 3 * (2 * m) by ring, show 4 * (3 * m) = 3 * (4 * m) by ring,
    apProd_mul_left, apProd_mul_left, show 10 * (3 * m) = 30 * m by ring,
    show 5 * (3 * m) = 15 * m by ring, show 3 * (4 * m) = 12 * m by ring,
    show 3 * (2 * m) = 6 * m by ring]
  have hX1 := factorial_mul_prod_succ (2 * m) (3 * m)
  rw [show 2 * m + 3 * m = 5 * m by ring] at hX1
  have hX2 := factorial_mul_prod_succ (4 * m) (6 * m)
  rw [show 4 * m + 6 * m = 10 * m by ring] at hX2
  have ha := a295456_mul m
  apply Nat.eq_of_mul_eq_mul_left (mul_pos (2 * m).factorial_pos (4 * m).factorial_pos)
  calc (2 * m).factorial * (4 * m).factorial *
        (3 ^ (3 * m) * (30 * m).factorial *
          (3 ^ (3 * m) * ∏ i ∈ range (3 * m), (2 * m + i + 1)))
      = 3 ^ (6 * m) * (30 * m).factorial * (4 * m).factorial *
          ((2 * m).factorial * ∏ i ∈ range (3 * m), (2 * m + i + 1)) := by ring
    _ = 3 ^ (6 * m) * ((30 * m).factorial * (5 * m).factorial * (4 * m).factorial) := by
          rw [hX1]; ring
    _ = 3 ^ (6 * m) * ((15 * m).factorial * (12 * m).factorial * (10 * m).factorial *
          (2 * m).factorial * a295456 m) := by rw [ha]
    _ = _ := by rw [← hX2]; ring

/-- For every `n`, `(5n)! (4n)! ∏_{i<2n} (4n + 3(i+1))` divides
`3^n (10n)! ∏_{i<n} (2n + 3(i+1))`. -/
theorem third_exists (n : ℕ) : ∃ c : ℕ,
    3 ^ n * (10 * n).factorial * apProd (2 * n) 3 n =
      (5 * n).factorial * (4 * n).factorial * apProd (4 * n) 3 (2 * n) * c := by
  by_cases h3 : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3
    exact ⟨a295456 m, third_three_mul_eq m⟩
  · obtain ⟨c, hc⟩ := third_dvd n h3
    exact ⟨3 ^ n * c, by rw [mul_assoc (3 ^ n), hc]; ring⟩

/-- The Gamma bridge for the third index. Suppose
`3^n (10n)! ∏_{i<n} (2n + 3(i+1)) = (5n)! (4n)! ∏_{i<2n} (4n + 3(i+1)) · c`. Then
`a(n/3) = c`. It uses `Γ(5n/3 + 1) = Γ(2n/3 + 1) ∏_{i<n} (2n/3 + 1 + i)` and
`Γ(10n/3 + 1) = Γ(4n/3 + 1) ∏_{i<2n} (4n/3 + 1 + i)`. -/
theorem thirdRatio_eq {n c : ℕ}
    (hc : 3 ^ n * (10 * n).factorial * apProd (2 * n) 3 n =
      (5 * n).factorial * (4 * n).factorial * apProd (4 * n) 3 (2 * n) * c) :
    thirdRatio n = c := by
  set Q₁ := ∏ i ∈ range n, (2 * (n : ℝ) / 3 + 1 + i) with hQ₁
  set Q₂ := ∏ i ∈ range (2 * n), (4 * (n : ℝ) / 3 + 1 + i) with hQ₂
  have hQ₁pos : 0 < Q₁ := prod_pos fun i _ => by positivity
  have hQ₂pos : 0 < Q₂ := prod_pos fun i _ => by positivity
  have hΓ₁ : Real.Gamma (5 * (n : ℝ) / 3 + 1) = Real.Gamma (2 * (n : ℝ) / 3 + 1) * Q₁ := by
    rw [show 5 * (n : ℝ) / 3 + 1 = (2 * (n : ℝ) / 3 + 1) + (n : ℝ) by ring,
      gamma_add_nat _ (by positivity)]
  have hΓ₂ : Real.Gamma (10 * (n : ℝ) / 3 + 1) = Real.Gamma (4 * (n : ℝ) / 3 + 1) * Q₂ := by
    rw [show 10 * (n : ℝ) / 3 + 1 = (4 * (n : ℝ) / 3 + 1) + ((2 * n : ℕ) : ℝ) by
      push_cast; ring, gamma_add_nat _ (by positivity)]
  have hP₁ : (apProd (2 * n) 3 n : ℝ) = 3 ^ n * Q₁ := by
    rw [apProd_real (2 * n) 3 n (by norm_num)]
    push_cast
    rfl
  have hP₂ : (apProd (4 * n) 3 (2 * n) : ℝ) = 3 ^ (2 * n) * Q₂ := by
    rw [apProd_real (4 * n) 3 (2 * n) (by norm_num)]
    push_cast
    rfl
  have hcR : (3 : ℝ) ^ n * ((10 * n).factorial : ℝ) * (apProd (2 * n) 3 n : ℝ) =
      ((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * (apProd (4 * n) 3 (2 * n) : ℝ) * c := by
    exact_mod_cast hc
  rw [hP₁, hP₂] at hcR
  have key : ((10 * n).factorial : ℝ) * Q₁ =
      c * Q₂ * (5 * n).factorial * (4 * n).factorial := by
    have h3 : (3 : ℝ) ^ (2 * n) ≠ 0 := by positivity
    apply mul_left_cancel₀ h3
    rw [pow_mul', sq] at hcR ⊢
    linear_combination hcR
  have hG₁ : 0 < Real.Gamma (2 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG₂ : 0 < Real.Gamma (4 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold thirdRatio
  rw [hΓ₁, hΓ₂, div_eq_iff (by positivity)]
  linear_combination Real.Gamma (2 * (n : ℝ) / 3 + 1) * Real.Gamma (4 * (n : ℝ) / 3 + 1) * key

/-- Consistency with the entry: at even `n = 2m` the half-index ratio is `a(m)`. -/
theorem halfRatio_two_mul (m : ℕ) : halfRatio (2 * m) = a295456 m :=
  halfRatio_eq (half_even_eq m)

/-- Consistency with the entry: at `n = 3m` the third-index ratio is `a(m)`. -/
theorem thirdRatio_three_mul (m : ℕ) : thirdRatio (3 * m) = a295456 m :=
  thirdRatio_eq (third_three_mul_eq m)

/-! ## Ground truth -/

example : a295456 0 = 1 := by decide

example : a295456 1 = 168043980 := by decide

/-- `a(1/2) = 15! Γ(7/2) 2! / (Γ(17/2) 6! 5! 1!) = 7168`. -/
theorem halfRatio_one : halfRatio 1 = 7168 := halfRatio_eq (c := 7168) (by decide)

/-- `a(1/3) = 10! Γ(8/3) Γ(7/3) / (5! 4! Γ(13/3) Γ(5/3)) = 270`. -/
theorem thirdRatio_one : thirdRatio 1 = 270 := thirdRatio_eq (c := 270) (by decide)

/-- `a(2/3) = 20! Γ(13/3) Γ(11/3) / (10! 8! Γ(23/3) Γ(7/3)) = 200070`. -/
theorem thirdRatio_two : thirdRatio 2 = 200070 := thirdRatio_eq (c := 200070) (by decide)

/-! ## The conjecture -/

/-- **Bala's conjecture, first half (A295456, Peter Bala, Jun 13 2026).** For every
`n ≥ 0`, `a(n/2) = (15n)! (5n/2)! (2n)! / ((15n/2)! (6n)! (5n)! n!)` is a natural
number, with `x! := Γ(x + 1)`. -/
theorem halfRatio_integral (n : ℕ) : ∃ k : ℕ, halfRatio n = k := by
  obtain ⟨c, hc⟩ := half_exists n
  exact ⟨c, halfRatio_eq hc⟩

/-- **Bala's conjecture, second half (A295456, Peter Bala, Jun 13 2026).** For every
`n ≥ 0`, `a(n/3) = (10n)! (5n/3)! (4n/3)! / ((5n)! (4n)! (10n/3)! (2n/3)!)` is a
natural number, with `x! := Γ(x + 1)`. -/
theorem thirdRatio_integral (n : ℕ) : ∃ k : ℕ, thirdRatio n = k := by
  obtain ⟨c, hc⟩ := third_exists n
  exact ⟨c, thirdRatio_eq hc⟩

/-- **Bala's conjecture (A295456, Peter Bala, Jun 13 2026).** Verbatim:
"Conjecture: for n >= 0, both a(n/2) = (15*n)!*(5*n/2)!*(2*n)! /
((15*n/2)!*(6*n)!*(5*n)!*n!) and a(n/3) = (10*n)!*(5*n/3)!*(4*n/3)! /
((5*n)!*(4*n)!*(10*n/3)!*(2*n/3)!) are integers, where fractional factorials are
defined using the Gamma function; for example (5*n/2)! := Gamma(5*n/2 + 1)."
Both ratios are natural numbers, for every `n`. -/
theorem bala_both (n : ℕ) : (∃ k : ℕ, halfRatio n = k) ∧ (∃ k : ℕ, thirdRatio n = k) :=
  ⟨halfRatio_integral n, thirdRatio_integral n⟩

end Candidates.A295456BalaBoth
