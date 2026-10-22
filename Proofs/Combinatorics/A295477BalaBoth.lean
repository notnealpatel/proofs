/-
# A295477 — integrality at half and quarter indices

Peter Bala (OEIS A295477, Jul 31 2026) conjectured that both `a(n/2)`
and `a(n/4)` are integral for every natural `n`, where
`a(n) = (24n)! n! / ((12n)! (8n)! (5n)!)` and `x! = Γ(x+1)`.
Chai Wah Wu (Feb 16 2026) also gave binomial-quotient formulas for `a(n)`.

* Gamma is removed by the Pochhammer identity `Γ(x + k) = Γ(x) ∏_{i<k} (x + i)`:
  `a(n/2) = 2^(2n) (12n)! / ((6n)! (4n)! ∏_{i<2n} (n + 2(i+1)))` and
  `a(n/4) = 4^n (6n)! / ((3n)! (2n)! ∏_{i<n} (n + 4(i+1)))`.
* Half index, `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion.
* Half index, `n` odd: `2` divides no progression term. For every other prime
  power `q`, choose `ñ` with `2ñ ≡ n (mod q)`. The number of multiples of `q`
  among the progression terms is an exact Legendre difference in `ñ`, and the
  term inequality becomes Landau's inequality for `a` at `ñ / q`:
  `⌊12y⌋ + ⌊8y⌋ + ⌊5y⌋ ≤ ⌊24y⌋ + ⌊y⌋`.
* Quarter index, `n` odd: the same argument with `4ñ ≡ n (mod q)`.
* Quarter index, `n = 2m`: `∏_{i<2m} (2m + 4(i+1)) = 2^(2m) ∏_{i<2m} (m + 2(i+1))`,
  so `a(2m/4) = a(m/2)`, which is the half-index case.
-/
import Mathlib
import Combinatorics.A295437BalaJunBoth

set_option autoImplicit false

namespace Candidates.A295477BalaBoth

open Finset
open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq)
open Candidates.A295437BalaJunBoth (apProd dvd_of_terms gamma_add_nat apProd_real
  factorial_mul_prod_succ apProd_mul_left card_eq_zero_of_dvd)

/-! ## Definitions -/

/-- The OEIS sequence A295477:
`a(n) = (24n)! n! / ((12n)! (8n)! (5n)!)`. The truncating `Nat` division is
exact; see `a295477_mul`. -/
def a295477 (n : ℕ) : ℕ :=
  (24 * n).factorial * n.factorial /
    ((12 * n).factorial * (8 * n).factorial * (5 * n).factorial)

/-- Bala's half-index value
`a(n/2) = (12n)! (n/2)! / ((6n)! (4n)! (5n/2)!)`, with `x! := Γ(x + 1)`.
The denominator is positive (Gamma is positive on `(0, ∞)`), so the real division
never takes its junk value. -/
noncomputable def halfRatio (n : ℕ) : ℝ :=
  ((12 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((6 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1))

/-- Bala's quarter-index value
`a(n/4) = (6n)! (n/4)! / ((3n)! (2n)! (5n/4)!)`, with `x! := Γ(x + 1)`.
The denominator is positive. -/
noncomputable def quarterRatio (n : ℕ) : ℝ :=
  ((6 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 4 + 1) /
    (((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 4 + 1))

/-! ## Landau's inequality for A295477 -/

/-- Landau's step inequality for A295477 in `j = ⌊120y⌋`:
`⌊12y⌋ + ⌊8y⌋ + ⌊5y⌋ ≤ ⌊24y⌋ + ⌊y⌋`. -/
theorem step_a (j : ℕ) : j / 10 + j / 15 + j / 24 ≤ j / 5 + j / 120 := by
  -- The defect is `120`-periodic; reduce to `j = 120a + r` and check each residue `r`.
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r : ℕ, r < 120 ∧ j = 120 * a + r :=
    ⟨j / 120, j % 120, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 120).symm⟩
  interval_cases r <;> omega

/-- Landau's term inequality for A295477, valid for every `m` and `q`:
`⌊12m/q⌋ + ⌊8m/q⌋ + ⌊5m/q⌋ ≤ ⌊24m/q⌋ + ⌊m/q⌋`. -/
theorem term_a (m q : ℕ) :
    12 * m / q + 8 * m / q + 5 * m / q ≤ 24 * m / q + 1 * m / q := by
  have hs := step_a (120 * m / q)
  rw [div_div_eq_of_mul_eq 120 m q 12 10 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 8 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 5 24 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 24 5 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 1 120 1 (by norm_num) (by norm_num) (by norm_num)] at hs
  simpa only [one_mul] using hs

/-- Integrality of A295477: `(12m)! (8m)! (5m)!` divides `(24m)! m!`. -/
theorem factorial_dvd_a295477 (m : ℕ) :
    (12 * m).factorial * (8 * m).factorial * (5 * m).factorial ∣
      (24 * m).factorial * m.factorial := by
  have h := landau_list [24 * m, m] [12 * m, 8 * m, 5 * m] (24 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have hs := term_a m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        one_mul] at hs ⊢
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295477`. -/
theorem a295477_mul (m : ℕ) :
    (12 * m).factorial * (8 * m).factorial * (5 * m).factorial * a295477 m =
      (24 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295477 m)

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

/-- Exact count of multiples of `q` in the progression `n + d(i+1)`, `i < L`. If
`q` is coprime to `d` and `d ñ = n + q t`, it equals `⌊(ñ+L)/q⌋ - ⌊ñ/q⌋`. -/
theorem card_ap_eq (d n q t ñ L : ℕ) (hcop : Nat.Coprime q d) (h : d * ñ = n + q * t) :
    #{i ∈ range L | q ∣ n + d * (i + 1)} = (ñ + L) / q - ñ / q := by
  rw [← card_dvd_add_succ]
  congr 1
  refine filter_congr fun i _ => ?_
  have key : d * (ñ + i + 1) = (n + d * (i + 1)) + q * t := by
    calc d * (ñ + i + 1) = d * ñ + d * (i + 1) := by ring
      _ = _ := by rw [h]; ring
  constructor
  · intro hq
    apply hcop.dvd_of_dvd_mul_left
    rw [key]
    exact dvd_add hq (dvd_mul_right _ _)
  · intro hq
    have hdq : q ∣ d * (ñ + i + 1) := dvd_mul_of_dvd_right hq _
    rw [key] at hdq
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).1 hdq

/-- `(x + q t)/q = x/q + t`, in the orientation used below. -/
theorem div_eq_of_eq_add_mul {x y q t : ℕ} (hq : 0 < q) (h : y = x + q * t) :
    y / q = x / q + t := by
  rw [h, Nat.add_mul_div_left _ _ hq]

/-! ## The odd cases -/

/-- For odd `n`, `(6n)! (4n)! ∏_{i < 2n} (n + 2(i+1))` divides `(12n)!`. -/
theorem half_odd_dvd (n : ℕ) (hn : ¬ 2 ∣ n) :
    (6 * n).factorial * (4 * n).factorial * apProd n 2 (2 * n) ∣ (12 * n).factorial := by
  have h := dvd_of_terms [12 * n] [6 * n, 4 * n] n 2 (2 * n) (12 * n) (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp2 : p = 2
      · subst hp2
        rw [card_eq_zero_of_dvd n 2 (2 * n) 2 k hk dvd_rfl hn, add_zero]
        calc 6 * n / 2 ^ k + 4 * n / 2 ^ k ≤ (6 * n + 4 * n) / 2 ^ k :=
              Nat.add_div_le_add_div _ _ _
          _ ≤ 12 * n / 2 ^ k := Nat.div_le_div_right (by omega)
      · set q := p ^ k with hqdef
        have hq : 0 < q := pow_pos hp.pos k
        have hcop : Nat.Coprime q 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
        obtain ⟨ñ, t, ht⟩ := exists_lift 2 n q (by norm_num) hq hcop.symm
        rw [card_ap_eq 2 n q t ñ (2 * n) hcop ht]
        have hmono : ñ / q ≤ (ñ + 2 * n) / q := Nat.div_le_div_right (by omega)
        have r1 := div_eq_of_eq_add_mul (x := ñ + 2 * n) (y := 5 * ñ) (t := 2 * t) hq
          (by rw [mul_left_comm q 2 t]; omega)
        have r2 := div_eq_of_eq_add_mul (x := 6 * n) (y := 12 * ñ) (t := 6 * t) hq
          (by rw [mul_left_comm q 6 t]; omega)
        have r3 := div_eq_of_eq_add_mul (x := 4 * n) (y := 8 * ñ) (t := 4 * t) hq
          (by rw [mul_left_comm q 4 t]; omega)
        have r4 := div_eq_of_eq_add_mul (x := 12 * n) (y := 24 * ñ) (t := 12 * t) hq
          (by rw [mul_left_comm q 12 t]; omega)
        have hs := term_a ñ q
        rw [one_mul] at hs
        omega)
  simpa [mul_assoc] using h

/-- For odd `n`, `(3n)! (2n)! ∏_{i < n} (n + 4(i+1))` divides `(6n)!`. -/
theorem quarter_odd_dvd (n : ℕ) (hn : ¬ 2 ∣ n) :
    (3 * n).factorial * (2 * n).factorial * apProd n 4 n ∣ (6 * n).factorial := by
  have h := dvd_of_terms [6 * n] [3 * n, 2 * n] n 4 n (6 * n) (by norm_num)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (by omega)
    (fun p k hp hk => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases hp2 : p = 2
      · subst hp2
        rw [card_eq_zero_of_dvd n 4 n 2 k hk (by norm_num) hn, add_zero]
        calc 3 * n / 2 ^ k + 2 * n / 2 ^ k ≤ (3 * n + 2 * n) / 2 ^ k :=
              Nat.add_div_le_add_div _ _ _
          _ ≤ 6 * n / 2 ^ k := Nat.div_le_div_right (by omega)
      · set q := p ^ k with hqdef
        have hq : 0 < q := pow_pos hp.pos k
        have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
        have hcop4 : Nat.Coprime p 4 := by
          simpa using Nat.Coprime.pow_right 2 hcop2
        have hcop : Nat.Coprime q 4 := Nat.Coprime.pow_left k hcop4
        obtain ⟨ñ, t, ht⟩ := exists_lift 4 n q (by norm_num) hq hcop.symm
        rw [card_ap_eq 4 n q t ñ n hcop ht]
        have hmono : ñ / q ≤ (ñ + n) / q := Nat.div_le_div_right (by omega)
        have r1 := div_eq_of_eq_add_mul (x := ñ + n) (y := 5 * ñ) (t := t) hq (by omega)
        have r2 := div_eq_of_eq_add_mul (x := 3 * n) (y := 12 * ñ) (t := 3 * t) hq
          (by rw [mul_left_comm q 3 t]; omega)
        have r3 := div_eq_of_eq_add_mul (x := 2 * n) (y := 8 * ñ) (t := 2 * t) hq
          (by rw [mul_left_comm q 2 t]; omega)
        have r4 := div_eq_of_eq_add_mul (x := 6 * n) (y := 24 * ñ) (t := 6 * t) hq
          (by rw [mul_left_comm q 6 t]; omega)
        have hs := term_a ñ q
        rw [one_mul] at hs
        omega)
  simpa [mul_assoc] using h

/-! ## The even cases -/

/-- For `n = 2m`: `2^(2n) (12n)! = (6n)! (4n)! ∏_{i<2n} (n + 2(i+1)) · a(m)`. -/
theorem half_even_eq (m : ℕ) :
    2 ^ (2 * (2 * m)) * (12 * (2 * m)).factorial =
      (6 * (2 * m)).factorial * (4 * (2 * m)).factorial *
        apProd (2 * m) 2 (2 * (2 * m)) * a295477 m := by
  rw [show 2 * (2 * m) = 4 * m by ring, apProd_mul_left,
    show 12 * (2 * m) = 24 * m by ring, show 6 * (2 * m) = 12 * m by ring,
    show 4 * (2 * m) = 8 * m by ring]
  have hX := factorial_mul_prod_succ m (4 * m)
  rw [show m + 4 * m = 5 * m by ring] at hX
  have ha := a295477_mul m
  apply Nat.eq_of_mul_eq_mul_left m.factorial_pos
  calc m.factorial * (2 ^ (4 * m) * (24 * m).factorial)
      = 2 ^ (4 * m) * ((24 * m).factorial * m.factorial) := by ring
    _ = 2 ^ (4 * m) * ((12 * m).factorial * (8 * m).factorial * (5 * m).factorial *
          a295477 m) := by rw [ha]
    _ = _ := by rw [← hX]; ring

/-- For every `n`, `(6n)! (4n)! ∏_{i<2n} (n + 2(i+1))` divides `2^(2n) (12n)!`. -/
theorem half_exists (n : ℕ) : ∃ c : ℕ,
    2 ^ (2 * n) * (12 * n).factorial =
      (6 * n).factorial * (4 * n).factorial * apProd n 2 (2 * n) * c := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    exact ⟨a295477 m, half_even_eq m⟩
  · obtain ⟨c, hc⟩ := half_odd_dvd n h2
    exact ⟨2 ^ (2 * n) * c, by rw [hc]; ring⟩

/-- Halving the progression: `∏_{i<L} (2m + 4(i+1)) = 2^L ∏_{i<L} (m + 2(i+1))`. -/
theorem apProd_two_mul (m L : ℕ) : apProd (2 * m) 4 L = 2 ^ L * apProd m 2 L := by
  unfold apProd
  rw [show 2 ^ L = ∏ _i ∈ range L, 2 by simp, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by ring

/-- The quarter-index identity at `n = 2m` follows from the half-index identity at `m`
with the same cofactor `c`. -/
theorem quarter_of_half {m c : ℕ}
    (hc : 2 ^ (2 * m) * (12 * m).factorial =
      (6 * m).factorial * (4 * m).factorial * apProd m 2 (2 * m) * c) :
    4 ^ (2 * m) * (6 * (2 * m)).factorial =
      (3 * (2 * m)).factorial * (2 * (2 * m)).factorial * apProd (2 * m) 4 (2 * m) * c := by
  rw [apProd_two_mul, show 6 * (2 * m) = 12 * m by ring, show 3 * (2 * m) = 6 * m by ring,
    show 2 * (2 * m) = 4 * m by ring,
    show (4 : ℕ) ^ (2 * m) = 2 ^ (2 * m) * 2 ^ (2 * m) by rw [← mul_pow]; norm_num]
  calc 2 ^ (2 * m) * 2 ^ (2 * m) * (12 * m).factorial
      = 2 ^ (2 * m) * (2 ^ (2 * m) * (12 * m).factorial) := by ring
    _ = _ := by rw [hc]; ring

/-- For every `n`, `(3n)! (2n)! ∏_{i<n} (n + 4(i+1))` divides `4^n (6n)!`. -/
theorem quarter_exists (n : ℕ) : ∃ c : ℕ,
    4 ^ n * (6 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 4 n * c := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    obtain ⟨c, hc⟩ := half_exists m
    exact ⟨c, quarter_of_half hc⟩
  · obtain ⟨c, hc⟩ := quarter_odd_dvd n h2
    exact ⟨4 ^ n * c, by rw [hc]; ring⟩

/-! ## The Gamma bridges -/

/-- The Gamma bridge for the half index. Suppose
`2^(2n) (12n)! = (6n)! (4n)! ∏_{i<2n} (n + 2(i+1)) · c`. Then `a(n/2) = c`.
It uses `Γ(5n/2 + 1) = Γ(n/2 + 1) ∏_{i<2n} (n/2 + 1 + i)`. -/
theorem halfRatio_eq {n c : ℕ}
    (hc : 2 ^ (2 * n) * (12 * n).factorial =
      (6 * n).factorial * (4 * n).factorial * apProd n 2 (2 * n) * c) :
    halfRatio n = c := by
  set Q := ∏ i ∈ range (2 * n), ((n : ℝ) / 2 + 1 + i) with hQ
  have hQpos : 0 < Q := prod_pos fun i _ => by positivity
  have hΓ : Real.Gamma (5 * (n : ℝ) / 2 + 1) = Real.Gamma ((n : ℝ) / 2 + 1) * Q := by
    rw [show 5 * (n : ℝ) / 2 + 1 = ((n : ℝ) / 2 + 1) + ((2 * n : ℕ) : ℝ) by
      push_cast; ring, gamma_add_nat _ (by positivity)]
  have hP : (apProd n 2 (2 * n) : ℝ) = 2 ^ (2 * n) * Q := by
    rw [apProd_real n 2 (2 * n) (by norm_num)]
    push_cast
    rfl
  have hcR : (2 : ℝ) ^ (2 * n) * ((12 * n).factorial : ℝ) =
      ((6 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * (apProd n 2 (2 * n) : ℝ) * c := by
    exact_mod_cast hc
  rw [hP] at hcR
  have key : ((12 * n).factorial : ℝ) = c * Q * (6 * n).factorial * (4 * n).factorial := by
    have h2 : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    linear_combination hcR
  have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold halfRatio
  rw [hΓ, div_eq_iff (by positivity), key]
  ring

/-- The Gamma bridge for the quarter index. Suppose
`4^n (6n)! = (3n)! (2n)! ∏_{i<n} (n + 4(i+1)) · c`. Then `a(n/4) = c`.
It uses `Γ(5n/4 + 1) = Γ(n/4 + 1) ∏_{i<n} (n/4 + 1 + i)`. -/
theorem quarterRatio_eq {n c : ℕ}
    (hc : 4 ^ n * (6 * n).factorial =
      (3 * n).factorial * (2 * n).factorial * apProd n 4 n * c) :
    quarterRatio n = c := by
  set Q := ∏ i ∈ range n, ((n : ℝ) / 4 + 1 + i) with hQ
  have hQpos : 0 < Q := prod_pos fun i _ => by positivity
  have hΓ : Real.Gamma (5 * (n : ℝ) / 4 + 1) = Real.Gamma ((n : ℝ) / 4 + 1) * Q := by
    rw [show 5 * (n : ℝ) / 4 + 1 = ((n : ℝ) / 4 + 1) + (n : ℝ) by ring,
      gamma_add_nat _ (by positivity)]
  have hP : (apProd n 4 n : ℝ) = 4 ^ n * Q := by
    rw [apProd_real n 4 n (by norm_num)]
    push_cast
    rfl
  have hcR : (4 : ℝ) ^ n * ((6 * n).factorial : ℝ) =
      ((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * (apProd n 4 n : ℝ) * c := by
    exact_mod_cast hc
  rw [hP] at hcR
  have key : ((6 * n).factorial : ℝ) = c * Q * (3 * n).factorial * (2 * n).factorial := by
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    apply mul_left_cancel₀ h4
    linear_combination hcR
  have hG : 0 < Real.Gamma ((n : ℝ) / 4 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold quarterRatio
  rw [hΓ, div_eq_iff (by positivity), key]
  ring

/-- Consistency with the entry: at even `n = 2m` the half-index ratio is `a(m)`. -/
theorem halfRatio_two_mul (m : ℕ) : halfRatio (2 * m) = a295477 m :=
  halfRatio_eq (half_even_eq m)

/-- At even `n = 2m` the quarter-index ratio is the half-index ratio at `m`:
`a(2m/4) = a(m/2)`. -/
theorem quarterRatio_two_mul (m : ℕ) : quarterRatio (2 * m) = halfRatio m := by
  obtain ⟨c, hc⟩ := half_exists m
  rw [quarterRatio_eq (quarter_of_half hc), halfRatio_eq hc]

/-- Consistency with the entry: at `n = 4m` the quarter-index ratio is `a(m)`. -/
theorem quarterRatio_four_mul (m : ℕ) : quarterRatio (4 * m) = a295477 m := by
  rw [show 4 * m = 2 * (2 * m) by ring, quarterRatio_two_mul, halfRatio_two_mul]

/-! ## Examples -/

example : a295477 0 = 1 := by decide

example : a295477 1 = 267711444 := by decide

/-- `a(1/2) = 12! Γ(3/2) / (6! 4! Γ(7/2)) = 7392`. -/
theorem halfRatio_one : halfRatio 1 = 7392 := halfRatio_eq (c := 7392) (by decide)

/-- `a(1/4) = 6! Γ(5/4) / (3! 2! Γ(9/4)) = 48`. -/
theorem quarterRatio_one : quarterRatio 1 = 48 := quarterRatio_eq (c := 48) (by decide)

/-- `a(3/4) = 18! Γ(7/4) / (9! 6! Γ(19/4)) = 1357824`. -/
theorem quarterRatio_three : quarterRatio 3 = 1357824 :=
  quarterRatio_eq (c := 1357824) (by decide)

/-- `a(2/2) = a(1) = 267711444`, the second listed term. -/
example : halfRatio 2 = 267711444 := by
  rw [show (2 : ℕ) = 2 * 1 by norm_num, halfRatio_two_mul,
    show a295477 1 = 267711444 by decide]
  norm_num

/-- `a(2/4) = a(1/2) = 7392`. -/
example : quarterRatio 2 = 7392 := by
  rw [show (2 : ℕ) = 2 * 1 by norm_num, quarterRatio_two_mul, halfRatio_one]

/-! ## The conjecture -/

/-- **Bala's conjecture, first half (A295477, Peter Bala, Jul 31 2026).** For every
`n ≥ 0`, `a(n/2) = (12n)! (n/2)! / ((6n)! (4n)! (5n/2)!)` is a natural number, with
`x! := Γ(x + 1)`. -/
theorem halfRatio_integral (n : ℕ) : ∃ k : ℕ, halfRatio n = k := by
  obtain ⟨c, hc⟩ := half_exists n
  exact ⟨c, halfRatio_eq hc⟩

/-- **Bala's conjecture, second half (A295477, Peter Bala, Jul 31 2026).** For every
`n ≥ 0`, `a(n/4) = (6n)! (n/4)! / ((3n)! (2n)! (5n/4)!)` is a natural number, with
`x! := Γ(x + 1)`. -/
theorem quarterRatio_integral (n : ℕ) : ∃ k : ℕ, quarterRatio n = k := by
  obtain ⟨c, hc⟩ := quarter_exists n
  exact ⟨c, quarterRatio_eq hc⟩

/-- Bala's conjecture (OEIS A295477, Peter Bala, Jul 31 2026):
both `a(n/2)` and `a(n/4)` are natural numbers for every natural `n`,
with fractional factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_both (n : ℕ) : (∃ k : ℕ, halfRatio n = k) ∧ (∃ k : ℕ, quarterRatio n = k) :=
  ⟨halfRatio_integral n, quarterRatio_integral n⟩

end Candidates.A295477BalaBoth
