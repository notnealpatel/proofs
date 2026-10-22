/-
# A295445 — integrality of `(6n)! (2n/3)! / ((3n)! (2n)! (5n/3)!)` (= A364175)

## OEIS source (pulled with `oeis show A295445` and `oeis show A364175`, retrieved 2026-10-21)

```
A295445
NAME:     a(n) = (18*n)!*(2*n)!/((9*n)!*(6*n)!*(5*n)!).
TERMS:    1,408408,802241960520,1823169705017624880,...
COMMENT (the conjecture):
  Conjecture: for n >= 0, a(n/3) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!) is
  an integer, where fractional factorials are defined using the Gamma function;
  for example, (2*n/3)! := Gamma(2*n/3 + 1). See A364175. - _Peter Bala_,
  Jun 13 2026
FORMULA:
  a(n) = binomial(18*n,9*n)*binomial(9*n,3*n)/binomial(5*n,2*n) = ...
  - _Chai Wah Wu_, Feb 15 2026

A364175
NAME:     a(n) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!).
TERMS:    1,36,3564,408408,49697388,6249195036,802241960520,104466877291260,
          13746018177013356,1823169705017624880,...
COMMENTS: This sequence is only conjecturally an integer sequence.
          The integrality conjecture is true. See Links.
          - _David Radcliffe_, Jul 19 2026
FORMULA:  a(n) = 3^n * (6*n)!/((3*n)!*(2*n)!) * 1/P where
          P = Product_{k = 1..n} (2*n + 3*k). - _Peter Bala_, Jun 14 2026
```

## Status (triage)

Proved elsewhere: D. G. Radcliffe, "Integrality of a Ratio of Fractional
Factorials" (OEIS A364175 link, Jul 19 2026).  The A295445 entry still states
it as a conjecture.  Re-validated here: `3^n (6n)!` is divisible by
`(3n)! (2n)! ∏_{k=1}^n (2n+3k)` for every `n ≤ 600`, with the quotients matching
the listed A364175 terms.

## Proof (kernel-checked below, following Radcliffe)

* Gamma recurrence: `Γ(5n/3+1) = Γ(2n/3+1) ∏_{j=1}^n (2n/3+j)`, so the ratio is
  `3^n (6n)! / ((3n)! (2n)! P n)` with `P n = ∏_{k=1}^n (2n+3k)`.
* Prime `p ≠ 3`: Legendre, plus the per-`q = p^k` floor inequality
  `#{j ≤ n : q ∣ 2n+3j} + ⌊3n/q⌋ + ⌊2n/q⌋ ≤ ⌊6n/q⌋` for `q` coprime to `3`.
* `p = 3`, `3 ∤ n`: no factor `2n+3k` is divisible by `3`.
* `3 ∣ n`: reduction to Vasyunin's ratio `(18m)!(2m)!/((9m)!(6m)!(5m)!)`,
  integral by Landau's criterion.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A295445Conj

open Finset Nat

/-! ## Definition layer -/

/-- Bala's product `P n = ∏_{k=1}^{n} (2n + 3k)` from the A364175 formula line. -/
def P (n : ℕ) : ℕ := ∏ j ∈ Icc 1 n, (2 * n + 3 * j)

/-- A364175 via Bala's formula `a(n) = 3^n (6n)! / ((3n)! (2n)! P n)` (natural-number
division; `gamma_ratio_eq` and `a364175_divisible` show it is exact and equals the
Gamma-function definition). -/
def a364175 (n : ℕ) : ℕ := 3 ^ n * (6 * n)! / ((3 * n)! * (2 * n)! * P n)

/-- A295445 as named in the entry: `a(n) = (18n)! (2n)! / ((9n)! (6n)! (5n)!)`. -/
def a295445 (n : ℕ) : ℕ := (18 * n)! * (2 * n)! / ((9 * n)! * (6 * n)! * (5 * n)!)

example : P 2 = 7 * 10 := by decide

example : [0, 1, 2, 3, 4, 5, 6, 7, 8].map a364175 =
    [1, 36, 3564, 408408, 49697388, 6249195036, 802241960520, 104466877291260,
      13746018177013356] := by decide

example : [0, 1, 2].map a295445 = [1, 408408, 802241960520] := by decide

/-! ## Local floor inequalities -/

/-- Scaling trick: `⌊a/q⌋ = ⌊⌊ac/q⌋/c⌋` for `c > 0`. -/
theorem div_scale (a c q : ℕ) (hc : 0 < c) : a / q = a * c / q / c := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ hc]

/-- Block count: for `q > 0` coprime to `3`, the number of `j ∈ [1, n]` with
`q ∣ 2n + 3j` is at most `⌊n/q⌋`, plus one only when `q ≤ 6 (n mod q)`. -/
theorem card_le (q n : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q 3) :
    #{j ∈ Icc 1 n | q ∣ 2 * n + 3 * j} ≤ n / q + (if q ≤ 6 * (n % q) then 1 else 0) := by
  set t := n / q with ht
  set r := n % q with hr
  have hn : n = q * t + r := (Nat.div_add_mod n q).symm
  have hrq : r < q := Nat.mod_lt n hq
  set e := (if q ≤ 6 * r then 1 else 0) with he
  calc #{j ∈ Icc 1 n | q ∣ 2 * n + 3 * j} ≤ #(range (t + e)) := by
        refine card_le_card_of_injOn (fun j => (j - 1) / q) ?_ ?_
        · intro j hj
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj
          obtain ⟨⟨hj1, hjn⟩, hjd⟩ := hj
          simp only [coe_range, Set.mem_Iio]
          have hle : (j - 1) / q ≤ t := Nat.div_le_div_right (by omega)
          by_cases htop : t ≤ (j - 1) / q
          · have hqt : q * t ≤ j - 1 := by
              rw [Nat.le_div_iff_mul_le hq] at htop
              linarith [mul_comm q t]
            obtain ⟨s, hs⟩ : ∃ s, j = q * t + s := ⟨j - q * t, by omega⟩
            have hs1 : 1 ≤ s := by omega
            have hsr : s ≤ r := by omega
            have hd : q ∣ q * (5 * t) + (2 * r + 3 * s) := by
              have h1 : 2 * n + 3 * j = q * (5 * t) + (2 * r + 3 * s) := by rw [hs, hn]; ring
              rwa [h1] at hjd
            replace hd : q ∣ 2 * r + 3 * s :=
              (Nat.dvd_add_right (dvd_mul_right q (5 * t))).mp hd
            have h6 : q ≤ 6 * r := by
              have hq5 := Nat.le_of_dvd (by omega) hd
              omega
            have he1 : e = 1 := if_pos h6
            omega
          · omega
        · intro j1 hj1 j2 hj2 hdiv
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj1 hj2
          obtain ⟨⟨hj11, -⟩, hjd1⟩ := hj1
          obtain ⟨⟨hj21, -⟩, hjd2⟩ := hj2
          have hmod : 2 * n + 3 * j1 ≡ 2 * n + 3 * j2 [MOD q] :=
            (Nat.modEq_zero_iff_dvd.mpr hjd1).trans (Nat.modEq_zero_iff_dvd.mpr hjd2).symm
          have h3 : 3 * j1 ≡ 3 * j2 [MOD q] := Nat.ModEq.add_left_cancel' _ hmod
          have hj : j1 ≡ j2 [MOD q] := Nat.ModEq.cancel_left_of_coprime hcop h3
          have hj' : j1 - 1 ≡ j2 - 1 [MOD q] := by
            refine Nat.ModEq.add_right_cancel' 1 ?_
            rwa [Nat.sub_add_cancel hj11, Nat.sub_add_cancel hj21]
          have e1 := Nat.div_add_mod (j1 - 1) q
          have e2 := Nat.div_add_mod (j2 - 1) q
          simp only at hdiv
          rw [hdiv, hj'] at e1
          omega
    _ = t + e := card_range _

/-- Radcliffe's Lemma 1: for `q > 0` coprime to `3`,
`#{j ∈ [1, n] : q ∣ 2n + 3j} + ⌊3n/q⌋ + ⌊2n/q⌋ ≤ ⌊6n/q⌋`. -/
theorem local_ineq (q n : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q 3) :
    #{j ∈ Icc 1 n | q ∣ 2 * n + 3 * j} + 3 * n / q + 2 * n / q ≤ 6 * n / q := by
  have hcard := card_le q n hq hcop
  set t := n / q with ht
  set r := n % q with hr
  have hn : n = q * t + r := (Nat.div_add_mod n q).symm
  have hrq : r < q := Nat.mod_lt n hq
  have h6 : 6 * n / q = 6 * t + 6 * r / q := by
    rw [hn, show 6 * (q * t + r) = q * (6 * t) + 6 * r by ring, Nat.mul_add_div hq]
  have h3 : 3 * n / q = 3 * t + 6 * r / q / 2 := by
    rw [hn, show 3 * (q * t + r) = q * (3 * t) + 3 * r by ring, Nat.mul_add_div hq,
      div_scale (3 * r) 2 q (by norm_num), show 3 * r * 2 = 6 * r by ring]
  have h2 : 2 * n / q = 2 * t + 6 * r / q / 3 := by
    rw [hn, show 2 * (q * t + r) = q * (2 * t) + 2 * r by ring, Nat.mul_add_div hq,
      div_scale (2 * r) 3 q (by norm_num), show 2 * r * 3 = 6 * r by ring]
  have hu : 6 * r / q < 6 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  rw [h6, h3, h2]
  by_cases hbig : q ≤ 6 * r
  · rw [if_pos hbig] at hcard
    have hu1 : 1 ≤ 6 * r / q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
    omega
  · rw [if_neg hbig] at hcard
    have hu0 : 6 * r / q = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- Landau's floor inequality for Vasyunin's ratio:
`⌊9m/q⌋ + ⌊6m/q⌋ + ⌊5m/q⌋ ≤ ⌊18m/q⌋ + ⌊2m/q⌋` for every `q`. -/
theorem vasyunin_ineq (q m : ℕ) :
    9 * m / q + 6 * m / q + 5 * m / q ≤ 18 * m / q + 2 * m / q := by
  rw [div_scale (9 * m) 10 q (by norm_num), div_scale (6 * m) 15 q (by norm_num),
    div_scale (5 * m) 18 q (by norm_num), div_scale (18 * m) 5 q (by norm_num),
    div_scale (2 * m) 45 q (by norm_num),
    show 9 * m * 10 = 90 * m by ring, show 6 * m * 15 = 90 * m by ring,
    show 5 * m * 18 = 90 * m by ring, show 18 * m * 5 = 90 * m by ring,
    show 2 * m * 45 = 90 * m by ring]
  omega

/-! ## Valuations -/

/-- `log_p y < b` whenever `y < b` and `p > 1`. -/
theorem log_lt_of_lt {p y b : ℕ} (hp : 1 < p) (hyb : y < b) : Nat.log p y < b := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simpa using (show 0 < b by omega)
  · exact Nat.log_lt_of_lt_pow hy.ne' (hyb.trans (Nat.lt_pow_self hp))

/-- Bala's product is nonzero. -/
theorem P_ne_zero (n : ℕ) : P n ≠ 0 := by
  unfold P
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  simp only [mem_Icc] at hj
  omega

/-- Legendre-type formula for `P n`: `v_p(P n) = ∑_{k ∈ [1, b)} #{j ∈ [1, n] : p^k ∣ 2n+3j}`
for any `b > 5n`. -/
theorem factorization_P {p : ℕ} (hp : p.Prime) (n b : ℕ) (hb : 5 * n < b) :
    (P n).factorization p = ∑ k ∈ Ico 1 b, #{j ∈ Icc 1 n | p ^ k ∣ 2 * n + 3 * j} := by
  unfold P
  rw [Nat.factorization_prod (fun j hj => by simp only [mem_Icc] at hj; omega),
    Finset.sum_apply']
  have hterm : ∀ j ∈ Icc 1 n, (2 * n + 3 * j).factorization p
      = ∑ k ∈ Ico 1 b, if p ^ k ∣ 2 * n + 3 * j then 1 else 0 := by
    intro j hj
    simp only [mem_Icc] at hj
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
      ((show 2 * n + 3 * j < b by omega).trans (Nat.lt_pow_self hp.one_lt)), card_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [card_filter]

/-- For a prime `p ≠ 3`, `v_p((3n)! (2n)! P n) ≤ v_p(3^n (6n)!)`. -/
theorem factorization_le_of_ne_three {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (n : ℕ) :
    ((3 * n)! * (2 * n)! * P n).factorization p ≤ (3 ^ n * (6 * n)!).factorization p := by
  have hb : ∀ y, y ≤ 6 * n → Nat.log p y < 6 * n + 1 := fun y hy =>
    log_lt_of_lt hp.one_lt (by omega)
  rw [Nat.factorization_mul (by positivity) (P_ne_zero n),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_factorial hp (hb _ (by omega)),
    Nat.factorization_factorial hp (hb _ (by omega)),
    Nat.factorization_factorial hp (hb _ le_rfl), factorization_P hp n (6 * n + 1) (by omega),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine le_add_left (Finset.sum_le_sum (fun k _ => ?_))
  have hcop : Nat.Coprime (p ^ k) 3 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
  have hloc := local_ineq (p ^ k) n (pow_pos hp.pos k) hcop
  omega

/-- For `3 ∤ n`, `v_3((3n)! (2n)! P n) ≤ v_3(3^n (6n)!)`: no factor of `P n` is
divisible by `3`, and `(3n)! (2n)! ∣ (6n)!`. -/
theorem factorization_three_le_of_not_dvd {n : ℕ} (hn : ¬ 3 ∣ n) :
    ((3 * n)! * (2 * n)! * P n).factorization 3 ≤ (3 ^ n * (6 * n)!).factorization 3 := by
  have hP : (P n).factorization 3 = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd (fun h => ?_)
    unfold P at h
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h
    omega
  have hdvd : (3 * n)! * (2 * n)! ∣ (6 * n)! :=
    (Nat.factorial_mul_factorial_dvd_factorial_add (3 * n) (2 * n)).trans
      (Nat.factorial_dvd_factorial (by omega))
  have hle := (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mpr hdvd 3
  rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hle
  rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (P_ne_zero n),
    Nat.factorization_mul (Nat.factorial_ne_zero (3 * n)) (Nat.factorial_ne_zero (2 * n)),
    Nat.factorization_mul (pow_ne_zero n three_ne_zero) (Nat.factorial_ne_zero (6 * n))]
  simp only [Finsupp.coe_add, Pi.add_apply, hP, add_zero] at hle ⊢
  omega

/-- The case `3 ∤ n` of the integrality: `(3n)! (2n)! P n ∣ 3^n (6n)!`. -/
theorem dvd_of_not_three_dvd {n : ℕ} (hn : ¬ 3 ∣ n) :
    (3 * n)! * (2 * n)! * P n ∣ 3 ^ n * (6 * n)! := by
  refine (Nat.factorization_prime_le_iff_dvd (Nat.mul_ne_zero (by positivity) (P_ne_zero n))
    (by positivity)).mp (fun p hp => ?_)
  by_cases hp3 : p = 3
  · subst hp3
    exact factorization_three_le_of_not_dvd hn
  · exact factorization_le_of_ne_three hp hp3 n

/-- Vasyunin's sporadic integral factorial ratio (Bober, Table 2, Entry 15):
`(9m)! (6m)! (5m)! ∣ (18m)! (2m)!`, i.e. A295445 is an integer sequence. -/
theorem vasyunin_dvd (m : ℕ) : (9 * m)! * (6 * m)! * (5 * m)! ∣ (18 * m)! * (2 * m)! := by
  refine (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mp (fun p hp => ?_)
  have hb : ∀ y, y ≤ 18 * m → Nat.log p y < 18 * m + 1 := fun y hy =>
    log_lt_of_lt hp.one_lt (by omega)
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_factorial hp (hb _ (by omega)),
    Nat.factorization_factorial hp (hb _ (by omega)),
    Nat.factorization_factorial hp (hb _ (by omega)), Nat.factorization_factorial hp (hb _ le_rfl),
    Nat.factorization_factorial hp (hb _ (by omega)),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun k _ => vasyunin_ineq (p ^ k) m)

/-- `(a+1)(a+2)⋯(a+k) · a! = (a+k)!`. -/
theorem prod_add_mul_factorial (a k : ℕ) :
    (∏ j ∈ Icc 1 k, (a + j)) * a ! = (a + k)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, ← add_assoc,
      Nat.factorial_succ, mul_comm]

/-- At `n = 3m`, `P(3m) · (2m)! = 3^{3m} (5m)!`. -/
theorem P_three_mul (m : ℕ) : P (3 * m) * (2 * m)! = 3 ^ (3 * m) * (5 * m)! := by
  have h : P (3 * m) = 3 ^ (3 * m) * ∏ j ∈ Icc 1 (3 * m), (2 * m + j) := by
    unfold P
    rw [show (3 : ℕ) ^ (3 * m) = ∏ _j ∈ Icc 1 (3 * m), 3 by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => by ring)
  rw [h, mul_assoc, prod_add_mul_factorial, show 2 * m + 3 * m = 5 * m by ring]

/-- The case `3 ∣ n` of the integrality, reduced to Vasyunin's ratio. -/
theorem dvd_of_three_dvd {n : ℕ} (hn : 3 ∣ n) :
    (3 * n)! * (2 * n)! * P n ∣ 3 ^ n * (6 * n)! := by
  obtain ⟨m, rfl⟩ := hn
  have hV := vasyunin_dvd m
  have key : (3 * (3 * m))! * (2 * (3 * m))! * P (3 * m) * (2 * m)!
      ∣ 3 ^ (3 * m) * (6 * (3 * m))! * (2 * m)! := by
    rw [mul_assoc _ (P (3 * m)), P_three_mul, show 3 * (3 * m) = 9 * m by ring,
      show 2 * (3 * m) = 6 * m by ring, show 6 * (3 * m) = 18 * m by ring]
    have hV3 := Nat.mul_dvd_mul_left (3 ^ (3 * m)) hV
    convert hV3 using 1 <;> ring
  exact Nat.dvd_of_mul_dvd_mul_right (by positivity) key

/-- **Integer form of the conjecture** (Bala's formula): for every `n`,
`(3n)! (2n)! ∏_{k=1}^n (2n+3k)` divides `3^n (6n)!`. -/
theorem a364175_divisible (n : ℕ) : (3 * n)! * (2 * n)! * P n ∣ 3 ^ n * (6 * n)! := by
  by_cases hn : 3 ∣ n
  · exact dvd_of_three_dvd hn
  · exact dvd_of_not_three_dvd hn

/-- The subsequence `n = 3m` of A364175 is A295445: `a364175 (3m) = a295445 m`. -/
theorem a364175_three_mul (m : ℕ) : a364175 (3 * m) = a295445 m := by
  obtain ⟨k, hk⟩ := a364175_divisible (3 * m)
  have hb : 0 < (3 * (3 * m))! * (2 * (3 * m))! * P (3 * m) :=
    Nat.pos_of_ne_zero (Nat.mul_ne_zero (by positivity) (P_ne_zero _))
  have hk' : a364175 (3 * m) = k := by
    unfold a364175; rw [hk, Nat.mul_div_cancel_left _ hb]
  rw [hk']
  unfold a295445
  symm
  refine Nat.div_eq_of_eq_mul_left (by positivity) ?_
  have hPm := P_three_mul m
  rw [show 3 * (3 * m) = 9 * m by ring, show 2 * (3 * m) = 6 * m by ring,
    show 6 * (3 * m) = 18 * m by ring] at hk
  have h3 : (0 : ℕ) < 3 ^ (3 * m) := by positivity
  refine Nat.eq_of_mul_eq_mul_left h3 ?_
  calc 3 ^ (3 * m) * ((18 * m)! * (2 * m)!) = (3 ^ (3 * m) * (18 * m)!) * (2 * m)! := by ring
    _ = (9 * m)! * (6 * m)! * P (3 * m) * k * (2 * m)! := by rw [hk]
    _ = (9 * m)! * (6 * m)! * (P (3 * m) * (2 * m)!) * k := by ring
    _ = 3 ^ (3 * m) * (k * ((9 * m)! * (6 * m)! * (5 * m)!)) := by rw [hPm]; ring

/-! ## Gamma-function bridge -/

/-- `∏_{j=1}^k f j = ∏_{j<k} f (j+1)`. -/
theorem prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ j ∈ Icc 1 k, f j = ∏ j ∈ range k, f (j + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), prod_range_succ, ih]

/-- Iterated Gamma recurrence: `Γ(x+1+k) = Γ(x+1) ∏_{j<k} (x+1+j)` for `x ≥ 0`. -/
theorem gamma_add_nat {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.Gamma (x + 1 + k) = Real.Gamma (x + 1) * ∏ j ∈ range k, (x + 1 + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ, ← add_assoc,
      Real.Gamma_add_one (by positivity), mul_comm]

/-- The Gamma-function denominator of the entry's ratio is positive, so the real
division below is never the junk value `x / 0`. -/
theorem gamma_denominator_pos (n : ℕ) :
    0 < Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
      * Real.Gamma (5 * (n : ℝ) / 3 + 1) := by
  have h1 := Real.Gamma_pos_of_pos (show 0 < 3 * (n : ℝ) + 1 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show 0 < 2 * (n : ℝ) + 1 by positivity)
  have h3 := Real.Gamma_pos_of_pos (show 0 < 5 * (n : ℝ) / 3 + 1 by positivity)
  positivity

/-- Eliminating the fractional factorials: the entry's Gamma ratio
`Γ(6n+1) Γ(2n/3+1) / (Γ(3n+1) Γ(2n+1) Γ(5n/3+1))` equals
`3^n (6n)! / ((3n)! (2n)! P n)` as a real number. -/
theorem gamma_ratio_eq (n : ℕ) :
    Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) / 3 + 1)
        / (Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
          * Real.Gamma (5 * (n : ℝ) / 3 + 1))
      = ((3 ^ n * (6 * n)! : ℕ) : ℝ) / (((3 * n)! * (2 * n)! * P n : ℕ) : ℝ) := by
  have hfac : ∀ a : ℕ, Real.Gamma ((a : ℝ) + 1) = (a ! : ℝ) := Real.Gamma_nat_eq_factorial
  have h6 : Real.Gamma (6 * (n : ℝ) + 1) = ((6 * n)! : ℝ) := by
    rw [← hfac]; push_cast; ring_nf
  have h3 : Real.Gamma (3 * (n : ℝ) + 1) = ((3 * n)! : ℝ) := by
    rw [← hfac]; push_cast; ring_nf
  have h2 : Real.Gamma (2 * (n : ℝ) + 1) = ((2 * n)! : ℝ) := by
    rw [← hfac]; push_cast; ring_nf
  have hP : ((P n : ℕ) : ℝ) = 3 ^ n * ∏ j ∈ range n, (2 * (n : ℝ) / 3 + 1 + j) := by
    unfold P
    rw [prod_Icc_one_eq_prod_range, Nat.cast_prod,
      show (3 : ℝ) ^ n = ∏ _j ∈ range n, (3 : ℝ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast; ring
  have h5 : Real.Gamma (5 * (n : ℝ) / 3 + 1)
      = Real.Gamma (2 * (n : ℝ) / 3 + 1) * ∏ j ∈ range n, (2 * (n : ℝ) / 3 + 1 + j) := by
    rw [← gamma_add_nat (by positivity)]
    congr 1; ring
  have hG : 0 < Real.Gamma (2 * (n : ℝ) / 3 + 1) := Real.Gamma_pos_of_pos (by positivity)
  rw [h6, h3, h2, h5]
  push_cast
  rw [hP]
  field_simp

/-- The natural-number sequence `a364175` agrees with the entry's Gamma-function
definition `(6n)! (2n/3)! / ((3n)! (2n)! (5n/3)!)`. -/
theorem a364175_eq_gamma_ratio (n : ℕ) :
    (a364175 n : ℝ) = Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) / 3 + 1)
        / (Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
          * Real.Gamma (5 * (n : ℝ) / 3 + 1)) := by
  rw [gamma_ratio_eq, a364175, Nat.cast_div (a364175_divisible n)]
  exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))
    (P_ne_zero n)

/-! ## The conjecture -/

/-- **Bala's integrality conjecture (A295445 comment, Peter Bala, Jun 13 2026),
natural-number form.**

Verbatim: "Conjecture: for n >= 0, a(n/3) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!)
is an integer, where fractional factorials are defined using the Gamma function;
for example, (2*n/3)! := Gamma(2*n/3 + 1). See A364175."

Here `x!` is `Real.Gamma (x + 1)`.  The ratio is a nonnegative integer for every
`n ≥ 0`.  Proved by D. G. Radcliffe (Jul 2026, linked from A364175); this is a
kernel-checked formalization of his argument.  The denominator is positive
(`gamma_denominator_pos`), so the real division is genuine. -/
theorem a295445_conj_nat (n : ℕ) :
    ∃ k : ℕ, (k : ℝ) = Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) / 3 + 1)
        / (Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
          * Real.Gamma (5 * (n : ℝ) / 3 + 1)) :=
  ⟨a364175 n, a364175_eq_gamma_ratio n⟩

/-- **Bala's integrality conjecture (A295445 comment, Peter Bala, Jun 13 2026).**

For every `n ≥ 0`, `(6n)! (2n/3)! / ((3n)! (2n)! (5n/3)!)`, with fractional
factorials `x! := Γ(x + 1)`, is an integer.  Proved by D. G. Radcliffe
(Jul 2026); see `a295445_conj_nat` for the stronger natural-number form. -/
theorem a295445_conj (n : ℕ) :
    ∃ k : ℤ, (k : ℝ) = Real.Gamma (6 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) / 3 + 1)
        / (Real.Gamma (3 * (n : ℝ) + 1) * Real.Gamma (2 * (n : ℝ) + 1)
          * Real.Gamma (5 * (n : ℝ) / 3 + 1)) := by
  obtain ⟨k, hk⟩ := a295445_conj_nat n
  exact ⟨k, by rw [← hk]; norm_cast⟩

end Candidates.A295445Conj
