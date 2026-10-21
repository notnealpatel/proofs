/-
# A389079 — Karttunen: no Euler-form terms, and every term has ω ≥ 3

## OEIS source (retrieved with `oeis show A389079` and the live entry, 2026-10-21)

```
NAME:     Odd nonsquarefree numbers k such that {sum of unitary divisors of k}
          plus {sum of squarefree divisors of k} >= 2*k.
TERMS:    315,495,585,3465,4095,5355,5775,5985,6435,6825,7245,8085,8415,8925,
          9009,9135,9405,9555,9765,9945,9975,10725,11115,11385,11655,11781,...
FORMULA:  {k | k == 1 (mod 2), A008683(k) = 0 and A034448(k)+A048250(k) >= 2*k}.
COMMENT (the conjecture, unsigned; entry AUTHOR: Antti Karttunen, Sep 30 2025):
  It is conjectured that there are no common terms with A228058 (see also
  A388986), and for all terms, A001221(a(n)) >= 3.
```

A228058: "Odd numbers of the form p^(1+4k) * r^2, where p is prime of the form
1+4m, r > 1, and gcd(p,r) = 1. (Euler's criteria for odd perfect numbers)."
A388986 (numbers with U(k) + S(k) < 2k) asks: "Is A228058 a subsequence?"

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell; A388986 still prints the question on 2026-10-21).  Computation:
odd k ≤ 3·10^6 give 6123 terms, none with ω < 3; over the 34998 Euler-form
k ≤ 3·10^6 the maximum of (U + S)/k is 28/15, at k = 45.

This module proves both parts (`a389079_conjecture`).  Argument: U and S are
multiplicative with U(p^e) = 1 + p^e and S(p^e) = 1 + p.  Part (i) reduces,
via p ≥ 5, to 3(U(r²) + S(r²)) < 5r² for odd r > 1, which follows from
U(r²)/r² ≤ ∏(1 + 1/q²) ≤ 4/3 (telescoping ∑_{odd q ≥ 3} 1/q² ≤ 1/4) and
S(r²)/r² ≤ (4/9)^ω(r), with the case ω(r) = 1 done directly.  Part (ii) is
an explicit check of the one- and two-prime cases.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A389079SumUnitaryDivisors

/-! ## Definition layer -/

/-- `usigma k` is the sum of the unitary divisors of `k` (A034448): divisors `d ∣ k`
with `gcd(d, k / d) = 1`. -/
def usigma (k : ℕ) : ℕ := ∑ d ∈ k.divisors with Nat.Coprime d (k / d), d

/-- `sqfsigma k` is the sum of the squarefree divisors of `k` (A048250). -/
def sqfsigma (k : ℕ) : ℕ := ∑ d ∈ k.divisors with Squarefree d, d

/-- Membership in A389079: `k` is odd, not squarefree, and
`usigma k + sqfsigma k ≥ 2 * k`. -/
def IsA389079 (k : ℕ) : Prop := Odd k ∧ ¬ Squarefree k ∧ 2 * k ≤ usigma k + sqfsigma k

/-! ### Ground truth -/

example : usigma 315 = 480 := by decide
example : sqfsigma 315 = 192 := by decide +kernel
example : usigma 45 = 60 := by decide
example : sqfsigma 45 = 24 := by decide +kernel
example : IsA389079 315 := by unfold IsA389079; decide +kernel
example : IsA389079 495 := by unfold IsA389079; decide +kernel
example : IsA389079 585 := by unfold IsA389079; decide +kernel
example : IsA389079 3465 := by unfold IsA389079; decide +kernel
/-- `45 = 5^1 * 3^2` (the first term of A228058) is not a term. -/
example : ¬ IsA389079 45 := by unfold IsA389079; decide +kernel
/-- `315` is the least term. -/
example : ∀ k < 315, ¬ IsA389079 k := by unfold IsA389079; decide +kernel

/-! ## Multiplicativity and product formulas -/

/-- For coprime `m`, `n`, a divisor sum over `m * n` whose summand splits as
`h (a * b) = f a * g b` on `a ∣ m`, `b ∣ n` factors as a product of divisor sums. -/
theorem sum_divisors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) (h f g : ℕ → ℕ)
    (hfg : ∀ a ∈ m.divisors, ∀ b ∈ n.divisors, h (a * b) = f a * g b) :
    ∑ d ∈ (m * n).divisors, h d = (∑ a ∈ m.divisors, f a) * ∑ b ∈ n.divisors, g b := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hmn.mul_injOn_divisors,
    Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hfg a ha b hb

/-- The unitary-divisor sum is multiplicative on coprime arguments. -/
theorem usigma_mul {m n : ℕ} (hmn : m.Coprime n) : usigma (m * n) = usigma m * usigma n := by
  unfold usigma
  simp only [Finset.sum_filter]
  apply sum_divisors_mul_of_coprime hmn
  intro a ha b hb
  rw [Nat.mem_divisors] at ha hb
  rw [← Nat.div_mul_div_comm ha.1 hb.1]
  have hma : (m / a) ∣ m := Nat.div_dvd_of_dvd ha.1
  have hnb : (n / b) ∣ n := Nat.div_dvd_of_dvd hb.1
  have hab : Nat.Coprime a (n / b) := (hmn.coprime_dvd_left ha.1).coprime_dvd_right hnb
  have hba : Nat.Coprime b (m / a) := ((hmn.coprime_dvd_left hma).coprime_dvd_right hb.1).symm
  have key : Nat.Coprime (a * b) (m / a * (n / b)) ↔
      Nat.Coprime a (m / a) ∧ Nat.Coprime b (n / b) := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    tauto
  by_cases h1 : Nat.Coprime a (m / a) <;> by_cases h2 : Nat.Coprime b (n / b)
  · rw [if_pos (key.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]
  · rw [if_neg (fun h => h2 (key.mp h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (key.mp h).1), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (key.mp h).1), if_neg h1, zero_mul]

/-- The squarefree-divisor sum is multiplicative on coprime arguments. -/
theorem sqfsigma_mul {m n : ℕ} (hmn : m.Coprime n) :
    sqfsigma (m * n) = sqfsigma m * sqfsigma n := by
  unfold sqfsigma
  simp only [Finset.sum_filter]
  apply sum_divisors_mul_of_coprime hmn
  intro a ha b hb
  rw [Nat.mem_divisors] at ha hb
  have hab : Nat.Coprime a b := (hmn.coprime_dvd_left ha.1).coprime_dvd_right hb.1
  by_cases h1 : Squarefree a <;> by_cases h2 : Squarefree b <;>
    simp [Nat.squarefree_mul_iff, hab, h1, h2]

/-- `usigma (p ^ k) = 1 + p ^ k` for a prime `p` and `k ≠ 0`: the unitary divisors of
`p ^ k` are `1` and `p ^ k`. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : usigma (p ^ k) = 1 + p ^ k := by
  unfold usigma
  rw [Finset.sum_filter, Nat.sum_divisors_prime_pow hp]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ i ∈ Finset.range j, (if Nat.Coprime (p ^ (i + 1)) (p ^ (j + 1) / p ^ (i + 1))
      then p ^ (i + 1) else 0) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hdiv : p ^ (j + 1) / p ^ (i + 1) = p ^ (j - i) := by
      rw [Nat.pow_div (by omega) hp.pos]
      congr 1
      omega
    rw [hdiv, if_neg]
    rw [Nat.coprime_pow_left_iff (by omega), Nat.coprime_pow_right_iff (by omega)]
    exact (Nat.coprime_self p).not.mpr hp.one_lt.ne'
  rw [Finset.sum_eq_zero hmid]
  rw [Nat.div_self (pow_pos hp.pos _), pow_zero, if_pos (Nat.coprime_one_right _),
    if_pos (Nat.coprime_one_left _)]
  simp


/-- `sqfsigma (p ^ k) = 1 + p` for a prime `p` and `k ≠ 0`: the squarefree divisors of
`p ^ k` are `1` and `p`. -/
theorem sqfsigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    sqfsigma (p ^ k) = 1 + p := by
  unfold sqfsigma
  rw [Finset.sum_filter, Nat.sum_divisors_prime_pow hp]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hmid : ∀ i ∈ Finset.range j,
      (if Squarefree (p ^ (i + 1 + 1)) then p ^ (i + 1 + 1) else 0) = 0 := by
    intro i _
    rw [if_neg]
    rw [Nat.squarefree_pow_iff hp.one_lt.ne' (by omega)]
    omega
  rw [Finset.sum_eq_zero hmid, zero_add, zero_add, pow_one, pow_zero,
    if_pos hp.squarefree, if_pos squarefree_one, add_comm]

/-- Product formula (A034448): `usigma n = ∏_{p ∣ n} (1 + p ^ v_p(n))` for `n ≠ 0`. -/
theorem usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization usigma (fun x y h => usigma_mul h) rfl hn,
    Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.mem_primeFactors] at hp
  exact usigma_prime_pow hp.1 (Nat.pos_iff_ne_zero.mp
    (hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1))

/-- Product formula (A048250): `sqfsigma n = ∏_{p ∣ n} (1 + p)` for `n ≠ 0`. -/
theorem sqfsigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sqfsigma n = ∏ p ∈ n.primeFactors, (1 + p) := by
  rw [Nat.multiplicative_factorization sqfsigma (fun x y h => sqfsigma_mul h)
    (by rw [sqfsigma, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]; rfl) hn,
    Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.mem_primeFactors] at hp
  exact sqfsigma_prime_pow hp.1 (Nat.pos_iff_ne_zero.mp
    (hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1))

/-- For nonnegative rationals `x i`, `1 ≤ ∏ (1 + x i)` and
`(∏ (1 + x i)) * (1 - ∑ x i) ≤ 1`. -/
theorem prod_one_add_mul_one_sub_sum_le_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℚ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 ≤ ∏ i ∈ s, (1 + x i) ∧ (∏ i ∈ s, (1 + x i)) * (1 - ∑ i ∈ s, x i) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hy : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set P := ∏ i ∈ s, (1 + x i)
    set X := ∑ i ∈ s, x i
    refine ⟨by nlinarith, ?_⟩
    have h3 : (1 + x a) * (P * (1 - X)) ≤ (1 + x a) * 1 :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : x a * (1 + x a) * 1 ≤ x a * (1 + x a) * P :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith

/-- Telescoping bound: `∑_{j < N} 1 / (2j + 3)^2 ≤ 1/4 - 1/(4(N + 1))`. -/
theorem sum_range_inv_sq_odd_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 : ℚ) / ((2 * j + 3) ^ 2) ≤ 1 / 4 - 1 / (4 * ((N : ℚ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have key : (1 : ℚ) / ((2 * N + 3) ^ 2) ≤ 1 / (4 * (N + 1)) - 1 / (4 * (N + 1 + 1)) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith [ih, key]


/-- For a finite set `T` of odd numbers `≥ 3`, `∑_{q ∈ T} 1 / q^2 ≤ 1/4`. -/
theorem sum_inv_sq_le_quarter (T : Finset ℕ) (hT : ∀ q ∈ T, Odd q ∧ 3 ≤ q) :
    ∑ q ∈ T, (1 : ℚ) / (q : ℚ) ^ 2 ≤ 1 / 4 := by
  set N := T.sup id
  have hsub : T ⊆ (Finset.range N).image (fun j => 2 * j + 3) := by
    intro q hq
    obtain ⟨⟨c, hc⟩, h3⟩ := hT q hq
    have hle : q ≤ N := Finset.le_sup (f := id) hq
    rw [Finset.mem_image]
    exact ⟨c - 1, Finset.mem_range.mpr (by omega), by omega⟩
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + 3) ↑(Finset.range N) := by
    intro a _ b _ hab
    simp only at hab
    omega
  calc ∑ q ∈ T, (1 : ℚ) / (q : ℚ) ^ 2
      ≤ ∑ q ∈ (Finset.range N).image (fun j : ℕ => 2 * j + 3), (1 : ℚ) / ((q : ℕ) : ℚ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ j ∈ Finset.range N, (1 : ℚ) / ((2 * j + 3) ^ 2) := by
        rw [Finset.sum_image hinj]
        push_cast
        rfl
    _ ≤ 1 / 4 - 1 / (4 * ((N : ℚ) + 1)) := sum_range_inv_sq_odd_le N
    _ ≤ 1 / 4 := by
        have : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 1)) := by positivity
        linarith

/-- If every `q ∈ T` is odd with `3 ≤ q` and `2 ≤ E q`, then
`3 * ∏ (1 + q ^ E q) ≤ 4 * ∏ q ^ E q`. -/
theorem three_mul_prod_one_add_pow_le (T : Finset ℕ) (E : ℕ → ℕ)
    (hT : ∀ q ∈ T, Odd q ∧ 3 ≤ q) (hE : ∀ q ∈ T, 2 ≤ E q) :
    3 * ∏ q ∈ T, (1 + q ^ E q) ≤ 4 * ∏ q ∈ T, q ^ E q := by
  have hpos : ∀ q ∈ T, (0 : ℚ) < (q : ℚ) ^ E q := fun q hq => by
    have : (3 : ℚ) ≤ q := by exact_mod_cast (hT q hq).2
    positivity
  set x : ℕ → ℚ := fun q => 1 / (q : ℚ) ^ E q
  have hx0 : ∀ q ∈ T, 0 ≤ x q := fun q hq => by positivity
  have hxle : ∀ q ∈ T, x q ≤ 1 / (q : ℚ) ^ 2 := by
    intro q hq
    have h3 : (1 : ℚ) ≤ q := by
      have := (hT q hq).2
      exact_mod_cast (by omega : 1 ≤ q)
    have h3' : (0 : ℚ) < (q : ℚ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le h3' (pow_le_pow_right₀ h3 (hE q hq))
  have hsum : ∑ q ∈ T, x q ≤ 1 / 4 :=
    (Finset.sum_le_sum hxle).trans (sum_inv_sq_le_quarter T hT)
  obtain ⟨h1, h2⟩ := prod_one_add_mul_one_sub_sum_le_one T x hx0
  have hprod : 3 * ∏ q ∈ T, (1 + x q) ≤ 4 := by nlinarith
  have hfac : ∏ q ∈ T, ((1 : ℚ) + (q : ℚ) ^ E q) =
      (∏ q ∈ T, (q : ℚ) ^ E q) * ∏ q ∈ T, (1 + x q) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have := (hpos q hq).ne'
    simp only [x]
    field_simp
    ring
  have hP : (0 : ℚ) ≤ ∏ q ∈ T, (q : ℚ) ^ E q := Finset.prod_nonneg fun q hq => (hpos q hq).le
  have key : (3 : ℚ) * ∏ q ∈ T, ((1 : ℚ) + (q : ℚ) ^ E q) ≤ 4 * ∏ q ∈ T, (q : ℚ) ^ E q := by
    rw [hfac]
    nlinarith
  exact_mod_cast key


/-- If every `q ∈ T` is odd with `3 ≤ q` and `2 ≤ E q`, and `T` has at least two
elements, then `81 * ∏ (1 + q) ≤ 16 * ∏ q ^ E q`. -/
theorem eighty_one_mul_prod_one_add_le (T : Finset ℕ) (E : ℕ → ℕ)
    (hT : ∀ q ∈ T, Odd q ∧ 3 ≤ q) (hE : ∀ q ∈ T, 2 ≤ E q) (hcard : 2 ≤ T.card) :
    81 * ∏ q ∈ T, (1 + q) ≤ 16 * ∏ q ∈ T, q ^ E q := by
  have hq : ∀ q ∈ T, 9 * (1 + q) ≤ 4 * q ^ E q := by
    intro q hqT
    have h3 := (hT q hqT).2
    have hsq : q ^ 2 ≤ q ^ E q := Nat.pow_le_pow_right (by omega) (hE q hqT)
    nlinarith
  have hprod : 9 ^ T.card * ∏ q ∈ T, (1 + q) ≤ 4 ^ T.card * ∏ q ∈ T, q ^ E q := by
    rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hq
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hcard
  rw [hc, pow_add, pow_add] at hprod
  have h49 : 4 ^ c ≤ 9 ^ c := Nat.pow_le_pow_left (by norm_num) c
  have hpos : 0 < 4 ^ c := by positivity
  have key : 4 ^ c * (81 * ∏ q ∈ T, (1 + q)) ≤ 4 ^ c * (16 * ∏ q ∈ T, q ^ E q) := by
    calc 4 ^ c * (81 * ∏ q ∈ T, (1 + q)) ≤ 9 ^ c * (81 * ∏ q ∈ T, (1 + q)) :=
          Nat.mul_le_mul_right _ h49
      _ = 9 ^ 2 * 9 ^ c * ∏ q ∈ T, (1 + q) := by ring
      _ ≤ 4 ^ 2 * 4 ^ c * ∏ q ∈ T, q ^ E q := hprod
      _ = 4 ^ c * (16 * ∏ q ∈ T, q ^ E q) := by ring
  exact Nat.le_of_mul_le_mul_left key hpos

/-- If `T` is a nonempty set of odd numbers `≥ 3` and `2 ≤ E q` on `T`, then
`3 * (∏ (1 + q ^ E q) + ∏ (1 + q)) < 5 * ∏ q ^ E q`. -/
theorem three_mul_add_lt_five_mul (T : Finset ℕ) (E : ℕ → ℕ)
    (hT : ∀ q ∈ T, Odd q ∧ 3 ≤ q) (hE : ∀ q ∈ T, 2 ≤ E q) (hne : T.Nonempty) :
    3 * (∏ q ∈ T, (1 + q ^ E q) + ∏ q ∈ T, (1 + q)) < 5 * ∏ q ∈ T, q ^ E q := by
  have hR : 0 < ∏ q ∈ T, q ^ E q :=
    Finset.prod_pos fun q hq => pow_pos (by have := (hT q hq).2; omega) _
  rcases Nat.lt_or_ge T.card 2 with hlt | hge
  · have hpos := hne.card_pos
    have h1 : T.card = 1 := by omega
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.prod_singleton] at hR ⊢
    have h3 := (hT q (Finset.mem_singleton_self q)).2
    have hsq : q ^ 2 ≤ q ^ E q :=
      Nat.pow_le_pow_right (by omega) (hE q (Finset.mem_singleton_self q))
    nlinarith
  · have hA := three_mul_prod_one_add_pow_le T E hT hE
    have hB := eighty_one_mul_prod_one_add_le T E hT hE hge
    omega

/-- Two-prime arithmetic: for `3 ≤ p, q`, one of them `≥ 5`, `p ^ 2 ≤ P` and `q ≤ Q`,
`(1 + P) * (1 + Q) + (1 + p) * (1 + q) < 2 * (P * Q)`. -/
theorem two_prime_bound (p q P Q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) (hpq : 5 ≤ p ∨ 5 ≤ q)
    (hP : p ^ 2 ≤ P) (hQ : q ≤ Q) : (1 + P) * (1 + Q) + (1 + p) * (1 + q) < 2 * (P * Q) := by
  have h1 : (p ^ 2 - 1 : ℤ) * (q - 1) ≤ ((P : ℤ) - 1) * ((Q : ℤ) - 1) := by
    apply mul_le_mul <;> nlinarith
  have h3 : (2 : ℤ) ≤ ((p : ℤ) - 2) * ((q : ℤ) - 1) - 2 := by
    rcases hpq with h | h
    · have := mul_le_mul (show (3 : ℤ) ≤ (p : ℤ) - 2 by omega)
        (show (2 : ℤ) ≤ (q : ℤ) - 1 by omega) (by norm_num) (by omega)
      linarith
    · have := mul_le_mul (show (1 : ℤ) ≤ (p : ℤ) - 2 by omega)
        (show (4 : ℤ) ≤ (q : ℤ) - 1 by omega) (by norm_num) (by omega)
      linarith
  have h4 : (p ^ 2 - 1 : ℤ) * (q - 1) - (1 + p) * (1 + q) =
      ((p : ℤ) + 1) * (((p : ℤ) - 2) * ((q : ℤ) - 1) - 2) := by ring
  have h5 : (8 : ℤ) ≤ ((p : ℤ) + 1) * (((p : ℤ) - 2) * ((q : ℤ) - 1) - 2) := by
    have := mul_le_mul (show (4 : ℤ) ≤ (p : ℤ) + 1 by omega) h3 (by norm_num) (by omega)
    linarith
  zify
  nlinarith

/-- If `T` is a set of at most two odd numbers `≥ 3`, `1 ≤ E q` on `T`, and some
`q₀ ∈ T` has `2 ≤ E q₀`, then `∏ (1 + q ^ E q) + ∏ (1 + q) < 2 * ∏ q ^ E q`. -/
theorem prod_lt_of_card_le_two (T : Finset ℕ) (E : ℕ → ℕ)
    (hT : ∀ q ∈ T, Odd q ∧ 3 ≤ q) (hE : ∀ q ∈ T, 1 ≤ E q) (q₀ : ℕ) (hq₀ : q₀ ∈ T)
    (hE₀ : 2 ≤ E q₀) (hcard : T.card ≤ 2) :
    ∏ q ∈ T, (1 + q ^ E q) + ∏ q ∈ T, (1 + q) < 2 * ∏ q ∈ T, q ^ E q := by
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨q₀, hq₀⟩
  rcases (by omega : T.card = 1 ∨ T.card = 2) with h1 | h2
  · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.mem_singleton] at hq₀
    subst hq₀
    simp only [Finset.prod_singleton]
    have h3 := (hT q₀ (Finset.mem_singleton_self q₀)).2
    have hsq : q₀ ^ 2 ≤ q₀ ^ E q₀ := Nat.pow_le_pow_right (by omega) hE₀
    nlinarith
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rw [Finset.prod_pair hab, Finset.prod_pair hab, Finset.prod_pair hab]
    obtain ⟨⟨ka, hka⟩, ha3⟩ := hT a (by simp)
    obtain ⟨⟨kb, hkb⟩, hb3⟩ := hT b (by simp)
    have h5 : 5 ≤ a ∨ 5 ≤ b := by omega
    have hEa := hE a (by simp)
    have hEb := hE b (by simp)
    have hga : a ≤ a ^ E a := Nat.le_self_pow (by omega) a
    have hgb : b ≤ b ^ E b := Nat.le_self_pow (by omega) b
    rcases Finset.mem_insert.mp hq₀ with rfl | hq
    · have hsq : q₀ ^ 2 ≤ q₀ ^ E q₀ := Nat.pow_le_pow_right (by omega) hE₀
      exact two_prime_bound q₀ b _ _ ha3 hb3 h5 hsq hgb
    · rw [Finset.mem_singleton] at hq
      subst hq
      have hsq : q₀ ^ 2 ≤ q₀ ^ E q₀ := Nat.pow_le_pow_right (by omega) hE₀
      have := two_prime_bound q₀ a _ _ hb3 ha3 h5.symm hsq hga
      linarith [mul_comm (a ^ E a) (q₀ ^ E q₀), mul_comm (1 + a ^ E a) (1 + q₀ ^ E q₀),
        mul_comm (1 + a) (1 + q₀)]

/-- A prime factor of an odd number is odd and at least `3`. -/
theorem odd_three_le_of_mem_primeFactors {k q : ℕ} (hk : Odd k) (hq : q ∈ k.primeFactors) :
    Odd q ∧ 3 ≤ q := by
  rw [Nat.mem_primeFactors] at hq
  have hqodd : Odd q := hk.of_dvd_nat hq.2.1
  refine ⟨hqodd, ?_⟩
  have h2 := hq.1.two_le
  rcases hqodd with ⟨c, hc⟩
  omega

/-- **Karttunen's conjecture, part (ii)** (A389079): every term has at least three
distinct prime factors, i.e. `3 ≤ A001221(k)`. -/
theorem three_le_card_primeFactors {k : ℕ} (h : IsA389079 k) : 3 ≤ k.primeFactors.card := by
  obtain ⟨hodd, hns, hle⟩ := h
  have hk0 : k ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  by_contra hlt
  have hcard : k.primeFactors.card ≤ 2 := by omega
  rw [Nat.squarefree_iff_factorization_le_one hk0] at hns
  push Not at hns
  obtain ⟨q₀, hq₀⟩ := hns
  have hq₀mem : q₀ ∈ k.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hE : ∀ q ∈ k.primeFactors, 1 ≤ k.factorization q := fun q hq => by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hq
    omega
  have hkprod : ∏ q ∈ k.primeFactors, q ^ k.factorization q = k := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hk0]
    rw [Finsupp.prod, Nat.support_factorization]
  have key := prod_lt_of_card_le_two k.primeFactors k.factorization
    (fun q hq => odd_three_le_of_mem_primeFactors hodd hq) hE q₀ hq₀mem (by omega) hcard
  rw [← usigma_eq_prod hk0, ← sqfsigma_eq_prod hk0, hkprod] at key
  omega


/-- For odd `r > 1`, `3 * (usigma (r^2) + sqfsigma (r^2)) < 5 * r^2`. -/
theorem three_mul_usigma_add_sqfsigma_sq_lt {r : ℕ} (hr : 1 < r) (hodd : Odd r) :
    3 * (usigma (r ^ 2) + sqfsigma (r ^ 2)) < 5 * r ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := by positivity
  have hodd2 : Odd (r ^ 2) := hodd.pow
  have hne : (r ^ 2).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr (Nat.one_lt_pow two_ne_zero hr)
  have hE : ∀ q ∈ (r ^ 2).primeFactors, 2 ≤ (r ^ 2).factorization q := by
    intro q hq
    rw [Nat.primeFactors_pow r two_ne_zero] at hq
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hq
    omega
  have hprod : ∏ q ∈ (r ^ 2).primeFactors, q ^ (r ^ 2).factorization q = r ^ 2 := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hr2]
    rw [Finsupp.prod, Nat.support_factorization]
  have key := three_mul_add_lt_five_mul (r ^ 2).primeFactors (r ^ 2).factorization
    (fun q hq => odd_three_le_of_mem_primeFactors hodd2 hq) hE hne
  rwa [← usigma_eq_prod hr2, ← sqfsigma_eq_prod hr2, hprod] at key

/-- For `k = p^(4m+1) * r^2` with `p ≡ 1 (mod 4)` prime, odd `r > 1`, `gcd(p, r) = 1`,
the strict inequality `usigma k + sqfsigma k < 2 * k` holds, i.e. `k` lies in A388986. -/
theorem usigma_add_sqfsigma_lt_of_eulerForm (p m r : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hr : 1 < r) (hodd : Odd r) (hcop : Nat.Coprime p r) :
    usigma (p ^ (4 * m + 1) * r ^ 2) + sqfsigma (p ^ (4 * m + 1) * r ^ 2) <
      2 * (p ^ (4 * m + 1) * r ^ 2) := by
  have hcop' : Nat.Coprime (p ^ (4 * m + 1)) (r ^ 2) := Nat.Coprime.pow _ _ hcop
  rw [usigma_mul hcop', sqfsigma_mul hcop', usigma_prime_pow hp (by omega),
    sqfsigma_prime_pow hp (by omega)]
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h <;> simp_all
  have hpP : p ≤ p ^ (4 * m + 1) := Nat.le_self_pow (by omega) p
  have hr' := three_mul_usigma_add_sqfsigma_sq_lt hr hodd
  set P := p ^ (4 * m + 1)
  set U := usigma (r ^ 2)
  set S := sqfsigma (r ^ 2)
  set R := r ^ 2
  have hP : 0 < P := by omega
  have h1 : 5 * (1 + P) ≤ 6 * P := by omega
  have h2 : 5 * (1 + p) ≤ 6 * P := by omega
  have h3 : 6 * P * (U + S) < 10 * (P * R) := by nlinarith
  nlinarith

/-- **Karttunen's conjecture, part (i)** (A389079): no number of Euler's odd-perfect
form `p^(4m+1) * r^2` (`p ≡ 1 (mod 4)` prime, `r > 1`, `gcd(p, r) = 1`) is a term. -/
theorem not_isA389079_eulerForm (p m r : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (hr : 1 < r)
    (hcop : Nat.Coprime p r) : ¬ IsA389079 (p ^ (4 * m + 1) * r ^ 2) := by
  rintro ⟨hodd, _, hle⟩
  have hoddr : Odd r := (Nat.odd_pow_iff two_ne_zero).mp (Nat.Odd.of_mul_right hodd)
  have := usigma_add_sqfsigma_lt_of_eulerForm p m r hp hp4 hr hoddr hcop
  omega

/-! ## The conjecture -/

/-- **Karttunen's conjecture (A389079, comment in the entry by Antti Karttunen, 2025).**

Verbatim: "It is conjectured that there are no common terms with A228058 (see also
A388986), and for all terms, A001221(a(n)) >= 3."

(i) No `k = p^(4m+1) * r^2` with `p` prime, `p ≡ 1 (mod 4)`, `r > 1`, `gcd(p, r) = 1`
(the A228058 form; the oddness of A228058 is implied by membership) is a term.
(ii) Every term has at least three distinct prime factors (`A001221 = ω`). -/
theorem a389079_conjecture :
    (∀ p m r : ℕ, p.Prime → p % 4 = 1 → 1 < r → Nat.Coprime p r →
      ¬ IsA389079 (p ^ (4 * m + 1) * r ^ 2)) ∧
    (∀ k : ℕ, IsA389079 k → 3 ≤ k.primeFactors.card) :=
  ⟨fun p m r hp hp4 hr hcop => not_isA389079_eulerForm p m r hp hp4 hr hcop,
    fun _ hk => three_le_card_primeFactors hk⟩

/-! ### Non-vacuity -/

/-- The Euler-form hypotheses are jointly satisfiable (`45 = 5 * 3^2`). -/
example : Nat.Prime 5 ∧ 5 % 4 = 1 ∧ 1 < 3 ∧ Nat.Coprime 5 3 ∧ 5 ^ (4 * 0 + 1) * 3 ^ 2 = 45 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Part (ii) applies to an actual term (`315 = 3^2 * 5 * 7`). -/
example : 3 ≤ (315 : ℕ).primeFactors.card := three_le_card_primeFactors
  (by unfold IsA389079; decide +kernel)

end Candidates.A389079SumUnitaryDivisors
