/-
# A002104 — Peter Bala's prime-power congruences for the logarithmic numbers

Peter Bala's prime-power congruences for the logarithmic numbers, OEIS
A002104 (2022). We use `a(n) = Σ_{j=1..n} C(n,j)(j-1)!`, the binomial form
of the entry's falling-factorial sum, with e.g.f. `-log(1-x) exp(x)`.

## Proof outline

* Step 1 (`a_add_modEq`): `a(n + M) ≡ a(n) + a(M) (mod M)` for all `n, M`, because
  `a(n+1) - a(n) = b(n) = Sum_j n^{(j)}` and each falling factorial is a polynomial
  in `n`, so `b` is `M`-periodic modulo `M`.
* Step 2 (`pow_dvd_a_add_odd`, `two_pow_dvd_a`): with `M = m p^k`, every term
  `C(M,j)(j-1)!` of `a(M)` is divisible by `p^k` except `j = p` (and `j = 4` when
  `p = 2`), using `j C(M,j) = M C(M-1,j-1)` and `p^{v_p(j)} ∣ (j-1)!`.  The exceptional
  term is `≡ -m p^(k-1)` by Wilson's theorem for odd `p`; for `p = 2` the two
  exceptional terms sum to a multiple of `M`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A002104PeterBalaConjectures

open Finset Nat

/-- The logarithmic numbers (OEIS A002104):
`a(n) = Sum_{j=1..n} C(n,j) * (j-1)!`, with e.g.f. `-log(1-x) * exp(x)`. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Icc 1 n, n.choose j * (j - 1)!

example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9] =
    [0, 1, 3, 8, 24, 89, 415, 2372, 16072, 125673] := by decide

/-- The first differences of `a` (OEIS A000522):
`b(n) = Sum_{j=0..n} n!/(n-j)!`, written with falling factorials. -/
def b (n : ℕ) : ℕ := ∑ j ∈ range (n + 1), n.descFactorial j

example : [b 0, b 1, b 2, b 3, b 4] = [1, 2, 5, 16, 65] := by decide

/-- Reindexing of `a` over `range`: `a n = Sum_{j<n} C(n, j+1) * j!`. -/
theorem a_eq_sum_range (n : ℕ) : a n = ∑ j ∈ range n, n.choose (j + 1) * j ! := by
  rw [a, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  refine sum_congr (by simp) fun j _ => ?_
  rw [add_comm 1 j, Nat.add_sub_cancel]

/-- The difference recurrence `a(n+1) = a(n) + b(n)`. -/
theorem a_succ (n : ℕ) : a (n + 1) = a n + b n := by
  rw [a_eq_sum_range, a_eq_sum_range, b]
  simp_rw [Nat.choose_succ_succ', add_mul, sum_add_distrib]
  rw [sum_range_succ (fun j => n.choose (j + 1) * j !), Nat.choose_succ_self, zero_mul,
    add_zero, add_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]


/-- `b n` may be summed over any longer range, since `n.descFactorial j = 0` for `n < j`. -/
theorem b_eq_sum_range_of_le (n N : ℕ) (h : n + 1 ≤ N) :
    b n = ∑ j ∈ range N, n.descFactorial j := by
  rw [b]
  refine sum_subset (range_subset_range.mpr h) fun j _ hj => ?_
  rw [mem_range, not_lt] at hj
  exact Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)

/-- `b` is periodic modulo `M` with period `M`. -/
theorem b_add_cast (M i : ℕ) : (b (i + M) : ZMod M) = b i := by
  rw [b_eq_sum_range_of_le (i + M) (i + M + 1) le_rfl,
    b_eq_sum_range_of_le i (i + M + 1) (by omega)]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [← descPochhammer_eval_eq_descFactorial, ← descPochhammer_eval_eq_descFactorial]
  push_cast
  rw [ZMod.natCast_self, add_zero]

/-- `a(n + M) = a(n) + Sum_{t<M} b(n+t)`. -/
theorem a_add_eq (n M : ℕ) : a (n + M) = a n + ∑ t ∈ range M, b (n + t) := by
  induction M with
  | zero => simp
  | succ M ih => rw [← add_assoc, a_succ, ih, sum_range_succ, add_assoc]

/-- Sums of `b` over a full period are independent of the starting point modulo `M`. -/
theorem sum_b_period_cast (M n : ℕ) :
    (∑ t ∈ range M, (b (n + t) : ZMod M)) = ∑ t ∈ range M, (b t : ZMod M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 := sum_range_succ (fun t => (b (n + t) : ZMod M)) M
    have h2 := sum_range_succ' (fun t => (b (n + t) : ZMod M)) M
    rw [b_add_cast] at h1
    rw [add_zero] at h2
    have h3 : ∑ t ∈ range M, (b (n + (t + 1)) : ZMod M) =
        ∑ t ∈ range M, (b (n + 1 + t) : ZMod M) :=
      sum_congr rfl fun t _ => by rw [show n + (t + 1) = n + 1 + t by omega]
    rw [h3] at h2
    exact add_right_cancel (h2.symm.trans h1)

/-- **Step 1.** `a(n + M) ≡ a(n) + a(M) (mod M)` for all `n, M`. -/
theorem a_add_modEq (n M : ℕ) : a (n + M) ≡ a n + a M [MOD M] := by
  have h0 : a M = ∑ t ∈ range M, b t := by
    have h := a_add_eq 0 M
    simp only [zero_add] at h
    rw [h, a, Icc_eq_empty (by omega), sum_empty, zero_add]
  rw [← ZMod.natCast_eq_natCast_iff, a_add_eq, h0]
  push_cast
  rw [sum_b_period_cast]


/-- `p^s ∣ (s*p)!`, since `(p!)^s ∣ (s*p)!` and `p ∣ p!`. -/
theorem pow_dvd_factorial_mul (p s : ℕ) (hp : 0 < p) : p ^ s ∣ (s * p)! := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, add_mul, one_mul]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/-- `s * p < p ^ s` for `p ≥ 2`, `s ≥ 2`, except at `p = s = 2`. -/
theorem mul_lt_pow (p s : ℕ) (hp : 2 ≤ p) (hs : 2 ≤ s) (h : 3 ≤ p ∨ 3 ≤ s) :
    s * p < p ^ s := by
  have step : ∀ t, 1 ≤ t → t * p < p ^ t → (t + 1) * p < p ^ (t + 1) := by
    intro t ht hlt
    have hpt : p ≤ p ^ t := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < p) ht
    rw [pow_succ]
    nlinarith
  rcases h with h3 | h3
  · induction s, hs using Nat.le_induction with
    | base => rw [pow_two]; nlinarith
    | succ t ht ih => exact step t (by omega) ih
  · induction s, h3 using Nat.le_induction with
    | base => rw [pow_succ, pow_two]; nlinarith
    | succ t ht ih => exact step t (by omega) (ih (by omega))

/-- For `j = p^s * u` with `p ∤ u`, the `p`-part `p^s` of `j` divides `(j-1)!`,
except at `j = p` and, when `p = 2`, at `j = 4`. -/
theorem pow_dvd_factorial_pred (p s u : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u)
    (hne : p ^ s * u ≠ p) (hne4 : p = 2 → p ^ s * u ≠ 4) :
    p ^ s ∣ (p ^ s * u - 1)! := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  have hps : 0 < p ^ s := pow_pos hp.pos s
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · obtain rfl : u = 1 := by omega
    rw [mul_one] at hne hne4 ⊢
    rcases Nat.lt_or_ge s 2 with hs | hs
    · interval_cases s
      · simp
      · simp at hne
    · have hlt : s * p < p ^ s := by
        refine mul_lt_pow p s hp.two_le hs ?_
        by_contra hcon
        have hp2 : p = 2 := by have := hp.two_le; omega
        have hs2 : s = 2 := by omega
        subst hp2 hs2
        exact hne4 rfl (by norm_num)
      exact (pow_dvd_factorial_mul p s hp.pos).trans
        (Nat.factorial_dvd_factorial (by omega))
  · have hlt : p ^ s < p ^ s * u := by nlinarith
    exact Nat.dvd_factorial hps (by omega)

/-- If `p^k ∣ M`, then `p^k ∣ C(M, j) * (j-1)!` for every `j ≥ 1` other than `j = p`
(and other than `j = 4` when `p = 2`).  Uses `j * C(M, j) = M * C(M-1, j-1)`. -/
theorem pow_dvd_term (p k M j : ℕ) (hp : p.Prime) (hM : p ^ k ∣ M) (hj : 1 ≤ j)
    (hne : j ≠ p) (hne4 : p = 2 → j ≠ 4) : p ^ k ∣ M.choose j * (j - 1)! := by
  obtain ⟨s, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p
    hp.one_lt.ne'
  have hfac := pow_dvd_factorial_pred p s u hp hu hne hne4
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    exact dvd_zero _
  obtain ⟨i, hi⟩ : ∃ i, p ^ s * u = i + 1 := ⟨p ^ s * u - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  -- `(i+1) * C(N+1, i+1) = (N+1) * C(N, i)`
  have hkey : (p ^ s * u) * ((N + 1).choose (p ^ s * u) * (p ^ s * u - 1)!) =
      (N + 1) * (N.choose i * i !) := by
    rw [hi, Nat.add_sub_cancel, ← mul_assoc, ← mul_assoc, mul_comm (i + 1),
      ← Nat.add_one_mul_choose_eq]
  have hdiv : p ^ s * p ^ k ∣ p ^ s * (u * ((N + 1).choose (p ^ s * u) * (p ^ s * u - 1)!)) := by
    rw [← mul_assoc, hkey, mul_comm (p ^ s)]
    refine mul_dvd_mul hM ?_
    rw [hi, Nat.add_sub_cancel] at hfac
    exact hfac.trans (Dvd.intro_left _ rfl)
  have hcop : Nat.Coprime (p ^ k) u :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos s) hdiv)


/-- Wilson-type congruence: if `p` is an odd prime and `p ∣ M` with `M ≥ 1`, then
`(M-1)(M-2)...(M-p+1) ≡ (p-1)! ≡ -1 (mod p)`. -/
theorem dvd_descFactorial_add_one (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hM : p ∣ M)
    (hM1 : 1 ≤ M) : p ∣ (M - 1).descFactorial (p - 1) + 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff]
  have hM0 : ((M - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hM1, (ZMod.natCast_eq_zero_iff M p).mpr hM, Nat.cast_one, zero_sub]
  have hprod : ∏ j ∈ range (p - 1), ((-1 : ZMod p) - j) =
      (-1) ^ (p - 1) * ((p - 1)! : ℕ) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    have hterm : ∏ j ∈ range (p - 1), ((-1 : ZMod p) - j) =
        ∏ j ∈ range (p - 1), ((-1 : ZMod p) * ((j + 1 : ℕ) : ZMod p)) :=
      prod_congr rfl fun j _ => by push_cast; ring
    rw [hterm, prod_mul_distrib, prod_const, card_range]
  push_cast
  rw [← descPochhammer_eval_eq_descFactorial, hM0, descPochhammer_eval_eq_prod_range, hprod,
    (hp.even_sub_one hp2).neg_one_pow, one_mul, ZMod.wilsons_lemma, neg_add_cancel]


/-- The exceptional term `j = p` for an odd prime `p`:
`C(m p^k, p) * (p-1)! ≡ -m p^(k-1) (mod p^k)` for `k ≥ 1`, `m ≥ 1`. -/
theorem pow_dvd_term_p_add (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hm : 1 ≤ m) :
    p ^ k ∣ (m * p ^ k).choose p * (p - 1)! + m * p ^ (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set M := m * p ^ (k + 1) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero))
  have hpM : p ∣ M := ⟨m * p ^ k, by rw [hMdef, pow_succ]; ring⟩
  obtain ⟨c, hc⟩ := dvd_descFactorial_add_one p M hp hp2 hpM hM1
  -- `p * (C(M,p) (p-1)!) = M * (M-1)^{(p-1)}`
  have hpT : p * (M.choose p * (p - 1)!) = M * (M - 1).descFactorial (p - 1) := by
    have hdesc := Nat.succ_descFactorial_succ (M - 1) (p - 1)
    rw [Nat.sub_add_cancel hM1, Nat.sub_add_cancel hp.one_le] at hdesc
    rw [← hdesc, Nat.descFactorial_eq_factorial_mul_choose, mul_left_comm,
      Nat.mul_factorial_pred hp.ne_zero, mul_comm]
  have hmul : p * (M.choose p * (p - 1)! + m * p ^ k) = p * (M * c) := by
    rw [mul_add, hpT, mul_left_comm p m, ← _root_.pow_succ', mul_left_comm p M, ← hc, mul_add,
      mul_one, hMdef]
  rw [Nat.eq_of_mul_eq_mul_left hp.pos hmul]
  exact Dvd.dvd.mul_right (Dvd.intro_left _ hMdef.symm) c

/-- The two exceptional terms `j = 2, 4` for `p = 2`: their sum
`C(M,2) * 1! + C(M,4) * 3!` is divisible by `M` whenever `4 ∣ M`, `M ≥ 4`. -/
theorem dvd_two_terms (t : ℕ) :
    (4 * t + 4) ∣ (4 * t + 4).choose 2 * (2 - 1)! + (4 * t + 4).choose 4 * (4 - 1)! := by
  have e2 : 2 * (4 * t + 4).choose 2 = (4 * t + 4) * (4 * t + 3) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (4 * t + 4) 2
    rw [show (4 * t + 4) = (4 * t + 3) + 1 by ring, Nat.succ_descFactorial_succ,
      Nat.descFactorial_one] at h
    simpa using h.symm
  have e4 : 24 * (4 * t + 4).choose 4 =
      (4 * t + 4) * (4 * t + 3) * (4 * t + 2) * (4 * t + 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (4 * t + 4) 4
    rw [show (4 * t + 4) = (4 * t) + 1 + 1 + 1 + 1 by ring] at h ⊢
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show (4 : ℕ)! = 24 by rfl] at h
    rw [← h]
    ring
  refine ⟨(4 * t + 3) * (4 * t ^ 2 + 3 * t + 1), ?_⟩
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) ?_
  have h4 : 4 * ((4 * t + 4).choose 2 * (2 - 1)! + (4 * t + 4).choose 4 * (4 - 1)!) =
      2 * (2 * (4 * t + 4).choose 2) + 24 * (4 * t + 4).choose 4 := by
    simp only [show (2 - 1)! = 1 by rfl, show (4 - 1)! = 6 by rfl]
    ring
  rw [h4, e2, e4]
  ring


/-- **Step 2, odd primes.** For an odd prime `p` and `k ≥ 1`,
`a(m p^k) ≡ -m p^(k-1) (mod p^k)`. -/
theorem pow_dvd_a_add_odd (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    p ^ k ∣ a (m * p ^ k) + m * p ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [a]
  have hpmem : p ∈ Icc 1 (m * p ^ k) := by
    rw [mem_Icc]
    refine ⟨hp.one_le, ?_⟩
    calc p ≤ p ^ k := Nat.le_self_pow (by omega) p
      _ ≤ m * p ^ k := Nat.le_mul_of_pos_left _ hm
  rw [a, ← add_sum_erase _ _ hpmem, add_right_comm]
  refine dvd_add (pow_dvd_term_p_add p k m hp hp2 hk hm) (dvd_sum fun j hj => ?_)
  rw [mem_erase, mem_Icc] at hj
  exact pow_dvd_term p k _ j hp (dvd_mul_left _ _) hj.2.1 hj.1 (fun h => absurd h hp2)

/-- **Step 2, `p = 2`.** For `k ≥ 2`, `a(m 2^k) ≡ 0 (mod 2^k)`. -/
theorem two_pow_dvd_a (k m : ℕ) (hk : 2 ≤ k) : 2 ^ k ∣ a (m * 2 ^ k) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [a]
  obtain ⟨t, ht⟩ : ∃ t, m * 2 ^ k = 4 * t + 4 := by
    refine ⟨m * 2 ^ (k - 2) - 1, ?_⟩
    have hpow : 2 ^ k = 4 * 2 ^ (k - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_add, Nat.add_sub_cancel' hk]
    have hpos : 1 ≤ m * 2 ^ (k - 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hpow, mul_left_comm]
    omega
  have h2 : 2 ∈ Icc 1 (m * 2 ^ k) := by rw [mem_Icc]; omega
  have h4 : 4 ∈ (Icc 1 (m * 2 ^ k)).erase 2 := by rw [mem_erase, mem_Icc]; omega
  rw [a, ← add_sum_erase _ _ h2, ← add_sum_erase _ _ h4, ← add_assoc]
  refine dvd_add ?_ (dvd_sum fun j hj => ?_)
  · exact (Dvd.intro_left m rfl).trans (ht ▸ dvd_two_terms t)
  · rw [mem_erase, mem_erase, mem_Icc] at hj
    exact pow_dvd_term 2 k _ j Nat.prime_two (dvd_mul_left _ _) hj.2.2.1 hj.2.1
      (fun _ => hj.1)

/-- **Step 1 in `ℤ`.** `M ∣ a(n + M) - a(n) - a(M)`, differences taken after casting. -/
theorem dvd_a_add_sub (n M : ℕ) : (M : ℤ) ∣ (a (n + M) : ℤ) - (a n + a M) := by
  have h := Nat.modEq_iff_dvd.mp (a_add_modEq n M).symm
  push_cast at h
  exact h

/-- **Bala's conjecture (1), A002104 (Peter Bala, 2022).**
"for n, m >= 0, k >= 2, a(n + m*2^k) - a(n) is divisible by 2^k."
Stated in `ℤ` with the difference taken after casting. -/
theorem bala_conjecture_one (n m k : ℕ) (hk : 2 ≤ k) :
    (2 : ℤ) ^ k ∣ (a (n + m * 2 ^ k) : ℤ) - a n := by
  have h1 := dvd_a_add_sub n (m * 2 ^ k)
  have h2 : (2 : ℤ) ^ k ∣ (a (m * 2 ^ k) : ℤ) := by exact_mod_cast two_pow_dvd_a k m hk
  have hM : (2 : ℤ) ^ k ∣ ((m * 2 ^ k : ℕ) : ℤ) := by push_cast; exact dvd_mul_left _ _
  have hsplit : (a (n + m * 2 ^ k) : ℤ) - a n =
      (a (m * 2 ^ k) : ℤ) + ((a (n + m * 2 ^ k) : ℤ) - (a n + a (m * 2 ^ k))) := by ring
  rw [hsplit]
  exact dvd_add h2 (hM.trans h1)

/-- **Bala's conjecture (2), A002104 (Peter Bala, 2022).**
"for n >= 0, a(n + m*p^k) - a(n) + m*p^(k-1) is divisible by p^k for all
positive integers m and k, and for all odd primes p."
Stated in `ℤ`; `k - 1` is guarded by `0 < k`.  The entry quantifies over positive `m`;
the statement is proved for every `m : ℕ`, the case `m = 0` being the trivial
identity `p^k ∣ 0`, so this is the entry's claim with that trivial case included. -/
theorem bala_conjecture_two (p n m k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    (p : ℤ) ^ k ∣ (a (n + m * p ^ k) : ℤ) - a n + m * p ^ (k - 1) := by
  have h1 := dvd_a_add_sub n (m * p ^ k)
  have h2 : (p : ℤ) ^ k ∣ (a (m * p ^ k) : ℤ) + m * p ^ (k - 1) := by
    exact_mod_cast pow_dvd_a_add_odd p k m hp hp2 hk
  have hM : (p : ℤ) ^ k ∣ ((m * p ^ k : ℕ) : ℤ) := by push_cast; exact dvd_mul_left _ _
  have hsplit : (a (n + m * p ^ k) : ℤ) - a n + m * p ^ (k - 1) =
      ((a (m * p ^ k) : ℤ) + m * p ^ (k - 1)) +
        ((a (n + m * p ^ k) : ℤ) - (a n + a (m * p ^ k))) := by ring
  rw [hsplit]
  exact dvd_add h2 (hM.trans h1)

/-! ## Examples -/

-- Non-vacuity of (2): Adamchuk's case `p = 3, n = m = k = 1`, hypotheses jointly
-- satisfiable, and the concrete instance `3 ∣ a 4 - a 1 + 1 = 24`.
example : (3 : ℤ) ^ 1 ∣ (a (1 + 1 * 3 ^ 1) : ℤ) - a 1 + 1 * 3 ^ (1 - 1) :=
  bala_conjecture_two 3 1 1 1 Nat.prime_three (by norm_num) (by norm_num)

example : (a (1 + 1 * 3 ^ 1) : ℤ) - a 1 + 1 * 3 ^ (1 - 1) = 24 := by decide

-- Non-vacuity of (1): `k = 2, n = m = 1`, where `a 5 - a 1 = 88 = 4 * 22`.
example : (2 : ℤ) ^ 2 ∣ (a (1 + 1 * 2 ^ 2) : ℤ) - a 1 :=
  bala_conjecture_one 1 1 2 le_rfl

example : (a (1 + 1 * 2 ^ 2) : ℤ) - a 1 = 88 := by decide

-- The guard `k ≥ 2` in (1) is load-bearing: at `k = 1, n = 0, m = 1`,
-- `a 2 - a 0 = 3` is odd.
example : ¬ (2 : ℤ) ^ 1 ∣ (a (0 + 1 * 2 ^ 1) : ℤ) - a 0 := by decide

-- Side finding: the in-entry congruence printed as
-- "a(n) - a(n + m) == a(1) - a(m) (mod m)" fails as printed at `n = 0, m = 2`
-- (Step 1 gives `a(n) - a(n + m) ≡ -a(m) ≡ a(1) - a(m + 1) (mod m)` instead).
example : ¬ (a 0 : ℤ) - a (0 + 2) ≡ a 1 - a 2 [ZMOD 2] := by decide

end Candidates.A002104PeterBalaConjectures
