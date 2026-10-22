/-
# A265310 — least `k` with `∏_{d ∣ n} d ∣ k!`: the fixed points `a(n) = n`

Gionata Neri's conjecture in OEIS A265310 characterizes the fixed points of
the least positive `k` for which the divisor product of `n` divides `k!`:
`a(n) = n` iff `n` is prime, twice a prime, or one of `1,8,9`.

## Proof outline

* `P(n) ∣ n!` always: the divisors are distinct elements of `[1, n]`.  Hence
  `a(n) ≤ n`, and for `n ≥ 2`, `a(n) = n ↔ P(n) ∤ (n - 1)!`.
* Pair lemma: if `x ≠ y` are non-divisors of `n` in `[1, n)` with `n ∣ x y`,
  then the proper divisors with `x, y` are distinct elements of `[1, n - 1]`,
  and `P(n) = (∏ proper divisors) · n ∣ (n - 1)!`.
* `n = a b` with `3 ≤ a, b`, `a ≠ b`: take `x = a (b - 1)`, `y = b (a - 1)`.
  `n = a²` with `a ≥ 5`: take `x = a (a - 1)`, `y = a (a - 2)`.  `n = 16` is
  checked directly.  Every composite `n ∉ {8, 9}` that is not `2p` is covered.
* Fixed points: `p ∣ P(p)`, `p ∤ (p - 1)!`; `p² ∣ P(2p)` (divisors `p, 2p`)
  and `p² ∤ (2p - 1)!` (Legendre); `n = 8, 9` by direct computation.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A265310ProdLeastPrime

open Nat

/-- The product of the divisors of `n` (OEIS A007955): `P(n) = ∏_{d ∣ n} d`.
At `n = 0` the Mathlib divisor set is empty and the value is `1`. -/
def divisorProd (n : ℕ) : ℕ := ∏ d ∈ n.divisors, d

/-- The divisors of `n` are distinct elements of `[1, n]`, so their product divides `n!`. -/
theorem divisorProd_dvd_factorial (n : ℕ) : divisorProd n ∣ n ! := by
  rw [← Finset.prod_Ico_id_eq_factorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro d hd
  rw [Nat.mem_divisors] at hd
  rw [Finset.mem_Ico]
  exact ⟨Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2),
    Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1)⟩

/-- Some positive `k` has `P(n) ∣ k!` (for instance `k = n + 1`). -/
theorem exists_pos_dvd_factorial (n : ℕ) : ∃ k, 0 < k ∧ divisorProd n ∣ k ! :=
  ⟨n + 1, Nat.succ_pos n,
    (divisorProd_dvd_factorial n).trans (Nat.factorial_dvd_factorial (Nat.le_succ n))⟩

/-- OEIS A265310: the least positive `k` such that the product of the divisors of `n`
divides `k!`. -/
def a (n : ℕ) : ℕ := Nat.find (exists_pos_dvd_factorial n)

/-- Characterization of `a n = k` as "least positive `k` with `P(n) ∣ k!`". -/
theorem a_eq_iff (n k : ℕ) :
    a n = k ↔ (0 < k ∧ divisorProd n ∣ k !) ∧ ∀ j < k, ¬ (0 < j ∧ divisorProd n ∣ j !) :=
  Nat.find_eq_iff _

/-- `P(n) = (∏ proper divisors) * n` for `n ≠ 0`. -/
theorem divisorProd_eq_mul {n : ℕ} (hn : n ≠ 0) :
    divisorProd n = (∏ d ∈ n.properDivisors, d) * n := by
  unfold divisorProd
  rw [← Nat.insert_self_properDivisors hn, Finset.prod_insert Nat.self_notMem_properDivisors,
    mul_comm]

/-- **Pair lemma.** If two distinct non-divisors `x, y` of `n` in `[1, n)` satisfy
`n ∣ x * y`, then `P(n) ∣ (n - 1)!`: the proper divisors together with `x, y` are
distinct elements of `[1, n - 1]`. -/
theorem divisorProd_dvd_factorial_pred_of_pair {n x y : ℕ} (hx0 : 0 < x) (hy0 : 0 < y)
    (hxn : x < n) (hyn : y < n) (hxy : x ≠ y) (hxd : ¬ x ∣ n) (hyd : ¬ y ∣ n)
    (hdvd : n ∣ x * y) : divisorProd n ∣ (n - 1) ! := by
  have hn : n ≠ 0 := by omega
  have hxP : x ∉ n.properDivisors := fun h => hxd (Nat.mem_properDivisors.mp h).1
  have hyP : y ∉ n.properDivisors := fun h => hyd (Nat.mem_properDivisors.mp h).1
  have hxT : x ∉ insert y n.properDivisors := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hxy, hxP⟩
  have hsub : insert x (insert y n.properDivisors) ⊆ Finset.Ico 1 (n - 1 + 1) := by
    intro d hd
    rw [Finset.mem_Ico]
    rcases Finset.mem_insert.mp hd with rfl | hd
    · omega
    rcases Finset.mem_insert.mp hd with rfl | hd
    · omega
    have hd' := Nat.mem_properDivisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (Nat.pos_of_ne_zero hn)
    omega
  have hprod : ∏ d ∈ insert x (insert y n.properDivisors), d
      = (∏ d ∈ n.properDivisors, d) * (x * y) := by
    rw [Finset.prod_insert hxT, Finset.prod_insert hyP]
    ring
  rw [divisorProd_eq_mul hn, ← Finset.prod_Ico_id_eq_factorial]
  calc (∏ d ∈ n.properDivisors, d) * n ∣ (∏ d ∈ n.properDivisors, d) * (x * y) :=
        Nat.mul_dvd_mul_left _ hdvd
    _ = ∏ d ∈ insert x (insert y n.properDivisors), d := hprod.symm
    _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- If `0 < c < b - c` then `a * (b - c)` does not divide `a * b` (for `0 < a`). -/
theorem mul_sub_not_dvd_mul {a b c : ℕ} (ha : 0 < a) (hc : 0 < c) (h : c < b - c) :
    ¬ a * (b - c) ∣ a * b := by
  intro hdvd
  have hbc : b - c ∣ b := (Nat.mul_dvd_mul_iff_left ha).mp hdvd
  have hsum : b - c ∣ (b - c) + c := by rwa [Nat.sub_add_cancel (by omega)]
  have hc' : b - c ∣ c := (Nat.dvd_add_right (dvd_refl (b - c))).mp hsum
  have hle : b - c ≤ c := Nat.le_of_dvd hc hc'
  omega

/-- **Rectangle case.** For `3 ≤ a`, `3 ≤ b`, `a ≠ b`: `P(a b) ∣ (a b - 1)!`, using the
non-divisors `a (b - 1)` and `b (a - 1)`. -/
theorem divisorProd_mul_dvd_factorial_pred {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) :
    divisorProd (a * b) ∣ (a * b - 1) ! := by
  have hx : a * (b - 1) + a = a * b := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right a (by omega))]
  have hy : b * (a - 1) + b = a * b := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right b (by omega)), mul_comm]
  have hxpos : 0 < a * (b - 1) := Nat.mul_pos (by omega) (by omega)
  have hypos : 0 < b * (a - 1) := Nat.mul_pos (by omega) (by omega)
  refine divisorProd_dvd_factorial_pred_of_pair hxpos hypos (by omega) (by omega)
    (by omega) ?_ ?_ ?_
  · exact mul_sub_not_dvd_mul (by omega) one_pos (by omega)
  · rw [mul_comm a b]
    exact mul_sub_not_dvd_mul (by omega) one_pos (by omega)
  · exact ⟨(b - 1) * (a - 1), by ring⟩

/-- **Square case.** For `5 ≤ a`: `P(a²) ∣ (a² - 1)!`, using the non-divisors
`a (a - 1)` and `a (a - 2)`. -/
theorem divisorProd_sq_dvd_factorial_pred {a : ℕ} (ha : 5 ≤ a) :
    divisorProd (a * a) ∣ (a * a - 1) ! := by
  have hx : a * (a - 1) + a = a * a := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right a (by omega))]
  have hy : a * (a - 2) + 2 * a = a * a := by
    rw [Nat.mul_sub, mul_comm 2 a, Nat.sub_add_cancel (Nat.mul_le_mul_left a (by omega))]
  have hxpos : 0 < a * (a - 1) := Nat.mul_pos (by omega) (by omega)
  have hypos : 0 < a * (a - 2) := Nat.mul_pos (by omega) (by omega)
  refine divisorProd_dvd_factorial_pred_of_pair hxpos hypos (by omega) (by omega)
    (by omega) ?_ ?_ ?_
  · exact mul_sub_not_dvd_mul (by omega) one_pos (by omega)
  · exact mul_sub_not_dvd_mul (by omega) two_pos (by omega)
  · exact ⟨(a - 1) * (a - 2), by ring⟩

/-- The exceptional power of two `n = 16`: `P(16) = 2^10` divides `15!`. -/
theorem divisorProd_sixteen_dvd : divisorProd 16 ∣ 15 ! := by
  decide

/-- A composite `n ≥ 2` factors as `q * m` with `q` prime and `q ≤ m` (take `q = minFac n`). -/
theorem exists_prime_mul_of_not_prime {n : ℕ} (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    ∃ q m : ℕ, q.Prime ∧ q ≤ m ∧ n = q * m := by
  have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hp
  have hn' : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
  refine ⟨n.minFac, n / n.minFac, hq, ?_, hn'⟩
  have hle : n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) := by
    rw [← hn', ← pow_two]
    exact hsq
  exact Nat.le_of_mul_le_mul_left hle hq.pos

/-- **Key upper bound.** If `n ≥ 2` is not prime, not twice a prime, and not `8` or `9`,
then `P(n) ∣ (n - 1)!`. -/
theorem divisorProd_dvd_factorial_pred_of_not_special {n : ℕ} (hn : 2 ≤ n) (hp : ¬ n.Prime)
    (h8 : n ≠ 8) (h9 : n ≠ 9) (h2p : ¬ ∃ p, p.Prime ∧ n = 2 * p) :
    divisorProd n ∣ (n - 1) ! := by
  obtain ⟨q, m, hq, hqm, rfl⟩ := exists_prime_mul_of_not_prime hn hp
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · -- `q = 2`, so `n = 2 m` with `m` composite
    have hq2 : q = 2 := le_antisymm (by omega) hq.two_le
    subst hq2
    have hm : ¬ m.Prime := fun hm => h2p ⟨m, hm, rfl⟩
    obtain ⟨r, s, hr, hrs, rfl⟩ := exists_prime_mul_of_not_prime hqm hm
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · have hr2 : r = 2 := le_antisymm (by omega) hr.two_le
      subst hr2
      have hs16 : 2 * (2 * s) = 4 * s := by ring
      rw [hs16]
      rcases Nat.lt_trichotomy s 4 with hs | hs | hs
      · have hs3 : s = 3 := by omega
        subst hs3
        exact divisorProd_mul_dvd_factorial_pred (a := 4) (b := 3) (by norm_num) le_rfl (by norm_num)
      · subst hs
        exact divisorProd_sixteen_dvd
      · exact divisorProd_mul_dvd_factorial_pred (by norm_num) (by omega) (by omega)
    · have hrs2 : 2 * (r * s) = r * (2 * s) := by ring
      rw [hrs2]
      exact divisorProd_mul_dvd_factorial_pred hr3 (by omega) (by omega)
  · rcases Nat.lt_or_ge q m with hlt | hge
    · exact divisorProd_mul_dvd_factorial_pred hq3 (by omega) (by omega)
    · have hqm' : m = q := le_antisymm hge hqm
      subst hqm'
      have hq5 : 5 ≤ m := by
        rcases Nat.lt_or_ge m 5 with h5 | h5
        · interval_cases m
          · exact absurd rfl h9
          · exact absurd hq (by decide)
        · exact h5
      exact divisorProd_sq_dvd_factorial_pred hq5

/-- Any subfamily of the divisors has product dividing `P(n)`. -/
theorem prod_dvd_divisorProd_of_subset {n : ℕ} {T : Finset ℕ} (hT : T ⊆ n.divisors) :
    ∏ d ∈ T, d ∣ divisorProd n :=
  Finset.prod_dvd_prod_of_subset _ _ _ hT

/-- For `p` prime, `P(p) ∤ (p - 1)!`. -/
theorem divisorProd_prime_not_dvd {p : ℕ} (hp : p.Prime) : ¬ divisorProd p ∣ (p - 1) ! := by
  intro h
  have hpP : p ∣ divisorProd p :=
    Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self p hp.ne_zero)
  have hle : p ≤ p - 1 := (hp.dvd_factorial).mp (hpP.trans h)
  have h2 := hp.two_le
  omega

/-- For `p` prime, `p^2 ∤ (2p - 1)!`. -/
theorem prime_sq_not_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ (2 * p - 1) ! := by
  have h2 := hp.two_le
  have hlt : 2 * p - 1 < p ^ 2 := by
    rw [pow_two]
    have : 2 * p ≤ p * p := Nat.mul_le_mul_right p h2
    omega
  have hlog : Nat.log p (2 * p - 1) < 2 := Nat.log_lt_of_lt_pow (by omega) hlt
  rw [hp.pow_dvd_factorial_iff hlog]
  have hdiv : (2 * p - 1) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [hdiv]

/-- For `p` prime, `P(2p) ∤ (2p - 1)!`: the distinct divisors `p` and `2p` give
`p^2 ∣ P(2p)`. -/
theorem divisorProd_two_mul_prime_not_dvd {p : ℕ} (hp : p.Prime) :
    ¬ divisorProd (2 * p) ∣ (2 * p - 1) ! := by
  intro h
  have h2 := hp.two_le
  have hsub : ({p, 2 * p} : Finset ℕ) ⊆ (2 * p).divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    rcases hd with rfl | rfl
    · exact ⟨Dvd.intro_left 2 rfl, by omega⟩
    · exact ⟨dvd_rfl, by omega⟩
  have hne : p ∉ ({2 * p} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    omega
  have hprod : ∏ d ∈ ({p, 2 * p} : Finset ℕ), d = p * (2 * p) := by
    rw [Finset.prod_insert hne, Finset.prod_singleton]
  have hsq : p ^ 2 ∣ divisorProd (2 * p) := by
    refine Dvd.dvd.trans ?_ (prod_dvd_divisorProd_of_subset hsub)
    rw [hprod]
    exact ⟨2, by ring⟩
  exact prime_sq_not_dvd_factorial hp (hsq.trans h)

/-- `a n` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n := (Nat.find_spec (exists_pos_dvd_factorial n)).1

/-- `a n ≤ n` for `0 < n`, since `P(n) ∣ n!`. -/
theorem a_le_self {n : ℕ} (hn : 0 < n) : a n ≤ n :=
  Nat.find_le ⟨hn, divisorProd_dvd_factorial n⟩

/-- For `n ≥ 2`: `a n = n` iff `P(n) ∤ (n - 1)!`. -/
theorem a_eq_self_iff_not_dvd {n : ℕ} (hn : 2 ≤ n) :
    a n = n ↔ ¬ divisorProd n ∣ (n - 1) ! := by
  constructor
  · intro ha hdvd
    have hle : a n ≤ n - 1 := Nat.find_le ⟨by omega, hdvd⟩
    omega
  · intro hnd
    rw [a_eq_iff]
    refine ⟨⟨by omega, divisorProd_dvd_factorial n⟩, ?_⟩
    rintro j hj ⟨-, hdj⟩
    exact hnd (hdj.trans (Nat.factorial_dvd_factorial (by omega)))

/-- **A265310 conjecture (OEIS A265310, comment line, entry by Gionata Neri).**

Here `a n` is the least positive `k` with `∏_{d ∣ n} d ∣ k!`. For every `n ≥ 1`,
`a n = n` exactly when `n = 1`, `n = 8`, `n = 9`, `n` is prime, or `n = 2 p` with `p`
prime (this includes `n = 4 = 2 · 2`). -/
theorem a_eq_self_iff (n : ℕ) (hn : 0 < n) :
    a n = n ↔ n = 1 ∨ n = 8 ∨ n = 9 ∨ n.Prime ∨ ∃ p, p.Prime ∧ n = 2 * p := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hle := a_le_self one_pos
    have hpos := a_pos 1
    exact ⟨fun _ => Or.inl rfl, fun _ => by omega⟩
  rw [a_eq_self_iff_not_dvd h2]
  constructor
  · intro hnd
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨-, h8, h9, hp, h2p⟩ := hcon
    exact hnd (divisorProd_dvd_factorial_pred_of_not_special h2 hp h8 h9 h2p)
  · rintro (h | h | h | h | ⟨p, hp, rfl⟩)
    · omega
    · subst h
      decide
    · subst h
      decide
    · exact divisorProd_prime_not_dvd h
    · exact divisorProd_two_mul_prime_not_dvd hp

/-! ## the first 30 terms of the OEIS DATA line -/

-- `a n` matches the DATA line `1, 2, 3, ..., 29, 20` for `n = 1, ..., 30`.
example : a 1 = 1 := by rw [a_eq_iff]; decide
example : a 2 = 2 := by rw [a_eq_iff]; decide
example : a 3 = 3 := by rw [a_eq_iff]; decide
example : a 4 = 4 := by rw [a_eq_iff]; decide
example : a 5 = 5 := by rw [a_eq_iff]; decide
example : a 6 = 6 := by rw [a_eq_iff]; decide
example : a 7 = 7 := by rw [a_eq_iff]; decide
example : a 8 = 8 := by rw [a_eq_iff]; decide
example : a 9 = 9 := by rw [a_eq_iff]; decide
example : a 10 = 10 := by rw [a_eq_iff]; decide
example : a 11 = 11 := by rw [a_eq_iff]; decide
example : a 12 = 9 := by rw [a_eq_iff]; decide
example : a 13 = 13 := by rw [a_eq_iff]; decide
example : a 14 = 14 := by rw [a_eq_iff]; decide
example : a 15 = 10 := by rw [a_eq_iff]; decide
example : a 16 = 12 := by rw [a_eq_iff]; decide
example : a 17 = 17 := by rw [a_eq_iff]; decide
example : a 18 = 15 := by rw [a_eq_iff]; decide
example : a 19 = 19 := by rw [a_eq_iff]; decide
example : a 20 = 15 := by rw [a_eq_iff]; decide
example : a 21 = 14 := by rw [a_eq_iff]; decide
example : a 22 = 22 := by rw [a_eq_iff]; decide
example : a 23 = 23 := by rw [a_eq_iff]; decide
example : a 24 = 16 := by rw [a_eq_iff]; decide
example : a 25 = 15 := by rw [a_eq_iff]; decide
example : a 26 = 26 := by rw [a_eq_iff]; decide
example : a 27 = 15 := by rw [a_eq_iff]; decide
example : a 28 = 21 := by rw [a_eq_iff]; decide
example : a 29 = 29 := by rw [a_eq_iff]; decide
example : a 30 = 20 := by rw [a_eq_iff]; decide

-- Both sides of the main equivalence are realized: a fixed point that is none of
-- prime, `2p`, `1` (namely `8`), and a non-fixed point (`12`).
example : a 8 = 8 ∧ a 12 ≠ 12 := by
  refine ⟨(a_eq_self_iff 8 (by norm_num)).mpr (Or.inr (Or.inl rfl)), ?_⟩
  rw [Ne, a_eq_self_iff 12 (by norm_num)]
  rintro (h | h | h | h | ⟨p, hp, hp12⟩)
  · omega
  · omega
  · omega
  · exact absurd h (by decide)
  · have hp6 : p = 6 := by omega
    subst hp6
    exact absurd hp (by decide)

-- `P(n)` matches A007955 at small arguments.
example : divisorProd 12 = 1728 ∧ divisorProd 16 = 1024 ∧ divisorProd 8 = 64 := by decide

end Candidates.A265310ProdLeastPrime
