/-
Refutation of part (2) of the A086551 conjectures (Amarnath Murthy, Aug 28 2003).

For the least k≥2 with τ(k)=n τ(k-1), or zero if absent,
a(17)=983040=2^16*3*5 and a(17)-1=241*4079 is composite.
David Wasserman records this counterexample (Mar 24 2005).
The proof establishes minimality, not just a solution of the divisor equation.
Also a(2)=2, so a(2)-1=1 is not prime. The nonzeroness claim for every n,
part (1), is not addressed; the conjunction is refuted through part (2).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086551Refutation

/-! ## Definition layer -/

/-- The set of `k ≥ 2` with `tau(k) = n * tau(k - 1)`, where `tau` is the
number of divisors.  The guard `2 ≤ k` keeps `k - 1` a positive integer
(OEIS `tau` is defined on positive integers; Mathlib has
`Nat.divisors 0 = ∅`, so `k = 0` would be a junk solution). -/
def tauMultSet (n : ℕ) : Set ℕ :=
  {k | 2 ≤ k ∧ k.divisors.card = n * (k - 1).divisors.card}

/-- A086551: `a(n)` is the smallest `k` with `tau(k) = n * tau(k - 1)`, or `0`
if no such `k` exists (`sInf ∅ = 0` on `ℕ` realises the OEIS convention). -/
noncomputable def a (n : ℕ) : ℕ := sInf (tauMultSet n)

/-- If `k` is the least element of `tauMultSet n`, then `a n = k`. -/
theorem a_eq_of_isLeast {n k : ℕ} (h : IsLeast (tauMultSet n) k) : a n = k :=
  h.csInf_eq

/-- A finite criterion for `IsLeast (tauMultSet n) k`: `k` is a solution and
no `j` with `2 ≤ j < k` is. -/
theorem isLeast_tauMultSet {n k : ℕ} (hk : 2 ≤ k)
    (hsol : k.divisors.card = n * (k - 1).divisors.card)
    (hmin : ∀ j, 2 ≤ j → j < k → j.divisors.card ≠ n * (j - 1).divisors.card) :
    IsLeast (tauMultSet n) k := by
  refine ⟨⟨hk, hsol⟩, fun j hj => ?_⟩
  by_contra hlt
  exact hmin j hj.1 (Nat.lt_of_not_le hlt) hj.2

/-! ## The first listed terms `3, 2, 12, 24, 48, 60` -/

example : a 1 = 3 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide) (by decide))

example : a 2 = 2 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide) (by decide))

example : a 3 = 12 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide) (by decide))

example : a 4 = 24 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide) (by decide))

example : a 5 = 48 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide +kernel) (by decide +kernel))

example : a 6 = 60 :=
  a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide +kernel) (by decide +kernel))

/-! ## The conjecture -/

/-- Murthy's two claims: no term is zero, and every predecessor is prime,
for source indices `n≥1`. Writing the second clause as `a n=p+1` for prime
`p` avoids truncated natural subtraction and excludes `a n=0`. -/
def Conjecture : Prop :=
  (∀ n, 1 ≤ n → a n ≠ 0) ∧ (∀ n, 1 ≤ n → ∃ p, p.Prime ∧ a n = p + 1)

/-! ## The counterexample `n = 17` -/

/-- `tau(2^16) = 17`. -/
theorem card_divisors_two_pow_sixteen : (2 ^ 16 : ℕ).divisors.card = 17 := by
  rw [Nat.divisors_prime_pow Nat.prime_two 16, Finset.card_map, Finset.card_range]

/-- If `0 < k < 983040` and `17 ∣ tau(k)`, then the exponent of `2` in `k` is
exactly `16`: some prime exponent `e` has `17 ∣ e + 1`, the bound `k < 2^20`
forces `e = 16`, and `k < 3^16` forces the prime to be `2`. -/
theorem factorization_two_eq_sixteen {k : ℕ} (hk : k ≠ 0) (hlt : k < 983040)
    (h17 : 17 ∣ k.divisors.card) : k.factorization 2 = 16 := by
  rw [Nat.card_divisors hk, Prime.dvd_finsetProd_iff (by norm_num : Nat.Prime 17).prime] at h17
  obtain ⟨p, hp, hdvd⟩ := h17
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  set f := k.factorization p with hf
  have hpow_le : p ^ f ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.ordProj_dvd k p)
  have hf_lt : f < 20 := by
    by_contra hcon
    have h1 : 2 ^ 20 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ f ≤ p ^ f := Nat.pow_le_pow_left hpp.two_le f
    omega
  have hf16 : f = 16 := by omega
  have hp2 : p = 2 := by
    by_contra hne
    have hp3 : 3 ≤ p := by
      have h2le := hpp.two_le
      omega
    have h1 : 3 ^ 16 ≤ p ^ 16 := Nat.pow_le_pow_left hp3 16
    rw [hf16] at hpow_le
    omega
  rw [← hp2]
  exact hf16

/-- Four distinct divisors `1 < q < k / q < k` give `4 ≤ tau(k)`. -/
theorem four_le_card_divisors {k q r : ℕ} (hk : k = q * r) (hq : 1 < q) (hqr : q < r) :
    4 ≤ k.divisors.card := by
  have hr : 1 < r := hq.trans hqr
  have hk0 : k ≠ 0 := by subst hk; positivity
  have hrk : r < k := by
    subst hk
    calc r = 1 * r := (one_mul r).symm
      _ < q * r := Nat.mul_lt_mul_of_pos_right hq (by omega)
  have hsub : ({1, q, r, k} : Finset ℕ) ⊆ k.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, hk0⟩
    rcases hd with hd | hd | hd | hd
    · exact hd ▸ one_dvd k
    · exact hd ▸ ⟨r, hk⟩
    · exact hd ▸ ⟨q, hk.trans (Nat.mul_comm q r)⟩
    · exact hd ▸ dvd_refl k
  have hcard : ({1, q, r, k} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (by omega)]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  calc 4 = ({1, q, r, k} : Finset ℕ).card := hcard.symm
    _ ≤ k.divisors.card := Finset.card_le_card hsub

/-- No `k` with `2 ≤ k < 983040` satisfies `tau(k) = 17 * tau(k - 1)`. -/
theorem not_mem_tauMultSet_seventeen_of_lt {k : ℕ} (hk : 2 ≤ k) (hlt : k < 983040)
    (hsol : k.divisors.card = 17 * (k - 1).divisors.card) : False := by
  have hk0 : k ≠ 0 := by omega
  have h17 : 17 ∣ k.divisors.card := ⟨_, hsol⟩
  have hf : k.factorization 2 = 16 := factorization_two_eq_sixteen hk0 hlt h17
  set m := k / 2 ^ 16 with hm
  have hdecomp : 2 ^ 16 * m = k := by
    have h := Nat.ordProj_mul_ordCompl_eq_self k 2
    rw [hf] at h
    exact h
  have hcop2 : Nat.Coprime 2 m := by
    have h := Nat.coprime_ordCompl Nat.prime_two hk0
    rw [hf] at h
    exact h
  have hcop : Nat.Coprime (2 ^ 16) m := Nat.Coprime.pow_left 16 hcop2
  have htau : k.divisors.card = 17 * m.divisors.card := by
    rw [← hdecomp, Nat.Coprime.card_divisors_mul hcop, card_divisors_two_pow_sixteen]
  have hpred : (k - 1).divisors.card = m.divisors.card := by
    have h := hsol.symm.trans htau
    omega
  have hm15 : m < 15 := by omega
  have hm0 : m ≠ 0 := by
    rintro hm0
    rw [hm0] at hdecomp
    omega
  interval_cases m
  all_goals first
    | exact absurd hcop2 (by decide)
    | skip
  · -- m = 1: 65535 = 3 * 21845
    have h4 := four_le_card_divisors (k := k - 1) (q := 3) (r := 21845) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 1).card = 1 := by decide
    omega
  · -- m = 3: 196607 = 421 * 467
    have h4 := four_le_card_divisors (k := k - 1) (q := 421) (r := 467) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 3).card = 2 := by decide
    omega
  · -- m = 5: 327679 = 11 * 29789
    have h4 := four_le_card_divisors (k := k - 1) (q := 11) (r := 29789) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 5).card = 2 := by decide
    omega
  · -- m = 7: 458751 = 3 * 152917
    have h4 := four_le_card_divisors (k := k - 1) (q := 3) (r := 152917) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 7).card = 2 := by decide
    omega
  · -- m = 9: 589823 = 13 * 45371
    have h4 := four_le_card_divisors (k := k - 1) (q := 13) (r := 45371) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 9).card = 3 := by decide
    omega
  · -- m = 11: 720895 = 5 * 144179
    have h4 := four_le_card_divisors (k := k - 1) (q := 5) (r := 144179) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 11).card = 2 := by decide
    omega
  · -- m = 13: 851967 = 3 * 283989
    have h4 := four_le_card_divisors (k := k - 1) (q := 3) (r := 283989) (by omega) (by norm_num)
      (by norm_num)
    have hm' : (Nat.divisors 13).card = 2 := by decide
    omega

/-- `tau(983040) = 68 = 17 * tau(983039)`, using `983040 = 2^16 * 15` and
`983039 = 241 * 4079` with `241`, `4079` prime. -/
theorem card_divisors_983040 :
    (983040 : ℕ).divisors.card = 17 * (983040 - 1 : ℕ).divisors.card := by
  have h15 : (Nat.divisors 15).card = 4 := by decide
  have hlhs : (983040 : ℕ).divisors.card = 68 := by
    have h : (983040 : ℕ) = 2 ^ 16 * 15 := by norm_num
    rw [h, Nat.Coprime.card_divisors_mul (by norm_num), card_divisors_two_pow_sixteen, h15]
  have hp1 : Nat.Prime 241 := by norm_num
  have hp2 : Nat.Prime 4079 := by norm_num
  have hrhs : (983040 - 1 : ℕ).divisors.card = 4 := by
    have h : (983040 - 1 : ℕ) = 241 * 4079 := by norm_num
    rw [h, Nat.Coprime.card_divisors_mul ((Nat.coprime_primes hp1 hp2).2 (by norm_num)),
      hp1.divisors, hp2.divisors]
    decide
  rw [hlhs, hrhs]

/-- `983040` is the least `k` with `tau(k) = 17 * tau(k - 1)`. -/
theorem isLeast_tauMultSet_seventeen : IsLeast (tauMultSet 17) 983040 :=
  isLeast_tauMultSet (by norm_num) card_divisors_983040
    fun _ hj hlt hsol => not_mem_tauMultSet_seventeen_of_lt hj hlt hsol

/-- `a(17) = 983040 = 2^16 * 3 * 5`. -/
theorem a_seventeen : a 17 = 983040 :=
  a_eq_of_isLeast isLeast_tauMultSet_seventeen

/-- `a(17) - 1 = 983039 = 241 * 4079` is a product of two primes (Wasserman). -/
theorem a_seventeen_pred_eq :
    a 17 = 241 * 4079 + 1 ∧ Nat.Prime 241 ∧ Nat.Prime 4079 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [a_seventeen]

/-- **Refutation of A086551 conjecture (2)** (Murthy, Aug 28 2003).

For `n = 17` the least `k` with `tau(k) = 17 * tau(k - 1)` is
`a(17) = 983040`, and `a(17) - 1 = 983039 = 241 * 4079` is not prime
(Wasserman, Mar 24 2005).  Hence `Conjecture` fails. -/
theorem a086551_false : ¬ Conjecture := by
  rintro ⟨-, h2⟩
  obtain ⟨p, hp, hap⟩ := h2 17 (by norm_num)
  rw [a_seventeen] at hap
  have hp_eq : p = 983039 := by omega
  rw [hp_eq] at hp
  norm_num at hp

/-- Even with the boundary `n=2` excluded, some `a(n)-1` is composite
at an index `n≥3`. -/
theorem exists_a_pred_composite :
    ∃ n, 3 ≤ n ∧ ∃ q r, 1 < q ∧ 1 < r ∧ a n = q * r + 1 :=
  ⟨17, by norm_num, 241, 4079, by norm_num, by norm_num, a_seventeen_pred_eq.1⟩

/-- Boundary failure of conjecture (2) at `n = 2`: `a(2) = 2`, so
`a(2) - 1 = 1`, which is not prime. -/
theorem a_two : a 2 = 2 ∧ ¬ ∃ p, p.Prime ∧ a 2 = p + 1 := by
  have ha : a 2 = 2 :=
    a_eq_of_isLeast (isLeast_tauMultSet (by norm_num) (by decide) (by decide))
  refine ⟨ha, ?_⟩
  rintro ⟨p, hp, hap⟩
  rw [ha] at hap
  have hp1 : p = 1 := by omega
  exact Nat.not_prime_one (hp1 ▸ hp)

end Candidates.A086551Refutation
