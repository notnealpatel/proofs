/-
# A342039 — refutation of the conjecture `a(n) ≥ prime(n) - 1`

OEIS A342039, Jianing Song: the proposed lower bound
`a(n) ≥ prime(n)-1` fails for `p = 653`. Here A307437 is the least
positive `m` with `2k ∣ λ(m)`. Since `A307437(489) = 4571 = 7·653`,
the first admissible index is at most `489 < 652`. The formal prime
index is obtained as `Nat.count Nat.Prime 653 + 1`, not evaluated.

* `978 = 2 · 489` divides `λ(4571) = lcm(λ 7, λ 653) = lcm(6, 652) = 1956`.
* For `0 < m < 4571`, `978 ∤ φ(m)` (hence `978 ∤ λ(m)`): a factor `163` of
  `φ(m)` forces `163² ∣ m` (too large) or a prime `q ∣ m` with `q ≡ 1 (mod 163)`,
  and below `4571` those primes are only `653` and `2609`; the remaining
  candidates `653 r` (`r ≤ 6`) and `2609` have totient not divisible by `3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A342039Refutation

open ArithmeticFunction

/-! ## Definitions -/

/-- **A307437**: `a307437 k` is the least `m ≥ 1` such that `2k ∣ λ(m)`, where
`λ = ArithmeticFunction.carmichael` is Carmichael's function (OEIS A002322).

The infimum of an empty set of naturals is the junk value `0`; this happens
only at `k = 0` (for `m ≥ 1`, `λ(m) ≥ 1`).  For `k ≥ 1` the set is nonempty by
Dirichlet's theorem, as the entry notes; nothing below relies on that fact. -/
noncomputable def a307437 (k : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ 2 * k ∣ carmichael m}

/-- `IsIndex p k` says that `k ≥ 1` and `A307437(k)` is a multiple of `p`
strictly greater than `p`.  The junk value `a307437 0 = 0` can never satisfy
`p < a307437 k`, and `0 < k` is required in any case. -/
def IsIndex (p k : ℕ) : Prop :=
  0 < k ∧ p ∣ a307437 k ∧ p < a307437 k

/-- **A342039**: `a342039 n` is the least `k` such that `A307437(k)` is divisible
by `p = prime(n)` and greater than `p`.  OEIS indexes primes from `1`
(`prime(1) = 2`), Mathlib's `Nat.nth Nat.Prime` from `0`, hence the shift
`n - 1`; the offset of the entry is `n = 1`. -/
noncomputable def a342039 (n : ℕ) : ℕ :=
  sInf {k : ℕ | IsIndex (Nat.nth Nat.Prime (n - 1)) k}

/-! ## Computation helpers -/

/-- Carmichael's function at an odd prime `p` equals `p - 1`. -/
theorem carmichael_prime_of_ne_two {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) :
    carmichael p = p - 1 := by
  have h := carmichael_pow_of_prime_ne_two 1 hp hp₂
  rwa [pow_one, Nat.totient_prime hp] at h

/-- Characterisation of `a307437 k = v`: `v ≥ 1` works and no smaller positive
`m` does. -/
theorem a307437_eq_of {k v : ℕ} (hv : 0 < v) (hdvd : 2 * k ∣ carmichael v)
    (hmin : ∀ m, 0 < m → m < v → ¬ 2 * k ∣ carmichael m) : a307437 k = v := by
  have hmem : v ∈ {m : ℕ | 0 < m ∧ 2 * k ∣ carmichael m} := ⟨hv, hdvd⟩
  have hle : a307437 k ≤ v := Nat.sInf_le hmem
  have hinf : a307437 k ∈ {m : ℕ | 0 < m ∧ 2 * k ∣ carmichael m} := Nat.sInf_mem ⟨v, hmem⟩
  by_contra hne
  exact hmin (a307437 k) hinf.1 (lt_of_le_of_ne hle hne) hinf.2

/-- If `d ∤ φ(m)` then `d ∤ λ(m)`, since `λ(m) ∣ φ(m)`. -/
theorem not_dvd_carmichael_of_not_dvd_totient {d m : ℕ} (h : ¬ d ∣ m.totient) :
    ¬ d ∣ carmichael m :=
  fun hd => h (hd.trans (carmichael_dvd_totient m))

/-! ## Examples against the entries' data -/

/-- `A307437(1) = 3`. -/
example : a307437 1 = 3 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [carmichael_prime_of_ne_two (by norm_num) (by norm_num)]
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (by interval_cases m <;> decide)

/-- `A307437(2) = 5`. -/
example : a307437 2 = 5 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [carmichael_prime_of_ne_two (by norm_num) (by norm_num)]
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (by interval_cases m <;> decide)

/-- `A307437(3) = 7`. -/
example : a307437 3 = 7 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [carmichael_prime_of_ne_two (by norm_num) (by norm_num)]
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (by interval_cases m <;> decide)

/-- `A307437(5) = 11`. -/
example : a307437 5 = 11 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [carmichael_prime_of_ne_two (by norm_num) (by norm_num)]
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (by interval_cases m <;> decide)

/-- `A307437(10) = 25 = 5²`, the value quoted in the entry's example for
`a(3) = 10`. -/
theorem a307437_ten : a307437 10 = 25 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [show (25 : ℕ) = 5 ^ 2 by norm_num,
      carmichael_pow_of_prime_ne_two 2 (by norm_num) (by norm_num)]
    decide
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (by interval_cases m <;> decide)

/-- The entry's example `n = 3`: `k = 10` is admissible for `p = prime(3) = 5`. -/
example : IsIndex (Nat.nth Nat.Prime (3 - 1)) 10 := by
  rw [show 3 - 1 = 2 from rfl, Nat.nth_prime_two_eq_five, IsIndex, a307437_ten]
  norm_num

/-! ## The conjecture -/

/-- **Conjecture (A342039, Jianing Song, 2021).**
Stated for every `n ≥ 1` (the entry's offset).  The natural subtraction
`prime(n) - 1` is safe since `prime(n) ≥ 2`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → Nat.nth Nat.Prime (n - 1) - 1 ≤ a342039 n

/-! ## The refutation -/

/-- Primes below `4571` congruent to `1` modulo `163` are `653` and `2609`. -/
theorem prime_eq_of_lt_of_dvd_sub_one (p : ℕ) (hp : p.Prime) (hlt : p < 4571)
    (hdvd : 163 ∣ p - 1) : p = 653 ∨ p = 2609 := by
  obtain ⟨j, hj⟩ := hdvd
  have h2 : 2 ≤ p := hp.two_le
  have hpj : p = 163 * j + 1 := by omega
  have hj28 : j ≤ 28 := by omega
  subst hpj
  interval_cases j <;> first | (norm_num at hp; done) | norm_num

/-- If the prime `163` divides `φ(m)` with `m ≠ 0`, then `163² ∣ m` or some
prime `q ∣ m` has `163 ∣ q - 1` (from `φ(m) = ∏ q^(e-1) (q-1)`). -/
theorem sq_dvd_or_exists_prime_of_dvd_totient (m : ℕ) (hm : m ≠ 0)
    (h : 163 ∣ m.totient) :
    163 ^ 2 ∣ m ∨ ∃ q, q.Prime ∧ q ∣ m ∧ 163 ∣ q - 1 := by
  have h163 : (163 : ℕ).Prime := by norm_num
  rw [Nat.totient_eq_prod_factorization hm, Finsupp.prod] at h
  obtain ⟨q, hq, hqd⟩ := (Nat.prime_iff.mp h163).exists_mem_finset_dvd h
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
  rcases (Nat.prime_iff.mp h163).dvd_or_dvd hqd with h1 | h1
  · left
    have hk : 1 ≤ m.factorization q - 1 := by
      by_contra hk
      have hzero : m.factorization q - 1 = 0 := by omega
      rw [hzero, pow_zero] at h1
      exact h163.one_lt.ne' (Nat.dvd_one.mp h1)
    have hq163 : q = 163 :=
      ((Nat.prime_dvd_prime_iff_eq h163 hqp).mp (h163.dvd_of_dvd_pow h1)).symm
    subst hq163
    exact (Nat.pow_dvd_pow 163 (by omega)).trans (Nat.ordProj_dvd m 163)
  · exact Or.inr ⟨q, hqp, hqm, h1⟩

/-- No `m` with `0 < m < 4571` has `978 ∣ φ(m)`. -/
theorem not_dvd_totient_of_lt (m : ℕ) (hm : 0 < m) (hlt : m < 4571) :
    ¬ 978 ∣ m.totient := by
  intro h978
  have h163 : 163 ∣ m.totient := (show (163 : ℕ) ∣ 978 by norm_num).trans h978
  rcases sq_dvd_or_exists_prime_of_dvd_totient m hm.ne' h163 with hsq | ⟨q, hq, hqm, hq1⟩
  · have hle : 163 ^ 2 ≤ m := Nat.le_of_dvd hm hsq
    norm_num at hle
    omega
  · have hqle : q < 4571 := lt_of_le_of_lt (Nat.le_of_dvd hm hqm) hlt
    obtain ⟨r, rfl⟩ := hqm
    have hr : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rcases prime_eq_of_lt_of_dvd_sub_one q hq hqle hq1 with rfl | rfl
    · have hr7 : r ≤ 6 := by omega
      have hcop : Nat.Coprime 653 r := by interval_cases r <;> decide
      rw [Nat.totient_mul hcop, Nat.totient_prime hq] at h978
      interval_cases r <;> revert h978 <;> decide
    · have hr1 : r = 1 := by omega
      subst hr1
      rw [mul_one, Nat.totient_prime hq] at h978
      revert h978
      decide

/-- `λ(4571) = 1956 = 2 · 978`. -/
theorem carmichael_4571 : carmichael 4571 = 1956 := by
  rw [show (4571 : ℕ) = 7 * 653 by norm_num, carmichael_mul (by norm_num),
    carmichael_prime_of_ne_two (by norm_num) (by norm_num),
    carmichael_prime_of_ne_two (by norm_num) (by norm_num)]
  decide

/-- `A307437(489) = 4571 = 7 · 653`. -/
theorem a307437_489 : a307437 489 = 4571 := by
  refine a307437_eq_of (by norm_num) ?_ ?_
  · rw [carmichael_4571]
    norm_num
  · intro m hm hlt
    exact not_dvd_carmichael_of_not_dvd_totient (not_dvd_totient_of_lt m hm hlt)

/-- `k = 489` is admissible for `p = 653`: `653 ∣ 4571` and `653 < 4571`. -/
theorem isIndex_653_489 : IsIndex 653 489 := by
  rw [IsIndex, a307437_489]
  norm_num

/-- Song’s lower bound fails for the index of the prime `653`:
`A307437(489) = 4571 = 7·653`, so the first admissible index is
at most `489 < 652`. The proof uses the prime index
`Nat.count Nat.Prime 653 + 1` without evaluating it. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hprime : Nat.Prime 653 := by norm_num
  set n := Nat.count Nat.Prime 653 + 1 with hn
  have hnth : Nat.nth Nat.Prime (n - 1) = 653 := by
    rw [hn, Nat.add_sub_cancel]
    exact Nat.nth_count hprime
  have hle : a342039 n ≤ 489 := by
    unfold a342039
    rw [hnth]
    exact Nat.sInf_le isIndex_653_489
  have hbound := hconj n (by omega)
  rw [hnth] at hbound
  omega

end Candidates.A342039Refutation
