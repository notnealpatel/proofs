/-
# A142591 — Bouhamida: composite members of A143578 are the semiprimes `p*q` with `p+q ∣ p*q+1`

Mohamed Bouhamida's conjecture in OEIS A142591 characterizes the composite
members of A143578 as semiprimes `pq` with `p+q ∣ pq+1`.
For A143578, let `j` be the largest divisor of positive `n` not exceeding
`√n`; membership requires `j+n/j ∣ k+n/k` for every divisor `k`.
The characterization and M. F. Hasler's bound of two prime factors counted
with multiplicity are proved below.

## Definitional fidelity

* "the largest divisor `j` of `n` with `j ≤ sqrt n`" is encoded as the largest
  divisor `d` of `n` with `d * d ≤ n` (`lowDivisor`), avoiding `Real.sqrt`;
  for natural `d` the two conditions coincide.
* `A143578` is restricted to positive integers (`0 < n`), as in the entry name.
* `A142591` = composite members: `1 < n ∧ ¬ n.Prime`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A142591BouhamidaSetLargest

/-! ## Definitions -/

/-- `lowDivisor n` is the largest divisor `d` of `n` with `d * d ≤ n`, i.e. the
largest divisor of `n` that is `≤ sqrt n` (it is `0` for `n = 0`, where
`Nat.divisors 0 = ∅`). -/
def lowDivisor (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d * d ≤ n)).sup id

/-- Membership in OEIS A143578: `n` is a positive integer and, with
`j = lowDivisor n`, `j + n/j` divides `k + n/k` for every divisor `k` of `n`. -/
def InA143578 (n : ℕ) : Prop :=
  0 < n ∧ ∀ k ∈ n.divisors, (lowDivisor n + n / lowDivisor n) ∣ (k + n / k)

instance : DecidablePred InA143578 := fun n => by
  unfold InA143578; infer_instance

/-- Membership in OEIS A142591: the composite members of A143578. -/
def InA142591 (n : ℕ) : Prop :=
  InA143578 n ∧ 1 < n ∧ ¬ n.Prime

instance : DecidablePred InA142591 := fun n => by
  unfold InA142591; infer_instance

/-! ## Examples -/

example : lowDivisor 12 = 3 := by decide
example : lowDivisor 15 = 3 := by decide
example : lowDivisor 16 = 4 := by decide
example : InA143578 1 := by decide
example : InA143578 2 := by decide
example : InA142591 15 := by decide
example : ¬ InA142591 14 := by decide
example : ¬ InA143578 12 := by decide


/-! ## Basic properties of `lowDivisor` -/

/-- For `0 < n`, `lowDivisor n` is a divisor of `n` with square at most `n`. -/
theorem lowDivisor_spec {n : ℕ} (hn : 0 < n) :
    lowDivisor n ∣ n ∧ lowDivisor n * lowDivisor n ≤ n := by
  have hne : (n.divisors.filter (fun d => d * d ≤ n)).Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn.ne', by omega⟩⟩
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_filter, Nat.mem_divisors] at hi
  unfold lowDivisor
  rw [hsup]
  exact ⟨hi.1.1, hi.2⟩

/-- Every divisor `d` of `n` with `d * d ≤ n` is at most `lowDivisor n`. -/
theorem le_lowDivisor {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (hdd : d * d ≤ n) :
    d ≤ lowDivisor n := by
  have hmem : d ∈ n.divisors.filter (fun d => d * d ≤ n) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩, hdd⟩
  exact Finset.le_sup (f := id) hmem

/-- Characterisation: if `j ∣ n`, `j * j ≤ n`, and every divisor `d` with
`d * d ≤ n` satisfies `d ≤ j`, then `lowDivisor n = j`. -/
theorem lowDivisor_eq_of {n j : ℕ} (hn : 0 < n) (hj : j ∣ n) (hjj : j * j ≤ n)
    (hmax : ∀ d, d ∣ n → d * d ≤ n → d ≤ j) : lowDivisor n = j := by
  obtain ⟨h1, h2⟩ := lowDivisor_spec hn
  exact le_antisymm (hmax _ h1 h2) (le_lowDivisor hn hj hjj)

/-! ## The key divisibility -/

/-- **Key step.** Suppose `n = j * m` and `(j + m) ∣ k + n/k` for every divisor
`k` of `n`.  Then `(j + m) ∣ a * a - 1` for every positive divisor `a` of `n`.
(Take `k = 1` to get `(j+m) ∣ n + 1`, and `k = a` multiplied by `a` to get
`(j+m) ∣ a² + n`; subtract.) -/
theorem dvd_sq_sub_one {n j m a : ℕ} (hn : 0 < n)
    (hall : ∀ k ∈ n.divisors, (j + m) ∣ (k + n / k)) (ha : a ∣ n) (ha0 : 0 < a) :
    (j + m) ∣ a * a - 1 := by
  have h1 : (j + m) ∣ n + 1 := by
    have := hall 1 (Nat.one_mem_divisors.mpr hn.ne')
    simpa [add_comm] using this
  have h2 : (j + m) ∣ a * a + n := by
    have hk := hall a (Nat.mem_divisors.mpr ⟨ha, hn.ne'⟩)
    have hmul : a * (a + n / a) = a * a + n := by
      rw [mul_add, Nat.mul_div_cancel' ha]
    rw [← hmul]
    exact Dvd.dvd.mul_left hk a
  have hsplit : a * a + n = (a * a - 1) + (n + 1) := by
    have : 1 ≤ a * a := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [hsplit] at h2
  exact (Nat.dvd_add_left h1).mp h2

/-- Under the hypothesis of the key step, every divisor `x > 1` of `n` with
`x ≤ j + m` is prime: otherwise `a = minFac x` satisfies `2 ≤ a`, `a * a ≤ x`,
so `0 < a * a - 1 < j + m`, contradicting `(j + m) ∣ a * a - 1`. -/
theorem prime_of_dvd {n j m x : ℕ} (hn : 0 < n)
    (hall : ∀ k ∈ n.divisors, (j + m) ∣ (k + n / k)) (hx : x ∣ n) (hx1 : 1 < x)
    (hxle : x ≤ j + m) : x.Prime := by
  by_contra hnp
  set a := x.minFac with ha
  have hx0 : 0 < x := by omega
  have ha2 : 2 ≤ a := (Nat.minFac_prime (by omega)).two_le
  have hasq : a * a ≤ x := by
    have := Nat.minFac_sq_le_self hx0 hnp
    rw [pow_two] at this
    exact this
  have hadvd : a ∣ n := (Nat.minFac_dvd x).trans hx
  have hd := dvd_sq_sub_one hn hall hadvd (by omega)
  have hpos : 0 < a * a - 1 := by
    have : 4 ≤ a * a := Nat.mul_le_mul ha2 ha2
    omega
  have hle := Nat.le_of_dvd hpos hd
  omega


/-! ## The two directions -/

/-- **Forward direction.** A composite member `n` of A143578 is `p * q` with
primes `p < q` and `(p + q) ∣ p * q + 1`; namely `p = lowDivisor n` and
`q = n / lowDivisor n`. -/
theorem exists_primes_of_inA143578 {n : ℕ} (h1 : 1 < n) (hnp : ¬ n.Prime)
    (hA : InA143578 n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q ∧ (p + q) ∣ (p * q + 1) := by
  obtain ⟨hn, hall⟩ := hA
  set j := lowDivisor n with hjdef
  set m := n / j with hmdef
  obtain ⟨hjdvd, hjj⟩ := lowDivisor_spec hn
  rw [← hjdef] at hjdvd hjj
  have hj2 : 2 ≤ j := by
    have hmf : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self hn hnp
    rw [pow_two] at hmf
    have hle : n.minFac ≤ j := le_lowDivisor hn (Nat.minFac_dvd n) hmf
    have h2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    omega
  have hnjm : n = j * m := (Nat.mul_div_cancel' hjdvd).symm
  have hjm : j ≤ m := by
    rw [hnjm] at hjj
    exact Nat.le_of_mul_le_mul_left hjj (by omega)
  have hmdvd : m ∣ n := Nat.div_dvd_of_dvd hjdvd
  have hpj : j.Prime := prime_of_dvd hn hall hjdvd (by omega) (by omega)
  have hpm : m.Prime := prime_of_dvd hn hall hmdvd (by omega) (by omega)
  have hn1 : (j + m) ∣ n + 1 := by
    have := hall 1 (Nat.one_mem_divisors.mpr hn.ne')
    simpa [add_comm] using this
  have hne : j ≠ m := by
    intro hjm_eq
    have hsq : (j + m) ∣ j * j - 1 := dvd_sq_sub_one hn hall hjdvd (by omega)
    have hsub : (j + m) ∣ (n + 1) - (j * j - 1) := Nat.dvd_sub hn1 hsq
    have htwo : (n + 1) - (j * j - 1) = 2 := by
      rw [hnjm, ← hjm_eq]
      have : 1 ≤ j * j := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [htwo] at hsub
    have := Nat.le_of_dvd (by omega) hsub
    omega
  refine ⟨j, m, hpj, hpm, lt_of_le_of_ne hjm hne, hnjm, ?_⟩
  rw [← hnjm]
  exact hn1

/-- The divisors of a product of two primes `p * q` are `1`, `p`, `q`, `p * q`. -/
theorem dvd_mul_primes {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : d ∣ p * q) :
    d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := Nat.dvd_mul.mp hd
  rcases (Nat.dvd_prime hp).mp hd₁ with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hd₂ with rfl | rfl <;> simp

/-- For primes `p < q`, `lowDivisor (p * q) = p`. -/
theorem lowDivisor_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    lowDivisor (p * q) = p := by
  have hp1 := hp.two_le
  have hq1 := hq.two_le
  have hpos : 0 < p * q := by positivity
  refine lowDivisor_eq_of hpos (dvd_mul_right p q) (Nat.mul_le_mul_left p hpq.le) ?_
  intro d hd hdd
  rcases dvd_mul_primes hp hq hd with rfl | rfl | rfl | rfl
  · omega
  · exact le_rfl
  · have : d ≤ p := Nat.le_of_mul_le_mul_right hdd (by omega)
    omega
  · have : p * q ≤ 1 := by
      have h' : p * q * (p * q) ≤ p * q * 1 := by simpa using hdd
      exact Nat.le_of_mul_le_mul_left h' hpos
    have : 4 ≤ p * q := Nat.mul_le_mul hp1 hq1
    omega

/-- **Converse direction.** For primes `p < q` with `(p + q) ∣ p * q + 1`, the
number `p * q` belongs to A143578. -/
theorem inA143578_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hdvd : (p + q) ∣ (p * q + 1)) : InA143578 (p * q) := by
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have hpos : 0 < p * q := by positivity
  refine ⟨hpos, ?_⟩
  intro k hk
  rw [lowDivisor_mul_primes hp hq hpq, Nat.mul_div_cancel_left q hp0]
  rcases dvd_mul_primes hp hq (Nat.dvd_of_mem_divisors hk) with hk1 | hk1 | hk1 | hk1
  · rw [hk1, Nat.div_one, Nat.add_comm 1]
    exact hdvd
  · rw [hk1, Nat.mul_div_cancel_left q hp0]
  · rw [hk1, Nat.mul_div_cancel p hq0, Nat.add_comm q p]
  · rw [hk1, Nat.div_self hpos]
    exact hdvd

/-! ## The conjecture -/

/-- **Bouhamida's conjecture (A142591, Mohamed Bouhamida).**

"Conjecture: This consists exactly of the semiprimes p*q for which
p + q divides p*q + 1."  Here A142591 is the set of composite terms of A143578.
Formally: a composite `n` (`1 < n`, `¬ n.Prime`) lies in A143578 iff
`n = p * q` with primes `p < q` and `(p + q) ∣ p * q + 1`.

(The semiprime `p * p` never qualifies: `2p ∤ p² + 1`; so the ordering `p < q`
loses nothing.) -/
theorem bouhamida_conjecture (n : ℕ) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    InA143578 n ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q ∧ (p + q) ∣ (p * q + 1) := by
  constructor
  · exact exists_primes_of_inA143578 h1 hnp
  · rintro ⟨p, q, hp, hq, hpq, rfl, hdvd⟩
    exact inA143578_of_primes hp hq hpq hdvd

/-- The conjecture in terms of the A142591 predicate: `n` is a composite term of
A143578 iff `n = p * q` with primes `p < q` and `(p + q) ∣ p * q + 1`. -/
theorem inA142591_iff (n : ℕ) :
    InA142591 n ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q ∧ (p + q) ∣ (p * q + 1) := by
  constructor
  · rintro ⟨hA, h1, hnp⟩
    exact (bouhamida_conjecture n h1 hnp).mp hA
  · rintro ⟨p, q, hp, hq, hpq, rfl, hdvd⟩
    have hnp : ¬ (p * q).Prime := Nat.not_prime_mul hp.ne_one hq.ne_one
    have h1 : 1 < p * q := Nat.one_lt_mul_iff.mpr ⟨hp.pos, hq.pos, Or.inl hp.one_lt⟩
    exact ⟨inA143578_of_primes hp hq hpq hdvd, h1, hnp⟩

/-- **Hasler's remark (A143578), proved.** No member of A143578 has more than two
prime factors counted with multiplicity: `bigomega n ≤ 2`. -/
theorem primeFactorsList_length_le_two {n : ℕ} (hA : InA143578 n) :
    n.primeFactorsList.length ≤ 2 := by
  by_cases h1 : n ≤ 1
  · interval_cases n <;> simp
  by_cases hnp : n.Prime
  · rw [Nat.primeFactorsList_prime hnp]
    simp
  obtain ⟨p, q, hp, hq, -, rfl, -⟩ :=
    (bouhamida_conjecture n (by omega) hnp).mp hA
  rw [← ArithmeticFunction.cardFactors_apply,
    ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_apply_prime hq]

/-- Non-vacuity: the first listed term `15 = 3 * 5` satisfies the hypotheses and
the right-hand side of `bouhamida_conjecture`. -/
example : InA143578 15 ∧ 1 < 15 ∧ ¬ (15 : ℕ).Prime ∧
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 15 = p * q ∧ (p + q) ∣ (p * q + 1) :=
  ⟨by decide, by norm_num, by norm_num, 3, 5, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end Candidates.A142591BouhamidaSetLargest
