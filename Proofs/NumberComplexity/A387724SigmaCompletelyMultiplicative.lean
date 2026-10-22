/-
# A387724 — Karttunen: 6 is the only nondeficient term

Antti Karttunen's conjecture in OEIS A387724 says that `6` is the only
nondeficient term, and every other term lies in A337382.
A387724 consists of positive `k` with `k σ(A003961(k)) ≤ σ(k)²`;
A337382 requires `σ(A003961(k)) < 2σ(k)`. A003961 is completely multiplicative
and maps each prime to the next prime. David A. Corneth's separate question
about twice a prime is not treated.

## Proof outline

Write `f(k) = σ(k)^2 / (k σ(A003961 k))`; it is multiplicative because
`nextPrime` is injective on primes.  For an odd prime power `p^e ≠ 3`,
`σ(p^e)^5 ≤ p^(3e) σ(nextPrime(p)^e)^2` (`sigma_prime_pow_five_le`, by the
polynomial certificates `cert_one`, `cert_two`), i.e. `f(p^e)^2 σ(p^e)/p^e ≤ 1`.
Also `f(2) = 9/8`, `f(3) = 8/9`, and `f(2^a) < 1` for `a ≥ 2`.  Writing
`k = 2^a 3^j m` with `gcd(m, 6) = 1`, a six-way case split on `a ∈ {0, 1, ≥2}`
and `j = 1` or not closes the first clause; the second follows since a
deficient term has `σ(A003961 k) ≤ σ(k)^2/k < 2σ(k)`.

## Formal conventions

* `nextPrime p` is the least prime `> p`; `a003961 n = ∏ p^e ∥ n, nextPrime(p)^e`
  via `Nat.factorization` (junk value `a003961 0 = 1`, irrelevant since both
  sequences are restricted to `k ≥ 1`).
* Sequence memberships are stated in `ℕ` without division:
  `k · σ(A003961 k) ≤ σ(k)^2` and `σ(A003961 k) < 2 σ(k)`.
* "Nondeficient" is `2k ≤ σ(k)`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Candidates.A387724SigmaCompletelyMultiplicative

/-- The least prime strictly greater than `p` (OEIS `nextprime`). -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- A003961: the completely multiplicative function with `a(p) = nextprime(p)`,
i.e. `n = ∏ p^e ↦ ∏ nextPrime(p)^e`. -/
def a003961 (n : ℕ) : ℕ := n.factorization.prod fun p e => nextPrime p ^ e

/-- A387724 membership: `k ≥ 1` and `sigma(k)^2 ≥ k * sigma(A003961(k))`. -/
def IsA387724 (k : ℕ) : Prop := 0 < k ∧ k * σ 1 (a003961 k) ≤ σ 1 k ^ 2

/-- A337382 membership: `k ≥ 1` and `A003973(k) < 2 * sigma(k)`, where
`A003973(k) = sigma(A003961(k))`. -/
def IsA337382 (k : ℕ) : Prop := 0 < k ∧ σ 1 (a003961 k) < 2 * σ 1 k

/-- `nextPrime p` is a prime exceeding `p`. -/
theorem nextPrime_spec (p : ℕ) : p < nextPrime p ∧ (nextPrime p).Prime := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (p + 1))
  exact ⟨h.1, h.2⟩

/-- `nextPrime p` is at most any prime exceeding `p`. -/
theorem nextPrime_le {p q : ℕ} (hpq : p < q) (hq : q.Prime) : nextPrime p ≤ q :=
  Nat.find_min' _ ⟨hpq, hq⟩

/-- `nextPrime` is injective on primes. -/
theorem nextPrime_injOn {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : nextPrime p = nextPrime p') : p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · have h1 := nextPrime_le hlt hp'
    have h2 := (nextPrime_spec p').1
    omega
  · exact heq
  · have h1 := nextPrime_le hgt hp
    have h2 := (nextPrime_spec p).1
    omega

/-- For an odd prime `p`, `nextPrime p ≥ p + 2`. -/
theorem add_two_le_nextPrime {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : p + 2 ≤ nextPrime p := by
  obtain ⟨hlt, hq⟩ := nextPrime_spec p
  by_contra hcon
  have heq : nextPrime p = p + 1 := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : 2 ∣ nextPrime p := by
    rw [heq]
    exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)).two_dvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2
  omega

/-- To identify `nextPrime p`: a prime `q > p` with no prime strictly between. -/
theorem nextPrime_eq {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hgap : ∀ n, p < n → n < q → ¬ n.Prime) : nextPrime p = q := by
  unfold nextPrime
  rw [Nat.find_eq_iff]
  exact ⟨⟨hpq, hq⟩, fun n hn hprime => hgap n hprime.1 hn hprime.2⟩

/-- The prime after `2` is `3`. -/
theorem nextPrime_two : nextPrime 2 = 3 :=
  nextPrime_eq (by norm_num) Nat.prime_three fun n hlo hhi => by omega

/-- The prime after `3` is `5`. -/
theorem nextPrime_three : nextPrime 3 = 5 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    obtain rfl : n = 4 := by omega
    norm_num

/-- `A003961(m · n) = A003961(m) · A003961(n)` for nonzero `m, n`. -/
theorem a003961_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    a003961 (m * n) = a003961 m * a003961 n := by
  unfold a003961
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- `A003961(p^e) = nextPrime(p)^e` for prime `p`. -/
theorem a003961_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a003961 (p ^ e) = nextPrime p ^ e := by
  unfold a003961
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero _)

/-- Every prime factor of `A003961(n)` is `nextPrime p` for a prime factor `p` of `n`. -/
theorem exists_of_prime_dvd_a003961 {n r : ℕ} (hr : r.Prime) (hdvd : r ∣ a003961 n) :
    ∃ p, p.Prime ∧ p ∣ n ∧ r = nextPrime p := by
  unfold a003961 at hdvd
  rw [Finsupp.prod, Nat.support_factorization] at hdvd
  obtain ⟨p, hpmem, hpd⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hdvd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  refine ⟨p, hpp, Nat.dvd_of_mem_primeFactors hpmem, ?_⟩
  exact (Nat.prime_dvd_prime_iff_eq hr (nextPrime_spec p).2).mp (hr.dvd_of_dvd_pow hpd)

/-- `A003961` maps coprime arguments to coprime values. -/
theorem coprime_a003961 {m n : ℕ} (hmn : m.Coprime n) :
    (a003961 m).Coprime (a003961 n) := by
  apply Nat.coprime_of_dvd
  intro r hr hrm hrn
  obtain ⟨p, hp, hpm, rfl⟩ := exists_of_prime_dvd_a003961 hr hrm
  obtain ⟨p', hp', hpn, hpp'⟩ := exists_of_prime_dvd_a003961 hr hrn
  obtain rfl := nextPrime_injOn hp hp' hpp'
  have h1 : p ∣ 1 := hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-! ## Divisor-sum lemmas -/

/-- `σ ∘ A003961` is multiplicative on coprime nonzero arguments. -/
theorem sigma_a003961_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    σ 1 (a003961 (m * n)) = σ 1 (a003961 m) * σ 1 (a003961 n) := by
  rw [a003961_mul hm hn]
  exact isMultiplicative_sigma.map_mul_of_coprime (coprime_a003961 hmn)

/-- `n ≤ σ(n)` for `n ≠ 0`. -/
theorem le_sigma {n : ℕ} (hn : n ≠ 0) : n ≤ σ 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn)

/-- `n < σ(n)` for `1 < n`. -/
theorem lt_sigma {n : ℕ} (hn : 1 < n) : n < σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd n, hn⟩
  have h2 : 1 ≤ ∑ i ∈ n.properDivisors, i :=
    Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) h1
  omega

/-- Geometric-sum identity: `σ(p^e) · (p - 1) + 1 = p^(e+1)` for `p ≥ 1`, stated with
`p = r + 1` to avoid truncated subtraction. -/
theorem sigma_prime_pow_mul_add {r : ℕ} (hp : (r + 1).Prime) (e : ℕ) :
    σ 1 ((r + 1) ^ e) * r + 1 = (r + 1) ^ (e + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  exact geom_sum_mul_add r (e + 1)

/-- `q^e ≤ σ(q^e)` for prime `q`. -/
theorem pow_le_sigma_prime_pow {q : ℕ} (hq : q.Prime) (e : ℕ) : q ^ e ≤ σ 1 (q ^ e) :=
  le_sigma (pow_ne_zero e hq.ne_zero)

/-- `σ(p) = p + 1` for prime `p`. -/
theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, add_comm]

/-! ## The prime-power inequality -/

/-- Polynomial certificate for exponent `1`: `(p+1)^5 ≤ p^3 (p+3)^2` for `p ≥ 5`. -/
theorem cert_one (r : ℕ) : (r + 5 + 1) ^ 5 ≤ (r + 5) ^ 3 * (r + 5 + 3) ^ 2 := by
  have h : (r + 5) ^ 3 * (r + 5 + 3) ^ 2 =
      (r + 5 + 1) ^ 5 + (r ^ 4 + 19 * r ^ 3 + 125 * r ^ 2 + 320 * r + 224) := by ring
  omega

/-- Polynomial certificate for exponents `≥ 2`: `p^9 ≤ (p-1)^5 (p+2)^4` for `p ≥ 3`. -/
theorem cert_two (r : ℕ) : (r + 3) ^ 9 ≤ (r + 2) ^ 5 * (r + 5) ^ 4 := by
  have h : (r + 2) ^ 5 * (r + 5) ^ 4 = (r + 3) ^ 9 + (66 * r ^ 7 + 612 * r ^ 6 + 3099 * r ^ 5 +
      9264 * r ^ 4 + 16404 * r ^ 3 + 16068 * r ^ 2 + 6951 * r + 317 + 3 * r ^ 8) := by ring
  omega

/-- **Prime-power lemma.** For an odd prime `p` and `e ≥ 1`, except `p^e = 3`,
`σ(p^e)^5 ≤ p^(3e) · σ(nextPrime(p)^e)^2`; equivalently `f(p^e)^2 · σ(p^e)/p^e ≤ 1`
where `f(k) = σ(k)^2 / (k σ(A003961 k))`. -/
theorem sigma_prime_pow_five_le {p e : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (he : 1 ≤ e)
    (hex : e = 1 → 5 ≤ p) :
    σ 1 (p ^ e) ^ 5 ≤ p ^ (3 * e) * σ 1 (nextPrime p ^ e) ^ 2 := by
  have hq := (nextPrime_spec p).2
  have hqp := add_two_le_nextPrime hp h3
  rcases Nat.lt_or_ge e 2 with he1 | he2
  · obtain rfl : e = 1 := by omega
    have h5 := hex rfl
    rw [pow_one, pow_one, sigma_prime hp, sigma_prime hq]
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 5 := ⟨p - 5, by omega⟩
    calc (r + 5 + 1) ^ 5 ≤ (r + 5) ^ 3 * (r + 5 + 3) ^ 2 := cert_one r
      _ ≤ (r + 5) ^ (3 * 1) * (nextPrime (r + 5) + 1) ^ 2 := by
          rw [mul_one]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  · obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 3 := ⟨p - 3, by omega⟩
    set S := σ 1 ((r + 3) ^ (d + 2)) with hSdef
    have hS : S * (r + 2) + 1 = (r + 3) ^ (d + 3) := by
      have := sigma_prime_pow_mul_add (r := r + 2) hp (d + 2)
      simpa [hSdef] using this
    have hQ : (r + 5) ^ (d + 2) ≤ σ 1 (nextPrime (r + 3) ^ (d + 2)) :=
      (Nat.pow_le_pow_left (by omega) _).trans (pow_le_sigma_prime_pow hq _)
    have hlt : (r + 2) ^ 5 * S ^ 5 < (r + 3) ^ (5 * d + 15) := by
      have h1 : S * (r + 2) < (r + 3) ^ (d + 3) := by omega
      calc (r + 2) ^ 5 * S ^ 5 = (S * (r + 2)) ^ 5 := by ring
        _ < ((r + 3) ^ (d + 3)) ^ 5 := Nat.pow_lt_pow_left h1 (by norm_num)
        _ = (r + 3) ^ (5 * d + 15) := by rw [← pow_mul]; ring_nf
    have hmain : (r + 3) ^ (5 * d + 15) ≤
        (r + 2) ^ 5 * ((r + 3) ^ (3 * (d + 2)) * ((r + 5) ^ (d + 2)) ^ 2) := by
      have hc := cert_two r
      have hd : ((r + 3) ^ 2) ^ d ≤ ((r + 5) ^ 2) ^ d :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (by omega) 2) d
      calc (r + 3) ^ (5 * d + 15) = (r + 3) ^ (3 * (d + 2)) * (((r + 3) ^ 2) ^ d * (r + 3) ^ 9) := by
            rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
        _ ≤ (r + 3) ^ (3 * (d + 2)) * (((r + 5) ^ 2) ^ d * ((r + 2) ^ 5 * (r + 5) ^ 4)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hd hc)
        _ = (r + 2) ^ 5 * ((r + 3) ^ (3 * (d + 2)) * ((r + 5) ^ (d + 2)) ^ 2) := by
            rw [← pow_mul]; ring
    have hfin : S ^ 5 ≤ (r + 3) ^ (3 * (d + 2)) * ((r + 5) ^ (d + 2)) ^ 2 :=
      le_of_mul_le_mul_left (hlt.le.trans hmain) (by positivity)
    exact hfin.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 2))

/-- `A003961(1) = 1`. -/
theorem a003961_one : a003961 1 = 1 := by
  simp [a003961]

/-- **Odd part coprime to `3`.** For `m ≠ 0` with `2 ∤ m` and `3 ∤ m`,
`σ(m)^5 ≤ m^3 · σ(A003961 m)^2` (product of the prime-power lemma over `m`). -/
theorem sigma_five_le_of_coprime_six (m : ℕ) (hm : m ≠ 0) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) :
    σ 1 m ^ 5 ≤ m ^ 3 * σ 1 (a003961 m) ^ 2 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    have hp' : p.Prime := hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h2 (dvd_pow_self 2 hn.ne')
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 (dvd_pow_self 3 hn.ne')
    have hp5 : 5 ≤ p := by
      have h2le := hp'.two_le
      rcases Nat.lt_or_ge p 5 with hlt | hge
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp' (by norm_num)
      · exact hge
    rw [a003961_prime_pow hp', ← pow_mul, mul_comm n 3]
    exact sigma_prime_pow_five_le hp' (by omega) hn (fun _ => hp5)
  | zero => exact absurd rfl hm
  | one => simp [a003961_one]
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have ha2 : ¬ 2 ∣ a := fun h => h2 (h.mul_right b)
    have hb2 : ¬ 2 ∣ b := fun h => h2 (h.mul_left a)
    have ha3 : ¬ 3 ∣ a := fun h => h3 (h.mul_right b)
    have hb3 : ¬ 3 ∣ b := fun h => h3 (h.mul_left a)
    have hA := iha ha0 ha2 ha3
    have hB := ihb hb0 hb2 hb3
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, sigma_a003961_mul ha0 hb0 hab]
    calc (σ 1 a * σ 1 b) ^ 5 = σ 1 a ^ 5 * σ 1 b ^ 5 := by ring
      _ ≤ (a ^ 3 * σ 1 (a003961 a) ^ 2) * (b ^ 3 * σ 1 (a003961 b) ^ 2) := Nat.mul_le_mul hA hB
      _ = (a * b) ^ 3 * (σ 1 (a003961 a) * σ 1 (a003961 b)) ^ 2 := by ring

/-- **The `2`-part.** For `a ≥ 2`, `σ(2^a)^2 < 2^a σ(3^a)`, i.e. `f(2^a) < 1`. -/
theorem sigma_two_pow_sq_lt {a : ℕ} (ha : 2 ≤ a) : σ 1 (2 ^ a) ^ 2 < 2 ^ a * σ 1 (3 ^ a) := by
  rcases Nat.lt_or_ge a 3 with hlt | hge
  · obtain rfl : a = 2 := by omega
    have h4 : σ 1 (2 ^ 2) = 7 := by
      rw [sigma_one_apply_prime_pow Nat.prime_two]
      simp [Finset.sum_range_succ]
    have h9 : σ 1 (3 ^ 2) = 13 := by
      rw [sigma_one_apply_prime_pow Nat.prime_three]
      simp [Finset.sum_range_succ]
    rw [h4, h9]
    norm_num
  · obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, by omega⟩
    have hS2 := sigma_prime_pow_mul_add (r := 1) Nat.prime_two (c + 3)
    have hS3 := sigma_prime_pow_mul_add (r := 2) Nat.prime_three (c + 3)
    norm_num only at hS2 hS3
    set S2 := σ 1 (2 ^ (c + 3))
    set S3 := σ 1 (3 ^ (c + 3))
    have huv : 2 ^ c ≤ 3 ^ c := Nat.pow_le_pow_left (by norm_num) c
    have hu : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    have e2 : 2 ^ (c + 3 + 1) = 16 * 2 ^ c := by ring
    have e3 : 3 ^ (c + 3 + 1) = 81 * 3 ^ c := by ring
    have e2' : 2 ^ (c + 3) = 8 * 2 ^ c := by ring
    rw [e2] at hS2
    rw [e3] at hS3
    rw [e2']
    have hmul := Nat.mul_le_mul_left (2 ^ c) huv
    nlinarith

/-- Cancellation helper: from `A · X^5 ≤ B · X^4` with `X > 0` get `A · X ≤ B`. -/
theorem le_of_mul_pow_five_le {A B X : ℕ} (hX : 0 < X) (h : A * X ^ 5 ≤ B * X ^ 4) :
    A * X ≤ B := by
  have h' : (A * X) * X ^ 4 ≤ B * X ^ 4 := by
    calc (A * X) * X ^ 4 = A * X ^ 5 := by ring
      _ ≤ B * X ^ 4 := h
  exact Nat.le_of_mul_le_mul_right h' (by positivity)

/-! ## Arithmetic endgames

`P` is the odd part `3^j m`, `X = σ(P)`, `Y = σ(A003961 P)`; when `v₃ = 1` the
variables are `m, s = σ(m), t = σ(A003961 m)`. -/

/-- Odd `k` with `v₃(k) ≠ 1`: a term cannot be nondeficient. -/
theorem endgame_a0 {X Y P : ℕ} (hP : 0 < P) (hF : X ^ 5 ≤ P ^ 3 * Y ^ 2)
    (hterm : P * Y ≤ X ^ 2) (hnd : 2 * P ≤ X) : False := by
  have hX : 0 < X := by omega
  have h : 1 * X ^ 5 ≤ P * X ^ 4 := by
    calc 1 * X ^ 5 ≤ P ^ 3 * Y ^ 2 := by rw [one_mul]; exact hF
      _ = P * (P * Y) ^ 2 := by ring
      _ ≤ P * (X ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hterm 2)
      _ = P * X ^ 4 := by ring
  have := le_of_mul_pow_five_le hX h
  omega

/-- `v₃ = 1`, with `f(3) = 8/9` absorbed: `18 m t ≤ 16 s^2` is impossible. -/
theorem endgame_j1 {s t m : ℕ} (hm : 0 < m) (hP : s ^ 5 ≤ m ^ 3 * t ^ 2) (hms : m ≤ s)
    (hterm : 18 * (m * t) ≤ 16 * s ^ 2) : False := by
  have hs : 0 < s := by omega
  have h : 324 * s ^ 5 ≤ (256 * m) * s ^ 4 := by
    calc 324 * s ^ 5 ≤ 324 * (m ^ 3 * t ^ 2) := Nat.mul_le_mul_left _ hP
      _ = m * (18 * (m * t)) ^ 2 := by ring
      _ ≤ m * (16 * s ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hterm 2)
      _ = (256 * m) * s ^ 4 := by ring
  have := le_of_mul_pow_five_le hs h
  omega

/-- `k = 2 · P` with `v₃(P) ≠ 1`: a term cannot be nondeficient. -/
theorem endgame_a1 {X Y P : ℕ} (hP : 0 < P) (hF : X ^ 5 ≤ P ^ 3 * Y ^ 2)
    (hterm : 8 * (P * Y) ≤ 9 * X ^ 2) (hnd : 4 * P ≤ 3 * X) : False := by
  have hX : 0 < X := by omega
  have h : 64 * X ^ 5 ≤ (81 * P) * X ^ 4 := by
    calc 64 * X ^ 5 ≤ 64 * (P ^ 3 * Y ^ 2) := Nat.mul_le_mul_left _ hF
      _ = P * (8 * (P * Y)) ^ 2 := by ring
      _ ≤ P * (9 * X ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hterm 2)
      _ = (81 * P) * X ^ 4 := by ring
  have := le_of_mul_pow_five_le hX h
  omega

/-- `k = 6 m`: the term condition forces `σ(m) ≤ m`. -/
theorem endgame_six {s t m : ℕ} (hs : 0 < s) (hP : s ^ 5 ≤ m ^ 3 * t ^ 2)
    (hterm : m * t ≤ s ^ 2) : s ≤ m := by
  have h : 1 * s ^ 5 ≤ m * s ^ 4 := by
    calc 1 * s ^ 5 ≤ m ^ 3 * t ^ 2 := by rw [one_mul]; exact hP
      _ = m * (m * t) ^ 2 := by ring
      _ ≤ m * (s ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hterm 2)
      _ = m * s ^ 4 := by ring
  simpa using le_of_mul_pow_five_le hs h

/-- `k = 2^a P` with `a ≥ 2` and `v₃(P) ≠ 1`: not a term. -/
theorem endgame_a2 {X Y P : ℕ} (hF : X ^ 5 ≤ P ^ 3 * Y ^ 2) (hPX : P ≤ X)
    (hterm : P * Y < X ^ 2) : False := by
  have hX : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · subst h0; simp at hterm
    · exact h0
  have h : 1 * X ^ 5 < P * X ^ 4 := by
    calc 1 * X ^ 5 ≤ P ^ 3 * Y ^ 2 := by rw [one_mul]; exact hF
      _ = P * (P * Y) ^ 2 := by ring
      _ < P * (X ^ 2) ^ 2 := by
          have hP : 0 < P := by
            rcases Nat.eq_zero_or_pos P with h0 | h0
            · subst h0
              have hX5 : X ^ 5 ≤ 0 := by simpa using hF
              exact absurd (pow_pos hX 5) (by omega)
            · exact h0
          exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hterm (by norm_num)) hP
      _ = P * X ^ 4 := by ring
  have h' : (1 * X) * X ^ 4 < P * X ^ 4 := by
    calc (1 * X) * X ^ 4 = 1 * X ^ 5 := by ring
      _ < P * X ^ 4 := h
  have := Nat.lt_of_mul_lt_mul_right h'
  omega

/-- Strict cancellation: from `Q · Z ≤ S · W` with `S < Q` and `W > 0` get `Z < W`. -/
theorem lt_of_mul_le_of_lt {Q S Z W : ℕ} (hSQ : S < Q) (hW : 0 < W) (h : Q * Z ≤ S * W) :
    Z < W := by
  by_contra hlt
  have hge : W ≤ Z := Nat.not_lt.mp hlt
  have h1 : Q * W ≤ Q * Z := Nat.mul_le_mul_left _ hge
  have h2 : S * W < Q * W := Nat.mul_lt_mul_of_pos_right hSQ hW
  omega

/-! ## The conjecture -/

/-- `σ(1) = 1`. -/
theorem sigma_one_one : σ 1 1 = 1 := isMultiplicative_sigma.map_one

/-- `σ(2) = 3`. -/
theorem sigma_two : σ 1 2 = 3 := sigma_prime Nat.prime_two

/-- `σ(3) = 4`. -/
theorem sigma_three : σ 1 3 = 4 := sigma_prime Nat.prime_three

/-- `σ(5) = 6`. -/
theorem sigma_five : σ 1 5 = 6 := sigma_prime Nat.prime_five

/-- The `3`-part with `v₃ ≠ 1`: `σ(3^j)^5 ≤ (3^j)^3 σ(5^j)^2` for `j ≠ 1`. -/
theorem sigma_three_pow_five_le {j : ℕ} (hj : j ≠ 1) :
    σ 1 (3 ^ j) ^ 5 ≤ (3 ^ j) ^ 3 * σ 1 (5 ^ j) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    simp
  · have h := sigma_prime_pow_five_le (e := j) Nat.prime_three le_rfl hpos (fun h => absurd h hj)
    rwa [nextPrime_three, pow_mul, ← pow_mul, mul_comm 3 j, pow_mul] at h

/-- **First clause of Karttunen's conjecture (A387724).** If `k ≥ 1` satisfies
`k · σ(A003961 k) ≤ σ(k)^2` and `k` is nondeficient (`2k ≤ σ(k)`), then `k = 6`. -/
theorem eq_six_of_isA387724_of_nondeficient {k : ℕ} (hk : IsA387724 k)
    (hnd : 2 * k ≤ σ 1 k) : k = 6 := by
  obtain ⟨hk0, hterm⟩ := hk
  obtain ⟨a, n, hn2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' 2 (by norm_num)
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hk0
  obtain ⟨j, m, hm3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn0
  have hm2 : ¬ 2 ∣ m := fun h => hn2 (h.mul_left _)
  have hcop2 : Nat.Coprime (2 ^ a) (3 ^ j * m) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn2)
  have hcop3 : Nat.Coprime (3 ^ j) m :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have h2a0 : 2 ^ a ≠ 0 := by positivity
  have h3j0 : 3 ^ j ≠ 0 := by positivity
  have hσk : σ 1 (2 ^ a * (3 ^ j * m)) = σ 1 (2 ^ a) * (σ 1 (3 ^ j) * σ 1 m) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop2,
      isMultiplicative_sigma.map_mul_of_coprime hcop3]
  have hσA : σ 1 (a003961 (2 ^ a * (3 ^ j * m))) =
      σ 1 (3 ^ a) * (σ 1 (5 ^ j) * σ 1 (a003961 m)) := by
    rw [sigma_a003961_mul h2a0 (mul_ne_zero h3j0 hm0) hcop2, sigma_a003961_mul h3j0 hm0 hcop3,
      a003961_prime_pow Nat.prime_two, a003961_prime_pow Nat.prime_three, nextPrime_two,
      nextPrime_three]
  have hodd_le : 3 ^ j * m ≤ σ 1 (3 ^ j) * σ 1 m := by
    have h := le_sigma (mul_ne_zero h3j0 hm0)
    rwa [isMultiplicative_sigma.map_mul_of_coprime hcop3] at h
  rw [hσk, hσA] at hterm
  rw [hσk] at hnd
  have hP := sigma_five_le_of_coprime_six m hm0 hm2 hm3
  have hms : m ≤ σ 1 m := le_sigma hm0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  set s := σ 1 m with hs
  set t := σ 1 (a003961 m) with ht
  have hPpos : 0 < 3 ^ j * m := by positivity
  have hF : j ≠ 1 →
      (σ 1 (3 ^ j) * s) ^ 5 ≤ (3 ^ j * m) ^ 3 * (σ 1 (5 ^ j) * t) ^ 2 := by
    intro hj
    have hF3 := sigma_three_pow_five_le hj
    calc (σ 1 (3 ^ j) * s) ^ 5 = σ 1 (3 ^ j) ^ 5 * s ^ 5 := by ring
      _ ≤ ((3 ^ j) ^ 3 * σ 1 (5 ^ j) ^ 2) * (m ^ 3 * t ^ 2) := Nat.mul_le_mul hF3 hP
      _ = (3 ^ j * m) ^ 3 * (σ 1 (5 ^ j) * t) ^ 2 := by ring
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · -- `a = 0`: `k` is odd
      simp only [pow_zero, sigma_one_one, one_mul] at hterm hnd
      by_cases hj : j = 1
      · subst hj
        simp only [pow_one, sigma_three, sigma_five] at hterm
        exact (endgame_j1 hmpos hP hms (by linarith)).elim
      · exact (endgame_a0 hPpos (hF hj) (by linarith) (by linarith)).elim
    · -- `a = 1`: `k = 2 · (odd)`
      simp only [pow_one, sigma_two, sigma_three] at hterm hnd
      by_cases hj : j = 1
      · subst hj
        simp only [pow_one, sigma_three, sigma_five] at hterm
        have hs0 : 0 < s := by omega
        have hsm : s ≤ m := endgame_six hs0 hP (by linarith)
        have hm1 : m = 1 := by
          by_contra hne
          have hlt := lt_sigma (n := m) (by omega)
          omega
        subst hm1
        norm_num
      · exact (endgame_a1 hPpos (hF hj) (by linarith) (by linarith)).elim
  · -- `a ≥ 2`: `f(2^a) < 1`
    have h2 := sigma_two_pow_sq_lt ha
    have hW : 0 < (σ 1 (3 ^ j) * s) ^ 2 := by
      have hpos : 0 < σ 1 (3 ^ j) * s := lt_of_lt_of_le hPpos hodd_le
      positivity
    have hlt : (3 ^ j * m) * (σ 1 (5 ^ j) * t) < (σ 1 (3 ^ j) * s) ^ 2 := by
      refine lt_of_mul_le_of_lt h2 hW ?_
      calc 2 ^ a * σ 1 (3 ^ a) * ((3 ^ j * m) * (σ 1 (5 ^ j) * t))
          = 2 ^ a * (3 ^ j * m) * (σ 1 (3 ^ a) * (σ 1 (5 ^ j) * t)) := by ring
        _ ≤ (σ 1 (2 ^ a) * (σ 1 (3 ^ j) * s)) ^ 2 := hterm
        _ = σ 1 (2 ^ a) ^ 2 * (σ 1 (3 ^ j) * s) ^ 2 := by ring
    by_cases hj : j = 1
    · subst hj
      simp only [pow_one, sigma_three, sigma_five] at hlt
      exact (endgame_j1 hmpos hP hms (by linarith)).elim
    · exact (endgame_a2 (hF hj) hodd_le hlt).elim

/-- **Second clause of Karttunen's conjecture (A387724).** Every term `k ≠ 6` of
A387724 lies in A337382, i.e. `σ(A003961 k) < 2 σ(k)`. -/
theorem isA337382_of_isA387724 {k : ℕ} (hk : IsA387724 k) (h6 : k ≠ 6) : IsA337382 k := by
  have hdef : σ 1 k < 2 * k := by
    by_contra hge
    exact h6 (eq_six_of_isA387724_of_nondeficient hk (Nat.not_lt.mp hge))
  obtain ⟨hk0, hterm⟩ := hk
  refine ⟨hk0, ?_⟩
  have hlt : k * σ 1 (a003961 k) < k * (2 * σ 1 k) := by
    have hσ0 : 0 < σ 1 k := lt_of_lt_of_le hk0 (le_sigma hk0.ne')
    calc k * σ 1 (a003961 k) ≤ σ 1 k ^ 2 := hterm
      _ = σ 1 k * σ 1 k := sq _
      _ < (2 * k) * σ 1 k := Nat.mul_lt_mul_of_pos_right hdef hσ0
      _ = k * (2 * σ 1 k) := by ring
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- `A003961(6) = 15`. -/
theorem a003961_six : a003961 6 = 15 := by
  rw [show (6 : ℕ) = 2 ^ 1 * 3 ^ 1 by norm_num, a003961_mul (by norm_num) (by norm_num),
    a003961_prime_pow Nat.prime_two, a003961_prime_pow Nat.prime_three, nextPrime_two,
    nextPrime_three]
  norm_num

/-- `6` is a nondeficient term of A387724: `σ(6) = 12 = 2 · 6` and
`6 · σ(15) = 144 = σ(6)^2`. -/
theorem isA387724_six : IsA387724 6 ∧ 2 * 6 ≤ σ 1 6 := by
  have h6 : σ 1 6 = 12 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, isMultiplicative_sigma.map_mul_of_coprime (by decide),
      sigma_two, sigma_three]
    norm_num
  have h15 : σ 1 15 = 24 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, isMultiplicative_sigma.map_mul_of_coprime (by decide),
      sigma_three, sigma_five]
    norm_num
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · rw [a003961_six, h6, h15]
    norm_num
  · rw [h6]

/-- **Karttunen's conjecture in A387724 (Sep 13 2025).** "Conjecture: 6 is the only
nondeficient term, and all other terms are in A337382 (which is a subsequence of
A005100)."  Formally: a positive `k` with `k · σ(A003961 k) ≤ σ(k)^2` is nondeficient
(`2k ≤ σ(k)`) iff `k = 6`; and every such `k ≠ 6` satisfies `σ(A003961 k) < 2 σ(k)`. -/
theorem a387724_conjecture :
    (∀ k : ℕ, (IsA387724 k ∧ 2 * k ≤ σ 1 k) ↔ k = 6) ∧
      (∀ k : ℕ, IsA387724 k → k ≠ 6 → IsA337382 k) := by
  refine ⟨fun k => ⟨fun h => eq_six_of_isA387724_of_nondeficient h.1 h.2, ?_⟩,
    fun k hk h6 => isA337382_of_isA387724 hk h6⟩
  rintro rfl
  exact isA387724_six

/-! ## Examples -/

/-- The prime after `5` is `7`. -/
theorem nextPrime_five : nextPrime 5 = 7 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    obtain rfl : n = 6 := by omega
    norm_num

/-- The prime after `7` is `11`. -/
theorem nextPrime_seven : nextPrime 7 = 11 :=
  nextPrime_eq (by norm_num) (by norm_num) fun n hlo hhi => by
    interval_cases n <;> norm_num

/-- `A003961(1..10) = 1, 3, 5, 9, 7, 15, 11, 27, 25, 21` (OEIS A003961 DATA). -/
theorem a003961_one_to_ten :
    a003961 1 = 1 ∧ a003961 2 = 3 ∧ a003961 3 = 5 ∧ a003961 4 = 9 ∧ a003961 5 = 7 ∧
      a003961 6 = 15 ∧ a003961 7 = 11 ∧ a003961 8 = 27 ∧ a003961 9 = 25 ∧
      a003961 10 = 21 := by
  have hp : ∀ {p : ℕ}, p.Prime → a003961 p = nextPrime p := fun hp => by
    simpa using a003961_prime_pow hp 1
  refine ⟨a003961_one, ?_, ?_, ?_, ?_, a003961_six, ?_, ?_, ?_, ?_⟩
  · rw [hp Nat.prime_two, nextPrime_two]
  · rw [hp Nat.prime_three, nextPrime_three]
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, a003961_prime_pow Nat.prime_two, nextPrime_two]
    norm_num
  · rw [hp (by norm_num), nextPrime_five]
  · rw [hp (by norm_num), nextPrime_seven]
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, a003961_prime_pow Nat.prime_two, nextPrime_two]
    norm_num
  · rw [show (9 : ℕ) = 3 ^ 2 by norm_num, a003961_prime_pow Nat.prime_three, nextPrime_three]
    norm_num
  · rw [show (10 : ℕ) = 2 * 5 by norm_num, a003961_mul (by norm_num) (by norm_num),
      hp Nat.prime_two, hp (by norm_num), nextPrime_two, nextPrime_five]

/-- Divisor sums used by the examples: `σ(n)` for
`n = 1..11, 15, 21, 25, 27` (OEIS A000203). -/
theorem sigma_table :
    σ 1 1 = 1 ∧ σ 1 2 = 3 ∧ σ 1 3 = 4 ∧ σ 1 4 = 7 ∧ σ 1 5 = 6 ∧ σ 1 6 = 12 ∧
      σ 1 7 = 8 ∧ σ 1 8 = 15 ∧ σ 1 9 = 13 ∧ σ 1 10 = 18 ∧ σ 1 11 = 12 ∧ σ 1 15 = 24 ∧
      σ 1 21 = 32 ∧ σ 1 25 = 31 ∧ σ 1 27 = 40 := by
  have hpp : ∀ {p : ℕ} (e : ℕ), p.Prime → σ 1 (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ i :=
    fun e hp => sigma_one_apply_prime_pow hp
  have hmul : ∀ {a b : ℕ}, a.Coprime b → σ 1 (a * b) = σ 1 a * σ 1 b :=
    fun h => isMultiplicative_sigma.map_mul_of_coprime h
  have h7 : σ 1 7 = 8 := sigma_prime (by norm_num)
  have h11 : σ 1 11 = 12 := sigma_prime (by norm_num)
  refine ⟨sigma_one_one, sigma_two, sigma_three, ?_, sigma_five, ?_, h7, ?_, ?_, ?_, h11,
    ?_, ?_, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, hpp 2 Nat.prime_two]
    simp [Finset.sum_range_succ]
  · rw [show (6 : ℕ) = 2 * 3 by norm_num, hmul (by decide), sigma_two, sigma_three]
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, hpp 3 Nat.prime_two]
    simp [Finset.sum_range_succ]
  · rw [show (9 : ℕ) = 3 ^ 2 by norm_num, hpp 2 Nat.prime_three]
    simp [Finset.sum_range_succ]
  · rw [show (10 : ℕ) = 2 * 5 by norm_num, hmul (by decide), sigma_two, sigma_five]
  · rw [show (15 : ℕ) = 3 * 5 by norm_num, hmul (by decide), sigma_three, sigma_five]
  · rw [show (21 : ℕ) = 3 * 7 by norm_num, hmul (by decide), sigma_three, h7]
  · rw [show (25 : ℕ) = 5 ^ 2 by norm_num, hpp 2 Nat.prime_five]
    simp [Finset.sum_range_succ]
  · rw [show (27 : ℕ) = 3 ^ 3 by norm_num, hpp 3 Nat.prime_three]
    simp [Finset.sum_range_succ]

-- The terms of A387724 up to `10` are exactly `1, 2, 6, 10` (OEIS DATA).
example : IsA387724 1 ∧ IsA387724 2 ∧ ¬ IsA387724 3 ∧ ¬ IsA387724 4 ∧ ¬ IsA387724 5 ∧
    IsA387724 6 ∧ ¬ IsA387724 7 ∧ ¬ IsA387724 8 ∧ ¬ IsA387724 9 ∧ IsA387724 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := a003961_one_to_ten
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s15, s21, s25, s27⟩ := sigma_table
  simp only [IsA387724, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, s1, s2, s3, s4, s5, s6, s7,
    s8, s9, s10, s11, s15, s21, s25, s27]
  norm_num

-- The terms of A337382 up to `11` are `1, 2, 3, 4, 5, 7, 10, 11` (OEIS DATA); checked
-- here up to `10`.
example : IsA337382 1 ∧ IsA337382 2 ∧ IsA337382 3 ∧ IsA337382 4 ∧ IsA337382 5 ∧
    ¬ IsA337382 6 ∧ IsA337382 7 ∧ ¬ IsA337382 8 ∧ ¬ IsA337382 9 ∧ IsA337382 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := a003961_one_to_ten
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s15, s21, s25, s27⟩ := sigma_table
  simp only [IsA337382, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, s1, s2, s3, s4, s5, s6, s7,
    s8, s9, s10, s11, s15, s21, s25, s27]
  norm_num

end Candidates.A387724SigmaCompletelyMultiplicative
