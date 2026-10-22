/-
# Hercher: positive integers `n` with `φ(n) = (2/3)(n + 1)`

Christian Hercher, “On Positive Integers n with φ(n) = (2/3)(n+1)”,
arXiv:2504.19915, §2, Theorem 1 and Corollary 2, and §3, Theorem 10.
Solutions are squarefree; if primes `p,r` satisfy `pr ∣ n`, then
`p ∤ r-1`. With at most four distinct prime factors the solutions are
exactly `5,35,1295,1679615`. The introduction's `1195` is a typo for
`1295 = 5·7·37`. The unrestricted classification and the paper's
computational exclusions for five or six factors and `n < 10^14` are
not formalized here.

* Squarefree: if `p² ∣ n` then `p ∣ φ(p²) ∣ φ(n)`, so `p ∣ 2(n+1)` and
  `p ∣ 2`; but `n` is odd because `φ(n)·2 ≤ n` for even `n`.
  (This replaces the paper's gcd argument on `N/D`.)
* `k ≤ 4`: sort the prime set as `5 ≤ q₁ < … < q_k`; the cases `q₁ ≥ 7`
  (and, for `k = 4`, `q₂ ≥ 17`) are excluded by explicit polynomial
  inequalities whose shifted coefficients are all positive; the remaining
  two-variable equations factor as `(a-3)(b-3) = 8`, `(b-6)(c-6) = 31`,
  `(c-36)(d-36) = 1261`, `5(cd-12c-12d+12) = 1`, `(7c-72)(7d-72) = 4687`
  and are solved by bounding and finite case splits.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.HercherTotientTwoThirds

open Finset

/-! ## Definitions -/

/-- Steinerberger's equation `φ(n) = (2/3)·(n+1)`, cleared of denominators:
`3·φ(n) = 2·(n+1)` (no division, so no junk values). -/
def IsSolution (n : ℕ) : Prop := 3 * n.totient = 2 * (n + 1)

/-- `IsSolution` is decidable (it is an equation of natural numbers). -/
instance : DecidablePred IsSolution := fun n =>
  inferInstanceAs (Decidable (3 * n.totient = 2 * (n + 1)))

/-! Examples: Steinerberger's first two solutions, and small non-solutions. -/
example : IsSolution 5 := by decide
example : IsSolution 35 := by decide
example : ¬ IsSolution 0 := by decide
example : ¬ IsSolution 1 := by decide
example : ¬ IsSolution 7 := by decide

/-! ## Basic totient facts -/

/-- For a prime `p ∣ n` with `n ≠ 0`: `φ(n)·p ≤ n·(p-1)`, i.e. `φ(n)/n ≤ 1 - 1/p`. -/
theorem totient_mul_le_of_prime_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    n.totient * p ≤ n * (p - 1) := by
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩
  have hkey := Nat.totient_mul_prod_primeFactors n
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ (fun q => q - 1) hmem] at hkey
  set A := ∏ q ∈ n.primeFactors.erase p, (q - 1) with hA
  set B := ∏ q ∈ n.primeFactors.erase p, q with hB
  have hAB : A ≤ B := Finset.prod_le_prod' (fun q _ => Nat.sub_le q 1)
  have hBpos : 0 < B := Finset.prod_pos (fun q hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)).pos)
  have hmul : n.totient * p * B ≤ n * (p - 1) * B := by
    calc n.totient * p * B = n * ((p - 1) * A) := by rw [← hkey]; ring
    _ ≤ n * ((p - 1) * B) := by gcongr
    _ = n * (p - 1) * B := by ring
  exact Nat.le_of_mul_le_mul_right hmul hBpos

/-- For squarefree `n`, `φ(n) = ∏_{p ∣ n} (p - 1)`. -/
theorem totient_eq_prod_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hkey := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn, mul_comm] at hkey
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn.ne_zero) hkey

/-! ## Elementary consequences of the equation -/

/-- A solution is nonzero. -/
theorem ne_zero_of_isSolution {n : ℕ} (h : IsSolution n) : n ≠ 0 := by
  rintro rfl
  simp [IsSolution] at h

/-- A solution is not divisible by `2` or `3` (paper, proof of Theorem 1:
"for all primes `q ∣ n` … `q ≥ 5`"); stated for a prime `p ≤ 3`. -/
theorem not_dvd_of_isSolution_of_le_three {n p : ℕ} (h : IsSolution n) (hp : p.Prime)
    (hp3 : p ≤ 3) : ¬ p ∣ n := by
  intro hpn
  have hle := totient_mul_le_of_prime_dvd (ne_zero_of_isSolution h) hp hpn
  have hp2 := hp.two_le
  unfold IsSolution at h
  interval_cases p
  · omega
  · omega

/-- Every prime factor of a solution is at least `5`. -/
theorem five_le_of_mem_primeFactors {n p : ℕ} (h : IsSolution n) (hp : p ∈ n.primeFactors) :
    5 ≤ p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  have hp2 := hpp.two_le
  interval_cases p
  · exact not_dvd_of_isSolution_of_le_three h hpp (by norm_num) hpn
  · exact not_dvd_of_isSolution_of_le_three h hpp (by norm_num) hpn
  · norm_num at hpp

/-- If a prime `p` divides both a solution `n` and `φ(n)`, contradiction:
`p ∣ 3φ(n) = 2n + 2` forces `p ∣ 2`, but `n` is odd. -/
theorem not_dvd_totient_of_isSolution {n p : ℕ} (h : IsSolution n) (hp : p.Prime)
    (hpn : p ∣ n) : ¬ p ∣ n.totient := by
  intro hpt
  have h3 : p ∣ 2 * n + 2 := by
    have h3' : p ∣ 3 * n.totient := hpt.mul_left 3
    rw [h] at h3'
    simpa [mul_add] using h3'
  have h4 : p ∣ 2 := (Nat.dvd_add_right (hpn.mul_left 2)).mp h3
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4] at hpn
  exact not_dvd_of_isSolution_of_le_three h Nat.prime_two (by norm_num) hpn

/-! ## Theorem 1 and Corollary 2 -/

/-- **Hercher, Theorem 1 (`Thm:square-free`)** (arXiv:2504.19915): every positive
integer `n` with
`φ(n) = (2/3)·(n+1)` is squarefree. -/
theorem squarefree_of_isSolution {n : ℕ} (h : IsSolution n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p ∣ (p * p).totient := by
    rw [← pow_two, Nat.totient_prime_pow hp two_pos]
    exact Dvd.dvd.mul_right (by norm_num) _
  exact not_dvd_totient_of_isSolution h hp ((Dvd.intro _ rfl).trans hpp)
    (h1.trans (Nat.totient_dvd_of_dvd hpp))

/-- **Hercher, Corollary 2 (`Cor:prdiv`)** (arXiv:2504.19915): if `n` solves
`φ(n) = (2/3)·(n+1)` and `p`, `r` are primes with `p·r ∣ n`, then `p ∤ (r - 1)`.
(`r - 1` is a true difference since `r` is prime.) -/
theorem not_dvd_sub_one_of_isSolution {n p r : ℕ} (h : IsSolution n) (hp : p.Prime)
    (hr : r.Prime) (hpr : p * r ∣ n) : ¬ p ∣ r - 1 := by
  intro hpr1
  have hrt : r - 1 ∣ n.totient := by
    rw [← Nat.totient_prime hr]
    exact Nat.totient_dvd_of_dvd ((Dvd.intro_left _ rfl).trans hpr)
  exact not_dvd_totient_of_isSolution h hp ((Dvd.intro _ rfl).trans hpr) (hpr1.trans hrt)

/-- The product `∏ (p - 1)` over a set of primes, cast to `ℤ`, is `∏ ((p : ℤ) - 1)`. -/
theorem cast_prod_sub_one {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) :
    ((∏ q ∈ Q, (q - 1) : ℕ) : ℤ) = ∏ q ∈ Q, ((q : ℤ) - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [Nat.cast_sub (hQ q hq).one_le, Nat.cast_one]

/-- **Hercher, reformulation (eq. NewFormulation)** (arXiv:2504.19915):
`n` solves `φ(n) = (2/3)·(n+1)` iff `n` is squarefree and its prime set `Q`
satisfies `3·∏_{q∈Q}(q-1) - 2·∏_{q∈Q} q = 2` (stated over `ℤ`). -/
theorem isSolution_iff (n : ℕ) :
    IsSolution n ↔ Squarefree n ∧
      3 * ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) = 2 * ∏ p ∈ n.primeFactors, (p : ℤ) + 2 := by
  have hQ : ∀ q ∈ n.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  rw [← cast_prod_sub_one hQ]
  constructor
  · intro h
    have hsq := squarefree_of_isSolution h
    refine ⟨hsq, ?_⟩
    rw [← totient_eq_prod_of_squarefree hsq, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
    have h' : (3 * n.totient : ℤ) = 2 * (n + 1) := by exact_mod_cast h
    linear_combination h'
  · rintro ⟨hsq, hE⟩
    rw [← totient_eq_prod_of_squarefree hsq, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq] at hE
    unfold IsSolution
    have hE' : ((3 * n.totient : ℕ) : ℤ) = ((2 * (n + 1) : ℕ) : ℤ) := by
      push_cast
      linear_combination hE
    exact_mod_cast hE'

/-! ## Section 3: prime sets with at most four elements

Polynomial cores over `ℤ` (the variables are the sorted primes `q₁ < q₂ < …`). -/

/-- A prime `p > m` with no prime strictly between `m` and `N` is at least `N`. -/
theorem le_of_prime_of_gap {p m N : ℕ} (hp : p.Prime) (hlt : m < p)
    (hgap : ∀ k, m < k → k < N → ¬ k.Prime) : N ≤ p := by
  by_contra hNp
  exact hgap p hlt (by omega) hp

/-- `k = 1` (Lemma 3, `Lemma:k=1`): `3(a-1) = 2a+2` forces `a = 5`. -/
theorem core_one {a : ℤ} (h : 3 * (a - 1) = 2 * a + 2) : a = 5 := by
  linarith

/-- `k = 2` (Lemma 4, `Lemma:k=2`): `(a-3)(b-3) = 8` with `5 ≤ a < b` forces `a = 5`, `b = 7`. -/
theorem core_two {a b : ℤ} (ha : 5 ≤ a) (hab : a < b)
    (h : 3 * (a - 1) * (b - 1) = 2 * (a * b) + 2) : a = 5 ∧ b = 7 := by
  have hf : (a - 3) * (b - 3) = 8 := by linear_combination h
  have ha5 : a ≤ 5 := by nlinarith
  have ha' : a = 5 := by omega
  subst ha'
  omega

/-- `k = 3`, smallest prime `≥ 7`: then `3∏(q-1) > 2∏q + 2`. -/
theorem core_three_big {a b c : ℤ} (ha : 7 ≤ a) (hb : 11 ≤ b) (hc : 13 ≤ c)
    (h : 3 * (a - 1) * (b - 1) * (c - 1) = 2 * (a * b * c) + 2) : False := by
  have hx : 0 ≤ a - 7 := by linarith
  have hy : 0 ≤ b - 11 := by linarith
  have hz : 0 ≤ c - 13 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hx hy) hz, mul_nonneg hx hy, mul_nonneg hx hz,
    mul_nonneg hy hz]

/-- `k = 3`, `q₁ = 5`: `(b-6)(c-6) = 31` with `5 < b < c` forces `b = 7`, `c = 37`. -/
theorem core_three_five {b c : ℤ} (hb : 5 < b) (hbc : b < c)
    (h : 3 * (5 - 1) * (b - 1) * (c - 1) = 2 * (5 * b * c) + 2) : b = 7 ∧ c = 37 := by
  have hf : (b - 6) * (c - 6) = 31 := by
    have h2 : 2 * ((b - 6) * (c - 6)) = 2 * 31 := by linear_combination h
    linarith
  have hb6 : 7 ≤ b := by
    by_contra hb6
    have hb6' : b = 6 := by omega
    subst hb6'
    norm_num at hf
  have hb11 : b ≤ 11 := by nlinarith
  interval_cases b <;> omega

/-- `k = 4`, smallest prime `≥ 7`: then `3∏(q-1) > 2∏q + 2`. -/
theorem core_four_big {a b c d : ℤ} (ha : 7 ≤ a) (hb : 11 ≤ b) (hc : 13 ≤ c) (hd : 17 ≤ d)
    (h : 3 * (a - 1) * (b - 1) * (c - 1) * (d - 1) = 2 * (a * b * c * d) + 2) : False := by
  have hx : 0 ≤ a - 7 := by linarith
  have hy : 0 ≤ b - 11 := by linarith
  have hz : 0 ≤ c - 13 := by linarith
  have hw : 0 ≤ d - 17 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hx hy) hz) hw,
    mul_nonneg (mul_nonneg hx hy) hz, mul_nonneg (mul_nonneg hx hy) hw,
    mul_nonneg (mul_nonneg hx hz) hw, mul_nonneg (mul_nonneg hy hz) hw,
    mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hx hw, mul_nonneg hy hz,
    mul_nonneg hy hw, mul_nonneg hz hw]

/-- `k = 4`, `q₁ = 5`, `q₂ ≥ 17`: then `3∏(q-1) > 2∏q + 2`. -/
theorem core_four_five_big {b c d : ℤ} (hb : 17 ≤ b) (hc : 19 ≤ c) (hd : 23 ≤ d)
    (h : 3 * (5 - 1) * (b - 1) * (c - 1) * (d - 1) = 2 * (5 * b * c * d) + 2) : False := by
  have hy : 0 ≤ b - 17 := by linarith
  have hz : 0 ≤ c - 19 := by linarith
  have hw : 0 ≤ d - 23 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hz) hw, mul_nonneg hy hz,
    mul_nonneg hy hw, mul_nonneg hz hw]

/-- `k = 4`, `(q₁,q₂) = (5,7)`: `(c-36)(d-36) = 1261` with `7 < c < d` forces
`(c,d) = (37,1297)` or `(49,133)`. -/
theorem core_four_five_seven {c d : ℤ} (hc : 7 < c) (hcd : c < d)
    (h : 3 * (5 - 1) * (7 - 1) * (c - 1) * (d - 1) = 2 * (5 * 7 * c * d) + 2) :
    (c = 37 ∧ d = 1297) ∨ (c = 49 ∧ d = 133) := by
  have hf : (c - 36) * (d - 36) = 1261 := by
    have h2 : 2 * ((c - 36) * (d - 36)) = 2 * 1261 := by linear_combination h
    linarith
  have hc37 : 37 ≤ c := by
    by_contra hc37
    rcases le_or_gt d 36 with hd | hd
    · nlinarith
    · nlinarith
  have hc71 : c ≤ 71 := by nlinarith
  interval_cases c <;> omega

/-- `k = 4`, `(q₁,q₂) = (5,11)`: impossible, as `5(cd - 12c - 12d + 12) = 1`. -/
theorem core_four_five_eleven {c d : ℤ}
    (h : 3 * (5 - 1) * (11 - 1) * (c - 1) * (d - 1) = 2 * (5 * 11 * c * d) + 2) : False := by
  have hf : 5 * (c * d - 12 * c - 12 * d + 12) = 1 := by
    have h2 : 2 * (5 * (c * d - 12 * c - 12 * d + 12)) = 2 * 1 := by linear_combination h
    linarith
  have h5 : (5 : ℤ) ∣ 1 := ⟨_, hf.symm⟩
  norm_num at h5

/-- `k = 4`, `(q₁,q₂) = (5,13)`: `(7c-72)(7d-72) = 4687` has no solution with `17 ≤ c < d`. -/
theorem core_four_five_thirteen {c d : ℤ} (hc : 17 ≤ c) (hcd : c < d)
    (h : 3 * (5 - 1) * (13 - 1) * (c - 1) * (d - 1) = 2 * (5 * 13 * c * d) + 2) : False := by
  have hf : (7 * c - 72) * (7 * d - 72) = 4687 := by
    have h2 : 2 * ((7 * c - 72) * (7 * d - 72)) = 2 * 4687 := by linear_combination 7 * h
    linarith
  have hc20 : c ≤ 20 := by nlinarith
  interval_cases c <;> omega

/-- Three sorted primes `5 ≤ a < b < c` solving the `k = 3` equation are `5, 7, 37`
(Lemma 6, `Lemma:k=3`). -/
theorem primes_three {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h5 : 5 ≤ a) (hab : a < b) (hbc : b < c)
    (h : 3 * ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) = 2 * ((a : ℤ) * b * c) + 2) :
    a = 5 ∧ b = 7 ∧ c = 37 := by
  rcases Nat.lt_or_ge a 7 with ha7 | ha7
  · have ha5 : a = 5 := by
      interval_cases a
      · rfl
      · norm_num at ha
    subst ha5
    push_cast at h
    obtain ⟨hb7, hc37⟩ := core_three_five (by exact_mod_cast hab) (by exact_mod_cast hbc) h
    exact ⟨rfl, by exact_mod_cast hb7, by exact_mod_cast hc37⟩
  · have hb11 : 11 ≤ b := le_of_prime_of_gap hb (show 7 < b by omega)
      (fun k h1 h2 => by interval_cases k <;> norm_num)
    have hc13 : 13 ≤ c := le_of_prime_of_gap hc (show 11 < c by omega)
      (fun k h1 h2 => by interval_cases k; norm_num)
    exact (core_three_big (by exact_mod_cast ha7) (by exact_mod_cast hb11)
      (by exact_mod_cast hc13) h).elim

/-- Four sorted primes `5 ≤ a < b < c < d` solving the `k = 4` equation are
`5, 7, 37, 1297` (Lemma 9, `Lemma:k=4`). -/
theorem primes_four {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (h5 : 5 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : 3 * ((a : ℤ) - 1) * ((b : ℤ) - 1) * ((c : ℤ) - 1) * ((d : ℤ) - 1) =
      2 * ((a : ℤ) * b * c * d) + 2) :
    a = 5 ∧ b = 7 ∧ c = 37 ∧ d = 1297 := by
  rcases Nat.lt_or_ge a 7 with ha7 | ha7
  · have ha5 : a = 5 := by
      interval_cases a
      · rfl
      · norm_num at ha
    subst ha5
    push_cast at h
    rcases Nat.lt_or_ge b 17 with hb17 | hb17
    · interval_cases b
      · -- b = 6
        norm_num at hb
      · -- b = 7
        push_cast at h
        rcases core_four_five_seven (by exact_mod_cast hbc) (by exact_mod_cast hcd) h with
          ⟨hc37, hd1297⟩ | ⟨hc49, _⟩
        · exact ⟨rfl, rfl, by exact_mod_cast hc37, by exact_mod_cast hd1297⟩
        · have hc49' : c = 49 := by exact_mod_cast hc49
          subst hc49'
          norm_num at hc
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · -- b = 11
        push_cast at h
        exact (core_four_five_eleven h).elim
      · norm_num at hb
      · -- b = 13
        push_cast at h
        have hc17 : 17 ≤ c := le_of_prime_of_gap hc hbc
          (fun k h1 h2 => by interval_cases k <;> norm_num)
        exact (core_four_five_thirteen (by exact_mod_cast hc17) (by exact_mod_cast hcd) h).elim
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
    · have hc19 : 19 ≤ c := le_of_prime_of_gap hc (show 17 < c by omega)
        (fun k h1 h2 => by interval_cases k; norm_num)
      have hd23 : 23 ≤ d := le_of_prime_of_gap hd (show 19 < d by omega)
        (fun k h1 h2 => by interval_cases k <;> norm_num)
      exact (core_four_five_big (by exact_mod_cast hb17) (by exact_mod_cast hc19)
        (by exact_mod_cast hd23) h).elim
  · have hb11 : 11 ≤ b := le_of_prime_of_gap hb (show 7 < b by omega)
      (fun k h1 h2 => by interval_cases k <;> norm_num)
    have hc13 : 13 ≤ c := le_of_prime_of_gap hc (show 11 < c by omega)
      (fun k h1 h2 => by interval_cases k; norm_num)
    have hd17 : 17 ≤ d := le_of_prime_of_gap hd (show 13 < d by omega)
      (fun k h1 h2 => by interval_cases k <;> norm_num)
    exact (core_four_big (by exact_mod_cast ha7) (by exact_mod_cast hb11)
      (by exact_mod_cast hc13) (by exact_mod_cast hd17) h).elim

/-! ## Sorting a prime set -/

/-- A nonempty finset of naturals splits off its minimum: `Q = insert a R`
with `a ∉ R` and `a < x` for every `x ∈ R`. -/
theorem exists_eq_insert_min {Q : Finset ℕ} (hQ : Q.Nonempty) :
    ∃ a R, a ∉ R ∧ Q = insert a R ∧ ∀ x ∈ R, a < x :=
  ⟨Q.min' hQ, Q.erase (Q.min' hQ), Finset.notMem_erase _ _,
    (Finset.insert_erase (Finset.min'_mem _ _)).symm,
    fun _ hx => Finset.min'_lt_of_mem_erase_min' _ _ hx⟩

/-- **Hercher, Theorem 10 on prime sets** (arXiv:2504.19915, Lemmas 3, 4, 6, 9):
a finite set `Q` of primes `≥ 5` with `|Q| ≤ 4` and
`3·∏_{q∈Q}(q-1) = 2·∏_{q∈Q} q + 2` is one of `{5}`, `{5,7}`, `{5,7,37}`,
`{5,7,37,1297}`. -/
theorem primeSet_eq_of_card_le_four {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q)
    (hk : Q.card ≤ 4)
    (hE : 3 * ∏ q ∈ Q, ((q : ℤ) - 1) = 2 * ∏ q ∈ Q, (q : ℤ) + 2) :
    Q = {5} ∨ Q = {5, 7} ∨ Q = {5, 7, 37} ∨ Q = {5, 7, 37, 1297} := by
  rcases Q.eq_empty_or_nonempty with rfl | hQne
  · simp at hE
  obtain ⟨a, R, haR, rfl, haR'⟩ := exists_eq_insert_min hQne
  have hkR : R.card ≤ 3 := by rw [Finset.card_insert_of_notMem haR] at hk; omega
  have hpa := hQ a (Finset.mem_insert_self _ _)
  rw [Finset.prod_insert haR, Finset.prod_insert haR] at hE
  rcases R.eq_empty_or_nonempty with rfl | hRne
  · simp only [Finset.prod_empty, mul_one] at hE
    left
    have ha5 : (a : ℤ) = 5 := core_one hE
    rw [show a = 5 by exact_mod_cast ha5, Finset.insert_empty]
  obtain ⟨b, S, hbS, rfl, hbS'⟩ := exists_eq_insert_min hRne
  have hkS : S.card ≤ 2 := by rw [Finset.card_insert_of_notMem hbS] at hkR; omega
  have hab : a < b := haR' b (Finset.mem_insert_self _ _)
  have hpb := hQ b (by simp)
  rw [Finset.prod_insert hbS, Finset.prod_insert hbS] at hE
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp only [Finset.prod_empty, mul_one] at hE
    right; left
    obtain ⟨ha5, hb7⟩ := core_two (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hpa.2)
      (by exact_mod_cast hab) (by linear_combination hE)
    rw [show a = 5 by exact_mod_cast ha5, show b = 7 by exact_mod_cast hb7, Finset.insert_empty]
  obtain ⟨c, T, hcT, rfl, hcT'⟩ := exists_eq_insert_min hSne
  have hkT : T.card ≤ 1 := by rw [Finset.card_insert_of_notMem hcT] at hkS; omega
  have hbc : b < c := hbS' c (Finset.mem_insert_self _ _)
  have hpc := hQ c (by simp)
  rw [Finset.prod_insert hcT, Finset.prod_insert hcT] at hE
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp only [Finset.prod_empty, mul_one] at hE
    right; right; left
    obtain ⟨ha5, hb7, hc37⟩ := primes_three hpa.1 hpb.1 hpc.1 hpa.2 hab hbc
      (by linear_combination hE)
    subst ha5 hb7 hc37
    rw [Finset.insert_empty]
  obtain ⟨d, U, hdU, rfl, hdU'⟩ := exists_eq_insert_min hTne
  have hkU : U.card = 0 := by rw [Finset.card_insert_of_notMem hdU] at hkT; omega
  rw [Finset.card_eq_zero] at hkU
  subst hkU
  have hcd : c < d := hcT' d (Finset.mem_insert_self _ _)
  have hpd := hQ d (by simp)
  rw [Finset.prod_insert hdU, Finset.prod_insert hdU] at hE
  simp only [Finset.prod_empty, mul_one] at hE
  right; right; right
  obtain ⟨ha5, hb7, hc37, hd1297⟩ := primes_four hpa.1 hpb.1 hpc.1 hpd.1 hpa.2 hab hbc hcd
    (by linear_combination hE)
  subst ha5 hb7 hc37 hd1297
  rw [Finset.insert_empty]

/-! ## Theorem 10: solutions with at most four prime factors -/

/-- **Hercher, Theorem 10** (arXiv:2504.19915, `Thm:k<=4`): every `n` with
`φ(n) = (2/3)·(n+1)` and at most four distinct prime factors is one of
Steinerberger's solutions `5, 35 = 5·7, 1295 = 5·7·37, 1679615 = 5·7·37·1297`. -/
theorem mem_of_isSolution_of_card_primeFactors_le_four {n : ℕ} (h : IsSolution n)
    (hk : n.primeFactors.card ≤ 4) : n ∈ ({5, 35, 1295, 1679615} : Finset ℕ) := by
  obtain ⟨hsq, hE⟩ := (isSolution_iff n).1 h
  have hQ : ∀ q ∈ n.primeFactors, q.Prime ∧ 5 ≤ q := fun q hq =>
    ⟨Nat.prime_of_mem_primeFactors hq, five_le_of_mem_primeFactors h hq⟩
  have hn : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  rcases primeSet_eq_of_card_le_four hQ hk hE with hP | hP | hP | hP <;>
    · rw [hP] at hn
      norm_num at hn
      subst hn
      decide

/-- `1679615 = 5·7·37·1297` has `φ = 4·6·36·1296`. -/
theorem totient_1679615 : Nat.totient 1679615 = 4 * 6 * 36 * 1296 := by
  rw [show (1679615 : ℕ) = 5 * 7 * 37 * 1297 by norm_num,
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `1295 = 5·7·37` has `φ = 4·6·36`. -/
theorem totient_1295 : Nat.totient 1295 = 4 * 6 * 36 := by
  rw [show (1295 : ℕ) = 5 * 7 * 37 by norm_num,
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num)]

/-- Steinerberger's four numbers solve `φ(n) = (2/3)·(n+1)` and have at most four
prime factors (converse of Theorem 10). -/
theorem isSolution_of_mem {n : ℕ} (hn : n ∈ ({5, 35, 1295, 1679615} : Finset ℕ)) :
    IsSolution n ∧ n.primeFactors.card ≤ 4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, by rw [Nat.Prime.primeFactors (by norm_num)]; simp⟩
  · refine ⟨by decide, ?_⟩
    rw [show (35 : ℕ) = 5 * 7 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide
  · refine ⟨by unfold IsSolution; rw [totient_1295], ?_⟩
    rw [show (1295 : ℕ) = 5 * 7 * 37 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    decide
  · refine ⟨by unfold IsSolution; rw [totient_1679615], ?_⟩
    rw [show (1679615 : ℕ) = 5 * 7 * 37 * 1297 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide

/-- **Hercher, Theorem 10, as an equivalence** (arXiv:2504.19915): the solutions of
`φ(n) = (2/3)·(n+1)` with at most four distinct prime factors are exactly
`5, 35, 1295, 1679615`. -/
theorem isSolution_and_card_le_four_iff (n : ℕ) :
    IsSolution n ∧ n.primeFactors.card ≤ 4 ↔ n ∈ ({5, 35, 1295, 1679615} : Finset ℕ) :=
  ⟨fun h => mem_of_isSolution_of_card_primeFactors_le_four h.1 h.2, isSolution_of_mem⟩

end Candidates.HercherTotientTwoThirds
