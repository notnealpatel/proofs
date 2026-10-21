/-
# A343260 — Bala: `a(p^r) ≡ 1 (mod p^(2r))` for `a(n) = 2 T_n((n+1)/2)`

## OEIS source (retrieved with `oeis show A343260`, 2026-10-21)

```
NAME:     a(n) = 2 * T(n,(n+1)/2) where T(n,x) is a Chebyshev polynomial of the
          first kind.
TERMS:    2,2,7,52,527,6726,103682,1874888,38925119,912670090,23855111399,
          687808321212,21687295069442,742397047217294,27420344506901023,...
FORMULA:  a(n) = 2 * cos(n*arccos((n+1)/2)).
FORMULA:  a(n) = 2 * n * Sum_{k=0..n} (n-1)^k * binomial(n+k,2*k)/(n+k) for n > 0.
FORMULA (the conjecture):
  Conjecture: a(p^r) == 1 (mod p^(2*r)) for positive integer r and all primes
  p >= 5. - _Peter Bala_, Mar 11 2024
```

## Status

Triage: open (no proof in the entry or, as far as the triage could tell, in the
literature).  Computation (Python, exact integers): the congruence holds for all
primes `5 ≤ p ≤ 37` and `r ≥ 1` with `p^r ≤ 3000`, and the stronger
`a(n) ≡ 2 cos(nπ/3) (mod n^2)` holds for all `1 ≤ n < 800`.

## Proof strategy (formalized below)

`a(n) = C_n(n+1)` where `C_n` is the Vieta–Lucas polynomial
(`Polynomial.Chebyshev.C`, `C_n(2x) = 2 T_n(x)`).  For every integer `m` and
every `k`, `C_k(1+m) ≡ c_k + m k s_k (mod m^2)`, where `c_k = C_k(1)` and
`s` satisfies `s_0 = 0, s_1 = 1, s_{k+2} = s_{k+1} - s_k`.  Taking `m = k = n`
gives `a(n) ≡ c_n (mod n^2)`; `c` has period 6 and `c_n = 1` when
`gcd(n, 6) = 1`.  This proves Bala's conjecture and extends it to every `n`
coprime to `6`.  The module is `sorry`-free; axiom audit (2026-10-21):
`propext`, `Classical.choice`, `Quot.sound` only.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A343260ChebyshevPolynomialFirst

open Polynomial Polynomial.Chebyshev

/-! ## Definition layer -/

/-- The OEIS definition verbatim: `a(n) = 2 * T(n, (n+1)/2)` with `T` the Chebyshev
polynomial of the first kind (`Polynomial.Chebyshev.T`), evaluated over `ℚ`. -/
noncomputable def aQ (n : ℕ) : ℚ := 2 * (T ℚ n).eval (((n : ℚ) + 1) / 2)

/-- Integer form of A343260: `a(n) = C_n(n+1)` with `C` the Vieta–Lucas polynomial
(`Polynomial.Chebyshev.C`, characterised by `C_n(2x) = 2 T_n(x)`). -/
noncomputable def a (n : ℕ) : ℤ := (C ℤ n).eval ((n : ℤ) + 1)

/-- Computable Vieta–Lucas recursion: `vl y 0 = 2`, `vl y 1 = y`,
`vl y (k+2) = y * vl y (k+1) - vl y k`. -/
def vl (y : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => y
  | k + 2 => y * vl y (k + 1) - vl y k

/-- The auxiliary sequence `s_0 = 0`, `s_1 = 1`, `s_{k+2} = s_{k+1} - s_k`
(period `0, 1, 1, 0, -1, -1`); `s_k = U_{k-1}(1/2)`. -/
def s : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => s (k + 1) - s k

/-- The Vieta–Lucas polynomial evaluates to the computable recursion. -/
theorem eval_C_eq_vl (y : ℤ) (k : ℕ) : (C ℤ k).eval y = vl y k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [vl]
    | 1, _ => simp [vl]
    | k + 2, ih =>
      have h2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      have h1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h2, C_add_two, eval_sub, eval_mul, eval_X, h1, ih k (by omega),
        ih (k + 1) (by omega)]
      rfl

/-- `a n` is the computable recursion evaluated at `n + 1`. -/
theorem a_eq_vl (n : ℕ) : a n = vl ((n : ℤ) + 1) n := eval_C_eq_vl _ _

/-- Fidelity bridge: the integer form agrees with the OEIS definition
`2 * T_n((n+1)/2)` over `ℚ`. -/
theorem aQ_eq_a (n : ℕ) : aQ n = (a n : ℚ) := by
  have hcomp := congrArg (fun p : ℚ[X] => p.eval (((n : ℚ) + 1) / 2))
    (C_comp_two_mul_X ℚ (n : ℤ))
  simp only [eval_comp, eval_mul, eval_X, eval_ofNat] at hcomp
  have hcast : ((a n : ℤ) : ℚ) = (C ℚ n).eval ((n : ℚ) + 1) := by
    have := algebraMap_eval_C (R := ℤ) (R' := ℚ) ((n : ℤ) + 1) (n : ℤ)
    simpa [a] using this
  rw [aQ, hcast, ← hcomp]
  congr 1
  ring

example : a 0 = 2 := by rw [a_eq_vl]; decide
example : a 1 = 2 := by rw [a_eq_vl]; decide
example : a 2 = 7 := by rw [a_eq_vl]; decide
example : a 3 = 52 := by rw [a_eq_vl]; decide
example : a 4 = 527 := by rw [a_eq_vl]; decide
example : a 5 = 6726 := by rw [a_eq_vl]; decide
example : a 9 = 912670090 := by rw [a_eq_vl]; decide
example : a 18 = 99042070146811639444802 := by rw [a_eq_vl]; decide


/-! ## The key congruence -/

/-- `c_{k+1} = s_{k+1} - 2 s_k` where `c_k = C_k(1) = vl 1 k`. -/
theorem vl_one_succ (k : ℕ) : vl 1 (k + 1) = s (k + 1) - 2 * s k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => decide
    | 1, _ => decide
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have e1 : vl 1 (k + 2 + 1) = 1 * vl 1 (k + 2) - vl 1 (k + 1) := rfl
      have e2 : s (k + 2 + 1) = s (k + 2) - s (k + 1) := rfl
      have e3 : s (k + 2) = s (k + 1) - s k := rfl
      rw [e1, e2, h1, e3, h0]
      ring

/-- **Key congruence.** For every integer `m` and every `k`,
`C_k(1 + m) ≡ C_k(1) + m k s_k (mod m^2)`. -/
theorem sq_dvd_vl_sub (m : ℤ) (k : ℕ) :
    m ^ 2 ∣ vl (1 + m) k - vl 1 k - m * k * s k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [vl, s]
    | 1, _ => simp [vl, s]
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hc := vl_one_succ k
      have e : vl (1 + m) (k + 2) - vl 1 (k + 2) - m * ((k + 2 : ℕ) : ℤ) * s (k + 2)
          = (1 + m) * (vl (1 + m) (k + 1) - vl 1 (k + 1) - m * ((k + 1 : ℕ) : ℤ) * s (k + 1))
            - (vl (1 + m) k - vl 1 k - m * (k : ℤ) * s k)
            + m ^ 2 * (((k + 1 : ℕ) : ℤ) * s (k + 1)) := by
        have ev : vl (1 + m) (k + 2) = (1 + m) * vl (1 + m) (k + 1) - vl (1 + m) k := rfl
        have e1 : vl 1 (k + 2) = 1 * vl 1 (k + 1) - vl 1 k := rfl
        have es : s (k + 2) = s (k + 1) - s k := rfl
        rw [ev, e1, es, hc]
        push_cast
        ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right h1 _) h0) (dvd_mul_right _ _)


/-! ## Periodicity of `C_k(1)` -/

/-- `c_k = C_k(1)` has period `6`. -/
theorem vl_one_add_six (k : ℕ) : vl 1 (k + 6) = vl 1 k := by
  simp only [vl]
  ring

/-- `c_n = c_{n mod 6}`. -/
theorem vl_one_eq_mod (n : ℕ) : vl 1 n = vl 1 (n % 6) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with hn | hn
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      rw [vl_one_add_six, ih k (by omega), Nat.add_mod_right]

/-- For `n` coprime to `6`, `C_n(1) = 1`. -/
theorem vl_one_of_coprime (n : ℕ) (h : Nat.Coprime n 6) : vl 1 n = 1 := by
  have h2 : ¬ 2 ∣ n := fun hd => by
    have := Nat.dvd_gcd hd (by norm_num : 2 ∣ 6)
    rw [h] at this
    omega
  have h3 : ¬ 3 ∣ n := fun hd => by
    have := Nat.dvd_gcd hd (by norm_num : 3 ∣ 6)
    rw [h] at this
    omega
  have hmod : n % 6 = 1 ∨ n % 6 = 5 := by omega
  rw [vl_one_eq_mod]
  rcases hmod with hm | hm <;> rw [hm] <;> decide

/-! ## Main results -/

/-- **Stronger congruence.** For every `n`, `a(n) ≡ C_n(1) = 2 cos(nπ/3) (mod n^2)`. -/
theorem a_modEq_vl_one (n : ℕ) : a n ≡ vl 1 n [ZMOD (n : ℤ) ^ 2] := by
  have hk := sq_dvd_vl_sub (n : ℤ) n
  have hdiv : (n : ℤ) ^ 2 ∣ vl (1 + (n : ℤ)) n - vl 1 n := by
    have e : vl (1 + (n : ℤ)) n - vl 1 n
        = (vl (1 + (n : ℤ)) n - vl 1 n - (n : ℤ) * (n : ℤ) * s n) + (n : ℤ) ^ 2 * s n := by
      ring
    rw [e]
    exact dvd_add hk (dvd_mul_right _ _)
  rw [a_eq_vl, add_comm]
  exact (Int.modEq_iff_dvd.mpr hdiv).symm

/-- **Extension of Bala's conjecture.** For every `n` coprime to `6`,
`a(n) ≡ 1 (mod n^2)`. -/
theorem a_modEq_one_of_coprime (n : ℕ) (h : Nat.Coprime n 6) :
    a n ≡ 1 [ZMOD (n : ℤ) ^ 2] := by
  have hv := a_modEq_vl_one n
  rwa [vl_one_of_coprime n h] at hv

/-- For every prime `p ≥ 5` and every `r` (including `r = 0`),
`a(p^r) ≡ 1 (mod p^(2r))`. -/
theorem a_prime_pow_modEq_one (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    a (p ^ r) ≡ 1 [ZMOD (p : ℤ) ^ (2 * r)] := by
  have hnd : ¬ p ∣ 6 := fun hd => by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> revert hd hp <;> decide
  have hcop : Nat.Coprime (p ^ r) 6 := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).pow_left r
  have hm := a_modEq_one_of_coprime (p ^ r) hcop
  have e : ((p ^ r : ℕ) : ℤ) ^ 2 = (p : ℤ) ^ (2 * r) := by
    push_cast
    rw [← pow_mul, mul_comm]
  rwa [e] at hm

/-- **Bala's conjecture (A343260, Peter Bala, Mar 11 2024).**
Verbatim: "Conjecture: a(p^r) == 1 (mod p^(2*r)) for positive integer r and all
primes p >= 5."  Here `a(n) = C_n(n+1) = 2 T_n((n+1)/2)` (bridge `aQ_eq_a`).
The hypothesis `1 ≤ r` is kept from the source; the proof does not need it
(`a_prime_pow_modEq_one`). -/
theorem bala_conjecture (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (_hr : 1 ≤ r) :
    a (p ^ r) ≡ 1 [ZMOD (p : ℤ) ^ (2 * r)] := by
  exact a_prime_pow_modEq_one p r hp h5

/-- Non-vacuity: the hypotheses of `bala_conjecture` hold jointly at `p = 5`, `r = 1`,
and the conclusion there reads `6726 ≡ 1 (mod 25)`. -/
example : Nat.Prime 5 ∧ 5 ≤ 5 ∧ 1 ≤ 1 ∧ a (5 ^ 1) = 6726 ∧ (6726 : ℤ) ≡ 1 [ZMOD 5 ^ (2 * 1)] := by
  refine ⟨by norm_num, le_rfl, le_rfl, by rw [a_eq_vl]; decide, by decide⟩

/-- **Bala's conjecture in the entry's own terms.** For every prime `p ≥ 5` and
`r ≥ 1`, `2 T_{p^r}((p^r+1)/2) = 1 + p^(2r) q` for some integer `q`. -/
theorem bala_conjecture_rat (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) :
    ∃ q : ℤ, aQ (p ^ r) = 1 + (p : ℚ) ^ (2 * r) * q := by
  obtain ⟨q, hq⟩ := (Int.modEq_iff_dvd.mp (bala_conjecture p r hp h5 hr).symm)
  refine ⟨q, ?_⟩
  rw [aQ_eq_a]
  have hq' : (a (p ^ r) : ℚ) = 1 + ((p : ℤ) ^ (2 * r) * q : ℤ) := by
    rw [← hq]
    push_cast
    ring
  rw [hq']
  push_cast
  ring

end Candidates.A343260ChebyshevPolynomialFirst
