/-
# A179929 — Bala: `2^n A_n(-1/2)` is eventually periodic modulo `k` with period dividing `φ(k)`

## OEIS source (pulled with `oeis show A179929`, retrieved 2026-10-21)

```
NAME:     a(n) = 2^n*A(n, -1/2), A(n, x) the Eulerian polynomials.
TERMS:    1,2,2,-6,-30,42,882,954,-39870,-203958,2300562,29677914,-120958110,...
KEYWORDS: sign,easy
FORMULA (Deléham, Dec 22 2011):
  a(n) = Sum_{k = 0..n} A173018(n,k)*2^(n-k)*(-1)^k.
FORMULA (Sykora, May 15 2014):
  a(n) = Sum_{k = 0..n} 3^(n-k)*(-1)^k*k!*S(n+1, k+1), S(m, l) the Stirling
  number of second kind.
COMMENT (the conjecture):
  Conjecture: the sequence {a(n)} reduced modulo a positive integer k is
  eventually periodic with period a divisor of phi(k), where phi() =
  A000010(k). For example, modulo 11 the sequence becomes [1, 2, 2, 5, 3, 9,
  2, 8, 5, 4, 0, 2, 2, 5, 3, 9, 2, 8, 5, 4, 0, 2, 2, 5, 3, 9, 2, 8, 5, 4, 0,
  ...], with an apparent period of 10 = phi(11) starting at n = 1.
  - _Peter Bala_, Feb 20 2026
```

## Status

Triage: "unclear" — the entry gives no proof; no literature search was run
by the triage. The general phenomenon (Stirling transforms of `k! c_k` are
eventually periodic modulo `m`) is classical in spirit (Gross 1962 on the
Fubini numbers), so the statement may follow from known results.
Computation (python, 2026-10-21): for every `1 ≤ m ≤ 200`, using 400 terms,
`a(n + φ(m)) ≡ a(n) (mod m)` holds from some `n ≤ 9` onward.

## Proof (kernel-checked below)

1. `k! S(n+1,k+1) = Σ_{j ≤ k} (-1)^(k-j) C(k,j) (j+1)^n` (induction on the
   Stirling recurrence), so the `k`-th summand of `a(n)` is
   `3^(n-k) Σ_{j ≤ k} (-1)^j C(k,j) (j+1)^n`.
2. For `k ≥ m`, `m ∣ k!`, so modulo `m` only the summands `k < m` survive.
3. For `e ≥ m`, `x^(e + L) ≡ x^e (mod m)` for every `L` with
   `x^L ≡ 1 (mod q)` whenever `q ∣ m` and `gcd(x, q) = 1`: check it on every
   prime power `p^i ∣ m` (if `p ∣ x` then `p^i ∣ x^e` since `i < p^i ≤ m ≤ e`).
   Both `L = φ(m)` and `L = λ(m)` (Carmichael) qualify.
4. Hence `a(n + L) ≡ a(n) (mod m)` for `n ≥ 2m`.

The Carmichael version implies Bala's statement (`λ(m) ∣ φ(m)`) and is
strictly sharper whenever `λ(m) < φ(m)`, e.g. `m = 8`.

## Definitional fidelity

The theorems are stated for the entry's Stirling formula (Sykora). The NAME
definition `2^n A_n(-1/2)` is encoded separately as `viaEulerian`; the two
agree on all twenty-one listed terms (kernel `decide` below), but a general
proof that `A179929 = viaEulerian` is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A179929EulerianMod

open Finset

/-! ## Definition layer -/

/-- OEIS A179929 via the entry's Stirling formula (Sykora, May 15 2014):
`a(n) = Σ_{k=0..n} 3^(n-k) (-1)^k k! S(n+1, k+1)`. -/
def A179929 (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (3 : ℤ) ^ (n - k) * (-1) ^ k * (k.factorial : ℤ) *
    (Nat.stirlingSecond (n + 1) (k + 1) : ℤ)

/-- Eulerian numbers in the convention of OEIS A173018: `eulerian n k` is the
number of permutations of `n` letters with `k` ascents, via the recurrence
`⟨n+1, k+1⟩ = (k+2)⟨n, k+1⟩ + (n-k)⟨n, k⟩`, `⟨n+1, 0⟩ = ⟨n, 0⟩`, `⟨0, 0⟩ = 1`.
(The `Nat` subtraction `n - k` only truncates when `k > n`, where
`eulerian n k = 0`.) -/
def eulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => eulerian n 0
  | n + 1, k + 1 => (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k

/-- The entry's NAME definition `2^n A_n(-1/2)`, expanded as in the formula of
Deléham (Dec 22 2011): `Σ_{k=0..n} A173018(n,k) 2^(n-k) (-1)^k`. -/
def viaEulerian (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (eulerian n k : ℤ) * 2 ^ (n - k) * (-1) ^ k

/-! ## Ground truth -/

-- Row 4 of A173018: `1, 11, 11, 1, 0`.
example : (List.range 5).map (fun k => eulerian 4 k) = [1, 11, 11, 1, 0] := by decide

-- All twenty-one listed terms, from the Stirling formula.
example : (List.range 21).map A179929 =
    [1, 2, 2, -6, -30, 42, 882, 954, -39870, -203958, 2300562,
      29677914, -120958110, -4657703958, -7059175758, 807984602874, 6667870853250, -145556787011958, -2827006784652078, 21703953751815834, 1108558810703202210] := by decide

-- The same twenty-one terms from the Eulerian-polynomial NAME definition.
example : (List.range 21).map viaEulerian =
    [1, 2, 2, -6, -30, 42, 882, 954, -39870, -203958, 2300562,
      29677914, -120958110, -4657703958, -7059175758, 807984602874, 6667870853250, -145556787011958, -2827006784652078, 21703953751815834, 1108558810703202210] := by decide

-- The entry's worked example: modulo 11 the terms `a(1), …, a(10)` repeat
-- from `a(11)` on (period `10 = φ(11)`), checked on the listed range.
example : ∀ n ∈ Finset.Icc 1 10, A179929 (n + 10) ≡ A179929 n [ZMOD 11] := by decide

/-! ## Helper lemmas -/

/-- Explicit formula for Stirling numbers of the second kind, in signed form:
`(-1)^k k! S(n+1, k+1) = Σ_{j=0..k} (-1)^j C(k, j) (j+1)^n`. -/
theorem neg_one_pow_mul_factorial_mul_stirlingSecond (n k : ℕ) :
    (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond (n + 1) (k + 1) : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n := by
  induction n generalizing k with
  | zero =>
    have h := (Int.alternating_sum_range_choose (n := k))
    simp only [pow_zero, mul_one]
    rw [h]
    rcases k with _ | k
    · simp [Nat.stirlingSecond_self]
    · simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ n ih =>
    rcases k with _ | k
    · simp [Nat.stirlingSecond_one_right]
    · have e1 := ih (k + 1)
      have e2 := ih k
      have hext : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n =
          ∑ j ∈ range (k + 2), (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n := by
        rw [sum_range_succ _ (k + 1), Nat.choose_succ_self]
        simp
      calc (-1 : ℤ) ^ (k + 1) * ((k + 1).factorial : ℤ) *
              (Nat.stirlingSecond (n + 1 + 1) (k + 1 + 1) : ℤ)
          = ((k : ℤ) + 2) * ((-1 : ℤ) ^ (k + 1) * ((k + 1).factorial : ℤ) *
              (Nat.stirlingSecond (n + 1) (k + 1 + 1) : ℤ)) - ((k : ℤ) + 1) *
              ((-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond (n + 1) (k + 1) : ℤ)) := by
            rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
            push_cast
            ring
        _ = _ := by
            rw [e1, e2, hext, mul_sum, mul_sum, ← sum_sub_distrib]
            refine sum_congr rfl fun j hj => ?_
            have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
            have hc : ((k.choose j : ℕ) : ℤ) * ((k : ℤ) + 1) =
                ((k + 1).choose j : ℤ) * ((k : ℤ) + 1 - j) := by
              have h := Nat.choose_mul_succ_eq k j
              have h' : ((k.choose j * (k + 1) : ℕ) : ℤ) =
                  (((k + 1).choose j * (k + 1 - j) : ℕ) : ℤ) := congrArg _ h
              rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hjk] at h'
              push_cast at h'
              exact h'
            push_cast
            linear_combination (-(-1 : ℤ) ^ j * ((j : ℤ) + 1) ^ n) * hc

/-- Eventual periodicity of powers modulo `m`: if `x^L ≡ 1 (mod q)` for every
divisor `q ∣ m` coprime to `x`, then `x^(e + L) ≡ x^e (mod m)` for all
`e ≥ m ≥ 1`. -/
theorem pow_add_modEq_pow_of_le (m x e L : ℕ) (hm : 0 < m) (he : m ≤ e)
    (hL : ∀ q : ℕ, q ∣ m → Nat.Coprime x q → x ^ L ≡ 1 [MOD q]) :
    x ^ (e + L) ≡ x ^ e [MOD m] := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have he0 : e ≠ 0 := by omega
    have hzero : ∀ f : ℕ, f ≠ 0 → (0 : ℕ) ^ f = 0 := fun f hf => zero_pow hf
    rw [hzero e he0, hzero (e + L) (by omega)]
  have hle : x ^ e ≤ x ^ (e + L) := Nat.pow_le_pow_right hx (by omega)
  refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
  have hfac : x ^ (e + L) - x ^ e = x ^ e * (x ^ L - 1) := by
    rw [Nat.mul_sub, mul_one, pow_add]
  rw [hfac, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p i hp hpi
  have hpi_le : p ^ i ≤ m := Nat.le_of_dvd hm hpi
  have hi_lt : i < p ^ i := Nat.lt_pow_self hp.one_lt
  by_cases hpx : p ∣ x
  · apply Dvd.dvd.mul_right
    exact (pow_dvd_pow_of_dvd hpx i).trans (pow_dvd_pow x (by omega))
  · apply Dvd.dvd.mul_left
    have hcop : Nat.Coprime x (p ^ i) :=
      Nat.Coprime.pow_right i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx).symm
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hx)).mp (hL _ hpi hcop).symm

/-- The signed column sum `T(n, k) = Σ_{j=0..k} (-1)^j C(k, j) (j+1)^n`, equal to
`(-1)^k k! S(n+1, k+1)` by `neg_one_pow_mul_factorial_mul_stirlingSecond`. -/
def altSum (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n

/-- Modulo `m`, only the summands `k < m` of `a(n)` survive (as `m ∣ k!` for
`k ≥ m`), and each is `3^(n-k) T(n, k)`. -/
theorem A179929_cast_eq_sum_range (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n + 1) :
    ((A179929 n : ℤ) : ZMod m) =
      ∑ k ∈ range m, ((3 : ℕ) : ZMod m) ^ (n - k) * ((altSum n k : ℤ) : ZMod m) := by
  unfold A179929
  rw [← sum_range_add_sum_Ico _ hmn, Int.cast_add]
  have htail : ((∑ k ∈ Ico m (n + 1), (3 : ℤ) ^ (n - k) * (-1) ^ k * (k.factorial : ℤ) *
      (Nat.stirlingSecond (n + 1) (k + 1) : ℤ) : ℤ) : ZMod m) = 0 := by
    rw [Int.cast_sum]
    refine sum_eq_zero fun k hk => ?_
    have hmk : m ≤ k := (mem_Ico.mp hk).1
    have hfac : ((k.factorial : ℕ) : ZMod m) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hm hmk)
    push_cast
    rw [hfac]
    ring
  rw [htail, add_zero, Int.cast_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [altSum, ← neg_one_pow_mul_factorial_mul_stirlingSecond]
  push_cast
  ring

/-- **Eventual periodicity with any admissible period.** If `L` satisfies
`x^L ≡ 1 (mod q)` for every `q ∣ m` and every `x` coprime to `q`, then
`a(n + L) ≡ a(n) (mod m)` for all `n ≥ 2m`. -/
theorem A179929_add_modEq_of_le (m L : ℕ) (hm : 0 < m)
    (hL : ∀ q x : ℕ, q ∣ m → Nat.Coprime x q → x ^ L ≡ 1 [MOD q])
    (n : ℕ) (hn : 2 * m ≤ n) :
    A179929 (n + L) ≡ A179929 n [ZMOD m] := by
  have hpow : ∀ x e : ℕ, m ≤ e → ((x : ℕ) : ZMod m) ^ (e + L) = ((x : ℕ) : ZMod m) ^ e := by
    intro x e he
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (pow_add_modEq_pow_of_le m x e L hm he (fun q hq hx => hL q x hq hx))
    push_cast at h
    exact h
  rw [← ZMod.intCast_eq_intCast_iff, A179929_cast_eq_sum_range m (n + L) hm (by omega),
    A179929_cast_eq_sum_range m n hm (by omega)]
  refine sum_congr rfl fun k hk => ?_
  have hkm : k < m := mem_range.mp hk
  have h3 : ((3 : ℕ) : ZMod m) ^ (n + L - k) = ((3 : ℕ) : ZMod m) ^ (n - k) := by
    rw [Nat.sub_add_comm (by omega : k ≤ n)]
    exact hpow 3 (n - k) (by omega)
  have hT : ((altSum (n + L) k : ℤ) : ZMod m) = ((altSum n k : ℤ) : ZMod m) := by
    unfold altSum
    push_cast
    refine sum_congr rfl fun j _ => ?_
    have hj := hpow (j + 1) n (by omega)
    push_cast at hj
    rw [hj]
  rw [h3, hT]

/-- **Bala's conjecture (A179929, Peter Bala, Feb 20 2026).**

Verbatim: "Conjecture: the sequence {a(n)} reduced modulo a positive integer k
is eventually periodic with period a divisor of phi(k), where phi() =
A000010(k)."

Formal reading: for every `m ≥ 1` there is `N` with
`a(n + φ(m)) ≡ a(n) (mod m)` for all `n ≥ N` (this is equivalent to the
reduction mod `m` being eventually periodic with minimal period dividing
`φ(m)`). Proved here with `N = 2m`. -/
theorem A179929_eventually_periodic_totient (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A179929 (n + Nat.totient m) ≡ A179929 n [ZMOD m] := by
  refine ⟨2 * m, fun n hn => A179929_add_modEq_of_le m (Nat.totient m) hm ?_ n hn⟩
  intro q x hq hx
  obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hq
  rw [hc, pow_mul]
  simpa using (Nat.ModEq.pow_totient hx).pow c

/-- **Carmichael strengthening.** For every `m ≥ 1`,
`a(n + λ(m)) ≡ a(n) (mod m)` for all `n ≥ 2m`, where `λ` is the Carmichael
function; since `λ(m) ∣ φ(m)` this refines Bala's conjecture. -/
theorem A179929_eventually_periodic_carmichael (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      A179929 (n + ArithmeticFunction.carmichael m) ≡ A179929 n [ZMOD m] := by
  refine ⟨2 * m, fun n hn => A179929_add_modEq_of_le m _ hm ?_ n hn⟩
  intro q x hq hx
  obtain ⟨c, hc⟩ := ArithmeticFunction.carmichael_dvd hq
  have h1 : ((x : ℕ) : ZMod q) ^ ArithmeticFunction.carmichael q = 1 := by
    have h := ArithmeticFunction.pow_carmichael (ZMod.unitOfCoprime x hx)
    have h' := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h'
    exact h'
  rw [← ZMod.natCast_eq_natCast_iff, hc, pow_mul]
  push_cast
  rw [h1, one_pow]

end Candidates.A179929EulerianMod
