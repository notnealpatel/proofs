/-
# A053871 — Richman: odd-modulus periodicity of `(-1)^n a(n)`

## OEIS source (retrieved with `oeis show A053871`, 2026-10-21)

```
NAME:     a(n) = 2*(n-1)*(a(n-1) + a(n-2)), starting a(0) = 1; a(1) = 0.
TERMS:    1,0,2,8,60,544,6040,79008,1190672,20314880,387099936,8148296320,...
FORMULA (the conjecture):
  Conjecture: if m == n (mod q) for q odd, then (-1)^m*a(m) == (-1)^n*a(n)
  (mod q). - _Harry Richman_, Aug 29 2023
FORMULA (used in the proof):
  a(n) = (-1)^n*Sum_{k=0..n} (-1)^k*C(n, k)*(2*k-1)!!.
  - _Benoit Cloitre_, May 01 2003; corrected by _David Fioramonti_, May 17 2016
COMMENT:
  Harry Richman's conjecture in the Formula section was proved by Ahaan
  Kallat (2026, Theorem 59); see the paper in the Links section.
  - _Ahaan Kallat_, Oct 14 2026
```

## Status

Proved elsewhere (Kallat 2026, Theorem 59, per the entry).  This module gives
an independent kernel-checked proof.

## Proof outline

Write `b n = (-1)^n a(n)`; then `b (n+2) = 2(n+1)(b n - b (n+1))`.

1. (`b_add_mul_congr`) For every modulus `q`, every `N` with `q ∣ N` and every
   `r`, `b (N + r) ≡ b N * b r [ZMOD q]`: the recurrence reduced mod `q` only
   sees `n mod q`, and `b (N+1) ≡ 0` since its factor `2N` vanishes.
2. Hence `b (j q) ≡ (b q)^j`, so periodicity reduces to `b q ≡ 1 [ZMOD q]`.
3. (`b_eq_sum`) `b n = ∑_k C(n,k) e_k` with `e_k = (-1)^k (2k-1)!!`.
4. (`dvd_choose_mul_doubleFactorial`) for odd `q` and `1 ≤ k`,
   `q ∣ C(q,k) (2k-1)!!`, because `2^k C(q,k) (2k-1)!! = q^{(k)} C(2k,k)`
   with the falling factorial `q^{(k)}` divisible by `q`.  So `b q ≡ e_0 = 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A053871RichmanOddMod

/-- OEIS A053871: `a 0 = 1`, `a 1 = 0`, `a n = 2 (n-1) (a (n-1) + a (n-2))`. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => 2 * (n + 1) * (a (n + 1) + a n)

example : (List.range 11).map a =
    [1, 0, 2, 8, 60, 544, 6040, 79008, 1190672, 20314880, 387099936] := by
  decide

/-- The signed sequence `b n = (-1)^n a(n)`. -/
def b (n : ℕ) : ℤ := (-1) ^ n * (a n : ℤ)

/-- The signed recurrence `b (n+2) = 2 (n+1) (b n - b (n+1))`. -/
theorem b_succ_succ (n : ℕ) :
    b (n + 2) = 2 * ((n : ℤ) + 1) * (b n - b (n + 1)) := by
  simp only [b, a, pow_succ]
  push_cast
  ring

/-- Step 1: for `q ∣ N`, `b (N + r) ≡ b N * b r [ZMOD q]` for every `r`. -/
theorem b_add_mul_congr (q N : ℕ) (hN : (q : ℤ) ∣ N) (r : ℕ) :
    b (N + r) ≡ b N * b r [ZMOD q] := by
  have hN0 : (N : ℤ) ≡ 0 [ZMOD q] := (Int.modEq_zero_iff_dvd).2 hN
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [b, a]
    | 1, _ =>
      have hb1 : b 1 = 0 := by simp [b, a]
      rw [hb1, mul_zero]
      rcases N with _ | M
      · simp [b, a]
      · refine (Int.modEq_zero_iff_dvd).2 ?_
        rw [show M + 1 + 1 = M + 2 by ring, b_succ_succ]
        have hM : (q : ℤ) ∣ (M : ℤ) + 1 := by exact_mod_cast hN
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hM 2) _
    | r + 2, ih =>
      have h0 : b (N + r) ≡ b N * b r [ZMOD q] := ih r (by omega)
      have h1 : b (N + r + 1) ≡ b N * b (r + 1) [ZMOD q] := ih (r + 1) (by omega)
      calc b (N + (r + 2)) = b ((N + r) + 2) := by rw [add_assoc]
        _ = 2 * (((N + r : ℕ) : ℤ) + 1) * (b (N + r) - b (N + r + 1)) := b_succ_succ _
        _ ≡ 2 * (((0 : ℤ) + r) + 1) * (b N * b r - b N * b (r + 1)) [ZMOD q] := by
          push_cast
          exact (((hN0.add_right (r : ℤ)).add_right 1).mul_left 2).mul (h0.sub h1)
        _ = b N * b (r + 2) := by rw [b_succ_succ]; ring

/-- Step 2: for `q ∣ N`, `b (N + q) ≡ b N * b q [ZMOD q]`; iterating,
`b (j * q) ≡ (b q) ^ j [ZMOD q]`. -/
theorem b_mul_congr_pow (q j : ℕ) : b (j * q) ≡ b q ^ j [ZMOD q] := by
  induction j with
  | zero => simp [b, a]
  | succ j ih =>
    have hdvd : (q : ℤ) ∣ ((j * q : ℕ) : ℤ) := by
      exact_mod_cast Nat.dvd_mul_left q j
    calc b ((j + 1) * q) = b (j * q + q) := by rw [add_mul, one_mul]
      _ ≡ b (j * q) * b q [ZMOD q] := b_add_mul_congr q (j * q) hdvd q
      _ ≡ b q ^ j * b q [ZMOD q] := ih.mul_right _
      _ = b q ^ (j + 1) := (pow_succ _ _).symm

/-- The signed odd double factorials `e k = (-1)^k (2k-1)!!` (with `(-1)!! = 1`). -/
def e (k : ℕ) : ℤ := (-1) ^ k * (((2 * k - 1).doubleFactorial : ℕ) : ℤ)

/-- `e (k+1) = -(2k+1) e k`. -/
theorem e_succ (k : ℕ) : e (k + 1) = -(2 * (k : ℤ) + 1) * e k := by
  rcases k with _ | k
  · simp [e]
  · have h : 2 * (k + 1 + 1) - 1 = (2 * k + 1) + 2 := by omega
    have h' : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    simp only [e, h, h', Nat.doubleFactorial_add_two, pow_succ]
    push_cast
    ring

/-- The shifted binomial transform `S n j = ∑_{k ≤ n} C(n,k) e (k + j)`. -/
def S (n j : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * e (k + j)

/-- Pascal rule for a binomial transform:
`∑_{k ≤ n+1} C(n+1,k) f k = ∑_{k ≤ n} C(n,k) f k + ∑_{k ≤ n} C(n,k) f (k+1)`. -/
theorem sum_choose_succ (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * f k
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k
        + ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * f k) n,
    Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * f (k + 1)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right]
  ring

/-- Pascal rule for the shifted transforms: `S (n+1) j = S n j + S n (j+1)`. -/
theorem S_succ (n j : ℕ) : S (n + 1) j = S n j + S n (j + 1) := by
  have h := sum_choose_succ (fun k => e (k + j)) n
  have hs : ∀ k, k + 1 + j = k + (j + 1) := fun k => by ring
  simp only [hs] at h
  exact h

/-- Three-term relation:
`S (n+1) (j+1) + (2j+1) S (n+1) j + 2(n+1) S n (j+1) = 0`. -/
theorem S_rel (n j : ℕ) :
    S (n + 1) (j + 1) + (2 * (j : ℤ) + 1) * S (n + 1) j
      + 2 * ((n : ℤ) + 1) * S n (j + 1) = 0 := by
  induction n generalizing j with
  | zero =>
    have h0 : ∀ i, S 0 i = e i := fun i => by simp [S]
    rw [S_succ, S_succ, h0, h0, h0]
    have e1 := e_succ j
    have e2 := e_succ (j + 1)
    simp only [show j + 1 + 1 = j + 2 by ring] at e2 ⊢
    push_cast at e2 ⊢
    linear_combination e2 + e1
  | succ n ih =>
    have h1 := ih j
    have h2 := ih (j + 1)
    have p1 := S_succ (n + 1) j
    have p2 := S_succ (n + 1) (j + 1)
    have p3 := S_succ n (j + 1)
    have p4 := S_succ n (j + 2)
    simp only [show j + 1 + 1 = j + 2 by ring] at h2 p2 p3
    push_cast at h1 h2 ⊢
    linear_combination p2 + (2 * (j : ℤ) + 1) * p1 + h1 + h2 + 2 * ((n : ℤ) + 1) * p3

/-- Step 3: `b n = S n 0 = ∑_{k ≤ n} C(n,k) (-1)^k (2k-1)!!` (Cloitre's formula). -/
theorem b_eq_S (n : ℕ) : b n = S n 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [b, a, S, e]
    | 1, _ => simp [b, a, S, e, Finset.sum_range_succ]
    | n + 2, ih =>
      rw [b_succ_succ, ih n (by omega), ih (n + 1) (by omega), S_succ (n + 1) 0]
      have r := S_rel n 0
      have p := S_succ n 0
      simp only [zero_add] at p ⊢
      push_cast at r
      linear_combination -r - 2 * ((n : ℤ) + 1) * p

/-- Step 4: for odd `q` and `1 ≤ k`, `q ∣ C(q,k) (2k-1)!!`, via the identity
`2^k C(q,k) (2k-1)!! = q (q-1) ⋯ (q-k+1) C(2k,k)`. -/
theorem dvd_choose_mul_doubleFactorial (q k : ℕ) (hq : Odd q) (hk : 1 ≤ k) :
    q ∣ q.choose k * (2 * k - 1).doubleFactorial := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hf : (2 * (k' + 1)).factorial
      = 2 ^ (k' + 1) * (k' + 1).factorial * (2 * (k' + 1) - 1).doubleFactorial := by
    have h1 : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
    have h2 : 2 * (k' + 1) = 2 * k' + 1 + 1 := by omega
    rw [h1, ← Nat.doubleFactorial_two_mul, h2, Nat.factorial_eq_mul_doubleFactorial]
  have hc := Nat.add_choose_mul_factorial_mul_factorial (k' + 1) (k' + 1)
  have hd := Nat.descFactorial_eq_factorial_mul_choose q (k' + 1)
  have key : 2 ^ (k' + 1) * (q.choose (k' + 1) * (2 * (k' + 1) - 1).doubleFactorial)
      = q.descFactorial (k' + 1) * (k' + 1 + (k' + 1)).choose (k' + 1) := by
    have hpos : 0 < (k' + 1).factorial * (k' + 1).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc 2 ^ (k' + 1) * (q.choose (k' + 1) * (2 * (k' + 1) - 1).doubleFactorial)
          * ((k' + 1).factorial * (k' + 1).factorial)
        = ((k' + 1).factorial * q.choose (k' + 1))
          * (2 ^ (k' + 1) * (k' + 1).factorial * (2 * (k' + 1) - 1).doubleFactorial) := by
          ring
      _ = q.descFactorial (k' + 1) * (2 * (k' + 1)).factorial := by rw [hd, hf]
      _ = q.descFactorial (k' + 1)
          * ((k' + 1 + (k' + 1)).choose (k' + 1) * (k' + 1).factorial * (k' + 1).factorial) := by
          rw [hc, two_mul]
      _ = q.descFactorial (k' + 1) * (k' + 1 + (k' + 1)).choose (k' + 1)
          * ((k' + 1).factorial * (k' + 1).factorial) := by ring
  have hqd : q ∣ q.descFactorial (k' + 1) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.pos; omega⟩
    rw [Nat.succ_descFactorial_succ]
    exact Nat.dvd_mul_right _ _
  have h2k : q ∣ 2 ^ (k' + 1) * (q.choose (k' + 1) * (2 * (k' + 1) - 1).doubleFactorial) := by
    rw [key]
    exact Dvd.dvd.mul_right hqd _
  exact (hq.coprime_two_right.pow_right (k' + 1)).dvd_of_dvd_mul_left h2k

/-- `b q ≡ 1 [ZMOD q]` for odd `q`. -/
theorem b_self_modEq_one (q : ℕ) (hq : Odd q) : b q ≡ 1 [ZMOD q] := by
  have hdiv : (q : ℤ) ∣ ∑ k ∈ Finset.range q, ((q.choose (k + 1) : ℕ) : ℤ) * e (k + 1 + 0) := by
    refine Finset.dvd_sum fun k _ => ?_
    have hn := Int.natCast_dvd_natCast.2
      (dvd_choose_mul_doubleFactorial q (k + 1) hq (by omega))
    push_cast at hn
    have hre : ((q.choose (k + 1) : ℕ) : ℤ) * e (k + 1 + 0)
        = (-1) ^ (k + 1) * (((q.choose (k + 1) : ℕ) : ℤ)
          * (((2 * (k + 1) - 1).doubleFactorial : ℕ) : ℤ)) := by
      simp only [e, add_zero]
      ring
    rw [hre]
    exact Dvd.dvd.mul_left hn _
  rw [b_eq_S, S, Finset.sum_range_succ']
  have h0 : ((q.choose 0 : ℕ) : ℤ) * e (0 + 0) = 1 := by simp [e]
  rw [h0]
  simpa using ((Int.modEq_zero_iff_dvd).2 hdiv).add_right 1

/-- **Richman's conjecture (OEIS A053871, Aug 29 2023; proved by Kallat 2026,
Theorem 59).**  For odd `q` and `m ≡ n (mod q)`,
`(-1)^m a(m) ≡ (-1)^n a(n) (mod q)`. -/
theorem richman_odd_mod (q m n : ℕ) (hq : Odd q) (h : m ≡ n [MOD q]) :
    (-1 : ℤ) ^ m * (a m : ℤ) ≡ (-1) ^ n * (a n : ℤ) [ZMOD q] := by
  have key : ∀ t : ℕ, b t ≡ b (t % q) [ZMOD q] := by
    intro t
    have hdvd : (q : ℤ) ∣ ((t / q * q : ℕ) : ℤ) := by
      exact_mod_cast Nat.dvd_mul_left q (t / q)
    calc b t = b (t / q * q + t % q) := by rw [Nat.div_add_mod']
      _ ≡ b (t / q * q) * b (t % q) [ZMOD q] := b_add_mul_congr q _ hdvd _
      _ ≡ 1 ^ (t / q) * b (t % q) [ZMOD q] :=
        ((b_mul_congr_pow q (t / q)).trans ((b_self_modEq_one q hq).pow _)).mul_right _
      _ = b (t % q) := by rw [one_pow, one_mul]
  have hmod : m % q = n % q := h
  change b m ≡ b n [ZMOD q]
  exact (key m).trans (hmod ▸ (key n).symm)

/-- The hypotheses of `richman_odd_mod` are jointly satisfiable with `m ≠ n`:
`q = 3`, `m = 2`, `n = 5`, and the conclusion reads `2 ≡ -544 (mod 3)`. -/
example : Odd 3 ∧ 2 ≡ 5 [MOD 3] ∧ (-1 : ℤ) ^ 2 * (a 2 : ℤ) ≡ (-1) ^ 5 * (a 5 : ℤ) [ZMOD 3] := by
  decide

end Candidates.A053871RichmanOddMod
