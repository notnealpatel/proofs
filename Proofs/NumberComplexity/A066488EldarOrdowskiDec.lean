/-
# A066488 — Eldar–Ordowski: a Fermat-type criterion modulo `M(k)^2 + M(k) + 1`

## OEIS source (retrieved 2026-10-21 with `oeis show A066488`)

```
NAME:     Composite numbers k which divide A001045(k-1).
TERMS:    341,1105,1387,1729,2047,2465,2701,2821,3277,4033,4369,4681,5461,
          6601,7957,8321,8911,10261,10585,11305,13741,13747,13981,14491,...
COMMENT:  Also composite numbers k such that (2^k - 2)/3 + 1 == 2^k - 1 == 1
          (mod k).
COMMENT:  An equivalent definition of this sequence: pseudoprimes to base 2
          that are not divisible by 3. - Arkadiusz Wesolowski, Nov 15 2011
COMMENT (the conjecture):
  Conjecture: these are composites k such that 2^M(k-1) == -1
  (mod M(k)^2 + M(k) + 1), where M(k) = 2^k - 1.
  - Amiram Eldar and Thomas Ordowski, Dec 19 2019
COMMENT:  These are composites k such that 2^(m-1) == 1 (mod (m+1)^6 - 1),
          where m = 2^k - 1. - Thomas Ordowski, Sep 17 2023
```

`A001045` is the Jacobsthal sequence `0, 1, 1, 3, 5, 11, 21, 43, 85, …`,
`a(n) = a(n-1) + 2 a(n-2)`, `a(n) = (2^n - (-1)^n)/3`.

The exponent `2^M(k-1)` is read as `2^(M(k-1)) = 2^(2^(k-1) - 1)`; the
other reading `2^(M(k) - 1)` never satisfies the congruence for `k > 1`.

## Status

Triage: open (no proof in the entry; Ordowski's 2023 comment is a
different reformulation; no other source found by a grep of the local
OEIS data, which is not a novelty claim).

Computation (Python, 2026-10-21): the equivalence
`k ∣ A001045(k-1) ↔ 2^(2^(k-1)-1) ≡ -1 (mod 4^k - 2^k + 1)` holds for
every `2 ≤ k ≤ 1200`, primes included, with no mismatch.

## Proof (formalized below)

Put `B = M(k) = 2^k - 1` and `N = B^2 + B + 1`.  Modulo `N`,
`(2^k)^2 = (B + 1)^2 = B`, so `2^(3k) = B (B + 1) = -1` and `2^(6k) = 1`.
For `k ≥ 2` no `2^s` with `s < 3k` is `≡ -1`, and none with `0 < s < 3k`
is `≡ 1`: for `s < 2k` the values `2^s ± 1` lie strictly between `0`
and `N`; for `s = 2k + t`, `t < k`, we have `2^s ≡ B 2^t`, and
`B 2^t ± 1` lies strictly between `0` and `N`.  Hence
`2^e ≡ -1 (mod N) ↔ e mod 6k = 3k`.  Finally, with `e = 2^(k-1) - 1`:
for even `k` both sides fail by parity (`e` and `J(k-1)` are odd); for
odd `k`, `e = 3 J(k-1)` is odd, so `e mod 6k = 3k ↔ k ∣ J(k-1)`.
The equivalence therefore holds for all `k ≥ 2`, and the conjecture is
its restriction to composite `k`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A066488EldarOrdowskiDec

/-! ## Definition layer -/

/-- The Mersenne number `M(j) = 2^j - 1` of the entry.  The natural
subtraction is never truncated because `1 ≤ 2^j`. -/
def M (j : ℕ) : ℕ := 2 ^ j - 1

/-- The Jacobsthal sequence `A001045`: `J(0) = 0`, `J(1) = 1`,
`J(n + 2) = J(n + 1) + 2 J(n)`. -/
def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

/-- Membership in `A066488`: `k` is composite (`1 < k`, not prime) and
`k` divides `A001045(k - 1)`. -/
def IsA066488 (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime ∧ k ∣ jacobsthal (k - 1)

/-- The Eldar–Ordowski congruence `2^M(k-1) ≡ -1 (mod M(k)^2 + M(k) + 1)`,
stated in `ZMod (M(k)^2 + M(k) + 1)`. -/
def EldarOrdowskiCongr (k : ℕ) : Prop :=
  (2 : ZMod (M k ^ 2 + M k + 1)) ^ M (k - 1) = -1

/-! ## Ground truth -/

-- `A001045`: 0, 1, 1, 3, 5, 11, 21, 43, 85, 171, 341.
example : (List.range 11).map jacobsthal = [0, 1, 1, 3, 5, 11, 21, 43, 85, 171, 341] := by
  decide

-- `M`: 0, 1, 3, 7, 15.
example : (List.range 5).map M = [0, 1, 3, 7, 15] := by decide

-- The modulus is `4^k - 2^k + 1`: for `k = 3` it is `49 + 7 + 1 = 57 = 64 - 8 + 1`.
example : M 3 ^ 2 + M 3 + 1 = 57 := by decide

/-! ## Jacobsthal closed form -/

/-- The Binet-type closed form `3 J(n) = 2^n - (-1)^n`. -/
theorem three_mul_jacobsthal : ∀ n : ℕ, (3 * jacobsthal n : ℤ) = 2 ^ n - (-1) ^ n
  | 0 => by simp [jacobsthal]
  | 1 => by norm_num [jacobsthal]
  | n + 2 => by
    have h1 := three_mul_jacobsthal (n + 1)
    have h0 := three_mul_jacobsthal n
    simp only [jacobsthal]
    push_cast
    linear_combination h1 + 2 * h0

/-- At an odd index, `3 J(2m + 1) = 2^(2m + 1) + 1`. -/
theorem three_mul_jacobsthal_odd (m : ℕ) :
    3 * jacobsthal (2 * m + 1) = 2 ^ (2 * m + 1) + 1 := by
  have h := three_mul_jacobsthal (2 * m + 1)
  rw [Odd.neg_one_pow ⟨m, rfl⟩] at h
  exact_mod_cast (by linear_combination h : (3 * jacobsthal (2 * m + 1) : ℤ) = 2 ^ (2 * m + 1) + 1)

/-- At an even index, `3 J(2m) + 1 = 2^(2m)`. -/
theorem three_mul_jacobsthal_even (m : ℕ) :
    3 * jacobsthal (2 * m) + 1 = 2 ^ (2 * m) := by
  have h := three_mul_jacobsthal (2 * m)
  rw [Even.neg_one_pow ⟨m, two_mul m⟩] at h
  exact_mod_cast (by linear_combination h : (3 * jacobsthal (2 * m) + 1 : ℤ) = 2 ^ (2 * m))

/-! ## The multiplicative order of `2` modulo `M(k)^2 + M(k) + 1` -/

/-- Two natural numbers below `N` that agree in `ZMod N` are equal. -/
theorem eq_of_natCast_eq_of_lt {N x y : ℕ} (hx : x < N) (hy : y < N)
    (h : (x : ZMod N) = (y : ZMod N)) : x = y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h

/-- `M(k) + 1 = 2^k`. -/
theorem M_add_one (k : ℕ) : M k + 1 = 2 ^ k :=
  Nat.sub_add_cancel Nat.one_le_two_pow

/-- `3 ≤ M(k)` for `k ≥ 2`. -/
theorem three_le_M {k : ℕ} (hk : 2 ≤ k) : 3 ≤ M k := by
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h := M_add_one k
  omega

/-- Modulo `N = M(k)^2 + M(k) + 1`, `2^(2k) ≡ M(k)`. -/
theorem two_pow_two_mul (k : ℕ) :
    (2 : ZMod (M k ^ 2 + M k + 1)) ^ (2 * k) = (M k : ZMod (M k ^ 2 + M k + 1)) := by
  have h0 : ((M k ^ 2 + M k + 1 : ℕ) : ZMod (M k ^ 2 + M k + 1)) = 0 := ZMod.natCast_self _
  have h2k : (2 : ZMod (M k ^ 2 + M k + 1)) ^ k = (M k : ZMod (M k ^ 2 + M k + 1)) + 1 := by
    have hc := congrArg (Nat.cast : ℕ → ZMod (M k ^ 2 + M k + 1)) (M_add_one k)
    push_cast at hc
    exact hc.symm
  push_cast at h0
  rw [pow_mul', h2k]
  linear_combination h0

/-- Modulo `N = M(k)^2 + M(k) + 1`, `2^(3k) ≡ -1`. -/
theorem two_pow_three_mul (k : ℕ) :
    (2 : ZMod (M k ^ 2 + M k + 1)) ^ (3 * k) = -1 := by
  have h0 : ((M k ^ 2 + M k + 1 : ℕ) : ZMod (M k ^ 2 + M k + 1)) = 0 := ZMod.natCast_self _
  have h2k : (2 : ZMod (M k ^ 2 + M k + 1)) ^ k = (M k : ZMod (M k ^ 2 + M k + 1)) + 1 := by
    have hc := congrArg (Nat.cast : ℕ → ZMod (M k ^ 2 + M k + 1)) (M_add_one k)
    push_cast at hc
    exact hc.symm
  push_cast at h0
  rw [pow_mul', h2k]
  linear_combination (↑(M k) + 2 : ZMod (M k ^ 2 + M k + 1)) * h0

/-- Modulo `N = M(k)^2 + M(k) + 1` with `k ≥ 2`, no `2^s` with `s < 3k`
is `≡ -1`. -/
theorem two_pow_ne_neg_one {k s : ℕ} (hk : 2 ≤ k) (hs : s < 3 * k) :
    (2 : ZMod (M k ^ 2 + M k + 1)) ^ s ≠ -1 := by
  intro h
  have hB := three_le_M hk
  have hB1 := M_add_one k
  rcases lt_or_ge s (2 * k) with hs2 | hs2
  · -- `s < 2k`: `0 < 2^s + 1 < N`.
    have hpow : 2 * 2 ^ s ≤ (M k + 1) ^ 2 := by
      rw [hB1, ← pow_succ', ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcast : ((2 ^ s + 1 : ℕ) : ZMod (M k ^ 2 + M k + 1)) = ((0 : ℕ) : ZMod _) := by
      push_cast; rw [h]; ring
    have hlt : 2 ^ s + 1 < M k ^ 2 + M k + 1 := by nlinarith
    have := eq_of_natCast_eq_of_lt hlt (by positivity) hcast
    omega
  · -- `s = 2k + t`: `2^s ≡ M(k) 2^t` and `0 < M(k) 2^t + 1 < N`.
    obtain ⟨t, rfl⟩ : ∃ t, s = 2 * k + t := ⟨s - 2 * k, by omega⟩
    have hpow : 2 * 2 ^ t ≤ M k + 1 := by
      rw [hB1, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add, two_pow_two_mul] at h
    have hcast : ((M k * 2 ^ t + 1 : ℕ) : ZMod (M k ^ 2 + M k + 1)) = ((0 : ℕ) : ZMod _) := by
      push_cast; rw [h]; ring
    have hlt : M k * 2 ^ t + 1 < M k ^ 2 + M k + 1 := by nlinarith
    have := eq_of_natCast_eq_of_lt hlt (by positivity) hcast
    omega

/-- Modulo `N = M(k)^2 + M(k) + 1` with `k ≥ 2`, no `2^s` with
`0 < s < 3k` is `≡ 1`. -/
theorem two_pow_ne_one {k s : ℕ} (hk : 2 ≤ k) (hs0 : 0 < s) (hs : s < 3 * k) :
    (2 : ZMod (M k ^ 2 + M k + 1)) ^ s ≠ 1 := by
  intro h
  have hB := three_le_M hk
  have hB1 := M_add_one k
  have hN : 1 < M k ^ 2 + M k + 1 := by nlinarith
  rcases lt_or_ge s (2 * k) with hs2 | hs2
  · -- `s < 2k`: `1 < 2^s < N`.
    have hpow : 2 * 2 ^ s ≤ (M k + 1) ^ 2 := by
      rw [hB1, ← pow_succ', ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs0
    have hcast : ((2 ^ s : ℕ) : ZMod (M k ^ 2 + M k + 1)) = ((1 : ℕ) : ZMod _) := by
      push_cast; exact h
    have hlt : 2 ^ s < M k ^ 2 + M k + 1 := by nlinarith
    have := eq_of_natCast_eq_of_lt hlt hN hcast
    omega
  · -- `s = 2k + t`: `2^s ≡ M(k) 2^t` and `1 < M(k) 2^t < N`.
    obtain ⟨t, rfl⟩ : ∃ t, s = 2 * k + t := ⟨s - 2 * k, by omega⟩
    have hpow : 2 * 2 ^ t ≤ M k + 1 := by
      rw [hB1, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have ht : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [pow_add, two_pow_two_mul] at h
    have hcast : ((M k * 2 ^ t : ℕ) : ZMod (M k ^ 2 + M k + 1)) = ((1 : ℕ) : ZMod _) := by
      push_cast; exact h
    have hlt : M k * 2 ^ t < M k ^ 2 + M k + 1 := by nlinarith
    have := eq_of_natCast_eq_of_lt hlt hN hcast
    nlinarith

/-- **Order lemma.** For `k ≥ 2` and every exponent `e`,
`2^e ≡ -1 (mod M(k)^2 + M(k) + 1)` iff `e mod 6k = 3k`
(the multiplicative order of `2` is `6k`). -/
theorem two_pow_eq_neg_one_iff {k : ℕ} (hk : 2 ≤ k) (e : ℕ) :
    (2 : ZMod (M k ^ 2 + M k + 1)) ^ e = -1 ↔ e % (6 * k) = 3 * k := by
  have h3k := two_pow_three_mul k
  have h6k : (2 : ZMod (M k ^ 2 + M k + 1)) ^ (6 * k) = 1 := by
    rw [show 6 * k = 3 * k * 2 by ring, pow_mul, h3k]; norm_num
  have hred : (2 : ZMod (M k ^ 2 + M k + 1)) ^ e = 2 ^ (e % (6 * k)) := by
    conv_lhs => rw [← Nat.div_add_mod e (6 * k), pow_add, pow_mul, h6k, one_pow, one_mul]
  have hr : e % (6 * k) < 6 * k := Nat.mod_lt _ (by omega)
  rw [hred]
  constructor
  · intro h
    rcases lt_or_ge (e % (6 * k)) (3 * k) with hlt | hge
    · exact absurd h (two_pow_ne_neg_one hk hlt)
    · obtain ⟨u, hu⟩ : ∃ u, e % (6 * k) = 3 * k + u := ⟨e % (6 * k) - 3 * k, by omega⟩
      rw [hu, pow_add, h3k] at h
      have h1 : (2 : ZMod (M k ^ 2 + M k + 1)) ^ u = 1 := by
        linear_combination -h
      rcases Nat.eq_zero_or_pos u with hu0 | hu0
      · omega
      · exact absurd h1 (two_pow_ne_one hk hu0 (by omega))
  · intro h
    rw [h, h3k]

/-! ## The arithmetic side -/

/-- **Parity lemma.** For `k ≥ 2`, `M(k-1) mod 6k = 3k` iff `k ∣ A001045(k-1)`. -/
theorem M_mod_eq_iff_dvd_jacobsthal {k : ℕ} (hk : 2 ≤ k) :
    M (k - 1) % (6 * k) = 3 * k ↔ k ∣ jacobsthal (k - 1) := by
  have hdm := Nat.div_add_mod (M (k - 1)) (6 * k)
  set q := M (k - 1) / (6 * k) with hq
  rcases Nat.even_or_odd k with hke | hko
  · -- Even `k = 2n + 2`: `M(k-1)` and `J(k-1)` are both odd; both sides fail.
    obtain ⟨n, hn⟩ : ∃ n, k = 2 * n + 2 := by
      obtain ⟨m, hm⟩ := hke
      exact ⟨m - 1, by omega⟩
    have hidx : k - 1 = 2 * n + 1 := by omega
    have hJ := three_mul_jacobsthal_odd n
    have hX : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have hpow : 2 ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := pow_succ' 2 (2 * n)
    have hMv : M (k - 1) = 2 * 2 ^ (2 * n) - 1 := by
      rw [M, hidx, hpow]
    constructor
    · intro h
      have hodd : Odd (M (k - 1)) := ⟨2 ^ (2 * n) - 1, by omega⟩
      have heven : Even (M (k - 1)) := by
        rw [← hdm, h]
        refine Even.add ⟨3 * k * q, by ring⟩ (hke.mul_left 3)
      exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
    · intro hdvd
      obtain ⟨d, hd⟩ := (even_iff_two_dvd.mp hke).trans hdvd
      rw [hidx] at hd
      rw [hd, hpow] at hJ
      omega
  · -- Odd `k = 2n + 1`, `n ≥ 1`: `M(k-1) = 3 J(k-1)` is odd.
    obtain ⟨n, hn⟩ := hko
    have hidx : k - 1 = 2 * n := by omega
    have hJ := three_mul_jacobsthal_even n
    have hpow : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hMv : M (k - 1) = 3 * jacobsthal (k - 1) := by
      rw [M, hidx]; omega
    rw [hMv] at hdm ⊢
    constructor
    · intro h
      rw [h] at hdm
      exact ⟨2 * q + 1, by linarith⟩
    · rintro ⟨j, hj⟩
      have hodd : Odd (3 * jacobsthal (k - 1)) := by
        rw [hidx]; exact ⟨2 ^ (2 * n - 1) - 1, by omega⟩
      have hjodd : Odd j := by
        rw [hj] at hodd
        exact (Nat.odd_mul.mp (Nat.odd_mul.mp hodd).2).2
      obtain ⟨i, hi⟩ := hjodd
      rw [hj, hi, show 3 * (k * (2 * i + 1)) = 3 * k + 6 * k * i by ring,
        Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)

/-! ## The conjecture -/

/-- **Eldar–Ordowski criterion, all `k ≥ 2` (stronger form).** For every
`k ≥ 2`, primes included, `k ∣ A001045(k-1)` iff
`2^M(k-1) ≡ -1 (mod M(k)^2 + M(k) + 1)`. -/
theorem dvd_jacobsthal_iff_congr {k : ℕ} (hk : 2 ≤ k) :
    k ∣ jacobsthal (k - 1) ↔ EldarOrdowskiCongr k := by
  rw [EldarOrdowskiCongr, two_pow_eq_neg_one_iff hk, M_mod_eq_iff_dvd_jacobsthal hk]

/-- **Eldar–Ordowski conjecture (A066488, Amiram Eldar and Thomas Ordowski,
Dec 19 2019).**

Verbatim: "Conjecture: these are composites k such that 2^M(k-1) == -1
(mod M(k)^2 + M(k) + 1), where M(k) = 2^k - 1."  Here "these" are the terms
of A066488, the composite `k` dividing `A001045(k-1)`.  For composite `k`
(`1 < k`, `¬ k.Prime`): `k ∣ A001045(k-1)` iff the congruence holds. -/
theorem eldar_ordowski {k : ℕ} (hk : 1 < k) (_hcomp : ¬ k.Prime) :
    k ∣ jacobsthal (k - 1) ↔ EldarOrdowskiCongr k :=
  dvd_jacobsthal_iff_congr hk

/-- **Eldar–Ordowski conjecture, set form.** `k` is a term of A066488 iff
`k` is composite and `2^M(k-1) ≡ -1 (mod M(k)^2 + M(k) + 1)`. -/
theorem isA066488_iff (k : ℕ) :
    IsA066488 k ↔ 1 < k ∧ ¬ k.Prime ∧ EldarOrdowskiCongr k := by
  constructor
  · rintro ⟨hk, hp, hd⟩
    exact ⟨hk, hp, (dvd_jacobsthal_iff_congr hk).mp hd⟩
  · rintro ⟨hk, hp, hc⟩
    exact ⟨hk, hp, (dvd_jacobsthal_iff_congr hk).mpr hc⟩

/-! ## Non-vacuity -/

-- `341 = 11 * 31`, the first term, satisfies the hypotheses and the
-- divisibility, so both sides of `eldar_ordowski` hold at `k = 341`.
example : IsA066488 341 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  decide +kernel

-- At the composite `k = 4` both sides fail; the congruence is checked directly.
example : ¬ EldarOrdowskiCongr 4 := by
  unfold EldarOrdowskiCongr M
  decide +kernel

-- At the prime `k = 5` both sides hold: `5 ∣ J(4) = 5` and `2^15 ≡ -1 (mod 241)`.
example : EldarOrdowskiCongr 5 := by
  unfold EldarOrdowskiCongr M
  decide +kernel

end Candidates.A066488EldarOrdowskiDec
