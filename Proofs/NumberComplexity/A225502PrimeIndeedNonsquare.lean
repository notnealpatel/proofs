/-
# A225502 — every prime times some triangular number is triangular

## OEIS source (retrieved with `oeis show A225502`, 2026-10-21)

```
NAME:     Least m > 0 such that prime(n)*triangular(m) is a triangular number,
          or 0 if no such m exists.
TERMS:    2,1,2,2,3,3,12,4,9,5,5,30,6,6,20,14,230,23,24,8,8,35,36,9,29,90,30,
          434,10,159,22,11,140,530,854,147,12,25,77,39,1938509,13,41,69,182,70,
          14,104,105,60,30,15,15,47,240,65274,6314,16,17009,33,50,68,17,264,371
COMMENT:  Conjecture: a(n) > 0.
```

The entry's comment carries no author or date in the local store.  The
target formulation (triage): "For every prime p (indeed every nonsquare d>0)
there is m>=1 and k with p*m(m+1)/2 = k(k+1)/2; i.e. a(n)>0 for all n."

## Status

Triage: proved elsewhere.  Chahal–Griffin–Priddis (arXiv:1806.07981,
Hardy–Ramanujan J.), Thm 1: for nonsquare `m > 1` there are infinitely many
triangular pairs with `T' = m T`; see also Pletser, arXiv:2102.13494, and
R. Israel's Pell reformulation in A225503.

## Proof used here

Let `(u, v)` be a Pell solution `u² - d v² = 1` with `u > 1`, `v > 0`
(`Pell.Solution₁.exists_pos_of_not_isSquare`).  Then
`m = u² + u v - 1` and `k = u² + d u v - 1` satisfy
`k (k + 1) - d m (m + 1) = u² (1 - d) (u² - d v² - 1) = 0`, and `m ≥ 1`
since `u ≥ 2`.  (This is the triage's squared-Pell construction
`X = u' + d v'`, `Y = u' + v'` with `(u', v') = (u, v)²`, written out:
`X = 2k + 1`, `Y = 2m + 1`.)
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A225502PrimeIndeedNonsquare

/-! ## Definition layer -/

/-- `t` is a triangular number: `t = k (k + 1) / 2` for some `k : ℕ`
(OEIS A000217, which starts at `T(0) = 0`). -/
def IsTriangular (t : ℕ) : Prop := ∃ k : ℕ, k * (k + 1) / 2 = t

/-- A triangular witness never exceeds the triangular number: it suffices to
search `k ≤ t`. -/
theorem isTriangular_iff_exists_le (t : ℕ) :
    IsTriangular t ↔ ∃ k ≤ t, k * (k + 1) / 2 = t := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    rw [← hk]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have h : (j + j) * (j + j + 1) / 2 = j * (j + j + 1) := by
        rw [show (j + j) * (j + j + 1) = 2 * (j * (j + j + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
      rw [h]; nlinarith
    · have h : (2 * j + 1) * (2 * j + 1 + 1) / 2 = (2 * j + 1) * (j + 1) := by
        rw [show (2 * j + 1) * (2 * j + 1 + 1) = 2 * ((2 * j + 1) * (j + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
      rw [h]; nlinarith
  · rintro ⟨k, -, hk⟩
    exact ⟨k, hk⟩

/-- Triangularity is decidable via the bounded search `k ≤ t`. -/
instance decidablePredIsTriangular : DecidablePred IsTriangular := fun t =>
  decidable_of_iff _ (isTriangular_iff_exists_le t).symm

/-- The defining property of A225502 at the number `p`: `m > 0` and
`p * T(m)` is triangular. -/
def Good (p m : ℕ) : Prop := 0 < m ∧ IsTriangular (p * (m * (m + 1) / 2))

/-- `Good p` is decidable for each `m`. -/
instance decidablePredGood (p : ℕ) : DecidablePred (Good p) := fun m =>
  inferInstanceAs (Decidable (0 < m ∧ IsTriangular (p * (m * (m + 1) / 2))))

/-- Least `m > 0` such that `p * T(m)` is triangular, or `0` if none exists. -/
noncomputable def leastM (p : ℕ) : ℕ := by
  classical
  exact if h : ∃ m, Good p m then Nat.find h else 0

/-- OEIS A225502 with its offset `1`: `a n = leastM (prime(n))`, where
`prime(n) = Nat.nth Nat.Prime (n - 1)` is the `n`-th prime for `n ≥ 1`.
(The value at the out-of-range index `n = 0` is junk and never used.) -/
noncomputable def a (n : ℕ) : ℕ := leastM (Nat.nth Nat.Prime (n - 1))

/-- `leastM p = m` as soon as `m` is good and no smaller positive number is. -/
theorem leastM_eq_of_good {p m : ℕ} (hm : Good p m) (hlt : ∀ j < m, ¬ Good p j) :
    leastM p = m := by
  classical
  have h : ∃ m, Good p m := ⟨m, hm⟩
  unfold leastM
  rw [dif_pos h, Nat.find_eq_iff]
  exact ⟨hm, hlt⟩

/-! ## Ground truth against the DATA line -/

example : a 1 = 2 := by
  rw [a, show 1 - 1 = 0 from rfl, Nat.nth_prime_zero_eq_two]
  exact leastM_eq_of_good (by decide) (by decide)

example : a 2 = 1 := by
  rw [a, show 2 - 1 = 1 from rfl, Nat.nth_prime_one_eq_three]
  exact leastM_eq_of_good (by decide) (by decide)

example : a 3 = 2 := by
  rw [a, show 3 - 1 = 2 from rfl, Nat.nth_prime_two_eq_five]
  exact leastM_eq_of_good (by decide) (by decide)

example : a 5 = 3 := by
  rw [a, show 5 - 1 = 4 from rfl, Nat.nth_prime_four_eq_eleven]
  exact leastM_eq_of_good (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- `prime(7) = 17` and `a(7) = 12`: `17 * T(12) = 1326 = T(51)`. -/
example : leastM 17 = 12 :=
  leastM_eq_of_good (by decide) (by decide)

/-! ## The construction -/

/-- **Pell-to-triangular identity.**  If `u² = d v² + 1` then with
`m = u² + u v - 1`, `k = u² + d u v - 1` one has `k (k + 1) = d m (m + 1)`.
Stated with `u = w + 1` to avoid natural subtraction. -/
theorem pell_identity (d w v : ℕ) (h : (w + 1) ^ 2 = d * v ^ 2 + 1) :
    let m := (w + 1) ^ 2 + (w + 1) * v - 1
    let k := (w + 1) ^ 2 + d * (w + 1) * v - 1
    k * (k + 1) = d * (m * (m + 1)) := by
  intro m k
  have hm : m = w ^ 2 + 2 * w + (w + 1) * v := by
    simp only [m]; ring_nf; omega
  have hk : k = w ^ 2 + 2 * w + d * (w + 1) * v := by
    simp only [k]; ring_nf; omega
  rw [hm, hk]
  have hz : ((w : ℤ) + 1) ^ 2 - d * v ^ 2 - 1 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast at this
    linarith
  zify
  linear_combination ((1 : ℤ) - d) * ((w : ℤ) + 1) ^ 2 * hz

/-- **Main theorem (general form).** For every nonsquare `d > 0` there are
`m ≥ 1` and `k` with `d * T(m) = T(k)`, where `T(n) = n (n + 1) / 2`. -/
theorem exists_pos_mul_tri_eq_tri (d : ℕ) (h0 : 0 < d) (hd : ¬ IsSquare d) :
    ∃ m k : ℕ, 0 < m ∧ d * (m * (m + 1) / 2) = k * (k + 1) / 2 := by
  have hd' : ¬ IsSquare (d : ℤ) := by rwa [Int.isSquare_natCast_iff]
  obtain ⟨s, hx, hy⟩ :=
    Pell.Solution₁.exists_pos_of_not_isSquare (by exact_mod_cast h0) hd'
  -- Lift the Pell solution `(s.x, s.y)` to naturals `(w + 1, v)`.
  set w : ℕ := (s.x - 1).toNat with hw
  set v : ℕ := s.y.toNat with hv
  have hwx : ((w : ℤ) + 1) = s.x := by
    rw [hw, Int.toNat_of_nonneg (by omega)]; ring
  have hvy : (v : ℤ) = s.y := by rw [hv, Int.toNat_of_nonneg hy.le]
  have hw1 : 1 ≤ w := by omega
  have hpell : (w + 1) ^ 2 = d * v ^ 2 + 1 := by
    have hprop := s.prop
    rw [← hwx, ← hvy] at hprop
    zify
    linarith
  refine ⟨(w + 1) ^ 2 + (w + 1) * v - 1, (w + 1) ^ 2 + d * (w + 1) * v - 1, ?_, ?_⟩
  · have hsq : 4 ≤ (w + 1) ^ 2 := by nlinarith
    omega
  · have hid := pell_identity d w v hpell
    simp only at hid
    rw [hid, Nat.mul_div_assoc d (Nat.even_mul_succ_self _).two_dvd]

-- Satisfiability of the hypotheses of `exists_pos_mul_tri_eq_tri` at `d = 2`,
-- and the concrete instance `2 * T(2) = T(3)` it covers.
example : 0 < 2 ∧ ¬ IsSquare (2 : ℕ) := ⟨by norm_num, Nat.prime_two.prime.not_isSquare⟩
example : 2 * (2 * (2 + 1) / 2) = 3 * (3 + 1) / 2 := by norm_num

/-- **A225502 conjecture (OEIS comment "Conjecture: a(n) > 0").** For every
prime `p` there are `m ≥ 1` and `k` with `p * T(m) = T(k)`, i.e. `p * T(m)` is
triangular. -/
theorem prime_exists_pos_mul_tri_eq_tri (p : ℕ) (hp : p.Prime) :
    ∃ m k : ℕ, 0 < m ∧ p * (m * (m + 1) / 2) = k * (k + 1) / 2 :=
  exists_pos_mul_tri_eq_tri p hp.pos hp.prime.not_isSquare

/-- For every prime `p`, `leastM p` is positive: some `m > 0` is good. -/
theorem leastM_pos_of_prime (p : ℕ) (hp : p.Prime) : 0 < leastM p := by
  classical
  obtain ⟨m, k, hm, hmk⟩ := prime_exists_pos_mul_tri_eq_tri p hp
  have h : ∃ m, Good p m := ⟨m, hm, k, hmk.symm⟩
  unfold leastM
  rw [dif_pos h]
  exact (Nat.find_spec h).1

/-- **A225502 conjecture, sequence form ("Conjecture: a(n) > 0"):**
`0 < a n` for every index `n ≥ 1` (the entry's offset). -/
theorem a_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < a n :=
  leastM_pos_of_prime _ (Nat.prime_nth_prime (n - 1))

end Candidates.A225502PrimeIndeedNonsquare
