/-
# A259145 — if k^2 - phi(k) is prime then k is a cyclic number

## OEIS source (retrieved with `oeis show A259145` and the live entry, 2026-10-21)

```
NAME:     Numbers k such that k^2 - phi(k) is prime, where phi() is A000010.
TERMS:    2,3,7,13,33,35,65,67,77,79,91,133,139,151,163,193,221,247,249,287,...
KEYWORDS: nonn,easy
AUTHOR:   Carlos Eduardo Olivieri, Jun 19 2015
COMMENT (the conjecture; the entry gives no separate attribution, so it is
the author's, Carlos Eduardo Olivieri, Jun 19 2015):
  Conjecture: a(n) is a cyclic number (see A003277) for all n.
```

A003277 (cyclic numbers): numbers `k` with `gcd(k, phi(k)) = 1`.

## Status

Triage: "open" in the sense that neither the entry nor the literature found by
the triage records a proof.  The statement has an elementary one-line proof:
`d = gcd(k, phi(k))` divides `k^2 - phi(k) = q`, a prime, and
`d ≤ k < k^2 - phi(k) = q` for `k ≥ 2`, so `d = 1`.  This module proves it.

Computational check (python, 2026-10-21): every `k ≤ 200000` with
`k^2 - phi(k)` prime (6626 values) satisfies `gcd(k, phi(k)) = 1`.

## Truncated subtraction

`k^2 - phi(k)` is written in `ℕ`.  Since `phi(k) ≤ k ≤ k^2`, the truncation is
never active; `sub_cast_eq` records that the natural-number difference agrees
with the integer difference.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A259145PhiPrimeCyclic

/-- Membership in A259145: `k^2 - phi(k)` is prime.  The natural-number
subtraction never truncates (see `sub_cast_eq`). -/
def IsTerm (k : ℕ) : Prop := (k ^ 2 - Nat.totient k).Prime

instance : DecidablePred IsTerm := fun k => by
  unfold IsTerm
  infer_instance

/-- A cyclic number (A003277): `gcd(k, phi(k)) = 1`. -/
def IsCyclic (k : ℕ) : Prop := Nat.Coprime k (Nat.totient k)

/-- The natural-number difference `k^2 - phi(k)` agrees with the integer
difference, so the definition `IsTerm` carries no truncation artefact. -/
theorem sub_cast_eq (k : ℕ) :
    (((k ^ 2 - Nat.totient k : ℕ)) : ℤ) = (k : ℤ) ^ 2 - (Nat.totient k : ℤ) := by
  have hle : Nat.totient k ≤ k ^ 2 :=
    (Nat.totient_le k).trans (Nat.le_self_pow (by norm_num) k)
  push_cast [hle]
  ring

/-! ## Ground truth -/

/-- The terms of A259145 below `40` are exactly the first six listed
terms `2, 3, 7, 13, 33, 35`. -/
example : (Finset.range 40).filter IsTerm = {2, 3, 7, 13, 33, 35} := by
  decide +kernel

/-! ## The proof -/

/-- `gcd(k, phi(k))` divides `k^2 - phi(k)`. -/
theorem gcd_dvd_sq_sub_totient (k : ℕ) :
    Nat.gcd k (Nat.totient k) ∣ k ^ 2 - Nat.totient k := by
  have hk : Nat.gcd k (Nat.totient k) ∣ k ^ 2 :=
    (Nat.gcd_dvd_left k (Nat.totient k)).trans (Dvd.intro_left _ (sq k).symm)
  exact Nat.dvd_sub hk (Nat.gcd_dvd_right k (Nat.totient k))

/-- For `2 ≤ k`, `k < k^2 - phi(k)`. -/
theorem lt_sq_sub_totient {k : ℕ} (hk : 2 ≤ k) : k < k ^ 2 - Nat.totient k := by
  have hphi : Nat.totient k < k := Nat.totient_lt k (by omega)
  have hsq : 2 * k ≤ k ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right k hk
  omega

/-- **A259145 conjecture (Carlos Eduardo Olivieri, Jun 19 2015).**
Verbatim: "Conjecture: a(n) is a cyclic number (see A003277) for all n."
That is: if `k^2 - phi(k)` is prime, then `gcd(k, phi(k)) = 1`.

Proof: `d = gcd(k, phi(k))` divides the prime `q = k^2 - phi(k)`; since
`q` is prime, `k ≥ 2`, so `d ≤ k < q`, forcing `d = 1`. -/
theorem isCyclic_of_isTerm {k : ℕ} (h : IsTerm k) : IsCyclic k := by
  unfold IsTerm at h
  unfold IsCyclic Nat.Coprime
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k <;> simp_all [Nat.not_prime_zero]
  have hdvd := gcd_dvd_sq_sub_totient k
  rcases (Nat.dvd_prime h).1 hdvd with hone | hq
  · exact hone
  · exfalso
    have hgle : Nat.gcd k (Nat.totient k) ≤ k := Nat.gcd_le_left _ (by omega)
    have hlt := lt_sq_sub_totient hk2
    omega

/-- Non-vacuity: the hypothesis of `isCyclic_of_isTerm` holds at `k = 2`
(`2^2 - phi(2) = 3`). -/
example : IsTerm 2 := by decide

end Candidates.A259145PhiPrimeCyclic
