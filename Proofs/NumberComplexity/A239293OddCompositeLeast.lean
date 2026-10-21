/-
# A239293 — Ordowski: `a(n) = n+1` iff `n+1` is an odd composite

## OEIS source (retrieved with `oeis show A239293`, 2026-10-21)

```
NAME:     Smallest composite c > n such that n^c == n (mod c).
TERMS:    4,341,6,6,10,10,14,9,12,15,15,22,21,15,21,20,34,25,38,21,28,33,33,
          25,28,27,39,36,35,49,49,33,44,35,45,42,45,39,57,52,82,66,77,45,55,...
COMMENT:  If n is even and n+1 is composite, then a(n) = n+1.
          [Corrected by _Thomas Ordowski_, Aug 03 2018]
COMMENT (the conjecture):
  Conjecture: a(n) = n+1 if and only if n+1 is an odd composite number.
  - _Thomas Ordowski_, Aug 03 2018
```

## Status

Listed as an open conjecture in the entry (triage: no proof in the entry or the
literature found).  The argument is elementary: `n ≡ -1 (mod n+1)`, so the
congruence at `c = n+1` reads `(-1)^(n+1) ≡ -1 (mod n+1)`.  For odd `n+1` it
always holds; for even `n+1` it forces `n+1 ∣ 2`, so `n+1 ≤ 2`, not composite.
Checked numerically for `n ≤ 8000` before formalization.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A239293OddCompositeLeast

/-- A natural number is composite when it is greater than `1` and not prime. -/
def IsComposite (c : ℕ) : Prop := 1 < c ∧ ¬ c.Prime

instance : DecidablePred IsComposite := fun c => by
  unfold IsComposite; infer_instance

/-- The set of composite `c > n` with `n^c ≡ n (mod c)` (weak pseudoprimes to
base `n` exceeding `n`). -/
def candidates (n : ℕ) : Set ℕ := {c | n < c ∧ IsComposite c ∧ n ^ c ≡ n [MOD c]}

/-- OEIS A239293: `a(n)` is the smallest composite `c > n` with
`n^c ≡ n (mod c)`.  (Defined as `sInf`; it is `0` only if no such `c` exists.) -/
noncomputable def a (n : ℕ) : ℕ := sInf (candidates n)

/-- `a n = c` as soon as `c` is a candidate and no smaller number is. -/
theorem a_eq_of_mem_of_forall_lt {n c : ℕ} (hc : c ∈ candidates n)
    (hmin : ∀ d < c, d ∉ candidates n) : a n = c := by
  apply le_antisymm (Nat.sInf_le hc)
  by_contra hlt
  push Not at hlt
  have hne : (candidates n).Nonempty := ⟨c, hc⟩
  exact hmin _ hlt (Nat.sInf_mem hne)

/-! ## Ground truth against the listed terms -/

example : a 1 = 4 :=
  a_eq_of_mem_of_forall_lt (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)
    (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)

example : a 3 = 6 :=
  a_eq_of_mem_of_forall_lt (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)
    (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)

example : a 8 = 9 :=
  a_eq_of_mem_of_forall_lt (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)
    (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide)

example : a 2 = 341 :=
  a_eq_of_mem_of_forall_lt
    (by
      simp only [candidates, IsComposite, Set.mem_ofPred_eq]
      exact ⟨by norm_num, ⟨by norm_num, by norm_num⟩, by decide +kernel⟩)
    (by simp only [candidates, IsComposite, Set.mem_ofPred_eq]; decide +kernel)

/-! ## The argument -/

/-- In `ZMod (n+1)`, the residue of `n` is `-1`. -/
theorem natCast_eq_neg_one (n : ℕ) : ((n : ℕ) : ZMod (n + 1)) = -1 := by
  have h0 : ((n + 1 : ℕ) : ZMod (n + 1)) = 0 := ZMod.natCast_self (n + 1)
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- The congruence `n^(n+1) ≡ n (mod n+1)` is equivalent to
`(-1)^(n+1) = -1` in `ZMod (n+1)`. -/
theorem modEq_iff_neg_one_pow (n : ℕ) :
    n ^ (n + 1) ≡ n [MOD n + 1] ↔ ((-1 : ZMod (n + 1)) ^ (n + 1) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [natCast_eq_neg_one]

/-- If `n+1` is odd, then `n^(n+1) ≡ n (mod n+1)`. -/
theorem modEq_of_odd {n : ℕ} (hodd : Odd (n + 1)) : n ^ (n + 1) ≡ n [MOD n + 1] :=
  (modEq_iff_neg_one_pow n).2 hodd.neg_one_pow

/-- If `n+1` is even and `n^(n+1) ≡ n (mod n+1)`, then `n+1 ∣ 2`. -/
theorem dvd_two_of_even_of_modEq {n : ℕ} (heven : Even (n + 1))
    (hmod : n ^ (n + 1) ≡ n [MOD n + 1]) : n + 1 ∣ 2 := by
  have h1 : (-1 : ZMod (n + 1)) ^ (n + 1) = -1 := (modEq_iff_neg_one_pow n).1 hmod
  rw [heven.neg_one_pow] at h1
  have h2 : ((2 : ℕ) : ZMod (n + 1)) = 0 := by
    push_cast
    calc (2 : ZMod (n + 1)) = 1 - (-1) := by ring
      _ = 0 := by rw [← h1, sub_self]
  exact (ZMod.natCast_eq_zero_iff 2 (n + 1)).1 h2

/-- `n+1` is a candidate for `a(n)` exactly when it is an odd composite. -/
theorem succ_mem_candidates_iff (n : ℕ) :
    n + 1 ∈ candidates n ↔ Odd (n + 1) ∧ IsComposite (n + 1) := by
  constructor
  · rintro ⟨-, hcomp, hmod⟩
    refine ⟨?_, hcomp⟩
    rcases Nat.even_or_odd (n + 1) with heven | hodd
    · exfalso
      have hle : n + 1 ≤ 2 := Nat.le_of_dvd two_pos (dvd_two_of_even_of_modEq heven hmod)
      have htwo : n + 1 = 2 := le_antisymm hle hcomp.1
      exact hcomp.2 (htwo ▸ Nat.prime_two)
    · exact hodd
  · rintro ⟨hodd, hcomp⟩
    exact ⟨Nat.lt_succ_self n, hcomp, modEq_of_odd hodd⟩

/-- For every `n`, `a(n) = n+1` iff `n+1` is an odd composite number
(the guard `1 ≤ n` of the conjecture is not needed). -/
theorem a_eq_succ_iff_all (n : ℕ) : a n = n + 1 ↔ Odd (n + 1) ∧ IsComposite (n + 1) := by
  rw [← succ_mem_candidates_iff]
  constructor
  · intro ha
    have hne : (candidates n).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have h0 : a n = 0 := by rw [a, hempty, Nat.sInf_empty]
      omega
    have hmem : a n ∈ candidates n := Nat.sInf_mem hne
    rwa [ha] at hmem
  · intro hmem
    refine a_eq_of_mem_of_forall_lt hmem ?_
    intro d hd hdmem
    have hnd : n < d := hdmem.1
    omega

/-- **Ordowski's conjecture (A239293, Thomas Ordowski, Aug 03 2018).**

Verbatim: "Conjecture: a(n) = n+1 if and only if n+1 is an odd composite
number."  Here `a(n)` is the smallest composite `c > n` with
`n^c ≡ n (mod c)`, and the entry's offset is `n ≥ 1`. -/
theorem conjecture (n : ℕ) (_hn : 0 < n) :
    a n = n + 1 ↔ Odd (n + 1) ∧ IsComposite (n + 1) :=
  a_eq_succ_iff_all n

/-- Non-vacuity: both sides occur.  At `n = 8` the right side holds (`9` is an
odd composite), at `n = 3` it fails (`4` is even) and indeed `a 3 = 6`. -/
example : a 8 = 9 ∧ a 3 ≠ 4 :=
  ⟨(conjecture 8 (by norm_num)).2 ⟨by decide, by norm_num, by norm_num⟩,
    fun h => by
      have h' := (conjecture 3 (by norm_num)).1 h
      exact absurd h'.1 (by decide)⟩

end Candidates.A239293OddCompositeLeast
