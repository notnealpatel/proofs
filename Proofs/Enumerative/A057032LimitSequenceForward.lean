/-
# A057032 — Kurkov: `a(n) - 1` is prime iff `a(n) = n + 1`

## OEIS source (retrieved with `oeis show A057032`, 2026-10-21)

```
NAME:     Let P(n) of a sequence s(1), s(2), s(3), ... be obtained by leaving
          s(1), ..., s(n-1) fixed and forward-cyclically permuting every n
          consecutive terms thereafter; apply P(2) to 1, 2, 3, ... to get PS(2),
          then apply P(3) to PS(2) to get PS(3), then apply P(4) to PS(3), etc.
          The limit of PS(n) as n -> oo is this sequence.
TERMS:    1,3,4,7,6,10,8,16,15,21,12,22,14,27,28,36,18,33,20,43,35,39,24,53,34,
          45,46,50,30,66,32,78,52,57,55,81,38,63,59,88,42,86,44,96,87,75,48,119,
          64,111,76,101,54,103,79,144,83,93,60,141,62,99,113,173,91,136,68,139
KEYWORDS: nonn,nice,easy
COMMENT (the conjecture):
  Conjecture: a(n) - 1 is prime if and only if a(n) = n + 1.
  - _Mikhail Kurkov_, Mar 10 2022
PROGRAM (Mathematica, Jean-François Alcover, Oct 20 2011, after MATLAB):
  PS[i_, n_] := If[i == 1, n, If[n < i, PS[i-1, n], If[Mod[n, i] == 0,
    PS[i-1, n+i-1], PS[i-1, n-1]]]]; a[n_] := PS[n, n]
PROGRAM (PARI, Rémy Sigrist, Aug 25 2020):
  a(n) = { my (p=0); forstep (d=n, 1, -1, if (p%d==0, p+=d)); p }
```

## Status

Triage: open (no proof in the entry or in the literature found by the triage).
Bogdanov's MathOverflow answer (q/416089) proves the analogous statement for the
reverse-cyclic sibling A057063; this forward version is not treated there.
This module proves the conjecture, together with the corollary
`a(n) = n + 1 ↔ n` prime for `n ≥ 2`, with no `sorry`.

## Proof outline

Tracing position `n` backwards through `P(n), P(n-1), …, P(2)` and writing
`z = position - step` turns the process into Sigrist's PARI loop: start from
`z = 0`, and for `d = n, n-1, …, 1` add `d` whenever `d ∣ z`; then `a(n) = z`.
The step `d = n` gives `z = n`, the step `d = 1` adds the final `1`.
If `n` is prime no `d ∈ [2, n-1]` fires, so `a(n) = n + 1`.
If `n` is composite, `minFac n` fires (or an earlier step already did), so
`a(n) > n + 1`.  If any step fires, the last firing `d` divides the final value
`a(n) - 1` with `2 ≤ d < a(n) - 1`, so `a(n) - 1` is composite.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A057032LimitSequenceForward

/-! ## Definition layer

Positions are 1-indexed, as in the entry; position `0` is carried along but
never read.  `P(k)` keeps positions `1, …, k-1` and splits the rest into the
blocks `[m k, m k + k - 1]` (`m ≥ 1`), each forward-cyclically permuted:
the new value at the block start `m k` is the old value at `m k + k - 1`, and
the new value at any other block position `c` is the old value at `c - 1`. -/

/-- Source position for the forward-cyclic permutation `P(k)` (1-indexed):
the value at position `c` of `P(k)(s)` is `s (src k c)`. Positions `c < k` are
fixed; a block start `c` (`k ∣ c`) receives the block end `c + k - 1`; every
other position `c ≥ k` receives position `c - 1`.  (The subtractions are only
evaluated in the branch `k ≤ c`, and `k ≥ 1` in every use.) -/
def src (k c : ℕ) : ℕ :=
  if k ≤ c then (if k ∣ c then c + k - 1 else c - 1) else c

/-- The entry's operator `P(k)`: leave `s(1), …, s(k-1)` fixed and
forward-cyclically permute every `k` consecutive terms thereafter. -/
def fwdPerm (k : ℕ) (s : ℕ → ℕ) : ℕ → ℕ := fun c => s (src k c)

/-- The entry's sequences `PS(k)`: `PS(0) = PS(1) = (1, 2, 3, …)` (the identity;
`P(1)` is the identity permutation) and `PS(k+1) = P(k+1)(PS(k))`.  Pointwise this
is the Mathematica/MATLAB recursion `PS[i, n] = PS[i-1, src i n]`
(see `PS_succ_apply`). -/
def PS : ℕ → ℕ → ℕ
  | 0 => id
  | k + 1 => fwdPerm (k + 1) (PS k)

/-- A057032: `a(n) = PS(n)(n)`.  By `PS_stable` and `tendsto_PS`, this is the
pointwise limit of `PS(k)` as `k → ∞`, as in the entry's definition. -/
def A057032 (n : ℕ) : ℕ := PS n n

/-- Ground truth for `P(3)` on `1, 2, 3, …`: positions `1, 2` fixed, blocks
`(3,4,5) ↦ (5,3,4)` and `(6,7,8) ↦ (8,6,7)`. -/
example : (List.range 8).map (fun i => fwdPerm 3 id (i + 1)) = [1, 2, 5, 3, 4, 8, 6, 7] := by
  decide

/-- Ground truth: the 68 listed terms of A057032. -/
example : (List.range 68).map (fun n => A057032 (n + 1)) =
    [1,3,4,7,6,10,8,16,15,21,12,22,14,27,28,36,18,33,20,43,35,39,24,53,34,45,46,50,30,66,32,78,
     52,57,55,81,38,63,59,88,42,86,44,96,87,75,48,119,64,111,76,101,54,103,79,144,83,93,60,141,
     62,99,113,173,91,136,68,139] := by
  decide +kernel

/-! ## Limit and reduction to Sigrist's loop -/

/-- `P(1)` is the identity: `src 1 c = c`. -/
theorem src_one (c : ℕ) : src 1 c = c := by
  unfold src
  split_ifs with h h'
  · omega
  · exact absurd (one_dvd c) h'
  · rfl

/-- One step of the backward trace: `PS(k+1)(c) = PS(k)(src (k+1) c)`. -/
theorem PS_succ_apply (k c : ℕ) : PS (k + 1) c = PS k (src (k + 1) c) := rfl

/-- Stabilization: for `k ≥ n`, `PS(k)(n) = a(n)`. -/
theorem PS_stable (n k : ℕ) (hk : n ≤ k) : PS k n = A057032 n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
    rw [PS_succ_apply]
    have hsrc : src (k + 1) n = n := by
      unfold src
      rw [if_neg (by omega)]
    rw [hsrc, ih]

/-- The entry's limit: `PS(k)(n) → a(n)` as `k → ∞`. -/
theorem tendsto_PS (n : ℕ) :
    Filter.Tendsto (fun k => PS k n) Filter.atTop (nhds (A057032 n)) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Filter.eventually_ge_atTop n] with k hk
  exact PS_stable n k hk

/-- One step of Sigrist's PARI loop: add `j` to `z` when `j ∣ z`. -/
def jump (j z : ℕ) : ℕ := if j ∣ z then z + j else z

/-- `descend k z` applies `jump k, jump (k-1), …, jump 2` to `z` (the step
`jump 1`, which always adds `1`, is accounted for separately). -/
def descend : ℕ → ℕ → ℕ
  | 0, z => z
  | 1, z => z
  | k + 2, z => descend (k + 1) (jump (k + 2) z)

/-- Backward-trace invariant: `PS(k+1)(z + (k+1)) = descend (k+1) z + 1`. -/
theorem PS_add_eq_descend (k z : ℕ) : PS (k + 1) (z + (k + 1)) = descend (k + 1) z + 1 := by
  induction k generalizing z with
  | zero =>
    rw [PS_succ_apply, src_one]
    rfl
  | succ k ih =>
    rw [PS_succ_apply]
    show PS (k + 1) (src (k + 2) (z + (k + 2))) = descend (k + 1) (jump (k + 2) z) + 1
    unfold src jump
    rw [if_pos (by omega)]
    by_cases hd : (k + 2) ∣ z
    · have hd' : (k + 2) ∣ z + (k + 2) := (Nat.dvd_add_self_right).2 hd
      rw [if_pos hd', if_pos hd, ← ih (z + (k + 2)),
        show z + (k + 2) + (k + 2) - 1 = z + (k + 2) + (k + 1) by omega]
    · have hd' : ¬ (k + 2) ∣ z + (k + 2) := fun h => hd ((Nat.dvd_add_self_right).1 h)
      rw [if_neg hd', if_neg hd, ← ih z, show z + (k + 2) - 1 = z + (k + 1) by omega]

/-- `a(1) = 1`. -/
theorem A057032_one : A057032 1 = 1 := rfl

/-- For `n = m + 2`, `a(n) = descend (n-1) n + 1`. -/
theorem A057032_add_two (m : ℕ) : A057032 (m + 2) = descend (m + 1) (m + 2) + 1 := by
  have h := PS_add_eq_descend (m + 1) 0
  simp only [zero_add] at h
  unfold A057032
  rw [h]
  show descend (m + 1) (jump (m + 2) 0) + 1 = _
  unfold jump
  rw [if_pos (dvd_zero _), zero_add]

/-- `descend` never decreases its argument. -/
theorem le_descend (k z : ℕ) : z ≤ descend k z := by
  induction k generalizing z with
  | zero => exact le_rfl
  | succ k ih =>
    rcases k with _ | k
    · exact le_rfl
    · show z ≤ descend (k + 1) (jump (k + 2) z)
      refine le_trans ?_ (ih _)
      unfold jump
      split_ifs <;> omega

/-- If some `j ∈ [2, k]` divides `z`, then `descend k z` exceeds `z`. -/
theorem lt_descend_of_dvd (k z j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) (hd : j ∣ z) :
    z < descend k z := by
  induction k generalizing z with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · omega
    · show z < descend (k + 1) (jump (k + 2) z)
      unfold jump
      by_cases hk : (k + 2) ∣ z
      · rw [if_pos hk]
        exact lt_of_lt_of_le (by omega) (le_descend _ _)
      · rw [if_neg hk]
        have hjk' : j ≠ k + 2 := by
          rintro rfl
          exact hk hd
        exact ih z (by omega) hd

/-- Load-bearing step: for `z ≥ 1`, either no jump fires, or the result is
not prime (the last firing `j` is a divisor with `2 ≤ j < result`). -/
theorem descend_eq_or_not_prime (k z : ℕ) (hz : 1 ≤ z) :
    descend k z = z ∨ ¬ (descend k z).Prime := by
  induction k generalizing z with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rcases k with _ | k
    · exact Or.inl rfl
    · show descend (k + 1) (jump (k + 2) z) = z ∨ ¬ (descend (k + 1) (jump (k + 2) z)).Prime
      unfold jump
      by_cases hk : (k + 2) ∣ z
      · rw [if_pos hk]
        rcases ih (z + (k + 2)) (by omega) with h | h
        · right
          rw [h]
          intro hp
          have hdvd : (k + 2) ∣ z + (k + 2) := (Nat.dvd_add_self_right).2 hk
          rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1 <;> omega
        · exact Or.inr h
      · rw [if_neg hk]
        exact ih z hz

/-- For prime `n` and `k < n`, no jump fires on `n`. -/
theorem descend_eq_of_prime (n : ℕ) (hn : n.Prime) (k : ℕ) (hk : k < n) : descend k n = n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases k with _ | k
    · rfl
    · show descend (k + 1) (jump (k + 2) n) = n
      unfold jump
      have hnd : ¬ (k + 2) ∣ n := by
        intro hd
        rcases hn.eq_one_or_self_of_dvd _ hd with h1 | h1 <;> omega
      rw [if_neg hnd]
      exact ih (by omega)

/-- Guard for the truncated subtraction in the conjecture: `1 ≤ a(n)` for `n ≥ 1`. -/
theorem one_le_A057032 (n : ℕ) (hn : 1 ≤ n) : 1 ≤ A057032 n := by
  rcases n with _ | _ | m
  · omega
  · rw [A057032_one]
  · rw [A057032_add_two]
    omega

/-- For prime `n`, `a(n) = n + 1`. -/
theorem A057032_eq_succ_of_prime (n : ℕ) (hn : n.Prime) : A057032 n = n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hn.two_le; omega⟩
  rw [A057032_add_two, descend_eq_of_prime (m + 2) hn (m + 1) (by omega)]

/-- For composite `n ≥ 2` (i.e. `n` not prime), `n + 1 < a(n)`. -/
theorem succ_lt_A057032_of_not_prime (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ n.Prime) : n + 1 < A057032 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [A057032_add_two]
  have hmin : (m + 2).minFac < m + 2 := (Nat.not_prime_iff_minFac_lt (by omega)).1 hnp
  have hmin2 : 2 ≤ (m + 2).minFac := (Nat.minFac_prime (by omega)).two_le
  have := lt_descend_of_dvd (m + 1) (m + 2) _ hmin2 (by omega) (Nat.minFac_dvd _)
  omega

/-- Corollary: for `n ≥ 2`, `a(n) = n + 1` iff `n` is prime. -/
theorem A057032_eq_succ_iff_prime (n : ℕ) (hn : 2 ≤ n) : A057032 n = n + 1 ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    have := succ_lt_A057032_of_not_prime n hn hnp
    omega
  · exact A057032_eq_succ_of_prime n

/-! ## The conjecture -/

/-- **Kurkov's conjecture (A057032, Mikhail Kurkov, Mar 10 2022).**

Verbatim: "Conjecture: a(n) - 1 is prime if and only if a(n) = n + 1."

Here `a = A057032` is the limit of the forward-cyclic block process (see
`tendsto_PS`), indexed from `n = 1` as in the entry.  The subtraction `a(n) - 1`
is a genuine subtraction since `1 ≤ a(n)` (`one_le_A057032`). -/
theorem A057032_sub_one_prime_iff (n : ℕ) (hn : 1 ≤ n) : (A057032 n - 1).Prime ↔ A057032 n = n + 1 := by
  rcases n with _ | _ | m
  · omega
  · rw [A057032_one]
    simp [Nat.not_prime_zero]
  · constructor
    · intro hp
      rw [A057032_add_two, Nat.add_sub_cancel] at hp
      rcases descend_eq_or_not_prime (m + 1) (m + 2) (by omega) with h | h
      · rw [A057032_add_two, h]
      · exact absurd hp h
    · intro h
      rw [h, Nat.add_sub_cancel]
      exact (A057032_eq_succ_iff_prime (m + 2) (by omega)).1 h

/-- Non-vacuity: both sides of the conjecture hold at `n = 2` (`a(2) = 3`) and
both fail at `n = 4` (`a(4) = 7`, `6` composite). -/
example : (A057032 2 - 1).Prime ∧ A057032 2 = 2 + 1 ∧
    ¬ (A057032 4 - 1).Prime ∧ A057032 4 ≠ 4 + 1 :=
  ⟨by decide, by decide, by decide, by decide⟩

end Candidates.A057032LimitSequenceForward
