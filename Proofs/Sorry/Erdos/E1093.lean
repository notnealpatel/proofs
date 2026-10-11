/-
  Erdős Problem #1093 — deficiency of binomial coefficients.
  Status: open.  Tier UB archive target with decidable certificates.

  Verbatim statement (`goof erdos fetch 1093`, pulled 2026-08-05):

    "For $n\geq 2k$ we define the deficiency of $\binom{n}{k}$ as
    follows. If $\binom{n}{k}$ is divisible by a prime $p\leq k$ then
    the deficiency is undefined. Otherwise, the deficiency is the
    number of $0\leq i<k$ such that $n-i$ is $k$-smooth, that is,
    divisible only by primes $\leq k$.

    Are there infinitely many binomial coefficients with deficiency
    $1$? Are there only finitely many with deficiency $>1$?"

  DB remarks (Erdős–Lacampagne–Selfridge [ELS88], [ELS93]): if the
  deficiency exists and is ≥ 1 then n ≪ 2^k·√k.  58 deficiency-1
  examples with n ≤ 10⁵, e.g. C(7,3), C(13,4), C(14,4), C(23,5),
  C(62,6), C(94,10), C(95,10).  All known deficiency-2 examples:
  C(44,8), C(74,10), C(174,12), C(239,14), C(5179,27), C(8413,28),
  C(8414,28), C(96622,42); deficiency 3: C(46,10), C(47,10),
  C(241,16), C(2105,25), C(1119,27), C(6459,33); deficiency 4:
  C(47,11); deficiency 9: C(284,28).  (List corrected Dec 2025 per
  Kevin Barreto's comment.)  Barreto also gives a conditional positive
  answer to question 2 under two strong conjectures (xyz-type) —
  comment-sourced.

  Mathlib inventory (leandoc 2026-08-05): `Nat.smoothNumbers n` uses
  primes < n (STRICT) — so "k-smooth = primes ≤ k" is
  `Nat.smoothNumbers (k+1)`; we define an explicit `≤ k` predicate to
  keep the statement readable and prove the bridge as sanity.
  `Nat.primeFactors`, `Nat.choose` otherwise.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1093

/-- `KSmooth k m`: every prime factor of `m` is `≤ k` (the problem's
    "k-smooth").  Note Mathlib's `Nat.smoothNumbers k` uses `< k`, so
    the bridge is `KSmooth k m ↔ m ∈ Nat.smoothNumbers (k+1)` for
    `m ≠ 0`. -/
def KSmooth (k m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p ≤ k

instance (k m : ℕ) : Decidable (KSmooth k m) := by
  unfold KSmooth; infer_instance

/-- Bridge to the Mathlib smooth-numbers API.  -- PROVABLE
    (`Nat.mem_smoothNumbers` + `Nat.lt_succ_iff`). -/
theorem kSmooth_iff_mem_smoothNumbers (k m : ℕ) (hm : m ≠ 0) :
    KSmooth k m ↔ m ∈ Nat.smoothNumbers (k + 1) := by
  sorry

/-- `DeficiencyDefined n k`: no prime `≤ k` divides `C(n,k)` — the
    condition under which the deficiency is defined. -/
def DeficiencyDefined (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ k → ¬ p ∣ n.choose k

/-- `deficiency n k`: the number of `0 ≤ i < k` with `n − i` being
    `k`-smooth.  (Total function; only meaningful under
    `DeficiencyDefined n k` and `2k ≤ n` — all theorems guard.) -/
def deficiency (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => KSmooth k (n - i))).card

/-- Ground truth at C(7,3) = 35: defined (2, 3 ∤ 35), and among
    7, 6, 5 only 6 is 3-smooth — deficiency 1.  -- PROVABLE (decide). -/
example : DeficiencyDefined 7 3 ∧ deficiency 7 3 = 1 := by
  sorry

/-- Ground truth at C(44,8): defined, deficiency 2 (the smallest
    deficiency-2 example).  -- PROVABLE (decide; C(44,8) =
    177232627? — kernel-computable). -/
example : DeficiencyDefined 44 8 ∧ deficiency 44 8 = 2 := by
  sorry

/-- Non-degeneracy: C(10,3) = 120 is divisible by 2 ≤ 3, so its
    deficiency is undefined.  -- PROVABLE (decide). -/
example : ¬ DeficiencyDefined 10 3 := by
  sorry

/-- **Erdős #1093, question 1 (OPEN)**: infinitely many binomial
    coefficients have (defined) deficiency exactly 1.  Encoded on the
    pair set with the `2k ≤ n` and definedness guards. -/
theorem erdos_1093_q1 :
    {q : ℕ × ℕ | 2 * q.2 ≤ q.1 ∧ 2 ≤ q.2 ∧ DeficiencyDefined q.1 q.2 ∧
      deficiency q.1 q.2 = 1}.Infinite := by
  sorry

/-- **Erdős #1093, question 2 (OPEN)**: only finitely many have
    deficiency > 1 (stated as `2 ≤ deficiency`).  All known examples
    are listed in the header; Barreto's conditional resolution rests
    on unproved xyz-type conjectures. -/
theorem erdos_1093_q2 :
    {q : ℕ × ℕ | 2 * q.2 ≤ q.1 ∧ 2 ≤ q.2 ∧ DeficiencyDefined q.1 q.2 ∧
      2 ≤ deficiency q.1 q.2}.Finite := by
  sorry

/-- **ELS93 bound**, the plausible lemma target: if the deficiency is
    defined and ≥ 1 (with `2k ≤ n`, `k ≥ 2`), then `n ≪ 2^k·√k` —
    stated with an explicit constant existential and `√k ≤ k` relaxed
    to the clean form `n ≤ C · 2^k · k` for a first landing (the √k
    refinement can follow). -/
theorem els93_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n k : ℕ, 2 * k ≤ n → 2 ≤ k →
      DeficiencyDefined n k → 1 ≤ deficiency n k →
      n ≤ C * 2 ^ k * k := by
  sorry

/-- Sanity: the guard `2k ≤ n` is load-bearing — without it question 2
    trivializes: `C(p, p−1) = p` has every `p − 1 − i` (i < p−1)
    among `1, …, p−1`, all `(p−1)`-smooth, so deficiency `p − 2 → ∞`
    (Barreto's comment).  Recorded as the explicit small instance
    deficiency C(5,4) = 3 with definedness.  -- PROVABLE (decide). -/
example : DeficiencyDefined 5 4 ∧ deficiency 5 4 = 3 ∧ ¬ (2 * 4 ≤ 5) := by
  sorry

end ErdosCandidates.E1093

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - C(7,3)=35: 2 nmid 35, 3 nmid 35 (defined); among 7,6,5 only 6 is
     3-smooth. Deficiency 1. Correct.
   - C(44,8)=177232627: no prime <= 8 divides it (verified 2,3,5,7).
     8-smooth among 44..37: 42 (=2*3*7) and 40 (=2^3*5). Deficiency 2.
     Correct.
   - C(5,4)=5: defined (2 nmid 5, 3 nmid 5); among 5,4,3,2: 4,3,2 are
     4-smooth (3 of them). Deficiency 3, and 2*4=8 > 5. Correct.
   - Deficiency-2/3/4/9 lists match DB (post Barreto Dec 2025 correction).
   - Barreto conditional resolution (xyz-type conjectures): comment-sourced,
     matches DB comment post-2215.
   - KSmooth vs Nat.smoothNumbers bridge: correctly notes strict < in
     Mathlib vs <= in the problem; k+1 offset is right.
   - ELS93 bound n << 2^k * sqrt(k): matches DB sections.
-/
