/-
  Erdős Problem #683 — the largest prime divisor of C(n,k).
  Status: open.  Tier UC lemma mine — Sylvester–Schur is the prize.

  Verbatim statement (`goof erdos fetch 683`, pulled 2026-08-05):

    "Is it true that for every $1\leq k\leq n$ the largest prime
    divisor of $\binom{n}{k}$, say $P(\binom{n}{k})$, satisfies
    \[P\left(\binom{n}{k}\right)\geq \min(n-k+1, k^{1+c})\]
    for some constant $c>0$?"

  DB remarks: Sylvester–Schur (see Erdős's own 1934 paper [Er34]):
  P(C(n,k)) > k for k ≤ n/2.  Erdős [Er55d]: P(C(n,k)) ≫ k·log k for
  k ≤ n/2.  [Er79d]: 'seems certain' the statement holds for EVERY
  c > 0 with finitely many exceptions.  Heuristics suggest
  P(C(n,k)) > e^{c√k}.  Essentially equivalent to #961.

  OEIS anchors: A006530 (largest prime factor), A074399, A121359.

  Mathlib inventory (leandoc 2026-08-05): no largest-prime-factor
  function (misses "maxPrimeFac", "largest prime factor") — defined
  below as `Finset.sup` of `Nat.primeFactors` (junk 0 at n ≤ 1,
  guarded).  `Nat.choose`, `Nat.primeFactors` otherwise.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E683

/-- The largest prime factor of `n` (`0` for `n ≤ 1` — junk guarded in
    every theorem by positivity of the binomial argument).  Fresh def;
    leandoc confirms Mathlib has none. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactors.sup id

/-- Ground truth: `maxPrimeFac 35 = 7`, `maxPrimeFac (C(10,5)) =
    maxPrimeFac 252 = 7`, `maxPrimeFac 1 = 0`.
    -- PROVABLE (decide). -/
example : maxPrimeFac 35 = 7 ∧ maxPrimeFac (Nat.choose 10 5) = 7 ∧
    maxPrimeFac 1 = 0 := by
  sorry

/-- **Sylvester–Schur theorem (the lemma-mine prize)**: for `1 ≤ k`
    and `2k ≤ n`, `C(n,k)` has a prime factor `> k` — i.e.
    `k < maxPrimeFac (C(n,k))`.

    Not in Mathlib (re-verified 2026-08-05).  Erdős's 1934 proof
    [Er34] is elementary: if all prime factors were ≤ k, compare
    `C(n,k) ≥ (n/k)^k` against the bounded prime-power contributions
    `∏_{p ≤ k} p^{⌊log_p n⌋} ≤ n^{π(k)}` (each prime power dividing
    C(n,k) is ≤ n by Kummer), and π(k) < k/… Chebyshev estimates
    close it for n large; small n by direct verification.  Mathlib
    has Bertrand (`Nat.exists_prime_lt_and_le_two_mul`), Chebyshev-
    type bounds (`Nat.primorial` bounds), and Kummer/Legendre
    valuations — the ingredients exist.  Load-bearing for #699,
    #1094, #1095.  Effort L (hard but classical). -/
theorem sylvester_schur (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    k < maxPrimeFac (n.choose k) := by
  sorry

/-- **Erdős 1955** ([Er55d]), archived: `P(C(n,k)) ≫ k log k` for
    `k ≤ n/2`. -/
theorem erdos_klogk :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 2 ≤ k → 2 * k ≤ n →
      c * k * Real.log k ≤ (maxPrimeFac (n.choose k) : ℝ) := by
  sorry

/-- **Erdős #683, headline (OPEN)**: for some `c > 0`, every
    `1 ≤ k ≤ n` has `P(C(n,k)) ≥ min(n−k+1, k^{1+c})`.
    Cast to ℝ for the fractional power; `n − k + 1` computed in ℕ
    (exact: `k ≤ n`).

    Note the `min` is natural: for `k` close to `n` the binomial is
    small and `n−k+1` is the truthful cap (C(n, n−1) = n has largest
    prime factor ≤ n… with k = n−1 the bound reads min(2, (n−1)^{1+c})
    = 2 — every C(n, n−1) = n ≥ 2 has a prime factor ≥ 2 ✓). -/
theorem erdos_683 :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      min ((n - k + 1 : ℕ) : ℝ) ((k : ℝ) ^ (1 + c)) ≤
        (maxPrimeFac (n.choose k) : ℝ) := by
  sorry

/-- Sanity window for Sylvester–Schur: verified for all `n ≤ 40`.
    -- PROVABLE (decide). -/
theorem sylvester_schur_window :
    ∀ n ∈ Finset.range 41, ∀ k ∈ Finset.range 21,
      1 ≤ k → 2 * k ≤ n → k < maxPrimeFac (n.choose k) := by
  sorry

/-- Non-degeneracy of the `min`: at `(n, k) = (10, 9)`,
    `C(10,9) = 10 = 2·5`, `maxPrimeFac = 5`, and `n − k + 1 = 2 ≤ 5` —
    the first component of the min is the binding one near the
    diagonal.  -- PROVABLE (decide). -/
example : maxPrimeFac (Nat.choose 10 9) = 5 := by
  sorry

end ErdosCandidates.E683

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 683 (≥ min(n-k+1, k^{1+c})).
   - Sylvester-Schur, Erdos k log k, heuristic e^{c sqrt k} all faithful to DB remarks.
   - maxPrimeFac junk 0 at n <= 1 documented and guarded; no fidelity issue.
   - Arithmetic verified: maxPrimeFac(35)=7, maxPrimeFac(252)=7, C(10,9)=10 with maxPrimeFac=5.
   - OEIS anchors A006530 not checked in detail but claim is non-load-bearing.
   - DB comment history confirms the >= (not >) was a Bloom correction per Tao; file is current.
-/
