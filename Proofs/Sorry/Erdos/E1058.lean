/-
  Erdős Problem #1058 — prime divisors of n! + 1.
  Status: proved (Luca 2001).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 1058`, pulled 2026-08-05):

    "Let $2=p_1<p_2<\cdots$ be the sequence of prime numbers. Are there
    only finitely many $n$ such that $n\in [p_{k-1},p_k)$ and the only
    primes dividing $n!+1$ are $p_{k}$ and $p_{k+1}$?"

  DB remarks: conjecture of Erdős–Stewart (Guy A2); only known cases
  n = 1, 2, 3, 4, 5.  Luca [Lu01] proved these are the only solutions.
  Comment thread (Tao, Sep 2025): the indexing "p_k and p_{k+1}" is the
  corrected form (the original "p_{k-1} and p_k" was a typo — n!+1 is
  never divisible by a prime ≤ n).

  Formalization choice: since n ∈ [p_{k-1}, p_k) determines k, the pair
  (p_k, p_{k+1}) is exactly (the least prime > n, the next prime after
  that).  This removes all index bookkeeping.

  Mathlib inventory (leandoc 2026-08-05): `Nat.factorial`, `Nat.Prime`,
  `Nat.exists_infinite_primes`, `Nat.primeFactors`, `Nat.minFac`;
  `Nat.nth Nat.Prime` available if the indexed form is preferred.
  Certificate-then-tail pattern from
  `Proofs/Erdos/Covering/ErdosMinus2k.lean`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1058

/-- The least prime strictly greater than `n`.  Total: the set is
    nonempty by Euclid (`Nat.exists_infinite_primes`), so `sInf` is
    attained and never the junk value. -/
noncomputable def nextPrime (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n < p}

/-- Ground-truth checks for `nextPrime`.
    -- PROVABLE (via `Nat.sInf_eq` characterization + decide). -/
example : nextPrime 1 = 2 ∧ nextPrime 4 = 5 ∧ nextPrime 5 = 7 ∧
    nextPrime 13 = 17 := by
  sorry

/-- `ErdosStewart n`: every prime divisor of `n! + 1` is one of the two
    smallest primes exceeding `n`.  For `n ∈ [p_{k-1}, p_k)` these two
    primes are precisely `p_k` and `p_{k+1}`, so this is the property in
    the problem statement with the interval bookkeeping absorbed. -/
def ErdosStewart (n : ℕ) : Prop :=
  ∀ q ∈ (n.factorial + 1).primeFactors,
    q = nextPrime n ∨ q = nextPrime (nextPrime n)

/-- Satisfiability: the five known cases.
    n=1: 2 = p₁ ✓;  n=2: 3 ✓;  n=3: 7 = p₄ = nextPrime(nextPrime 3) ✓;
    n=4: 25 = 5² ✓;  n=5: 121 = 11² and nextPrime(nextPrime 5) = 11 ✓.
    -- PROVABLE (decide, after rewriting `nextPrime` values). -/
example : ErdosStewart 1 ∧ ErdosStewart 2 ∧ ErdosStewart 3 ∧
    ErdosStewart 4 ∧ ErdosStewart 5 := by
  sorry

/-- Non-degeneracy: `n = 6` fails (6! + 1 = 721 = 7 · 103, and
    103 is not among {7, 11}).  -- PROVABLE (decide). -/
example : ¬ ErdosStewart 6 := by sorry

/-- **Erdős #1058, Luca's theorem** (Lu01): the only `n ≥ 1` with the
    Erdős–Stewart property are `n = 1, 2, 3, 4, 5`.  In particular the
    set is finite, answering the problem.

    Source text: "Are there only finitely many $n$ such that
    $n\in[p_{k-1},p_k)$ and the only primes dividing $n!+1$ are $p_k$
    and $p_{k+1}$?"  Luca proved yes, with the full solution list.

    Proof sketch (attack plan): if all prime factors of `n!+1` are among
    `{p, q}` with `p, q` the two primes following `n`, then
    `n! + 1 = p^a q^b`.  Both `p, q < 2n` for `n ≥ 2` well within
    Bertrand (`Nat.exists_prime_lt_and_le_two_mul`).  Luca's argument:
    compare `v_p` and sizes — `p^a q^b = n! + 1 < (2n)^{a+b}`-type
    counting against Stirling growth of `n!`, plus the classical
    congruence obstructions (`p ∣ n!+1` forces `p > n`; Wilson-type
    identities pin `a, b` small).  A 4-page elementary argument;
    factorial divisibility + Bertrand are the load-bearing inputs, both
    in Mathlib.  Full closure of an Erdős problem is plausible here.
    Effort M per candidates audit. -/
theorem luca_erdos_stewart :
    {n : ℕ | 1 ≤ n ∧ ErdosStewart n} = {1, 2, 3, 4, 5} := by
  sorry

/-- Finiteness corollary — the literal answer to the question as posed.
    -- PROVABLE from `luca_erdos_stewart` (finite explicit set). -/
theorem erdos_1058_finite : {n : ℕ | 1 ≤ n ∧ ErdosStewart n}.Finite := by
  sorry

/-- Sanity window: no further solutions up to 100.  Independent of the
    tail argument; a `decide`/`native_decide` sweep (the factorials get
    large, so kernel `decide` may need staging — note the enlarged trust
    surface if `native_decide` is used).
    -- PROVABLE (native_decide-scale). -/
theorem erdos_stewart_window_100 :
    ∀ n ∈ Finset.Icc 6 100, ¬ ErdosStewart n := by
  sorry

end ErdosCandidates.E1058

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - DB statement matches file header verbatim (with the corrected p_k/p_{k+1} indexing per TerenceTao comment post-753).
   - Solver attribution Luca [Lu01] matches DB.
   - `nextPrime` via `sInf` cleanly avoids the p_0 boundary issue for n=1.
   - Known cases verified: 1!+1=2={2}, 2!+1=3={3}, 3!+1=7={7}, 4!+1=25={5}, 5!+1=121={11}. All match nextPrime/nextPrime(nextPrime) values.
   - Non-example n=6: 6!+1=721=7*103, 103 is prime and not in {7,11}. Correct.
   - FLAG (minor): `nextPrime` is `noncomputable` and defined via `sInf`, so `ErdosStewart` is not `Decidable` without additional work. The `erdos_stewart_window_100` theorem acknowledges this needs `native_decide` with care. Not a fidelity error but a proof-engineering concern.
   - FLAG (minor): `luca_erdos_stewart` requires `1 ≤ n` in the set comprehension, which excludes n=0. The DB solution list "n=1,2,3,4,5" implicitly assumes n >= 1. 0!+1=2, nextPrime(0)=2, so ErdosStewart(0) would hold. The set should arguably be `{0,1,2,3,4,5}` or the guard should be documented as intentional. This is a genuine fidelity concern if Luca's theorem covers n=0.
-/
