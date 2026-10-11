/-
  Erdős Problem #688 — sieving [1, n] by congruences with large prime
  moduli.
  Status: open.  Tier UC lemma mine (interval-covering certificates).

  Verbatim statement (`goof erdos fetch 688`, pulled 2026-08-05):

    "Define $\epsilon_n$ to be maximal such that there exists some
    choice of congruence class $a_p$ for all primes
    $n^{\epsilon_n}<p\leq n$ such that every integer in $[1,n]$
    satisfies at least one of the congruences $\equiv a_p\pmod{p}$.

    Estimate $\epsilon_n$ - in particular is it true that
    $\epsilon_n=o(1)?$"

  DB remarks: Erdős: ε_n ≫ log log log n / log log n.  Cluster with
  #687, #689, #1200.

  Formalization: the real-exponent threshold `n^ε` is clumsy in ℕ;
  we parametrize by the integer cutoff `T` instead — `CoversWith n T`
  says the primes in `(T, n]` admit residues covering `[1, n]` — and
  express ε_n-statements through the least admissible `T`.

  Repo adjacency: same verification shape as `Erdos.Covering`
  (interval coverage instead of full residue coverage) — certified
  lower-bound data points are the lane.

  Mathlib inventory: `Nat.ModEq`, `Finset.filter Nat.Prime`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E688

/-- `CoversWith n T`: there is a choice of residue `a p` for each
    prime `p ∈ (T, n]` such that every `m ∈ [1, n]` satisfies
    `m ≡ a p (mod p)` for some such prime. -/
def CoversWith (n T : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
    ∃ p ∈ (Finset.Icc (T + 1) n).filter Nat.Prime, m % p = a p % p

/-- Ground truth probe shape: with `T = 1` (all primes `≤ n`
    available, including 2 and 3) covering `[1, 12]` is easy —
    e.g. a₂ = 0 (evens), a₃ = 1 ({1,4,7,10}), a₅ = 3 ({3}), a₇ = 5
    ({5}), a₁₁ = 9 ({9}), leaving 11 ← a₁₁… probe carefully; recorded
    as the satisfiability stub.  -- PROVABLE (decide once a concrete
    residue table is pinned; the table above needs re-checking —
    that is exactly what the stub is for). -/
example : CoversWith 12 1 := by
  sorry

/-- Monotonicity in `T` (smaller cutoff = more primes = easier):
    `CoversWith n T'` implies `CoversWith n T` for `T ≤ T'`.
    -- PROVABLE (weaken the prime pool; effort S). -/
theorem coversWith_mono (n T T' : ℕ) (hTT : T ≤ T')
    (h : CoversWith n T') : CoversWith n T := by
  sorry

/-- `minCutoff n`: the largest admissible cutoff — we track
    `sSup {T | CoversWith n T}`; `ε_n = log(minCutoff n)/log n` in
    the problem's normalization.  (T = 0 always works for n ≥ 1?
    No — coverage with all primes ≤ n is itself nontrivial for the
    m = 1 case… 1 % p = a p % p requires choosing a p ≡ 1 for some p;
    fine.  sSup honesty: the set is bounded by n.) -/
noncomputable def maxCutoff (n : ℕ) : ℕ := sSup {T : ℕ | CoversWith n T}

/-- **Erdős's lower bound** (DB): ε_n ≫ log log log n / log log n —
    in cutoff form: `maxCutoff n ≥ n^{c·lll n/ll n}` for some
    `c > 0` and large n.  Archived (the construction is a
    Rankin-style sieve). -/
theorem erdos_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (c * Real.log (Real.log (Real.log n)) /
        Real.log (Real.log n)) ≤ (maxCutoff n : ℝ) := by
  sorry

/-- **Erdős #688, headline (OPEN)**: `ε_n = o(1)` — in cutoff form:
    for every `δ > 0`, eventually `maxCutoff n < n^δ` — every
    covering must use some prime below `n^δ`. -/
theorem erdos_688 (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (maxCutoff n : ℝ) < (n : ℝ) ^ δ := by
  sorry

/-- Certificate lane: a concrete covering of `[1, 30]` using only
    primes in `(2, 30]` (no modulus 2) — a genuinely nontrivial
    interval-covering certificate; probe with sage for the residue
    table, then `decide`.  Yields the data point
    `maxCutoff 30 ≥ 2`.  -- PROVABLE-in-principle (decide). -/
theorem cutoff_30_ge_2 : CoversWith 30 2 := by
  sorry

end ErdosCandidates.E688

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch exactly.
   - Re-parametrization from real exponent n^epsilon to integer cutoff T is
     faithful: CoversWith n T uses primes in (T, n], and maxCutoff = sSup
     recovers epsilon_n = log(maxCutoff n)/log n.
   - Monotonicity direction is correct: T <= T' and CoversWith n T' (fewer
     primes) implies CoversWith n T (more primes) by extending the witness.
   - sSup honesty: set is bounded by n (T = n gives empty prime pool) and
     nonempty (T = 0 gives all primes <= n, sufficient for n >= 2).
   - Erdos lower bound lll/ll faithfully translates DB remark.
   - Headline epsilon_n = o(1) correctly encoded as maxCutoff n < n^delta.
-/
