/-
  Erdős Problem #1100 — coprime consecutive divisors.
  Status: open.  Tier UC lemma mine (τ⊥ decidable; trivial bounds and
  small tables immediate).

  Verbatim statement (`goof erdos fetch 1100`, pulled 2026-08-05):

    "If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then
    let $\tau_\perp(n)$ count the number of $i$ for which
    $(d_i,d_{i+1})=1$.

    Is it true that $\tau_\perp(n)/\omega(n)\to \infty$ for almost
    all $n$? Is it true that
    \[\tau_\perp(n)< \exp((\log n)^{o(1)})\]for all $n$?

    Let\[g(k) = \max_{\omega(n)=k}\tau_\perp(n),\]
    where $\omega(n)$ counts the number of distinct prime divisors of
    $n$, and $n$ is restricted to squarefree integers. Determine the
    growth of $g(k)$."

  DB remarks (Erdős–Hall [ErHa78]): trivially τ⊥(n) ≥ ω(n) (equality
  infinitely often).  Erdős–Hall: max_{n<x} τ⊥(n) >
  exp((log log x)^{2−ε}).  Erdős–Simonovits (see [Er81h]):
  (√2 + o(1))^k < g(k) < (2 − c)^k over squarefree n.

  ⚠ OEIS mismatch note: the DB's `goof erdos list` metadata links
  A325864, whose OEIS name is "Number of subsets of {1..n} of which
  every subset has a different sum" — unrelated to τ⊥ on its face.
  Do not use A325864 as ground truth without resolving the mismatch
  (possibly a DB metadata error).

  Repo adjacency: `Proofs/Erdos/Erdos542/SchinzelSzekeres.lean`
  (divisor-structure work).  Mathlib: `Nat.divisors`, sorted lists as
  in the E673 sketch, `Nat.primeFactors.card` for ω.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1100

/-- The increasing list of divisors of `n` (shared shape with the
    E673 sketch). -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- `tauPerp n`: the number of adjacent coprime pairs in the sorted
    divisor list — the `τ⊥(n)` of the problem. -/
def tauPerp (n : ℕ) : ℕ :=
  (List.zipWith (fun a b => Nat.gcd a b = 1) (divisorList n)
    (divisorList n).tail).count true

/-- Ground truth: divisors of 12: 1,2,3,4,6,12 — adjacent gcds:
    (1,2)=1 ✓, (2,3)=1 ✓, (3,4)=1 ✓, (4,6)=2, (6,12)=6 → τ⊥(12) = 3.
    ω(12) = 2.  -- PROVABLE (decide). -/
example : tauPerp 12 = 3 ∧ (12 : ℕ).primeFactors.card = 2 := by
  sorry

/-- **Trivial lower bound (first landing)**: `ω(n) ≤ τ⊥(n)` for
    `n ≥ 2` — below each prime power block boundary the divisors
    p·(largest divisor composed of smaller primes)… Erdős–Hall's
    observation: for each prime p ∣ n, the divisor just before p in
    the sorted list is coprime to p — wait, the clean classical
    argument: for each p ∣ n the pair (d, d') straddling where p
    first appears is coprime; formalize via the p-adic jump.
    Effort M (the combinatorial argument needs care).  -/
theorem omega_le_tauPerp (n : ℕ) (hn : 2 ≤ n) :
    n.primeFactors.card ≤ tauPerp n := by
  sorry

/-- **Erdős #1100, question 1 (OPEN)**: `τ⊥(n)/ω(n) → ∞` for almost
    all `n` (density form). -/
theorem erdos_1100_q1 (M : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.Icc 2 X).filter
          (fun n => tauPerp n ≤ M * n.primeFactors.card)).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  sorry

/-- **Erdős #1100, question 2 (OPEN)**: `τ⊥(n) < exp((log n)^{o(1)})`
    for all `n` — ε-form: for every `ε > 0`, eventually
    `τ⊥(n) < exp((log n)^ε)`. -/
theorem erdos_1100_q2 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (tauPerp n : ℝ) < Real.exp (Real.log n ^ ε) := by
  sorry

/-- `gPerp k`: max of τ⊥ over squarefree `n` with `ω(n) = k` — the
    `g(k)` of the third question.  (Well-defined: τ⊥(n) ≤ τ(n) = 2^k
    over squarefree n with ω(n) = k, so the sup is finite; encoded as
    an sSup over the value set.) -/
noncomputable def gPerp (k : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ n : ℕ, Squarefree n ∧ n.primeFactors.card = k ∧
    tauPerp n = t}

/-- **Erdős–Simonovits bounds** ([Er81h]), archived:
    `(√2 + o(1))^k < g(k) < (2 − c)^k`.  Stated as: for some c > 0
    and large k, `2^{k/2} ≤ g(k) ≤ (2 − c)^k`. -/
theorem erdos_simonovits_bounds :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (gPerp k : ℝ) ∧
      (gPerp k : ℝ) ≤ (2 - c) ^ (k : ℝ) := by
  sorry

/-- **Erdős–Hall max-order bound** ([ErHa78]), archived: for every
    `ε > 0` and large `x`, some `n < x` has
    `τ⊥(n) > exp((log log x)^{2−ε})`. -/
theorem erdos_hall_max_order (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, n < x ∧
        Real.exp (Real.log (Real.log x) ^ (2 - ε)) < (tauPerp n : ℝ) := by
  sorry

/-- Sanity: equality τ⊥ = ω happens — `n = 2`: divisors 1, 2;
    τ⊥ = 1 = ω(2).  And a squarefree table entry: τ⊥(30) — divisors
    1,2,3,5,6,10,15,30: coprime adjacent pairs (1,2),(2,3),(3,5),
    (5,6) → τ⊥(30) = 4 with ω = 3.  -- PROVABLE (decide). -/
example : tauPerp 2 = 1 ∧ tauPerp 30 = 4 := by
  sorry

end ErdosCandidates.E1100

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 1100 exactly.
   - tau_perp definition, both questions, g(k) over squarefree with omega=k all faithful.
   - Erdos-Simonovits (sqrt(2)+o(1))^k < g(k) < (2-c)^k matches DB remarks.
   - Erdos-Hall max order exp((log log x)^{2-eps}) matches DB remarks.
   - Arithmetic: tau_perp(12)=3 (adj coprime pairs: (1,2),(2,3),(3,4)), tau_perp(30)=4
     ((1,2),(2,3),(3,5),(5,6)), tau_perp(2)=1. All verified.
   - A325864 OEIS flag: confirmed. goof oeis show A325864 returns "Number of subsets of
     {1..n} of which every subset has a different sum" — indeed unrelated to tau_perp.
     The DB comments show AlexisOlson flagged it as "related but not identical" and the
     site was updated. The file's warning is correct and well-judged; the sequence is
     tangentially connected (distinct subset sums arise in the Erdos-Simonovits reduction
     per Woett's comment remark 3) but is NOT a direct encoding of tau_perp values.
     Flag is legitimate and should be retained.
-/
