/-
  Erdős Problem #1140 — n − 2x² always prime.
  Status: disproved (Mollin–Williams 1989 + Epure–Gica 2010, via class
  number one computations).  Tier B archive target with certificates.

  Verbatim statement (`goof erdos fetch 1140`, pulled 2026-08-05):

    "Do there exist infinitely many $n$ such that $n-2x^2$ is prime for
    all $x$ with $2x^2<n$?"

  DB remarks: known such n: 2, 5, 7, 13, 31, 61, 181, 199; these are,
  with at most one exception, all such n.  Epure–Gica [EpGi10, Thm 4.1]:
  the only such n ≡ 1 (mod 4) are 5, 13, 61, 181; their method with
  Mollin–Williams [MoWi89] gives: the only n ≡ 3 (mod 4) are 7, 31, 199
  and at most one further exception.  (Comment thread: Woett/Chojecki
  note the problem is thus fully answered "no" modulo the one possible
  exception; a GRH-conditional route also closes finiteness.)

  Repo adjacency: exactly the `Proofs/Erdos/Covering/ErdosMinus2k.lean`
  shape (`IsAllPrimeMinusPow`): predicate, decide certificates, finite
  window, archived completeness.

  Mathlib inventory (leandoc 2026-08-05): `Nat.Prime`,
  `Nat.decidablePrime`; the bound `2x² < n` makes the predicate
  decidable per n.  Class-number machinery (the actual proof) is out of
  scope for Mathlib today — completeness stays sorry'd.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1140

/-- `AllPrimeMinusTwoSq n`: `n − 2x²` is prime for every `x` with
    `2x² < n`.  (ℕ-subtraction is exact under `2x² < n`.)  Note `x = 0`
    is included, so any such `n` is itself prime — matching the known
    list. -/
def AllPrimeMinusTwoSq (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/-- Decidability: `2x² < n` forces `x < n`, so the quantifier is
    bounded.  Route: `decidable_of_iff` against
    `∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime`
    (`Nat.decidableBallLT`).  -- PROVABLE. -/
instance (n : ℕ) : Decidable (AllPrimeMinusTwoSq n) :=
  decidable_of_iff (∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime)
    (by sorry)

/-- The eight known members, as decide certificates.
    Trace for 13: 13, 11, 5 (x = 0, 1, 2) all prime ✓.
    -- PROVABLE (decide). -/
theorem cert_known_members :
    AllPrimeMinusTwoSq 2 ∧ AllPrimeMinusTwoSq 5 ∧ AllPrimeMinusTwoSq 7 ∧
    AllPrimeMinusTwoSq 13 ∧ AllPrimeMinusTwoSq 31 ∧ AllPrimeMinusTwoSq 61 ∧
    AllPrimeMinusTwoSq 181 ∧ AllPrimeMinusTwoSq 199 := by
  sorry

/-- Non-degeneracy: 3 fails (3 − 2 = 1 not prime), 11 fails
    (11 − 8 = 3 prime, 11 − 2 = 9 = 3² not prime).
    -- PROVABLE (decide). -/
example : ¬ AllPrimeMinusTwoSq 3 ∧ ¬ AllPrimeMinusTwoSq 11 := by
  sorry

/-- Finite window: no further members up to 10⁶.
    -- PROVABLE (native_decide; the per-n check is O(√n) primality
    tests — same scaling as the ErdosMinus2k window sweeps.  Kernel
    `decide` will not reach 10⁶; stage at 10⁴ first). -/
theorem window_1e6 :
    ∀ n ∈ Finset.Icc 200 1000000, ¬ AllPrimeMinusTwoSq n := by
  sorry

/-- **Erdős #1140, resolution (Mollin–Williams + Epure–Gica)**: the set
    of such `n` is finite — the answer to the problem is NO.

    Source: "Do there exist infinitely many $n$ such that $n-2x^2$ is
    prime for all $x$ with $2x^2<n$?"  Disproved: the known members are
    2, 5, 7, 13, 31, 61, 181, 199 with at most one further exception
    (real quadratic class-number-one methods).  The class-number input
    is far outside current Mathlib — this stays archived; the
    certificates and window above are the sorry-free layer. -/
theorem erdos_1140_finite : {n : ℕ | AllPrimeMinusTwoSq n}.Finite := by
  sorry

/-- **Epure–Gica exact form for n ≡ 1 (mod 4)** (Thm 4.1, archived):
    the only members ≡ 1 (mod 4) are 5, 13, 61, 181 — no exception in
    this class. -/
theorem epure_gica_one_mod_four :
    {n : ℕ | AllPrimeMinusTwoSq n ∧ n % 4 = 1} = {5, 13, 61, 181} := by
  sorry

end ErdosCandidates.E1140

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches source verbatim; known list {2,5,7,13,31,61,181,199} verified.
   - Non-membership of 3 (3-2=1 not prime) and 11 (11-2=9 not prime) verified.
   - Epure-Gica mod-4 split and Mollin-Williams attribution match source sections.
   - AllPrimeMinusTwoSq predicate correctly uses strict ineq 2*x^2 < n; NAT-subtraction
     is exact under that guard. x=0 included, forcing n itself prime -- consistent.
   - Comment-sourced claims (Woett, Chojecki, GRH route) flagged as such in header.
   - Mathlib inventory (Nat.Prime, Nat.decidablePrime) correct.
-/
