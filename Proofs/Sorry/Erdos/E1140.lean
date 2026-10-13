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
    is included, so any positive such `n` is itself prime. At `n = 0`
    the raw predicate is vacuously true: no x satisfies 2*x^2 < 0.
    It therefore differs from a positive-domain production predicate. -/
def AllPrimeMinusTwoSq (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/-- The raw predicate is equivalent to checking only natural numbers below `n`. -/
theorem allPrimeMinusTwoSq_iff_bounded (n : ℕ) :
    AllPrimeMinusTwoSq n ↔
      ∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime := by
  constructor
  · intro h x _ hx
    exact h x hx
  · intro h x hx
    have hx_sq : x ≤ x ^ 2 := Nat.le_self_pow (by decide) x
    have hx_twice_sq : x ≤ 2 * x ^ 2 := by omega
    exact h x (lt_of_le_of_lt hx_twice_sq hx) hx

example : AllPrimeMinusTwoSq 0 := by
  intro x hx
  exact False.elim (Nat.not_lt_zero _ hx)

/-- Decidability: `2x² < n` forces `x < n`, so the quantifier is bounded. -/
instance (n : ℕ) : Decidable (AllPrimeMinusTwoSq n) :=
  decidable_of_iff (∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime)
    (allPrimeMinusTwoSq_iff_bounded n).symm

set_option maxRecDepth 4096 in
/-- The eight known members, as kernel decide certificates.
    Trace for 13: 13, 11, 5 (x = 0, 1, 2) all prime. -/
theorem cert_known_members :
    AllPrimeMinusTwoSq 2 ∧ AllPrimeMinusTwoSq 5 ∧ AllPrimeMinusTwoSq 7 ∧
    AllPrimeMinusTwoSq 13 ∧ AllPrimeMinusTwoSq 31 ∧ AllPrimeMinusTwoSq 61 ∧
    AllPrimeMinusTwoSq 181 ∧ AllPrimeMinusTwoSq 199 := by
  decide

/-- Negative controls: 3 and 11 fail at `x = 1`, producing 1 and 9. -/
theorem cert_negative_controls : ¬ AllPrimeMinusTwoSq 3 ∧ ¬ AllPrimeMinusTwoSq 11 := by
  constructor
  · intro h
    have hprime : Nat.Prime 1 := h 1 (by decide)
    exact (by decide : ¬ Nat.Prime 1) hprime
  · intro h
    have hprime : Nat.Prime 9 := h 1 (by decide)
    exact (by decide : ¬ Nat.Prime 9) hprime

example : ¬ AllPrimeMinusTwoSq 3 ∧ ¬ AllPrimeMinusTwoSq 11 :=
  cert_negative_controls

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
    certificates and window above are also admitted targets, not a sorry-free layer. -/
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
   Disposition: retained admitted archive; raw zero case is vacuous
   - Statement matches source verbatim; known list {2,5,7,13,31,61,181,199} verified.
   - Non-membership of 3 (3-2=1 not prime) and 11 (11-2=9 not prime) verified.
   - Epure-Gica mod-4 split and Mollin-Williams attribution match source sections.
   - AllPrimeMinusTwoSq predicate correctly uses strict ineq 2*x^2 < n; NAT-subtraction
     is exact under that guard. For positive n, x=0 forces n prime; at n=0
     the predicate is vacuous, so the positive known list is not exhaustive for the raw predicate.
   - Comment-sourced claims (Woett, Chojecki, GRH route) flagged as such in header.
   - Mathlib inventory (Nat.Prime, Nat.decidablePrime) correct.
-/
