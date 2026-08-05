/-
  Erdős Problem #276 — all-composite Lucas sequences without a covering
  obstruction.
  Status: open.  Tier UA attack target (certificate slice, conditional
  on the PLAN.md C6 lane).

  Verbatim statement (`goof erdos fetch 276`, pulled 2026-08-05):

    "Is there an infinite Lucas sequence $a_0,a_1,\ldots$ where
    $a_{n+2}=a_{n+1}+a_n$ for $n\geq 0$ such that all $a_k$ are
    composite, and yet no integer has a common factor with every term of
    the sequence?"

  DB remarks: Graham [Gr64] produced an all-composite Lucas sequence via
  covering systems (33-digit seeds); Vsemirnov holds the record seeds
  a₀ = 106276436867, a₁ = 35256392432.  Wilf's example is OEIS A083216
  (the repo's PLAN.md lane C6 target).  Ismailescu–Son [IsSo14]
  'conjecturally solved' the problem: with p = 1, q a 129-digit number,
  a₀ = p² + q², a₁ = 2pq + q², the even-indexed terms are composite by a
  covering system and the odd-indexed terms factor algebraically as
  a_{2n+1} = (pFₙ + qF_{n+1})(pLₙ + qL_{n+1}) (F = Fibonacci,
  L = Lucas); no covering system appears responsible for the odd terms,
  but non-responsibility is unproved.

  Mathlib inventory (leandoc 2026-08-05): `Nat.fib` exists; general
  two-seed Lucas sequences do not (only `LucasLehmer`,
  `LinearRecurrence` — leandoc search "lucas sequence recurrence").
  Fresh def below.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E276

/-- The Lucas (Fibonacci-like) sequence with seeds `a₀, a₁`:
    `lucasSeq a₀ a₁ (n+2) = lucasSeq a₀ a₁ (n+1) + lucasSeq a₀ a₁ n`. -/
def lucasSeq (a₀ a₁ : ℕ) : ℕ → ℕ
  | 0 => a₀
  | 1 => a₁
  | n + 2 => lucasSeq a₀ a₁ (n + 1) + lucasSeq a₀ a₁ n

/-- Ground truth: seeds (0, 1) give Fibonacci.
    -- PROVABLE (rfl / induction against `Nat.fib`). -/
example : lucasSeq 0 1 10 = 55 := by sorry

/-- `AllComposite a₀ a₁`: every term of the sequence is composite
    (neither 0, 1, nor prime — we require `2 ≤ aₖ ∧ ¬ prime`, pinning
    the degenerate small values out per STYLE.md). -/
def AllComposite (a₀ a₁ : ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ lucasSeq a₀ a₁ k ∧ ¬ (lucasSeq a₀ a₁ k).Prime

/-- `NoCommonFactor a₀ a₁`: no integer `m ≥ 2` shares a factor with
    every term — the "no covering obstruction of gcd type" condition of
    the problem. -/
def NoCommonFactor (a₀ a₁ : ℕ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, Nat.Coprime m (lucasSeq a₀ a₁ k)

/-- **Erdős #276 (OPEN)**: is there an all-composite Lucas sequence with
    no common-factor obstruction?

    Source text: "Is there an infinite Lucas sequence ... such that all
    $a_k$ are composite, and yet no integer has a common factor with
    every term of the sequence?"

    Note on fidelity: "no integer has a common factor with every term"
    is the literal negative condition; the deeper intended question
    (whether a covering system is 'responsible') is informal — the DB
    itself only formalizes the gcd version, which is what
    `NoCommonFactor` states.  Ismailescu–Son give a candidate believed
    to satisfy both conjuncts. -/
theorem erdos_276 :
    ∃ a₀ a₁ : ℕ, AllComposite a₀ a₁ ∧ NoCommonFactor a₀ a₁ := by
  sorry

/-- **Graham/Vsemirnov certificate slice (the Tier-UA target)**: the
    Vsemirnov seeds generate an all-composite Lucas sequence.  This is
    the covering-system half only (the sequence does have a common
    factor structure — it is the classical construction).

    Attack: identical `IsFibonacciLike`-alpha-layer machinery to the
    PLAN.md C6 lane (A083216/Wilf); land C6 first, then instantiate:
    the covering system assigns to each residue class of indices a
    prime dividing the corresponding terms (via `lucasSeq` mod p
    periodicity — Pisano periods).  Mathlib: `Nat.ModEq`, periodicity
    of linear recurrences mod p is elementary induction.
    Effort M conditional on C6. -/
theorem vsemirnov_all_composite :
    AllComposite 106276436867 35256392432 := by
  sorry

/-- Sanity: the Vsemirnov seeds themselves are composite, and the
    recurrence's first terms are as expected.
    -- PROVABLE (decide / norm_num primality certificates). -/
example : ¬ (106276436867 : ℕ).Prime ∧ ¬ (35256392432 : ℕ).Prime ∧
    lucasSeq 106276436867 35256392432 2 = 141532829299 := by
  sorry

/-- Non-degeneracy of `NoCommonFactor`: the Fibonacci sequence (seeds
    1, 1) satisfies it — consecutive Fibonacci numbers are coprime, so
    no `m ≥ 2` divides every term (indeed `fib` hits 1).  But Fibonacci
    has prime terms, so it fails `AllComposite`: the two conjuncts of
    the problem are jointly nontrivial.  -- PROVABLE. -/
example : NoCommonFactor 1 1 ∧ ¬ AllComposite 1 1 := by
  sorry

end ErdosCandidates.E276

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - lucasSeq def is correct (ℕ → ℕ, additive recurrence, two seeds).  ℕ codomain is
     safe: the problem requires all terms composite (hence positive), and additive
     recurrence over ℕ seeds produces only ℕ values.
   - AllComposite: requires 2 ≤ a_k ∧ ¬ prime — correct reading of "composite" that
     excludes 0 and 1.
   - NoCommonFactor: ∀ m ≥ 2, ∃ k, Coprime m (a_k).  Faithful to "no integer has a
     common factor with every term" (m=0 trivially shares factors, m=1 trivially doesn't,
     negatives symmetric — restricting to m ≥ 2 is the standard reading).
   - Vsemirnov seeds (106276436867, 35256392432): verified both composite; sum
     106276436867 + 35256392432 = 141532829299 matches the file's example.
   - DB attribution chain (Graham [Gr64], Vsemirnov record, Ismailescu-Son [IsSo14])
     matches the file header and theorem docstrings.
   - Ismailescu-Son factorization a_{2n+1} = (pF_n + qF_{n+1})(pL_n + qL_{n+1}) is
     from the DB comment (Woett, Nov 2025); file correctly attributes.
-/
