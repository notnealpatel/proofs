import Sorry.Quarantine.Erdos.Erdos1140.MinusTwoSquare

/-!
Quarantined admissions and their dependent consequences. Production supplies the
independent infrastructure; the declarations below retain their original statements
and proofs. The original source and disclosure documentation is retained below.
No mathematical proof closure is claimed.
-/

/-
  Erdos/Erdos1140/MinusTwoSquare — erdosproblems.com #1140: the `n` for
  which `n - 2x²` is prime for every `x` with `2x² < n`.

  GROUND TRUTH PINNING (`goof erdos fetch 1140`, pulled 2026-08-05).

  Problem statement, verbatim:

    "Do there exist infinitely many $n$ such that $n-2x^2$ is prime for
    all $x$ with $2x^2<n$?"

  Database section, verbatim:

    "The known such $n$ are\[2,5,7,13,31,61,181,199.\]It is known that
    these are, with at most one exception, all such $n$. Theorem 4.1 of
    Epure and Gica \cite{EpGi10} implies that the only such $n\equiv
    1\pmod{4}$ are $5,13,61,181$. Epure and Gica also remark that their
    method, coupled with a result of Mollin and Williams \cite{MoWi89},
    implies that the only such $n\equiv 3\pmod{4}$ are $7,31,199$, and at
    most one other exception.

    See also [1141]."

  References section, verbatim:

    "[EpGi10] Epure, Mihai and Gica, Alexandru, *Principal quadratic real
    fields in connection with some additive problems*. Bull. Math. Soc.
    Sci. Math. Roumanie (N.S.) (2010), 251--259.

    [MoWi89] Mollin, R. A. and Williams, H. C., *Period four and real
    quadratic fields of class number one*. Proc. Japan Acad. Ser. A Math.
    Sci. (1989), 89--93."

  No OEIS entry exists for the member list: `goof oeis match
  "2,5,7,13,31,61,181,199"` and the same query without its first or last
  term all return 0 results (2026-08-05). The Erdős database is therefore
  the sole primary source pinned here.

  WHAT THE SOURCE DOES AND DOES NOT SETTLE. The three mod-4 classes are
  exhaustive once the even case is disposed of, and the even case is
  elementary (§5 below, proved): `x = 0` is always in range, so any such
  `n` is itself prime, and an even prime is `2`. So the database's two
  cited results — Epure–Gica Theorem 4.1 for `n ≡ 1 (mod 4)`, and their
  method with Mollin–Williams for `n ≡ 3 (mod 4)` — together bound the
  full solution set by nine elements, and the answer to the problem as
  posed is NO. Both cited results are class-number-one statements about
  real quadratic fields, far outside current Mathlib; they are this
  file's two intended `sorry`s (§8). Everything else is proved.

  THE VACUITY TRAP, AND WHY `0 < n` IS PART OF THE PREDICATE. The raw
  body `∀ x, 2x² < n → (n - 2x²).Prime` is satisfied *vacuously* at
  `n = 0`: no `x` has `2x² < 0`. It is the only vacuous solution — at
  `n ≥ 1` the value `x = 0` is always in range, which is also why every
  member is prime. `n = 1` is therefore excluded on its merits
  (`1` is not prime), not by the guard. §2 discloses this explicitly.

  A TRAP IN THE OBSTRUCTION ARGUMENT (§6). Terence Tao, in the #1140
  comment thread (post-3742, 06:25 on 25 Jan 2026), verbatim: "$p|n-2x^2$
  and $n-2x^2>1$ does not quite imply that $n-2x^2$ is composite, because
  it could be equal to $p$." The congruence obstructions below are stated
  so that this cannot happen: `not_dvd_sub_of_two_mul_sq` carries the
  hypothesis `P + q < n`, i.e. `q < n - P` *strictly*, so `q ∣ (n - P)`
  with `n - P` prime is a genuine contradiction.

  CONTENTS.
    § 1 `AllPrimeMinusTwoSq` (raw body), `IsAllPrimeMinusTwoSq` (guarded
        predicate), the finite-range reformulation, `Decidable` instances.
    § 2 Degeneracy disclosure: `n = 0` is the unique vacuous solution;
        above the guard the quantified domain is nonempty, and every
        member is prime.
    § 3 The eight membership certificates of the database list, checked
        by kernel reduction.
    § 4 Negative controls, each with its explicit witness `x`.
    § 5 The even case, PROVED: a member divisible by `2` equals `2`. This
        is what makes the source's mod-4 dichotomy exhaustive.
    § 6 The congruence obstruction, PROVED: every member `n > 5`
        satisfies `n ≡ 1 (mod 6)`. Cuts the §7 search by a factor of six.
    § 7 The finite completeness window: no member in `(199, 10 ^ 6]`.
        Kernel-checked to `10 ^ 4`, `native_decide`-checked to `10 ^ 6`.
    § 8 ARCHIVED (this file's two intended `sorry`s): Epure–Gica Thm 4.1,
        and Mollin–Williams + Epure–Gica for `n ≡ 3 (mod 4)`.
    § 9 Consequences, no new `sorry`: the solution set is finite (the
        answer NO), and differs from the database's eight-element list by
        at most one element.
    § 10 Axiom audit.

  TRUST SURFACE OF §7. The `native_decide` sweep is granted by this
  lane's brief and is the only one in the file. It is deliberately routed
  through `NoSmallFactor` — trial division by the primes below `100` —
  and *not* through `Nat.Prime`. Reason: Mathlib's kernel-facing
  `Nat.decidablePrime` is swapped for the fast `Nat.decidablePrime'` by a
  `@[csimp]` lemma, and `@[csimp]` axiom dependencies do not surface in
  downstream `#print axioms` (lean4#7463; STYLE.md). Routing the sweep
  through `NoSmallFactor` keeps that swap out of the trusted base; what
  remains is the irreducible `native_decide` baseline (the Lean compiler
  plus core's `@[extern]` GMP `Nat` primitives). `sweep_kernel` re-checks
  the same statement to `10 ^ 4` with no native evaluation at all, so the
  `10 ^ 4` window carries only the `decide` trust surface.

  Since `NoSmallFactor` appears in §7 only as a *hypothesis*, weakening
  primality to it makes each swept statement **stronger**;
  `noSmallFactor_of_prime` is the only direction the window proof needs.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/


set_option autoImplicit false

namespace Erdos1140

-- Satisfiability of the §8 hypotheses, jointly instantiated: both
-- archived statements are about nonempty situations, not vacuities.
example : IsAllPrimeMinusTwoSq 5 ∧ 5 % 4 = 1 := ⟨cert_5, by norm_num⟩
example : IsAllPrimeMinusTwoSq 181 ∧ 181 % 4 = 1 := ⟨cert_181, by norm_num⟩
example : (7 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_7, by norm_num⟩
example : (31 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_31, by norm_num⟩
example : (199 : ℕ) ∈ {n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} := ⟨cert_199, by norm_num⟩

/-- **Epure–Gica, Theorem 4.1** (erdosproblems.com #1140, verbatim:
"Theorem 4.1 of Epure and Gica \cite{EpGi10} implies that the only such
$n\equiv 1\pmod{4}$ are $5,13,61,181$").

INTENDED SORRY — archived literature input, disclosed in the module
header; one of this file's two. The cited result is a class-number-one
statement about principal real quadratic fields (Bull. Math. Soc. Sci.
Math. Roumanie 2010, 251–259); that machinery is far outside current
Mathlib, so this is archived rather than proved.

Note this class carries *no* exception in the source — the "at most one
exception" is attached only to `n ≡ 3 (mod 4)`.

Evidence in this file: `5, 13, 61, 181` are members (`cert_5`, `cert_13`,
`cert_61`, `cert_181`) and are exactly the members `≡ 1 (mod 4)` up to
`10 ^ 6` (`mem_of_isAllPrimeMinusTwoSq_of_le`, `native_decide`-checked;
`mem_of_isAllPrimeMinusTwoSq_of_le_10000` kernel-checked to `10 ^ 4`). -/
theorem epure_gica_thm_4_1 {n : ℕ} (h : IsAllPrimeMinusTwoSq n) (h4 : n % 4 = 1) :
    n ∈ ({5, 13, 61, 181} : Finset ℕ) := by
  -- intended sorry: archived class-number input [EpGi10, Thm 4.1].
  sorry

/-- **Mollin–Williams + Epure–Gica for `n ≡ 3 (mod 4)`**
(erdosproblems.com #1140, verbatim: "Epure and Gica also remark that
their method, coupled with a result of Mollin and Williams
\cite{MoWi89}, implies that the only such $n\equiv 3\pmod{4}$ are
$7,31,199$, and at most one other exception").

INTENDED SORRY — archived literature input, disclosed in the module
header; the second of this file's two. `Set.Subsingleton` on the set
difference is exactly "at most one other exception": the members
`≡ 3 (mod 4)` beyond `7, 31, 199` are pairwise equal, hence number at
most one. The exception is not effectively bounded — it comes from the
ineffective (Siegel–Tatuzawa) side of real quadratic class number one —
which is why no finite computation, this file's `10 ^ 6` window included,
can remove it.

Evidence in this file: `7, 31, 199` are members (`cert_7`, `cert_31`,
`cert_199`) and are exactly the members `≡ 3 (mod 4)` up to `10 ^ 6`
(`mem_of_isAllPrimeMinusTwoSq_of_le`), so any exception exceeds
`10 ^ 6`. -/
theorem mollin_williams_epure_gica :
    ({n : ℕ | IsAllPrimeMinusTwoSq n ∧ n % 4 = 3} \ ({7, 31, 199} : Set ℕ)).Subsingleton := by
  -- intended sorry: archived class-number input [MoWi89] + [EpGi10].
  sorry

-- ════════════════════════════════════════════════════════════════════
-- §9 CONSEQUENCES — no new `sorry`
-- ════════════════════════════════════════════════════════════════════

/-- The database's own summary, verbatim: "It is known that these are,
with at most one exception, all such $n$." Formally: the solution set
differs from the eight-element list by at most one element.

The three mod-4 classes are covered by §5 (even, proved), by
`epure_gica_thm_4_1` (`n ≡ 1`), and by `mollin_williams_epure_gica`
(`n ≡ 3`). No new `sorry`; `sorryAx`-dependent through those two. -/
theorem exceptional_subsingleton :
    ({n : ℕ | IsAllPrimeMinusTwoSq n} \
      ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)).Subsingleton := by
  refine mollin_williams_epure_gica.anti ?_
  rintro n ⟨hn, hnot⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
  obtain ⟨hn2, hn5, hn7, hn13, hn31, hn61, hn181, hn199⟩ := hnot
  have h4 : n % 4 = 3 := by
    rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h | h | h | h
    · exact absurd (eq_two_of_mod_four_even hn (Or.inl h)) hn2
    · -- the `n ≡ 1 (mod 4)` class is closed exactly by Epure–Gica
      have hmem := epure_gica_thm_4_1 hn h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    · exact absurd (eq_two_of_mod_four_even hn (Or.inr h)) hn2
    · exact h
  refine ⟨⟨hn, h4⟩, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hn7, hn31, hn199⟩

/-- **Erdős #1140, resolution: the answer is NO** — there are *not*
infinitely many `n` with `n - 2x²` prime for all `x` with `2x² < n`,
because there are only finitely many such `n` at all.

No new `sorry`; `sorryAx`-dependent through the two §8 literature inputs.
The bound is nine: the eight members of the database list plus the at
most one unlocated exception `≡ 3 (mod 4)`. -/
theorem erdos_1140 : {n : ℕ | IsAllPrimeMinusTwoSq n}.Finite := by
  have hknown : ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ).Finite :=
    (((((((Set.finite_singleton 199).insert 181).insert 61).insert 31).insert 13).insert
      7).insert 5).insert 2
  have hsub : {n : ℕ | IsAllPrimeMinusTwoSq n} ⊆
      ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) ∪
        ({n : ℕ | IsAllPrimeMinusTwoSq n} \ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)) := by
    intro n hn
    by_cases hm : n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)
    · exact Or.inl hm
    · exact Or.inr ⟨hn, hm⟩
  exact (hknown.union exceptional_subsingleton.finite).subset hsub

/-- The problem as posed — "Do there exist infinitely many $n$ such that
$n-2x^2$ is prime for all $x$ with $2x^2<n$?" — answered: **no**.

No new `sorry`; `sorryAx`-dependent through `erdos_1140`. -/
theorem not_infinite_setOf_isAllPrimeMinusTwoSq :
    ¬ {n : ℕ | IsAllPrimeMinusTwoSq n}.Infinite :=
  Set.not_infinite.mpr erdos_1140

end Erdos1140
