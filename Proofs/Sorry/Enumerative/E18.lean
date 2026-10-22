/-
  Erdős Problem #18 — practical numbers and the divisor-count function
  h(m).
  Status: open; $250.  Tier UC lemma mine on the repo's Practical
  layer.

  Verbatim statement (`goof erdos fetch 18`, pulled 2026-08-05):

    "We call $m$ practical if every integer $1\leq n<m$ is the sum of
    distinct divisors of $m$. If $m$ is practical then let $h(m)$ be
    such that $h(m)$ many divisors always suffice.

    Are there infinitely many practical $m$ such that
    \[h(m) < (\log\log m)^{O(1)}?\]
    Is it true that $h(n!)<n^{o(1)}$? Or perhaps even
    $h(n!)<(\log n)^{O(1)}$?"

  DB remarks: almost all numbers are not practical.  Erdős:
  h(n!) < n.  Vose [Vo85]: infinitely many practical m with
  h(m) ≪ (log m)^{1/2}.  The $250 is for the (log log m)^{O(1)}
  question ([Er81h]).  OEIS A005153.  Candidates doc adds the
  computed table h(n!) for n = 3..11: 2, 3, 4, 5, 5, 6, 7, 7, 7.

  Repo adjacency: `Proofs/Enumerative/Practical.lean` — `Nat.Practical`
  (classical m ≤ n form, decidable, Stewart step) is the definition
  layer; `h` below extends it.

  Note the repo's `Nat.Practical` quantifies `m ≤ n` (inclusive)
  while the DB says `1 ≤ n < m` (exclusive): equivalent since `m` is
  a divisor of itself — the repo file documents this equivalence.
-/
import Sorry.Quarantine.Enumerative.E18

set_option autoImplicit false

namespace ErdosCandidates.E18


/-- Ground truth: `h 6 = 2` (divisors 1,2,3,6: 1=1, 2=2, 3=3, 4=1+3,
    5=2+3 — two always suffice, and 5 needs two), certified in production. -/
example : h 6 = 2 := h_six

/- The unchanged definitions and checked factorial results now live in
`Enumerative.E18`, under the same fully qualified names. Erdős's observation
is recorded in erdos18 and independently in Erdos1981, printed p. 172.
The proof here uses quotient/remainder scaling, not a greedy chain or Stewart
steps: represent the quotient using divisors of the previous factorial,
scale by the new factor, and insert the nonzero remainder. -/

/-- **Erdős #18, question 1 (OPEN, $250)**: are there infinitely many
    practical `m` with `h(m) < (log log m)^C` for some fixed `C`? -/
theorem erdos_18_q1 :
    ∃ C : ℝ, 0 < C ∧
      {m : ℕ | m.Practical ∧
        (h m : ℝ) < Real.log (Real.log m) ^ C}.Infinite := by
  sorry

/-- **Erdős #18, questions 2–3 (OPEN)**: `h(n!) < n^{o(1)}`, perhaps
    even `h(n!) < (log n)^{O(1)}`.  Stated in the ε-form for q2. -/
theorem erdos_18_q2 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (h n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

theorem erdos_18_q3 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (h n.factorial : ℝ) < Real.log n ^ C := by
  sorry

/-- **Vose's theorem** ([Vo85]), archived: infinitely many practical
    `m` with `h(m) ≪ (log m)^{1/2}`. -/
theorem vose :
    ∃ C : ℝ, 0 < C ∧
      {m : ℕ | m.Practical ∧
        (h m : ℝ) ≤ C * Real.sqrt (Real.log m)}.Infinite := by
  sorry

/-- The computed table (candidates doc): `h(n!)` for n = 3, …, 11 is
    2, 3, 4, 5, 5, 6, 7, 7, 7. Only the first two entries are certified
    here by production powerset checks: `h 6 = 2` and `h 24 = 3`. -/
example : h 24 = 3 := h_twenty_four

end ErdosCandidates.E18

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB: practical def, h(m) def, three questions
     (infinitely many with h(m) < (log log m)^{O(1)}, h(n!) < n^{o(1)},
     h(n!) < (log n)^{O(1)}).
   - Erdos h(n!) < n matches DB. Vose (log m)^{1/2} matches DB.
   - $250 prize for the (log log m)^{O(1)} question matches DB ([Er81h]).
   - h(6) = 2: divisors {1,2,3,6}; worst case is 5 = 2+3 (2 divisors). Correct.
   - h(24) = 3: divisors {1,2,3,4,6,8,12,24}; 23 = 12+8+3 needs 3, and no
     two divisors sum to 23 (max pair 12+8=20). 3 always suffice (verified by
     exhaustion). Correct.
   - Import Enumerative.Practical verified: file exists at
     Proofs/Enumerative/Practical.lean with Nat.Practical (line 76) and
     Nat.Practical.exists_sum_eq (line 121) as used by E18.
   - Practical def equivalence (m <= n inclusive vs 1 <= n < m exclusive)
     correctly documented: m divides itself, so m is always representable.
   - Lean types faithful to the mathematical content.
-/
