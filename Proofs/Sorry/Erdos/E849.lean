/-
  Erdős Problem #849 — Singmaster-type multiplicities in Pascal's
  triangle.
  Status: open.  Tier UC lemma mine (exact multiplicity of 120 and
  3003 are clean finite theorems).

  Verbatim statement (`goof erdos fetch 849`, pulled 2026-08-05):

    "Is it true that, for every integer $t\geq 1$, there is some
    integer $a$ such that\[\binom{n}{k}=a\](with $1\leq k\leq n/2$)
    has exactly $t$ solutions?"

  DB remarks: Erdős [Er96b] credits Erdős–Gordon; commonly known as
  (adjacent to) Singmaster's conjecture.  t = 3 at a = 120; t = 4 at
  a = 3003.  Nothing known for t ≥ 5.  Erdős and Singmaster both
  believed the answer is NO — an absolute bound on multiplicities.
  Matomäki–Radziwiłł–Shao–Tao–Teräväinen [MRSTT22]: at most two
  solutions when k ≥ exp((log n)^{2/3+ε}) and a large.

  OEIS anchors: A003016 (occurrences of n in Pascal's triangle),
  A003015 (numbers occurring ≥ 5 times), A059233 and others.

  Mathlib inventory: `Nat.choose`; multiplicity as `Set.ncard` of the
  solution set (finite: `C(n,k) ≥ n` for `1 ≤ k ≤ n/2`… C(n,1) = n,
  and C(n,k) is ≥ n for 1 ≤ k ≤ n−1, so solutions have `n ≤ a` —
  bounded search). -/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E849

/-- The solution set of `C(n,k) = a` in the half-triangle
    `1 ≤ k ≤ n/2` (encoded `2k ≤ n`). -/
def solutions (a : ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ | 1 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧ q.1.choose q.2 = a}

/-- `multiplicity a`: the number of half-triangle representations. -/
noncomputable def multiplicity (a : ℕ) : ℕ := (solutions a).ncard

/-- Finiteness engine: for `a ≥ 2` every solution has `n ≤ a` (since
    `C(n,k) ≥ n` for `1 ≤ k ≤ n/2` via `C(n,1) = n ≤ C(n,k)` and
    binomial monotonicity in k up to n/2), so the solution set is
    finite and `ncard` is honest.
    -- PROVABLE (Mathlib: `Nat.choose_le_choose`-family monotonicity;
    effort S — the binomial monotonicity lemma is the reusable
    asset). -/
theorem solutions_finite (a : ℕ) (ha : 2 ≤ a) : (solutions a).Finite := by
  sorry

/-- Ground truth: `multiplicity 6 = 2` — `6 = C(6,1) = C(4,2)`.
    -- PROVABLE (bounded decide after `solutions_finite`). -/
example : multiplicity 6 = 2 := by sorry

/-- **The t = 3 certificate**: `multiplicity 120 = 3` —
    `120 = C(120,1) = C(16,2) = C(10,3)`.
    -- PROVABLE (bounded search n ≤ 120; decide-scale). -/
theorem multiplicity_120 : multiplicity 120 = 3 := by
  sorry

/-- **The t = 4 certificate**: `multiplicity 3003 = 4` —
    `3003 = C(3003,1) = C(78,2) = C(15,5) = C(14,6)`.
    -- PROVABLE (bounded search n ≤ 3003; decide/native_decide). -/
theorem multiplicity_3003 : multiplicity 3003 = 4 := by
  sorry

/-- **Erdős #849 (OPEN)**: for every `t ≥ 1` some `a ≥ 2` has exactly
    `t` representations.  (Believed FALSE by Erdős and Singmaster —
    t = 5 has no known witness; 3003 is conjectured maximal.) -/
theorem erdos_849 (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 2 ≤ a ∧ multiplicity a = t := by
  sorry

/-- The complementary believed-truth (Singmaster direction), archived:
    multiplicities are absolutely bounded. -/
theorem multiplicity_bounded :
    ∃ B : ℕ, ∀ a : ℕ, 2 ≤ a → multiplicity a ≤ B := by
  sorry

/-- **MRSTT interior bound** ([MRSTT22]), archived: for every ε > 0
    there is `A` such that for `a ≥ A`, at most two solutions have
    `k ≥ exp((log n)^{2/3+ε})`. -/
theorem mrstt_interior (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a →
      ({q : ℕ × ℕ | q ∈ solutions a ∧
        Real.exp (Real.log q.1 ^ ((2 : ℝ) / 3 + ε)) ≤ (q.2 : ℝ)}).ncard
        ≤ 2 := by
  sorry

/-- Sanity: `t = 1` and `t = 2` are realized — every prime `p` has
    `multiplicity p = 1` (only `C(p,1)`), and `multiplicity 6 = 2`.
    Keeps `erdos_849` honest at the small end (the content is t ≥ 5).
    -- PROVABLE (decide instances). -/
example : multiplicity 5 = 1 ∧ multiplicity 6 = 2 := by
  sorry

end ErdosCandidates.E849

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 849.
   - t=3 at 120: C(120,1)=C(16,2)=C(10,3)=120 verified, exactly 3 half-triangle solutions.
   - t=4 at 3003: C(3003,1)=C(78,2)=C(15,5)=C(14,6)=3003 verified, exactly 4.
   - multiplicity 6 = 2: solutions are (6,1) and (4,2) in the half-triangle; correct.
   - Half-triangle convention 2*k <= n (i.e. k <= n/2) matches the source "1 <= k <= n/2".
   - Erdos/Singmaster believed NO, MRSTT bound k >= exp((log n)^{2/3+eps}) faithful.
   - No fidelity issues found.
-/
