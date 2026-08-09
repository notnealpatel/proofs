/-
  Erdős Problem #535 — sets with no r elements of equal pairwise gcd.
  Status: open.  Tier UA attack target (sunflower-encoding reduction).

  Verbatim statement (`goof erdos fetch 535`, pulled 2026-08-05):

    "Let $r\geq 3$, and let $f_r(N)$ denote the size of the largest
    subset of $\{1,\ldots,N\}$ such that no subset of size $r$ has the
    same pairwise greatest common divisor between all elements.
    Estimate $f_r(N)$."

  DB remarks: Erdős [Er64]: f_r(N) ≤ N^{3/4+o(1)}; Abbott–Hanson
  [AbHa70] improved the exponent to 1/2-order.  Erdős: lower bound
  f_r(N) > N^{c_r/log log N}, conjectured sharp.  ALWZ sunflower bounds
  give f_r(N) ≤ N^{C_r · log log log N / log log N} = N^{o(1)}.
  Hrishi et al. (Apr 2026, comment-sourced): lower bound
  exp((log(r−1)+o(1)) log N / log log N) via a block construction; upper
  bound via smooth/rough split + Bell–Chueluecha–Warnke sunflower lemma.
  Key encoding (their §2, audit-promoted to Tier UA): map
  n ↦ S(n) = {(p, j) : 1 ≤ j ≤ v_p(n)}; then S(a) ∩ S(b) = S(gcd a b),
  so r elements with equal pairwise gcds are exactly an r-sunflower of
  the S(n).

  Repo adjacency: `Proofs/Erdos/Erdos20/ErdosRado.lean`
  (`erdos_rado_sunflower_same_card`) — pushing the repo's Erdős–Rado
  bound through the encoding yields an explicit (weaker than ALWZ,
  still nontrivial) upper bound on f_r(N): a genuinely new formal
  artifact.

  Mathlib inventory (leandoc 2026-08-05): `Nat.factorization`,
  `Nat.gcd`, `Nat.factorization_gcd`; sunflower side lives in the repo,
  not Mathlib.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E535

/-- `EqualPairwiseGcd S`: all pairs of distinct elements of `S` have the
    same gcd. -/
def EqualPairwiseGcd (S : Finset ℕ) : Prop :=
  ∃ d : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b = d

/-- `GcdPatternFree r A`: no `r`-element subset of `A` has constant
    pairwise gcd. -/
def GcdPatternFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard r, ¬ EqualPairwiseGcd S

/-- `fgcd r N`: the size of the largest gcd-pattern-free subset of
    `{1, …, N}` — the `f_r(N)` of the problem.  (`EqualPairwiseGcd` has
    an unbounded `∃ d`, so the filter runs classically; a decidable
    refactor — pin `d` to the gcd of the two smallest elements — is the
    first cleanup if ground computation is wanted.) -/
open scoped Classical in
noncomputable def fgcd (r N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (GcdPatternFree r)).sup Finset.card

/-- Ground truth: pairwise-coprime sets are pattern-full (all gcds 1)!
    `{2,3,5}` has all pairwise gcds equal to 1, so it is NOT
    3-pattern-free.  Guards against misreading the constraint: the
    forbidden pattern includes the coprime case.  -- PROVABLE (decide). -/
example : ¬ GcdPatternFree 3 ({2, 3, 5} : Finset ℕ) := by
  sorry

/-- Satisfiability: `{2, 4, 3}` — gcd(2,4) = 2, gcd(2,3) = 1,
    gcd(4,3) = 1 — not all equal, and no other 3-subset exists, so it IS
    3-pattern-free.  -- PROVABLE (decide). -/
example : GcdPatternFree 3 ({2, 4, 3} : Finset ℕ) := by
  sorry

/-- The prime-power layer encoding `n ↦ {(p, j) : p^j ∣ n, j ≥ 1}` as a
    Finset of pairs, realized via `Nat.factorization`. -/
def layerSet (n : ℕ) : Finset (ℕ × ℕ) :=
  n.factorization.support.biUnion
    (fun p => (Finset.Icc 1 (n.factorization p)).image (fun j => (p, j)))

/-- **The encoding lemma** (the audit-promoted reduction; Hrishi et al.
    §2, elementary): `layerSet a ∩ layerSet b = layerSet (gcd a b)`.
    With it, `r` elements with equal pairwise gcds form an `r`-sunflower
    of layer sets (common kernel `layerSet d`), and the repo's
    Erdős–Rado bound applies.  Mathlib: `Nat.factorization_gcd`
    (pointwise min) is the engine.  -- PROVABLE (target; effort S–M). -/
theorem layerSet_inter (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    layerSet a ∩ layerSet b = layerSet (Nat.gcd a b) := by
  sorry

/-- Injectivity of the encoding on positive integers — needed so that
    sunflower cardinality bounds transfer back to `f_r(N)`.
    -- PROVABLE (factorization determines n). -/
theorem layerSet_injective :
    Set.InjOn layerSet {n : ℕ | n ≠ 0} := by
  sorry

/-- **The reduction target (Tier-UA deliverable)**: any bound
    `|sunflower-free family of ≤ m-element sets| ≤ B(m, r)` transfers to
    `f_r(N) ≤ B(log₂ N, r)`, since `layerSet n` has
    `Ω(n) ≤ log₂ N` elements for `n ≤ N`.  Stated concretely with the
    repo's Erdős–Rado bound `B(m, r) = m! · (r−1)^m` (from
    `Erdos.Erdos20.erdos_rado_sunflower_same_card`, adapted to
    non-uniform families by layering): explicit, weaker than ALWZ,
    genuinely new as a formal artifact.  The `(Nat.log 2 N)`-layer
    bookkeeping is the work. -/
theorem fgcd_le_erdos_rado (r N : ℕ) (hr : 3 ≤ r) (hN : 2 ≤ N) :
    fgcd r N ≤
      (Nat.log 2 N + 1) *
        (Nat.log 2 N).factorial * (r - 1) ^ (Nat.log 2 N + 1) := by
  sorry

/-- **Erdős' lower bound** (Er64), archived: for every `r ≥ 3` there is
    `c_r > 0` with `f_r(N) > N^{c_r / log log N}` for large `N`. -/
theorem erdos_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ^ (c / Real.log (Real.log N)) ≤ (fgcd r N : ℝ) := by
  sorry

/-- **Abbott–Hanson upper bound** (AbHa70), archived:
    `f_r(N) ≤ N^{1/2 + o(1)}`.  Stated with ε-quantifier. -/
theorem abbott_hanson_upper (r : ℕ) (hr : 3 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (fgcd r N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

end ErdosCandidates.E535

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB pull exactly.
   - EqualPairwiseGcd correctly encodes constant pairwise gcd; GcdPatternFree
     correctly forbids r-element subsets with that property.
   - Ground truth examples verified: {2,3,5} all pairwise gcds = 1 (NOT pattern-free);
     {2,4,3} has gcds 2,1,1 (IS pattern-free). Both correct.
   - layerSet encoding n -> {(p,j) : 1 <= j <= v_p(n)} matches Hrishi et al. section 2
     exactly. layerSet_inter claim S(a) cap S(b) = S(gcd(a,b)) matches.
   - Erdos lower bound N^{c_r/log log N} matches DB body [Er64].
   - Abbott-Hanson exponent 1/2: DB says "improved this exponent to 1/2"; file states
     N^{1/2+eps} with eps-quantifier — faithful encoding of N^{1/2+o(1)}.
   - fgcd_le_erdos_rado: uses (Nat.log 2 N) for log_2 N, bound
     m! * (r-1)^m from Erdos-Rado — repo cross-reference to Erdos20 is noted.
   - Hrishi et al. correctly flagged as comment-sourced. DB confirms Bloom noted
     this is Erdos's original argument from [Er64], not new — file does not overclaim.
   - Types: all ℕ, fgcd uses Classical for the unbounded exists in EqualPairwiseGcd,
     correctly noted in docstring.
-/
