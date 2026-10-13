/- RETENTION NOTE: this card uses prime-power layers (p,j), not just
prime support. A production gcd/sunflower development using a different
encoding does not provide an exact port of these statements. The two
sanity checks, layer intersection, and injectivity below are proved.
The quantitative targets remain admitted: the cardinality/logarithm and
non-uniform layering bridges are unpaid. Historical source claims in the
archival comments below are not newly source-certified by these proofs.
Preservation is not promotion or a complete quantitative reduction. -/
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

open scoped Classical in
/-- `fgcd r N`: the size of the largest gcd-pattern-free subset of
    `{1, …, N}` — the `f_r(N)` of the problem.  (`EqualPairwiseGcd` has
    an unbounded `∃ d`, so the filter runs classically; a decidable
    refactor — pin `d` to the gcd of the two smallest elements — is the
    first cleanup if ground computation is wanted.) -/
noncomputable def fgcd (r N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (GcdPatternFree r)).sup Finset.card

/-- Ground truth: pairwise-coprime sets are pattern-full (all gcds 1)!
    `{2,3,5}` has all pairwise gcds equal to 1, so it is NOT
    3-pattern-free.  Guards against misreading the constraint: the
    forbidden pattern includes the coprime case.  -- PROVABLE (decide). -/
theorem not_gcdPatternFree_three_primes : ¬ GcdPatternFree 3 ({2, 3, 5} : Finset ℕ) := by
  intro hfree
  have hmem : ({2, 3, 5} : Finset ℕ) ∈ ({2, 3, 5} : Finset ℕ).powersetCard 3 := by
    simp
  apply hfree _ hmem
  refine ⟨1, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    first | exact (hab rfl).elim | norm_num

example : ¬ GcdPatternFree 3 ({2, 3, 5} : Finset ℕ) := by
  exact not_gcdPatternFree_three_primes

/-- Satisfiability: `{2, 4, 3}` — gcd(2,4) = 2, gcd(2,3) = 1,
    gcd(4,3) = 1 — not all equal, and no other 3-subset exists, so it IS
    3-pattern-free.  -- PROVABLE (decide). -/
theorem gcdPatternFree_two_four_three : GcdPatternFree 3 ({2, 4, 3} : Finset ℕ) := by
  intro S hS hequal
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  have hEq : S = ({2, 4, 3} : Finset ℕ) :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  subst S
  obtain ⟨d, hd⟩ := hequal
  have h24 : Nat.gcd 2 4 = d := hd 2 (by simp) 4 (by simp) (by decide)
  have h23 : Nat.gcd 2 3 = d := hd 2 (by simp) 3 (by simp) (by decide)
  norm_num at h24 h23
  omega

example : GcdPatternFree 3 ({2, 4, 3} : Finset ℕ) := by
  exact gcdPatternFree_two_four_three

/-- The prime-power layer encoding `n ↦ {(p, j) : p^j ∣ n, j ≥ 1}` as a
    Finset of pairs, realized via `Nat.factorization`. -/
def layerSet (n : ℕ) : Finset (ℕ × ℕ) :=
  n.factorization.support.biUnion
    (fun p => (Finset.Icc 1 (n.factorization p)).image (fun j => (p, j)))

/-- Membership in the layer encoding is exactly a positive exponent bounded by
    the prime factorization at the first coordinate. -/
theorem mem_layerSet (n p j : ℕ) :
    (p, j) ∈ layerSet n ↔ 1 ≤ j ∧ j ≤ n.factorization p := by
  constructor
  · intro h
    obtain ⟨q, hq, himage⟩ := Finset.mem_biUnion.mp h
    obtain ⟨k, hk, hpair⟩ := Finset.mem_image.mp himage
    have hp : q = p := congrArg Prod.fst hpair
    have hj : k = j := congrArg Prod.snd hpair
    subst q
    subst k
    exact Finset.mem_Icc.mp hk
  · intro h
    have hnonzero : n.factorization p ≠ 0 := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finsupp.mem_support_iff.mpr hnonzero, ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr h, rfl⟩

example : layerSet 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨p, j⟩ hmem
  have h := (mem_layerSet 0 p j).mp hmem
  simp only [Nat.factorization_zero, Finsupp.zero_apply] at h
  omega

example : layerSet 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨p, j⟩ hmem
  have h := (mem_layerSet 1 p j).mp hmem
  simp only [Nat.factorization_one, Finsupp.zero_apply] at h
  omega

example : (2, 1) ∈ layerSet 2 := by
  rw [mem_layerSet]
  norm_num

/-- **The encoding lemma** (the audit-promoted reduction; Hrishi et al.
    §2, elementary): `layerSet a ∩ layerSet b = layerSet (gcd a b)`.
    With it, `r` elements with equal pairwise gcds form an `r`-sunflower
    of layer sets (common kernel `layerSet d`), and the repo's
    Erdős–Rado bound applies.  Mathlib: `Nat.factorization_gcd`
    (pointwise min) is the engine.  -- PROVABLE (target; effort S–M). -/
theorem layerSet_inter (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    layerSet a ∩ layerSet b = layerSet (Nat.gcd a b) := by
  ext x
  rcases x with ⟨p, j⟩
  simp only [Finset.mem_inter, mem_layerSet, Nat.factorization_gcd ha hb,
    Finsupp.inf_apply, le_inf_iff]
  tauto

/-- Injectivity of the encoding on positive integers — needed so that
    sunflower cardinality bounds transfer back to `f_r(N)`.
    -- PROVABLE (factorization determines n). -/
theorem layerSet_injective :
    Set.InjOn layerSet {n : ℕ | n ≠ 0} := by
  intro a ha b hb hab
  apply Nat.factorization_inj ha hb
  apply Finsupp.ext
  intro p
  have hle : ∀ x y : ℕ, layerSet x = layerSet y →
      x.factorization p ≤ y.factorization p := by
    intro x y hxy
    by_cases hzero : x.factorization p = 0
    · simp [hzero]
    · have hpos : 1 ≤ x.factorization p := Nat.one_le_iff_ne_zero.mpr hzero
      have hmem : (p, x.factorization p) ∈ layerSet x :=
        (mem_layerSet x p _).mpr ⟨hpos, le_rfl⟩
      rw [hxy] at hmem
      exact ((mem_layerSet y p _).mp hmem).2
  exact Nat.le_antisymm (hle a b hab) (hle b a hab.symm)

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
