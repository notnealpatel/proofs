/-
  Erdős Problem #1020 — the Erdős matching conjecture.
  Status: falsifiable (open in general; r = 3 solved).  Tier UB archive
  target.

  Verbatim statement (`goof erdos fetch 1020`, pulled 2026-08-05):

    "Let $f(n;r,k)$ be the maximal number of edges in an $r$-uniform
    hypergraph which contains no set of $k$ many independent edges.

    For all $r\geq 3$,
    \[f(n;r,k)=\max\left(\binom{rk-1}{r},
      \binom{n}{r}-\binom{n-k+1}{r}\right).\]"

  DB remarks: r = 2 is Erdős–Gallai (also via EKR).  The two extremal
  families: all r-edges on rk−1 vertices; all r-edges meeting a fixed
  (k−1)-set.  Frankl [Fr87]: f(n;r,k) ≤ (k−1)·C(n−1, r−1).  Known
  ranges: trivial for n < kr; n = kr (Kleitman); Frankl [Fr17]
  kr ≤ n ≤ k(r + 1/(2r^{2r+1})); Kolupaev–Kupavskii; and for large n:
  Erdős [Er65d], Bollobás–Daykin–Erdős (n ≥ 2kr³), Huang–Loh–Sudakov
  (n ≥ 3kr²), Frankl–Łuczak–Mieczkowska, Łuczak–Mieczkowska (r = 3 all
  k).  Comments: FLMW26 (arXiv:2602.19230) r = 4, n ≥ 5(k−1); a Feb
  2026 claimed full proof (Mishra) has an identified fatal error
  (StijnC found the Lemma 4 counterexample) — the problem remains
  open.

  Formalization: hypergraph = `Finset (Finset (Fin n))` with all
  members of size r (repo convention, cf. Erdos20/Erdos857); "k
  independent edges" = k pairwise-disjoint members ("matching of size
  k").

  Mathlib inventory: `Finset.powersetCard`, `Set.Pairwise… `/
  `Finset.card`; no hypergraph matching layer (fresh defs below).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1020

/-- `HasMatching H k`: the family `H` contains `k` pairwise-disjoint
    edges. -/
def HasMatching {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (k : ℕ) : Prop :=
  ∃ S ⊆ H, S.card = k ∧ ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f

/-- `matchingNumberMax n r k`: the maximal number of edges of an
    `r`-uniform hypergraph on `Fin n` with no matching of size `k` —
    the `f(n; r, k)` of the problem (classical sup over a decidable-ish
    family; stated with classical choice). -/
open scoped Classical in
noncomputable def matchingNumberMax (n r k : ℕ) : ℕ :=
  Finset.sup
    (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter
      (fun H => ¬ HasMatching H k))
    Finset.card

/-- Ground truth, r = 2, k = 2 (no two disjoint edges in a graph on 4
    vertices): the triangle (3 edges) is optimal, and
    max(C(3,2), C(4,2) − C(3,2)) = max(3, 3) = 3.
    -- PROVABLE (decide). -/
example : matchingNumberMax 4 2 2 = 3 := by
  sorry

/-- **Erdős #1020, the Erdős matching conjecture (OPEN for r ≥ 4 in
    full)**: for `r ≥ 3`, `k ≥ 1`, and `n ≥ r`,
    `f(n;r,k) = max(C(rk−1, r), C(n,r) − C(n−k+1, r))`.

    Source text as displayed above.  ℕ-subtraction guards: for
    `n + 1 ≤ r + k` the second operand degenerates — the DB implicitly
    assumes `n ≥ rk` territory where both binomials are honest; we
    hypothesize `k ≤ n` so `n − k + 1 = n + 1 − k` is exact, and state
    the subtraction on the ℕ-binomials directly (both terms are
    genuine counts: the second is #edges meeting a fixed (k−1)-set).
    Archived; the shifting/absorption proofs are out of reach
    (candidates audit demoted from UA). -/
theorem erdos_matching_conjecture (n r k : ℕ) (hr : 3 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hrn : r ≤ n) :
    matchingNumberMax n r k =
      max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) := by
  sorry

/-- **The two extremal families are exact**, lower-bound slice — the
    formalizable fragment flagged in the candidates doc:
    (a) all `r`-subsets of an `(rk−1)`-set have no `k`-matching and
        there are `C(rk−1, r)` of them;
    (b) all `r`-subsets of `Fin n` meeting `{0, …, k−2}` have no
        `k`-matching and there are `C(n,r) − C(n−k+1, r)` of them.
    Both are pigeonhole + binomial identities.  -- PROVABLE (target,
    effort S–M each). -/
theorem lower_bound_clique_family (n r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (h : r * k - 1 ≤ n) :
    (r * k - 1).choose r ≤ matchingNumberMax n r k := by
  sorry

theorem lower_bound_star_family (n r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hrn : r ≤ n) :
    n.choose r - (n - k + 1).choose r ≤ matchingNumberMax n r k := by
  sorry

/-- **Frankl's bound** ([Fr87]), archived:
    `f(n;r,k) ≤ (k−1)·C(n−1, r−1)`.  The re-entry point if the repo
    ever ports Erdos20-style compression to matchings. -/
theorem frankl_bound (n r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hrn : r ≤ n) :
    matchingNumberMax n r k ≤ (k - 1) * (n - 1).choose (r - 1) := by
  sorry

/-- **Łuczak–Mieczkowska** ([LuMi14]), archived: the conjecture holds
    for `r = 3` and all `k` (with `n` in the honest range). -/
theorem luczak_mieczkowska (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hrn : 3 ≤ n) :
    matchingNumberMax n 3 k =
      max ((3 * k - 1).choose 3) (n.choose 3 - (n - k + 1).choose 3) := by
  sorry

end ErdosCandidates.E1020

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - Arithmetic: max(C(3,2), C(4,2)-C(3,2)) = max(3,3) = 3. Correct.
   - N-subtraction guards: rk >= 3 so rk-1 >= 2 OK; hkn : k <= n guards n-k+1. Sound.
   - Mishra claimed-proof rejection: DB confirms StijnC found Lemma 4
     counterexample (post-4231, 07 Feb 2026). File attribution accurate.
   - FLMW26 (r=4, n >= 5(k-1)) matches DB comment (post-4431).
   - Luczak-Mieczkowska r=3 all k: matches DB sections.
   - Frankl bound (k-1)*C(n-1,r-1): matches DB sections.
-/
