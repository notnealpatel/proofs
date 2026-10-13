/-
  Erdős Problem #1020 — the Erdős matching conjecture.
  Status: admitted/open in general; r = 3 known in the literature.  Tier UB archive
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

open scoped Classical in
/-- `matchingNumberMax n r k`: the maximal number of edges of an
    `r`-uniform hypergraph on `Fin n` with no matching of size `k` —
    the `f(n; r, k)` of the problem (classical sup over a decidable-ish
    family; stated with classical choice). -/
noncomputable def matchingNumberMax (n r k : ℕ) : ℕ :=
  Finset.sup
    (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter
      (fun H => ¬ HasMatching H k))
    Finset.card

/-- Every admissible uniform family contributes its cardinality to the maximum. -/
theorem card_le_matchingNumberMax {n r k : ℕ} (H : Finset (Finset (Fin n)))
    (hu : ∀ e ∈ H, e.card = r) (hm : ¬ HasMatching H k) :
    H.card ≤ matchingNumberMax n r k := by
  classical
  apply Finset.le_sup
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hm⟩
  intro e he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hu e he⟩

/-- Disjoint edges supported on a finite carrier consume the sum of their sizes. -/
theorem matching_size_le_carrier {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (C : Finset α) (r : ℕ)
    (hc : ∀ e ∈ S, e ⊆ C) (hr : ∀ e ∈ S, e.card = r)
    (hd : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f) :
    S.card * r ≤ C.card := by
  classical
  have hsum : (S.biUnion id).card = S.card * r := by
    rw [Finset.card_biUnion]
    · simp only [id_eq, Finset.sum_congr rfl hr, Finset.sum_const, smul_eq_mul]
    · exact hd
  rw [← hsum]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  exact hc e he hxe

/-- A matching whose edges all meet a carrier has at most as many edges as carrier vertices. -/
theorem matching_card_le_meeting_carrier {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (A : Finset α)
    (hm : ∀ e ∈ S, ¬ Disjoint e A)
    (hd : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f) :
    S.card ≤ A.card := by
  classical
  have hpos : ∀ e ∈ S, 1 ≤ (e ∩ A).card := by
    intro e he
    have hn : (e ∩ A).Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun hz => hm e he (Finset.disjoint_iff_inter_eq_empty.mpr hz))
    exact hn.card_pos
  have hd' : (S : Set (Finset α)).PairwiseDisjoint (fun e => e ∩ A) := by
    intro e he f hf hne
    exact (hd e he f hf hne).mono Finset.inter_subset_left Finset.inter_subset_left
  calc
    S.card = ∑ e ∈ S, 1 := by simp
    _ ≤ ∑ e ∈ S, (e ∩ A).card := Finset.sum_le_sum hpos
    _ = (S.biUnion (fun e => e ∩ A)).card := (Finset.card_biUnion hd').symm
    _ ≤ A.card := Finset.card_le_card (by
      intro x hx
      obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxe).2)

/-- The six two-element subsets of four vertices, displayed in the three complementary pairs. -/
theorem six_edge_universe :
    (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0, 1}, {2, 3}, {0, 2}, {1, 3}, {0, 3}, {1, 2}} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h | h | h | h <;> subst e <;>
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  · rw [Finset.card_powersetCard, Finset.card_fin]
    decide

/-- Complementation pairs the six edges as 01/23, 02/13, and 03/12. -/
theorem six_edge_complement_pairs :
    ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} ∧
    ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} ∧
    ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by
  decide

/-- Two distinct disjoint members witness a two-edge matching. -/
theorem hasMatching_two_of_disjoint {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (e f : Finset α) (he : e ∈ H) (hf : f ∈ H)
    (hne : e ≠ f) (hd : Disjoint e f) : HasMatching H 2 := by
  refine ⟨{e, f}, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  · simp [hne]
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hab rfl).elim

/-- A two-uniform family on four vertices with no two-edge matching has at most three edges. -/
theorem card_le_three_of_no_matching (H : Finset (Finset (Fin 4)))
    (hu : ∀ e ∈ H, e.card = 2) (hm : ¬ HasMatching H 2) : H.card ≤ 3 := by
  classical
  have hd : Disjoint H (H.image (fun e => eᶜ)) := by
    apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hi
    have hef : Disjoint e f := by rw [← hfe]; exact disjoint_compl_left
    have hne : e ≠ f := by
      intro heq
      have hz : e = ∅ := disjoint_self.mp (by simpa only [← heq] using hef)
      have hc := hu e he
      rw [hz, Finset.card_empty] at hc
      omega
    exact hm (hasMatching_two_of_disjoint H e f he hf hne hef)
  have hi : (H.image (fun e => eᶜ)).card = H.card :=
    Finset.card_image_of_injective H compl_injective
  have hsub : H ∪ H.image (fun e => eᶜ) ⊆
      (Finset.univ : Finset (Fin 4)).powersetCard 2 := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hu e he⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_compl, Fintype.card_fin, hu f hf]
  have hsix : ((Finset.univ : Finset (Fin 4)).powersetCard 2).card = 6 := by
    rw [six_edge_universe]
    decide
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hi, hsix] at hcard
  omega

/-- **Erdős #1020, the Erdős matching conjecture (OPEN for r ≥ 4 in
    full)**: for `r ≥ 3`, `k ≥ 1`, and `r * k ≤ n`,
    `f(n;r,k) = max(C(rk−1, r), C(n,r) − C(n−k+1, r))`.

    Source text as displayed above.  ℕ-subtraction guards: for
    `n + 1 ≤ r + k` the second operand degenerates — the DB implicitly
    assumes `n ≥ rk` territory where both binomials are honest; we
    explicitly require `r * k ≤ n` and retain `k ≤ n` so `n − k + 1 = n + 1 − k` is exact, and state
    the subtraction on the ℕ-binomials directly (both terms are
    genuine counts: the second is #edges meeting a fixed (k−1)-set).
    Archived; the shifting/absorption proofs are out of reach
    (candidates audit demoted from UA). -/
theorem erdos_matching_conjecture (n r k : ℕ) (hr : 3 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hrn : r ≤ n) (hrkn : r * k ≤ n) :
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
  classical
  obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := r * k - 1) (by simpa using h)
  have hu : ∀ e ∈ C.powersetCard r, e.card = r := by
    intro e he
    exact (Finset.mem_powersetCard.mp he).2
  have hm : ¬ HasMatching (C.powersetCard r) k := by
    rintro ⟨S, hS, hSk, hd⟩
    have hb := matching_size_le_carrier S C r
      (fun e he => (Finset.mem_powersetCard.mp (hS he)).1)
      (fun e he => hu e (hS he)) hd
    rw [hSk, hcard, Nat.mul_comm k r] at hb
    have hpos : 0 < r * k := Nat.mul_pos (by omega) (by omega)
    omega
  have hb := card_le_matchingNumberMax (C.powersetCard r) hu hm
  simpa only [Finset.card_powersetCard, hcard] using hb

/-- The uniform family meeting a fixed `(k - 1)`-element carrier gives the star binomial lower bound. -/
theorem lower_bound_star_family (n r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hrn : r ≤ n) :
    n.choose r - (n - k + 1).choose r ≤ matchingNumberMax n r k := by
  classical
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := k - 1) (by simp only [Finset.card_fin]; omega)
  let U := (Finset.univ : Finset (Fin n)).powersetCard r
  let B := (Finset.univ : Finset (Fin n)) \ A
  let H := U.filter (fun e => ¬ Disjoint e A)
  have hu : ∀ e ∈ H, e.card = r := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  have hm : ¬ HasMatching H k := by
    rintro ⟨S, hS, hSk, hd⟩
    have hb := matching_card_le_meeting_carrier S A
      (fun e he => (Finset.mem_filter.mp (hS he)).2) hd
    rw [hSk, hcard] at hb
    omega
  have hdiff : H = U \ B.powersetCard r := by
    ext e
    simp only [H, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_powersetCard]
    constructor
    · rintro ⟨he, hn⟩
      refine ⟨he, ?_⟩
      rintro ⟨heb, her⟩
      apply hn
      apply Finset.disjoint_left.mpr
      intro x hx
      exact (Finset.mem_sdiff.mp (heb hx)).2
    · rintro ⟨he, hn⟩
      refine ⟨he, ?_⟩
      intro hd
      apply hn
      refine ⟨?_, (Finset.mem_powersetCard.mp he).2⟩
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_left.mp hd hx⟩
  have hsub : B.powersetCard r ⊆ U := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, (Finset.mem_powersetCard.mp he).2⟩
  have hB : B.card = n - k + 1 := by
    dsimp only [B]
    rw [Finset.card_sdiff_of_subset hA, Finset.card_fin, hcard]
    omega
  have hH : H.card = n.choose r - (n - k + 1).choose r := by
    rw [hdiff, Finset.card_sdiff_of_subset hsub]
    simp only [U, Finset.card_powersetCard, Finset.card_fin, hB]
  rw [← hH]
  exact card_le_matchingNumberMax H hu hm

/-- The triangle lower bound and complementary-pair upper bound give the four-vertex maximum. -/
theorem matchingNumberMax_four_two_two : matchingNumberMax 4 2 2 = 3 := by
  classical
  apply Nat.le_antisymm
  · unfold matchingNumberMax
    apply Finset.sup_le
    intro H hH
    obtain ⟨hU, hm⟩ := Finset.mem_filter.mp hH
    have hu : ∀ e ∈ H, e.card = 2 := by
      intro e he
      exact (Finset.mem_powersetCard.mp (Finset.mem_powerset.mp hU he)).2
    exact card_le_three_of_no_matching H hu hm
  · have hb := lower_bound_clique_family 4 2 2 (by decide) (by decide) (by decide)
    have hchoose : (2 * 2 - 1).choose 2 = 3 := by decide
    simpa only [hchoose] using hb

/-- Ground truth, r = 2, k = 2 (no two disjoint edges in a graph on 4
    vertices): the triangle (3 edges) is optimal, and
    max(C(3,2), C(4,2) − C(3,2)) = max(3, 3) = 3.
    -- PROVABLE (decide). -/
example : matchingNumberMax 4 2 2 = 3 := by
  exact matchingNumberMax_four_two_two

/-- **Frankl's bound** ([Fr87]), archived:
    `f(n;r,k) ≤ (k−1)·C(n−1, r−1)`.  The re-entry point if the repo
    ever ports Erdos20-style compression to matchings. -/
theorem frankl_bound (n r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hrn : r ≤ n)
    (hrkn : r * k ≤ n) :
    matchingNumberMax n r k ≤ (k - 1) * (n - 1).choose (r - 1) := by
  sorry

/-- **Łuczak–Mieczkowska** ([LuMi14]), archived: the conjecture holds
    for `r = 3` and all `k` (with `n` in the honest range). -/
theorem luczak_mieczkowska (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hrn : 3 ≤ n) (h3kn : 3 * k ≤ n) :
    matchingNumberMax n 3 k =
      max ((3 * k - 1).choose 3) (n.choose 3 - (n - k + 1).choose 3) := by
  sorry

example : HasMatching ({{0}, {1}} : Finset (Finset (Fin 2))) 2 := by
  exact hasMatching_two_of_disjoint _ {0} {1} (by simp) (by simp)
    (by decide) (by decide)

example : ∃ H : Finset (Finset (Fin 4)), H.Nonempty ∧
    (∀ e ∈ H, e.card = 2) ∧ ¬ HasMatching H 2 := by
  refine ⟨{{0, 1}}, by simp, ?_, ?_⟩
  · intro e he
    have heq : e = {0, 1} := Finset.mem_singleton.mp he
    rw [heq]
    decide
  · rintro ⟨S, hS, hcard, hd⟩
    have hb := Finset.card_le_card hS
    simp only [Finset.card_singleton, hcard] at hb
    omega

example : ∃ S : Finset (Finset (Fin 2)), ∃ A : Finset (Fin 2),
    S.Nonempty ∧ A.Nonempty ∧
    (∀ e ∈ S, e ⊆ A) ∧ (∀ e ∈ S, e.card = 1) ∧
    (∀ e ∈ S, ¬ Disjoint e A) ∧
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f) := by
  refine ⟨{{0}}, {0}, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro e he
    have heq : e = {0} := Finset.mem_singleton.mp he
    simp [heq]
  · intro e he
    have heq : e = {0} := Finset.mem_singleton.mp he
    simp [heq]
  · intro e he
    have heq : e = {0} := Finset.mem_singleton.mp he
    simp [heq]
  · intro e he f hf hne
    have heq : e = {0} := Finset.mem_singleton.mp he
    have hfq : f = {0} := Finset.mem_singleton.mp hf
    exact (hne (heq.trans hfq.symm)).elim

example : (1 ≤ 2) ∧ (1 ≤ 2) ∧ (2 * 2 - 1 ≤ 4) ∧
    (2 ≤ 4) ∧ (2 ≤ 4) := by decide

end ErdosCandidates.E1020

/- REVIEWED STATEMENT REPAIR
   The prior PASS verdict is withdrawn: the old equality and Frankl bound
   omitted the range guard. In particular n=5, r=3, k=2 refutes the old
   Frankl bound (10 > 6). The equality and Frankl bound now require r*k ≤ n;
   the r=3 equality requires 3*k ≤ n. Other guards and lower-family
   statements are unchanged. These repaired statements remain admitted;
   range repair is not a proof of the conjecture or the literature results.
-/
