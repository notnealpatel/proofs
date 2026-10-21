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

/-- `circleArc r t`: the cyclic arc `{t, t+1, …, t+r-1}` of `Fin n` (addition mod `n`). -/
private def circleArc {n : ℕ} (r : ℕ) (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => (x - t).val < r)

example : circleArc 2 (3 : Fin 5) = {3, 4} := by decide

example : circleArc 2 (4 : Fin 5) = {4, 0} := by decide

/-- A cyclic arc of length `r ≤ n` has exactly `r` points. -/
private lemma card_circleArc {n : ℕ} [NeZero n] (r : ℕ) (hrn : r ≤ n) (t : Fin n) :
    (circleArc r t).card = r := by
  have h : circleArc r t = (circleArc r 0).map (Equiv.addRight t).toEmbedding := by
    ext x
    simp only [circleArc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding, Equiv.coe_addRight, sub_zero]
    constructor
    · intro hx
      exact ⟨x - t, hx, sub_add_cancel x t⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h, Finset.card_map]
  have h0 : circleArc r (0 : Fin n) = Finset.univ.filter (fun x : Fin n => x.val < r) := by
    ext x
    simp [circleArc]
  rw [h0, Fin.card_filter_val_lt]
  omega

/-- Arcs starting at `a < b` are disjoint when `b - a` lies in `[r, n - r]`. -/
private lemma disjoint_circleArc {n : ℕ} (r : ℕ) (a b : Fin n) (hab : a < b)
    (h1 : r ≤ b.val - a.val) (h2 : b.val - a.val ≤ n - r) :
    Disjoint (circleArc r a) (circleArc r b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  simp only [circleArc, Finset.mem_filter, Finset.mem_univ, true_and] at hxa hxb
  have hab' : a.val < b.val := hab
  have hxn : x.val < n := x.isLt
  have hbn : b.val < n := b.isLt
  rcases le_or_gt a x with hax | hax <;> rcases le_or_gt b x with hbx | hbx
  · rw [Fin.coe_sub_iff_le.mpr hax] at hxa
    rw [Fin.coe_sub_iff_le.mpr hbx] at hxb
    have : a.val ≤ x.val := hax
    have : b.val ≤ x.val := hbx
    omega
  · rw [Fin.coe_sub_iff_le.mpr hax] at hxa
    rw [Fin.coe_sub_iff_lt.mpr hbx] at hxb
    have : a.val ≤ x.val := hax
    have : x.val < b.val := hbx
    omega
  · exact absurd ((hab.trans_le hbx).trans hax) (lt_irrefl _)
  · rw [Fin.coe_sub_iff_lt.mpr hax] at hxa
    rw [Fin.coe_sub_iff_lt.mpr hbx] at hxb
    have : x.val < a.val := hax
    omega

/-- An order embedding `Fin m ↪o Fin n` spreads indices at least as far apart as they are. -/
private lemma orderEmb_val_add_le {m n : ℕ} (e : Fin m ↪o Fin n) (a b : Fin m) (hab : a ≤ b) :
    (e a).val + (b.val - a.val) ≤ (e b).val := by
  have hsub : (Finset.Icc a b).map e.toEmbedding ⊆ Finset.Icc (e a) (e b) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨e.monotone h1, e.monotone h2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map, Fin.card_Icc, Fin.card_Icc] at hc
  have : a.val ≤ b.val := hab
  have : (e a).val ≤ (e b).val := e.monotone hab
  omega


/-- Two distinct indices below `(s+1)r` in one residue class mod `r` differ by between `r` and `s r`. -/
private lemma residue_gap (r s a b : ℕ) (hr : 1 ≤ r) (hab : a < b) (hb : b < (s + 1) * r)
    (hmod : a % r = b % r) : r ≤ b - a ∧ b - a ≤ s * r := by
  have hdvd : r ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
  have hlow : r ≤ b - a := Nat.le_of_dvd (by omega) hdvd
  have hq : b / r < s + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hb
  have hqb : r * (b / r) ≤ r * s := Nat.mul_le_mul_left r (by omega)
  have hdb := Nat.div_add_mod b r
  have hma : a % r ≤ a := Nat.mod_le a r
  have hrs : r * s = s * r := Nat.mul_comm r s
  omega

/-- Circle lemma: if `n ≥ (s+1)r` and `T ⊆ ℤ/n` has more than `s r` points, then `T` contains
    `s + 1` points pairwise at cyclic distance at least `r` (pairwise disjoint arcs). -/
private lemma exists_separated_of_card_gt (n r s : ℕ) (hr : 1 ≤ r) (hn : (s + 1) * r ≤ n) (T : Finset (Fin n))
    (hT : s * r < T.card) :
    ∃ S ⊆ T, S.card = s + 1 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → r ≤ b.val - a.val ∧ b.val - a.val ≤ n - r := by
  obtain ⟨T₀, hT₀, hT₀c⟩ := Finset.exists_subset_card_eq (s := T) (n := s * r + 1) (by omega)
  obtain ⟨P, hP, hPc⟩ := Finset.exists_superset_card_eq (s := T₀) (n := (s + 1) * r)
    (by rw [hT₀c]; nlinarith) (by simpa using hn)
  set m := (s + 1) * r with hm
  let e : Fin m ↪o Fin n := P.orderEmbOfFin hPc
  let U : Finset (Fin m) := Finset.univ.filter (fun a => e a ∈ T₀)
  have hUc : s * r < U.card := by
    have hsub : T₀ ⊆ U.map e.toEmbedding := by
      intro x hx
      have hxr : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hP hx
      obtain ⟨a, rfl⟩ := hxr
      exact Finset.mem_map.mpr ⟨a, by simp [U, hx], rfl⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_map] at hc
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := U) (t := Finset.range r) (f := fun a : Fin m => a.val % r) (n := s)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    (by rw [Finset.card_range]; rw [Nat.mul_comm]; exact hUc)
  obtain ⟨V, hV, hVc⟩ := Finset.exists_subset_card_eq (n := s + 1) hj
  refine ⟨V.map e.toEmbedding, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have := (Finset.mem_filter.mp (hV ha)).1
    exact hT₀ (Finset.mem_filter.mp this).2
  · rw [Finset.card_map, hVc]
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    have hab : a < b := e.lt_iff_lt.mp hxy
    have hma := (Finset.mem_filter.mp (hV ha)).2
    have hmb := (Finset.mem_filter.mp (hV hb)).2
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) b.isLt
    have hgap := residue_gap r s a.val b.val hr hab (by simpa [hm] using b.isLt)
      (hma.trans hmb.symm)
    have h1 := orderEmb_val_add_le e a b hab.le
    have h2 := orderEmb_val_add_le e ⟨0, hmpos⟩ a (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    have h3 := orderEmb_val_add_le e b ⟨m - 1, by omega⟩ (Fin.le_iff_val_le_val.mpr (by
      have := b.isLt; simp only; omega))
    have h4 := (e ⟨m - 1, by omega⟩).isLt
    have hab' : a.val < b.val := hab
    have hb' : b.val < m := b.isLt
    simp only at h2 h3
    show r ≤ (e b).val - (e a).val ∧ (e b).val - (e a).val ≤ n - r
    have hms : m = s * r + r := by rw [hm]; ring
    constructor <;> omega

/-- Mapping a finset by a product of permutations is iterated mapping. -/
private lemma map_perm_mul {n : ℕ} (C : Finset (Fin n)) (σ π : Equiv.Perm (Fin n)) :
    C.map (σ * π).toEmbedding = (C.map π.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

/-- Mapping a finset by the identity permutation is the identity. -/
private lemma map_perm_one {n : ℕ} (C : Finset (Fin n)) :
    C.map (1 : Equiv.Perm (Fin n)).toEmbedding = C :=
  Finset.map_refl

/-- The number of permutations carrying `B` onto `A` depends only on the common cardinality. -/
private lemma card_perm_map_eq {n : ℕ} (B A B' A' : Finset (Fin n))
    (hBB : B'.card = B.card) (hAA : A.card = A'.card) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => B.map σ.toEmbedding = A).card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => B'.map σ.toEmbedding = A').card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq B' B hBB
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq A A' hAA
  have hτ' : B.map τ⁻¹.toEmbedding = B' := by
    rw [← hτ, ← map_perm_mul, inv_mul_cancel, map_perm_one]
  have hρ' : A'.map ρ⁻¹.toEmbedding = A := by
    rw [← hρ, ← map_perm_mul, inv_mul_cancel, map_perm_one]
  apply Finset.card_bij' (fun σ _ => ρ * σ * τ) (fun σ _ => ρ⁻¹ * σ * τ⁻¹)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [map_perm_mul, map_perm_mul, hτ, hσ, hρ]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [map_perm_mul, map_perm_mul, hτ', hσ, hρ']
  · intro σ _
    group
  · intro σ _
    group

/-- Katona-circle form of Frankl's bound: if `n ≥ (s+1)r`, `r ≥ 1`, and an `r`-uniform family
    on `Fin n` has no `s + 1` pairwise-disjoint members, it has at most `s · C(n-1, r-1)` members. -/
private theorem card_le_of_not_hasMatching (n r s : ℕ) (hr : 1 ≤ r) (hn : (s + 1) * r ≤ n)
    (F : Finset (Finset (Fin n))) (hu : ∀ e ∈ F, e.card = r)
    (hm : ¬ HasMatching F (s + 1)) :
    F.card ≤ s * (n - 1).choose (r - 1) := by
  classical
  have hrn : r ≤ n := le_trans (by nlinarith) hn
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let Tσ : Equiv.Perm (Fin n) → Finset (Fin n) :=
    fun σ => Finset.univ.filter (fun t => (circleArc r t).map σ.toEmbedding ∈ F)
  have hT : ∀ σ, (Tσ σ).card ≤ s * r := by
    intro σ
    by_contra hlt
    obtain ⟨S, hS, hSc, hsep⟩ := exists_separated_of_card_gt n r s hr hn (Tσ σ) (not_le.mp hlt)
    have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        Disjoint ((circleArc r a).map σ.toEmbedding) ((circleArc r b).map σ.toEmbedding) := by
      intro a ha b hb hab
      rw [Finset.disjoint_map]
      rcases lt_or_gt_of_ne hab with h | h
      · obtain ⟨h1, h2⟩ := hsep a ha b hb h
        exact disjoint_circleArc r a b h h1 h2
      · obtain ⟨h1, h2⟩ := hsep b hb a ha h
        exact (disjoint_circleArc r b a h h1 h2).symm
    have hne : ∀ a, ((circleArc r a).map σ.toEmbedding).Nonempty := by
      intro a
      rw [← Finset.card_pos, Finset.card_map, card_circleArc r hrn]
      omega
    have hinj : Set.InjOn (fun a => (circleArc r a).map σ.toEmbedding) S := by
      intro a ha b hb heq
      by_contra hab
      have hd := hdisj a ha b hb hab
      simp only at heq
      rw [heq, disjoint_self] at hd
      exact (hne b).ne_empty hd
    apply hm
    refine ⟨S.image (fun a => (circleArc r a).map σ.toEmbedding), ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp (hS ha)).2
    · rw [Finset.card_image_of_injOn hinj, hSc]
    · intro e he f hf hef
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
      exact hdisj a ha b hb (fun h => hef (h ▸ rfl))
  let B₀ := circleArc r (0 : Fin n)
  let c := (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => B₀.map σ.toEmbedding = B₀).card
  have hcA : ∀ t : Fin n, ∀ A : Finset (Fin n), A.card = r →
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => (circleArc r t).map σ.toEmbedding = A).card = c := by
    intro t A hA
    exact card_perm_map_eq _ _ _ _ (by rw [card_circleArc r hrn, card_circleArc r hrn])
      (by rw [hA, card_circleArc r hrn])
  have hfac : n.factorial = n.choose r * c := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun σ : Equiv.Perm (Fin n) => B₀.map σ.toEmbedding) (s := Finset.univ)
      (t := (Finset.univ : Finset (Fin n)).powersetCard r)
      (by
        intro σ _
        rw [Finset.mem_coe, Finset.mem_powersetCard, Finset.card_map]
        exact ⟨Finset.subset_univ _, card_circleArc r hrn 0⟩)
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
    rw [h, Finset.sum_congr rfl (fun A hA => hcA 0 A (Finset.mem_powersetCard.mp hA).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hinner : ∀ t : Fin n,
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => (circleArc r t).map σ.toEmbedding ∈ F).card =
        F.card * c := by
    intro t
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun σ : Equiv.Perm (Fin n) => (circleArc r t).map σ.toEmbedding) (t := F)
      (by intro σ hσ; exact (Finset.mem_filter.mp hσ).2)]
    rw [Finset.sum_congr rfl (fun A hA => ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.filter_filter]
    rw [← hcA t A (hu A hA)]
    congr 1
    apply Finset.filter_congr
    intro σ _
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hA, h⟩
  have hsum : ∑ σ, (Tσ σ).card = n * (F.card * c) := by
    simp only [Tσ, Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [← Finset.card_filter]
    rw [Finset.sum_congr rfl (fun t _ => hinner t), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hle : ∑ σ, (Tσ σ).card ≤ n.factorial * (s * r) := by
    calc ∑ σ, (Tσ σ).card ≤ ∑ _σ : Equiv.Perm (Fin n), s * r :=
          Finset.sum_le_sum (fun σ _ => hT σ)
      _ = n.factorial * (s * r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            smul_eq_mul]
  have hcpos : 0 < c := by
    have hp := Nat.factorial_pos n
    rw [hfac] at hp
    exact Nat.pos_of_mul_pos_left hp
  have hchoose : n.choose r * r = n * (n - 1).choose (r - 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact (Nat.add_one_mul_choose_eq n' r').symm
  have key : n * F.card * c ≤ n * (s * (n - 1).choose (r - 1)) * c := by
    calc n * F.card * c = ∑ σ, (Tσ σ).card := by rw [hsum]; ring
      _ ≤ n.factorial * (s * r) := hle
      _ = n.choose r * r * s * c := by rw [hfac]; ring
      _ = n * (s * (n - 1).choose (r - 1)) * c := by rw [hchoose]; ring
  have key' := Nat.le_of_mul_le_mul_right key hcpos
  exact Nat.le_of_mul_le_mul_left key' hn0

/-- **Frankl's bound** ([Fr87]), archived:
    `f(n;r,k) ≤ (k−1)·C(n−1, r−1)`.  The re-entry point if the repo
    ever ports Erdos20-style compression to matchings. -/
theorem frankl_bound (n r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hrn : r ≤ n)
    (hrkn : r * k ≤ n) :
    matchingNumberMax n r k ≤ (k - 1) * (n - 1).choose (r - 1) := by
  classical
  unfold matchingNumberMax
  apply Finset.sup_le
  intro H hH
  obtain ⟨hU, hm⟩ := Finset.mem_filter.mp hH
  have hu : ∀ e ∈ H, e.card = r := fun e he =>
    (Finset.mem_powersetCard.mp (Finset.mem_powerset.mp hU he)).2
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have hn : (s + 1) * r ≤ n := by rw [Nat.mul_comm]; exact hrkn
  simpa using card_le_of_not_hasMatching n r s (by omega) hn H hu hm

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
