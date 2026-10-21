/-
  Erdős Problem #548 — the Erdős–Sós conjecture on trees.
  Status: falsifiable (open).  Tier UB archive target.

  Verbatim statement (`goof erdos fetch 548`, pulled 2026-08-05):

    "Let $n\geq k+1$. Every graph on $n$ vertices with at least
    $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices."

  DB remarks: Erdős–Sós; the companion forest version has threshold
  max(C(2k−1,2)+1, (k−1)n−(k−1)²+C(k−1,2)+1) (Erdős–Gallai for k
  independent edges).  [Er78]: trivial for stars; Erdős–Gallai proved
  the path case.  Easy: n(k−1)+1 edges force every tree on k+1
  vertices.  Partial: girth ≥ 5 hosts (Brandt–Dobson), C₄-free hosts
  (Saclé–Woźniak), complement variants, K_{2,s}-free hosts (Haxell;
  Balasubramanian–Dobson), spiders (Fan–Hong–Liu), k ≤ 9
  (Eaton–Tiner; Tiner–Tomlin), n ∈ {k, …, k+4} hosts.  An announced
  Ajtai–Komlós–Simonovits–Szemerédi proof for large k remains
  unpublished.

  Mathlib inventory: `SimpleGraph.IsTree`, `SimpleGraph.Free`
  (`¬ A ⊑ B`; `A ⊑ B` = A has a copy in B — so "G contains every
  tree" is `T ⊑ G` for all trees T), `edgeFinset.card`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E548

open SimpleGraph

/-- `ContainsAllTrees G k`: `G` contains (a copy of) every tree on
    `k + 1` vertices. -/
def ContainsAllTrees {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T ⊑ G

/-- Ground truth: `K₄` contains both trees on 3 vertices... there is
    only one tree shape on 3 vertices (the path); on 4 vertices there
    are two (path, star) — `K₄` contains all of them (k = 3).
    -- PROVABLE (explicit embeddings). -/
theorem completeGraph_four_containsAllTrees :
    ContainsAllTrees (⊤ : SimpleGraph (Fin 4)) 3 := by
  intro T _hT
  refine ⟨{
    toHom := {
      toFun := id
      map_rel' := ?_ }
    injective' := Function.injective_id }⟩
  intro a b hab
  exact (SimpleGraph.top_adj a b).mpr hab.ne

example : ContainsAllTrees (⊤ : SimpleGraph (Fin 4)) 3 :=
  completeGraph_four_containsAllTrees

/-- **Erdős #548, the Erdős–Sós conjecture (OPEN)**: every graph on
    `n ≥ k + 1` vertices with more than `(k−1)n/2` edges contains every
    tree on `k + 1` vertices.

    Source text: "Every graph on $n$ vertices with at least
    $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices."
    Encoded division-free: `(k−1)·n < 2·#edges`, i.e. "#edges >
    (k−1)n/2" — the standard literature form of Erdős–Sós.  Parity
    note (review-corrected): when `(k−1)n` is odd this is ONE EDGE
    WEAKER as a hypothesis than the DB's literal "≥ (k−1)n/2 + 1"
    (which over-rounds); the statement here is the stronger claim and
    is the one the extremal witnesses (disjoint K_k's) are tight
    against.  Archived — serious extremal graph theory; the provable
    fragments are below. -/
theorem erdos_sos (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < 2 * G.edgeFinset.card) :
    ContainsAllTrees G k := by
  sorry

/-- Removing a vertex `v` from `insert v S` lowers the in-set degree sum
    `∑_{w ∈ S} |N(w) ∩ S|` (twice the edge count of `G[S]`) by twice the
    number of neighbours of `v` in `S`. -/
private lemma sum_card_filter_adj_insert {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : V) (hv : v ∉ S) :
    ∑ w ∈ insert v S, ((insert v S).filter (G.Adj w)).card =
      ∑ w ∈ S, (S.filter (G.Adj w)).card + 2 * (S.filter (G.Adj v)).card := by
  rw [Finset.sum_insert hv]
  have h1 : (insert v S).filter (G.Adj v) = S.filter (G.Adj v) := by
    rw [Finset.filter_insert, if_neg G.irrefl]
  have h2 : ∀ w ∈ S, ((insert v S).filter (G.Adj w)).card =
      (S.filter (G.Adj w)).card + if G.Adj w v then 1 else 0 := by
    intro w _hw
    rw [Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      simp [hv]
    · rfl
  have h3 : (S.filter fun w => G.Adj w v).card = (S.filter (G.Adj v)).card := by
    congr 1
    ext w
    simp [G.adj_comm]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, h3]
  ring

/-- **k-core extraction**: if the in-set degree sum of `S` exceeds
    `2(k−1)|S|`, then some nonempty `T ⊆ S` has every vertex with at least
    `k` neighbours inside `T`. -/
private lemma exists_core {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (S : Finset V) (hS : 2 * (k - 1) * S.card < ∑ w ∈ S, (S.filter (G.Adj w)).card) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T, k ≤ (T.filter (G.Adj v)).card := by
  induction S using Finset.strongInduction with
  | H S ih =>
  by_cases hall : ∀ v ∈ S, k ≤ (S.filter (G.Adj v)).card
  · refine ⟨S, subset_rfl, ?_, hall⟩
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hS
  · push Not at hall
    obtain ⟨v, hvS, hv⟩ := hall
    have hvS' : v ∉ S.erase v := Finset.notMem_erase v S
    have hid := sum_card_filter_adj_insert G (S.erase v) v hvS'
    rw [Finset.insert_erase hvS] at hid
    have hdeg : ((S.erase v).filter (G.Adj v)).card ≤ (S.filter (G.Adj v)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v S))
    have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hvS
    have hprod : 2 * (k - 1) * S.card = 2 * (k - 1) * (S.erase v).card + 2 * (k - 1) := by
      rw [← hcard]
      ring
    obtain ⟨T, hTsub, hTne, hT⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) (by omega)
    exact ⟨T, hTsub.trans (Finset.erase_subset v S), hTne, hT⟩

/-- In a tree, a vertex `a` has at most one neighbour one step closer to a
    fixed root `r`. -/
private lemma isTree_parent_unique {W : Type*} {T : SimpleGraph W} (hT : T.IsTree) (r : W)
    {a b b' : W} (hb : T.Adj a b) (hb' : T.Adj a b') (hd : T.dist r b + 1 = T.dist r a)
    (hd' : T.dist r b' + 1 = T.dist r a) : b = b' := by
  classical
  obtain ⟨q, hq, hql⟩ := (hT.connected r a).exists_path_of_dist
  have key : ∀ c, T.Adj a c → T.dist r c + 1 = T.dist r a → c = q.penultimate := by
    intro c hc hdc
    obtain ⟨p, hp, hpl⟩ := (hT.connected r c).exists_path_of_dist
    have ha : a ∉ p.support := by
      intro ha
      have h1 : (p.takeUntil a ha).length ≤ p.length := p.length_takeUntil_le_length ha
      have h2 : T.dist r a ≤ (p.takeUntil a ha).length := SimpleGraph.dist_le _
      omega
    have hc' : c ∈ q.support :=
      hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hc ha
    exact hT.isAcyclic.eq_penultimate_of_adj_end hq hc hc'
  rw [key b hb hd, key b' hb' hd']

/-- Every nonempty vertex set `A` of a tree contains a vertex with at most
    one neighbour in `A` (take a vertex of `A` farthest from a root). -/
private lemma isTree_exists_le_one_nbr {W : Type*} {T : SimpleGraph W} (hT : T.IsTree)
    (A : Finset W) (hA : A.Nonempty) :
    ∃ a ∈ A, ∀ b ∈ A, ∀ b' ∈ A, T.Adj a b → T.Adj a b' → b = b' := by
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨a, haA, hmax⟩ := A.exists_max_image (T.dist r) hA
  refine ⟨a, haA, fun b hbA b' hb'A hb hb' => ?_⟩
  have hpar : ∀ c ∈ A, T.Adj a c → T.dist r c + 1 = T.dist r a := by
    intro c hcA hc
    have hle := hmax c hcA
    rcases hT.dist_eq_dist_add_one_of_adj r hc with h | h <;> omega
  exact isTree_parent_unique hT r hb hb' (hpar b hbA hb) (hpar b' hb'A hb')

/-- **Greedy embedding**: if every nonempty vertex set of `T` has a vertex
    with at most one neighbour in it, and `S` is a nonempty vertex set of
    `G` in which every vertex has at least `k` neighbours, then every
    set `A` of at most `k + 1` vertices of `T` maps injectively into `S`,
    sending `T`-edges inside `A` to `G`-edges. -/
private lemma greedy_embed {W V : Type*} [DecidableEq W] [DecidableEq V] {T : SimpleGraph W}
    {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ)
    (hD : ∀ A : Finset W, A.Nonempty →
      ∃ a ∈ A, ∀ b ∈ A, ∀ b' ∈ A, T.Adj a b → T.Adj a b' → b = b')
    (S : Finset V) (hSne : S.Nonempty) (hS : ∀ v ∈ S, k ≤ (S.filter (G.Adj v)).card)
    (A : Finset W) (hAcard : A.card ≤ k + 1) :
    ∃ f : W → V, (∀ a ∈ A, f a ∈ S) ∧ Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, T.Adj a b → G.Adj (f a) (f b) := by
  obtain ⟨s₀, hs₀⟩ := hSne
  have hScard : k + 1 ≤ S.card := by
    have hsub : insert s₀ (S.filter (G.Adj s₀)) ⊆ S :=
      Finset.insert_subset hs₀ (Finset.filter_subset _ _)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp)] at hle
    have hk₀ := hS s₀ hs₀
    omega
  induction A using Finset.strongInduction with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨fun _ => s₀, by simp, by simp, by simp⟩
  obtain ⟨a, haA, huniq⟩ := hD A hAne
  have hmem : ∀ x ∈ A, x ≠ a → x ∈ A.erase a := fun x hx hxa => Finset.mem_erase.mpr ⟨hxa, hx⟩
  have hA'card : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one haA
  obtain ⟨f', hf'S, hf'inj, hf'hom⟩ := ih (A.erase a) (Finset.erase_ssubset haA) (by omega)
  have hUcard : ((A.erase a).image f').card ≤ k := Finset.card_image_le.trans (by omega)
  obtain ⟨s, hsS, hsU, hsadj⟩ : ∃ s ∈ S, s ∉ (A.erase a).image f' ∧
      ∀ b ∈ A.erase a, T.Adj a b → G.Adj s (f' b) := by
    by_cases hb : ∃ b ∈ A.erase a, T.Adj a b
    · obtain ⟨b, hbA', hab⟩ := hb
      have hfb : f' b ∈ S := hf'S b hbA'
      have hnot : ¬ (S.filter (G.Adj (f' b)) ⊆ (A.erase a).image f') := by
        intro hsub
        have hsub' : S.filter (G.Adj (f' b)) ⊆ ((A.erase a).image f').erase (f' b) := by
          intro x hx
          refine Finset.mem_erase.mpr ⟨?_, hsub hx⟩
          rintro rfl
          simp at hx
        have h1 := Finset.card_le_card hsub'
        have h2 : (((A.erase a).image f').erase (f' b)).card + 1 = ((A.erase a).image f').card :=
          Finset.card_erase_add_one (Finset.mem_image_of_mem f' hbA')
        have h3 := hS (f' b) hfb
        omega
      obtain ⟨s, hs, hsU⟩ := Finset.not_subset.mp hnot
      rw [Finset.mem_filter] at hs
      refine ⟨s, hs.1, hsU, fun b' hb'A' hab' => ?_⟩
      have hbb : b' = b :=
        huniq b' (Finset.mem_of_mem_erase hb'A') b (Finset.mem_of_mem_erase hbA') hab' hab
      rw [hbb]
      exact hs.2.symm
    · push Not at hb
      have hnot : ¬ (S ⊆ (A.erase a).image f') := fun hsub => by
        have hle := Finset.card_le_card hsub
        omega
      obtain ⟨s, hs, hsU⟩ := Finset.not_subset.mp hnot
      exact ⟨s, hs, hsU, fun b hbA' hab => absurd hab (hb b hbA')⟩
  refine ⟨Function.update f' a s, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxa : x = a
    · rw [hxa, Function.update_self]
      exact hsS
    · rw [Function.update_of_ne hxa]
      exact hf'S x (hmem x hx hxa)
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    by_cases hxa : x = a <;> by_cases hya : y = a
    · rw [hxa, hya]
    · rw [hxa, Function.update_self, Function.update_of_ne hya] at hxy
      exact absurd (hxy ▸ Finset.mem_image_of_mem f' (hmem y hy hya)) hsU
    · rw [hya, Function.update_self, Function.update_of_ne hxa] at hxy
      exact absurd (hxy ▸ Finset.mem_image_of_mem f' (hmem x hx hxa)) hsU
    · rw [Function.update_of_ne hxa, Function.update_of_ne hya] at hxy
      exact hf'inj (Finset.mem_coe.mpr (hmem x hx hxa)) (Finset.mem_coe.mpr (hmem y hy hya)) hxy
  · intro x hx y hy hxy
    by_cases hxa : x = a <;> by_cases hya : y = a
    · rw [hxa, hya] at hxy
      exact absurd hxy T.irrefl
    · rw [hxa] at hxy ⊢
      rw [Function.update_self, Function.update_of_ne hya]
      exact hsadj y (hmem y hy hya) hxy
    · rw [hya] at hxy ⊢
      rw [Function.update_self, Function.update_of_ne hxa]
      exact (hsadj x (hmem x hx hxa) hxy.symm).symm
    · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
      exact hf'hom x (hmem x hx hxa) y (hmem y hy hya) hxy

/-- **The easy bound** (DB: "easily proved by induction"): `n(k−1)+1`
    edges suffice — i.e. `(k−1)·n < #edges` forces every tree on
    `k+1` vertices.  The genuine first target: induction extracting a
    min-degree-≥ k subgraph (a graph with > n(k−1) edges has a
    subgraph of min degree ≥ k, which greedily embeds every tree on
    k+1 vertices).  Mathlib: `SimpleGraph.minDegree`, greedy embedding
    by strong induction.  Effort M. -/
theorem easy_double_bound (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < G.edgeFinset.card) :
    ContainsAllTrees G k := by
  classical
  intro T hT
  have hdeg : ∑ v, (Finset.univ.filter (G.Adj v)).card = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  have hcore : 2 * (k - 1) * (Finset.univ : Finset (Fin n)).card <
      ∑ v, (Finset.univ.filter (G.Adj v)).card := by
    rw [hdeg, Finset.card_univ, Fintype.card_fin, mul_assoc]
    omega
  obtain ⟨S, -, hSne, hS⟩ := exists_core G k Finset.univ hcore
  obtain ⟨f, -, hinj, hhom⟩ := greedy_embed k
    (fun A hA => isTree_exists_le_one_nbr hT A hA) S hSne hS Finset.univ (by simp)
  exact ⟨{
    toHom := {
      toFun := f
      map_rel' := fun {a b} hab => hhom a (Finset.mem_univ a) b (Finset.mem_univ b) hab }
    injective' := fun x y hxy =>
      hinj (Finset.mem_coe.mpr (Finset.mem_univ x)) (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy }⟩

/-- **The path case (Erdős–Gallai)**, archived-but-plausible: with
    more than `(k−1)n/2` edges, `G` contains the path on `k + 1`
    vertices.  This is the classical Erdős–Gallai path theorem — the
    natural provable slice (effort M–L; the standard proof is a
    longest-path/rotation argument).  `pathGraph (k+1)` is Mathlib's
    path graph. -/
theorem erdos_gallai_path (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < 2 * G.edgeFinset.card) :
    pathGraph (k + 1) ⊑ G := by
  sorry

/-- Sharpness sanity: the threshold is tight — a disjoint union of
    `K_k`'s has exactly `(k−1)n/2` edges and contains no tree on
    `k + 1` vertices (every component has only k vertices).  Stated at
    the smallest instance `n = k` (a single `K_k`):
    `K_k` has `(k−1)k/2` edges and no tree on `k+1` vertices embeds.
    -- PROVABLE (embedding would need k+1 distinct vertices). -/
theorem sharpness_kk (k : ℕ) (hk : 1 ≤ k) :
    2 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card = (k - 1) * k ∧
    ¬ ContainsAllTrees (⊤ : SimpleGraph (Fin k)) k := by
  constructor
  · rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    have hcount := Nat.add_one_mul_choose_eq (k - 1) 1
    simpa [Nat.sub_add_cancel hk, Nat.choose_one_right, Nat.mul_comm] using hcount.symm
  · intro hcontains
    obtain ⟨copy⟩ := hcontains (starGraph (0 : Fin (k + 1)))
      (SimpleGraph.isTree_starGraph _)
    have hcard : k + 1 ≤ k := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective copy.toHom copy.injective
    omega

end ErdosCandidates.E548

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - FLAG (parity): the division-free encoding `(k-1)*n < 2*edges`
     is equivalent to "more than (k-1)n/2 edges", which matches the
     standard Erdos-Sos conjecture. However, the DB literally says
     "at least (k-1)n/2 + 1 edges". When (k-1)n is odd these differ:
     the file accepts one fewer edge (e.g. k=2 n=3: file needs >= 2
     edges, DB literal needs >= 3). The file's comment "the strict
     form is the faithful reading ... for all parities" is incorrect
     against the literal DB text. The file's theorem is STRONGER
     (weaker hypothesis) than the DB statement for odd (k-1)n.
     Mathematically the standard conjecture IS "more than (k-1)n/2"
     and the file's encoding is the standard one; the DB's "+1" is
     redundant for even parity and overly strong for odd parity.
     Recommend: either tighten to `(k-1)*n + 1 < 2*edges` for literal
     fidelity, or explicitly note the strengthening in the comment.
   - Attributions: Erdos-Gallai path case, Brandt-Dobson girth >= 5,
     Haxell/Balasubramanian-Dobson K_{2,s}-free, Fan-Hong-Liu spiders,
     Eaton-Tiner k <= 8, Tiner-Tomlin k = 9, AKSS announced proof --
     all confirmed against DB comments.
   - Sharpness example (disjoint K_k): correct, extremal has (k-1)k/2
     edges per copy.
-/
