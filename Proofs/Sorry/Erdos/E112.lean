/-
  Erdős Problem #112 — independent sets versus transitive
  subtournaments in digraphs.
  Status: open.  Tier C infrastructure target (tournament layer).

  Verbatim statement (`goof erdos fetch 112`, pulled 2026-08-05):

    "Let $k=k(n,m)$ be minimal such that any directed graph on $k$
    vertices must contain either an independent set of size $n$ or a
    transitive tournament of size $m$. Determine $k(n,m)$."

  DB remarks (Erdős–Rado [ErRa67]): k(n,m) ≤
  (2^{m-1}(n-1)^m + n - 2)/(2n - 3).  Larson–Mitchell [LaMi97]:
  k(n,3) ≤ n².  Zach Hunter: R(n,m) ≤ k(n,m) ≤ R(n,m,m), so
  k(n,m) ≤ 3^{n+2m}.  The graphs-collection variant replaces
  transitive tournament by directed path; for THAT variant Hunter and
  Steiner have a simple argument giving the vertex-count threshold
  k(n,m) = (n−1)(m−1)+1. The quoted DB value without +1 is not the
  vertex-count threshold: n=m=2 requires two vertices, not one.

  Formalization: a "directed graph" here allows any irreflexive
  relation (edges may go both ways? For Erdős–Rado partition-relation
  provenance the digraph is an arbitrary irreflexive relation;
  independent = no arc either way; transitive tournament = linearly
  ordered subset with all forward arcs).  We use `r : V → V → Prop`
  irreflexive.

  Mathlib inventory (leandoc 2026-08-05): no tournament type
  (leandoc miss "Tournament"); `Digraph` exists in Mathlib
  (Combinatorics/Digraph/Basic) but carries no irreflexivity;
  the ~100-line layer here is the infrastructure contribution.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E112

variable {V : Type*}

/-- `IndepSet r S`: no arc of `r` joins two members of `S` (in either
    direction). -/
def IndepSet (r : V → V → Prop) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ r a b

/-- `TransTournamentOn r s S`: `S` contains a NON-INDUCED transitive
    tournament subgraph on `s` vertices. An injection enumerates `S` and
    requires all forward arcs. Reverse ambient arcs are allowed; the ambient
    digraph need not be a tournament. No induced iff condition is asserted. -/
def TransTournamentOn (r : V → V → Prop) (s : ℕ) (S : Finset V) : Prop :=
  ∃ e : Fin s ↪ V, (∀ i, e i ∈ S) ∧ S.card = s ∧
    ∀ i j : Fin s, i < j → r (e i) (e j)

/-- `RamseyDigraph N n m`: every irreflexive digraph on `N` vertices
    contains an independent `n`-set or a transitive tournament on `m`
    vertices. -/
def RamseyDigraph (N n m : ℕ) : Prop :=
  ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
    (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
    (∃ S : Finset (Fin N), TransTournamentOn r m S)

/-- `kDigraph n m`: the minimal such `N` — the `k(n,m)` of the
    problem.  Nonemptiness of the defining set is the Erdős–Rado
    bound (archived below), so `sInf` is honest modulo that input. -/
noncomputable def kDigraph (n m : ℕ) : ℕ := sInf {N : ℕ | RamseyDigraph N n m}

/-- Any qualifying vertex count is at least the smaller requested size. -/
private theorem min_le_of_ramsey (N n m : ℕ) (h : RamseyDigraph N n m) :
    min n m ≤ N := by
  obtain hind | htour := h (fun _ _ => False) (by simp)
  · obtain ⟨S, hcard, _⟩ := hind
    have hn : n ≤ N := by simpa [hcard] using Finset.card_le_univ S
    exact (min_le_left n m).trans hn
  · obtain ⟨S, e, _, hcard, _⟩ := htour
    have hm : m ≤ N := by simpa [hcard] using Finset.card_le_univ S
    exact (min_le_right n m).trans hm

/-- A single vertex contains a transitive tournament of size one. -/
private theorem ramsey_one_two_one : RamseyDigraph 1 2 1 := by
  intro r hirr
  right
  refine ⟨{0}, Function.Embedding.refl _, ?_, ?_, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  · simp
  · intro i j hij
    have heq : i = j := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hij) heq)

/-- Two vertices either have an arc or form an independent pair. -/
private theorem ramsey_two_two_two : RamseyDigraph 2 2 2 := by
  intro r hirr
  classical
  by_cases h01 : r 0 1
  · right
    refine ⟨Finset.univ, Function.Embedding.refl _, ?_, ?_, ?_⟩
    · intro i
      exact Finset.mem_univ _
    · simp
    · intro i j hij
      have hi : i = 0 := by fin_cases i <;> fin_cases j <;> simp_all
      have hj : j = 1 := by fin_cases i <;> fin_cases j <;> simp_all
      simpa [hi, hj] using h01
  · by_cases h10 : r 1 0
    · right
      refine ⟨Finset.univ, (Equiv.swap (0 : Fin 2) 1).toEmbedding, ?_, ?_, ?_⟩
      · intro i
        exact Finset.mem_univ _
      · simp
      · intro i j hij
        have hi : i = 0 := by fin_cases i <;> fin_cases j <;> simp_all
        have hj : j = 1 := by fin_cases i <;> fin_cases j <;> simp_all
        simpa [hi, hj] using h10
    · left
      refine ⟨Finset.univ, by simp, ?_⟩
      intro a ha b hb
      fin_cases a <;> fin_cases b
      · exact hirr 0
      · exact h01
      · exact h10
      · exact hirr 1

/-- Ground truth at the singleton boundary: `k(2,1) = 1`. -/
theorem kDigraph_two_one : kDigraph 2 1 = 1 := by
  have hmem : 1 ∈ {N : ℕ | RamseyDigraph N 2 1} := ramsey_one_two_one
  have hnonempty : Set.Nonempty {N : ℕ | RamseyDigraph N 2 1} := ⟨1, hmem⟩
  have hupper : kDigraph 2 1 ≤ 1 := Nat.sInf_le hmem
  have hramsey : RamseyDigraph (kDigraph 2 1) 2 1 := Nat.sInf_mem hnonempty
  have hlower := min_le_of_ramsey _ _ _ hramsey
  simpa using Nat.le_antisymm hupper hlower

/-- Ground truth at the first diagonal: `k(2,2) = 2`. -/
theorem kDigraph_two_two : kDigraph 2 2 = 2 := by
  have hmem : 2 ∈ {N : ℕ | RamseyDigraph N 2 2} := ramsey_two_two_two
  have hnonempty : Set.Nonempty {N : ℕ | RamseyDigraph N 2 2} := ⟨2, hmem⟩
  have hupper : kDigraph 2 2 ≤ 2 := Nat.sInf_le hmem
  have hramsey : RamseyDigraph (kDigraph 2 2) 2 2 := Nat.sInf_mem hnonempty
  have hlower := min_le_of_ramsey _ _ _ hramsey
  simpa using Nat.le_antisymm hupper hlower

example : RamseyDigraph 1 2 1 := ramsey_one_two_one
example : RamseyDigraph 2 2 2 := ramsey_two_two_two

/-- List form of a transitive tournament inside `S`: a list of length `m`
    with members in `S`, all of whose forward pairs are arcs. -/
private def HasTT (r : V → V → Prop) (m : ℕ) (S : Finset V) : Prop :=
  ∃ l : List V, l.length = m ∧ (∀ x ∈ l, x ∈ S) ∧ l.Pairwise r

/-- `S` contains an independent subset of size `n`. -/
private def HasIndep (r : V → V → Prop) (n : ℕ) (S : Finset V) : Prop :=
  ∃ T ⊆ S, T.card = n ∧ IndepSet r T

/-- An irreflexive list tournament yields a `TransTournamentOn` witness. -/
private theorem transTournamentOn_of_hasTT [DecidableEq V] {r : V → V → Prop}
    (hirr : ∀ v, ¬ r v v) {m : ℕ} {S : Finset V} (h : HasTT r m S) :
    ∃ T : Finset V, TransTournamentOn r m T := by
  obtain ⟨l, hlen, -, hpw⟩ := h
  subst hlen
  have hnodup : l.Nodup := hpw.imp fun {a b} hab => by
    rintro rfl
    exact hirr a hab
  let e : Fin l.length ↪ V := ⟨l.get, List.nodup_iff_injective_get.mp hnodup⟩
  refine ⟨Finset.univ.map e, e, ?_, ?_, ?_⟩
  · intro i
    exact Finset.mem_map_of_mem e (Finset.mem_univ i)
  · simp
  · intro i j hij
    exact List.pairwise_iff_get.mp hpw i j hij

/-- Subsets of independent sets are independent. -/
private theorem IndepSet.mono {r : V → V → Prop} {S T : Finset V} (hT : T ⊆ S)
    (hS : IndepSet r S) : IndepSet r T :=
  fun a ha b hb => hS a (hT ha) b (hT hb)

/-- Reduction of `RamseyDigraph` to the `Finset`-level dichotomy on `univ`. -/
private theorem ramseyDigraph_of_forall (N n m : ℕ)
    (h : ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
      HasIndep r n Finset.univ ∨ HasTT r m Finset.univ) :
    RamseyDigraph N n m := by
  intro r hirr
  rcases h r hirr with ⟨T, -, hcard, hind⟩ | htt
  · exact Or.inl ⟨T, hcard, hind⟩
  · exact Or.inr (transTournamentOn_of_hasTT hirr htt)

/-- Erdős–Rado recursion, shifted: `erH n k + 1` vertices force an
    independent `n`-set or a transitive tournament on `k + 1` vertices. -/
private def erH (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * (n - 1) * erH n k + (n - 1)

/-- Ground truth for the shifted Erdős–Rado recursion. -/
example : erH 2 0 = 0 ∧ erH 2 1 = 1 ∧ erH 2 2 = 3 ∧ erH 3 2 = 10 := by decide

/-- A maximum-cardinality independent subset of `S` dominates `S`, or `S`
    already has an independent `n`-set. -/
private theorem exists_dominating_indep [DecidableEq V] (r : V → V → Prop)
    (hirr : ∀ v, ¬ r v v) (n : ℕ) (S : Finset V) :
    HasIndep r n S ∨ ∃ I ⊆ S, I.card < n ∧
      ∀ x ∈ S \ I, ∃ v ∈ I, r v x ∨ r x v := by
  classical
  let C := S.powerset.filter (fun T => IndepSet r T)
  have hC : C.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.empty_mem_powerset S, fun a ha => absurd ha (Finset.notMem_empty a)⟩⟩
  obtain ⟨I, hIC, hImax⟩ := Finset.exists_max_image C Finset.card hC
  have hIS : I ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hIC).1
  have hIind : IndepSet r I := (Finset.mem_filter.mp hIC).2
  by_cases hn : n ≤ I.card
  · obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq hn
    exact Or.inl ⟨T, hTI.trans hIS, hTcard, hIind.mono hTI⟩
  · refine Or.inr ⟨I, hIS, by omega, ?_⟩
    intro x hx
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
    have hxI : x ∉ I := (Finset.mem_sdiff.mp hx).2
    by_contra hnone
    push Not at hnone
    have hins : insert x I ∈ C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.insert_subset hxS hIS), ?_⟩
      intro a ha b hb
      rcases Finset.mem_insert.mp ha with hax | ha <;>
        rcases Finset.mem_insert.mp hb with hbx | hb
      · rw [hax, hbx]
        exact hirr x
      · rw [hax]
        exact (hnone b hb).2
      · rw [hbx]
        exact (hnone a ha).1
      · exact hIind a ha b hb
    have hle := hImax _ hins
    rw [Finset.card_insert_of_notMem hxI] at hle
    omega

/-- Erdős–Rado: `erH n k + 1` vertices force an independent `n`-set or a
    transitive tournament on `k + 1` vertices. -/
private theorem erdos_rado_finset [DecidableEq V] (r : V → V → Prop)
    (hirr : ∀ v, ¬ r v v) (n : ℕ) (k : ℕ) :
    ∀ S : Finset V, erH n k + 1 ≤ S.card → HasIndep r n S ∨ HasTT r (k + 1) S := by
  classical
  induction k with
  | zero =>
    intro S hS
    obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by
      have h0 : erH n 0 = 0 := rfl
      omega)
    exact Or.inr ⟨[x], rfl, by simpa using hx, List.pairwise_singleton _ _⟩
  | succ k ih =>
    intro S hS
    rcases exists_dominating_indep r hirr n S with hind | ⟨I, hIS, hIcard, hdom⟩
    · exact Or.inl hind
    set D := S \ I with hD
    let Out : V → Finset V := fun v => D.filter (fun x => r v x)
    let In : V → Finset V := fun v => D.filter (fun x => r x v)
    have hDcard : D.card + I.card = S.card := Finset.card_sdiff_add_card_eq_card hIS
    have hbig : ∃ v ∈ I, erH n k + 1 ≤ (Out v).card ∨ erH n k + 1 ≤ (In v).card := by
      by_contra hsmall
      push Not at hsmall
      have hcover : D ⊆ I.biUnion (fun v => Out v ∪ In v) := by
        intro x hx
        obtain ⟨v, hv, hvx⟩ := hdom x hx
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rcases hvx with hvx | hxv
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hvx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxv⟩)
      have hsum : D.card ≤ I.card * (2 * erH n k) := by
        calc D.card ≤ (I.biUnion (fun v => Out v ∪ In v)).card :=
              Finset.card_le_card hcover
          _ ≤ ∑ v ∈ I, (Out v ∪ In v).card := Finset.card_biUnion_le
          _ ≤ I.card • (2 * erH n k) := by
              refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
              have h1 := hsmall v hv
              have h2 := Finset.card_union_le (Out v) (In v)
              omega
          _ = I.card * (2 * erH n k) := smul_eq_mul _ _
      have hIle : I.card * (2 * erH n k) ≤ (n - 1) * (2 * erH n k) :=
        Nat.mul_le_mul_right _ (by omega)
      have hrec : erH n (k + 1) = 2 * (n - 1) * erH n k + (n - 1) := rfl
      have hassoc : 2 * (n - 1) * erH n k = (n - 1) * (2 * erH n k) := by ring
      omega
    obtain ⟨v, hvI, hv⟩ := hbig
    have hvS : v ∈ S := hIS hvI
    have hOutS : Out v ⊆ S := fun x hx =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
    have hInS : In v ⊆ S := fun x hx =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
    rcases hv with hv | hv
    · rcases ih (Out v) hv with ⟨T, hT, hTcard, hTind⟩ | ⟨l, hlen, hmem, hpw⟩
      · exact Or.inl ⟨T, hT.trans hOutS, hTcard, hTind⟩
      · refine Or.inr ⟨v :: l, by simp [hlen], ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hvS
          · exact hOutS (hmem x hx)
        · exact List.pairwise_cons.mpr
            ⟨fun x hx => (Finset.mem_filter.mp (hmem x hx)).2, hpw⟩
    · rcases ih (In v) hv with ⟨T, hT, hTcard, hTind⟩ | ⟨l, hlen, hmem, hpw⟩
      · exact Or.inl ⟨T, hT.trans hInS, hTcard, hTind⟩
      · refine Or.inr ⟨l ++ [v], by simp [hlen], ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hInS (hmem x hx)
          · rw [List.mem_singleton.mp hx]
            exact hvS
        · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton.mp hb]
          exact (Finset.mem_filter.mp (hmem a ha)).2

/-- Closed form of the Erdős–Rado recursion:
    `(2n − 3)(erH n k + 1) = 2^k (n − 1)^(k+1) + n − 2`, written with
    `n = n' + 2`. -/
private theorem erH_closed (n' k : ℕ) :
    (2 * n' + 1) * (erH (n' + 2) k + 1) = 2 ^ k * (n' + 1) ^ (k + 1) + n' := by
  induction k with
  | zero =>
    simp only [erH]
    ring
  | succ k ih =>
    have hrec : erH (n' + 2) (k + 1) = 2 * (n' + 1) * erH (n' + 2) k + (n' + 1) := rfl
    rw [hrec]
    zify at ih ⊢
    rw [pow_succ 2 k, pow_succ (((n' : ℤ) + 1)) (k + 1)]
    linear_combination (2 * ((n' : ℤ) + 1)) * ih

/-- Larson–Mitchell, `Finset` form: `n²` vertices force an independent
    `n`-set or a transitive triple. -/
private theorem larson_mitchell_finset [DecidableEq V] (r : V → V → Prop)
    (hirr : ∀ v, ¬ r v v) (n : ℕ) (hn : 1 ≤ n) :
    ∀ S : Finset V, n ^ 2 ≤ S.card → HasIndep r n S ∨ HasTT r 3 S := by
  classical
  induction n, hn using Nat.le_induction with
  | base =>
    intro S hS
    obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    refine Or.inl ⟨{x}, by simpa using hx, by simp, ?_⟩
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact hirr x
  | succ n hn ih =>
    intro S hS
    obtain ⟨v, hvS⟩ : S.Nonempty := Finset.card_pos.mp (by nlinarith)
    set D := S.erase v with hD
    let Out := D.filter (fun x => r v x)
    let In := D.filter (fun x => r x v)
    let Non := D.filter (fun x => ¬ r v x ∧ ¬ r x v)
    have hDcard : D.card + 1 = S.card := Finset.card_erase_add_one hvS
    have hDS : D ⊆ S := Finset.erase_subset v S
    have hcover : D ⊆ Out ∪ In ∪ Non := by
      intro x hx
      by_cases h1 : r v x
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hx, h1⟩))
      · by_cases h2 : r x v
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hx, h2⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h1, h2⟩)
    have hDle : D.card ≤ Out.card + In.card + Non.card := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_union_le (Out ∪ In) Non
      have h3 := Finset.card_union_le Out In
      omega
    -- a large independent out- or in-neighbourhood, or an arc inside it
    by_cases hOut : n + 1 ≤ Out.card
    · by_cases harc : ∃ a ∈ Out, ∃ b ∈ Out, r a b
      · obtain ⟨a, ha, b, hb, hab⟩ := harc
        have haS : a ∈ S := hDS (Finset.mem_filter.mp ha).1
        have hbS : b ∈ S := hDS (Finset.mem_filter.mp hb).1
        refine Or.inr ⟨[v, a, b], rfl, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
          exact ⟨⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩, hab⟩
      · push Not at harc
        obtain ⟨T, hTO, hTcard⟩ := Finset.exists_subset_card_eq hOut
        refine Or.inl ⟨T, fun x hx => hDS (Finset.mem_filter.mp (hTO hx)).1, hTcard, ?_⟩
        exact fun a ha b hb => harc a (hTO ha) b (hTO hb)
    by_cases hIn : n + 1 ≤ In.card
    · by_cases harc : ∃ a ∈ In, ∃ b ∈ In, r a b
      · obtain ⟨a, ha, b, hb, hab⟩ := harc
        have haS : a ∈ S := hDS (Finset.mem_filter.mp ha).1
        have hbS : b ∈ S := hDS (Finset.mem_filter.mp hb).1
        refine Or.inr ⟨[a, b, v], rfl, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
          exact ⟨⟨hab, (Finset.mem_filter.mp ha).2⟩, (Finset.mem_filter.mp hb).2⟩
      · push Not at harc
        obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq hIn
        refine Or.inl ⟨T, fun x hx => hDS (Finset.mem_filter.mp (hTI hx)).1, hTcard, ?_⟩
        exact fun a ha b hb => harc a (hTI ha) b (hTI hb)
    -- otherwise the non-neighbourhood has at least `n²` vertices
    have hNon : n ^ 2 ≤ Non.card := by
      have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hNonS : Non ⊆ S := fun x hx => hDS (Finset.mem_filter.mp hx).1
    rcases ih Non hNon with ⟨T, hTN, hTcard, hTind⟩ | ⟨l, hlen, hmem, hpw⟩
    · have hvT : v ∉ T := fun hv =>
        Finset.notMem_erase v S (Finset.mem_filter.mp (hTN hv)).1
      refine Or.inl ⟨insert v T, Finset.insert_subset hvS (hTN.trans hNonS), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hvT, hTcard]
      · intro a ha b hb
        rcases Finset.mem_insert.mp ha with hav | ha <;>
          rcases Finset.mem_insert.mp hb with hbv | hb
        · rw [hav, hbv]
          exact hirr v
        · rw [hav]
          exact (Finset.mem_filter.mp (hTN hb)).2.1
        · rw [hbv]
          exact (Finset.mem_filter.mp (hTN ha)).2.2
        · exact hTind a ha b hb
    · exact Or.inr ⟨l, hlen, fun x hx => hNonS (hmem x hx), hpw⟩

/-- **Erdős #112 (OPEN)**: determine `k(n,m)`.  Archived via the known
    bounds; the determination question has no closed form conjectured
    in the DB.  **Erdős–Rado upper bound** ([ErRa67]), stated
    denominator-cleared: `(2n−3)·k(n,m) ≤ 2^{m−1}(n−1)^m + n − 2`
    (for n, m ≥ 2). -/
theorem erdos_rado_upper (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (2 * n - 3) * kDigraph n m ≤ 2 ^ (m - 1) * (n - 1) ^ m + n - 2 := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hR : RamseyDigraph (erH (n' + 2) j + 1) (n' + 2) (j + 1) :=
    ramseyDigraph_of_forall _ _ _ fun r hirr =>
      erdos_rado_finset r hirr (n' + 2) j Finset.univ (by simp)
  have hk : kDigraph (n' + 2) (j + 1) ≤ erH (n' + 2) j + 1 := Nat.sInf_le hR
  have hcoef : 2 * (n' + 2) - 3 = 2 * n' + 1 := by omega
  have hrhs : 2 ^ (j + 1 - 1) * (n' + 2 - 1) ^ (j + 1) + (n' + 2) - 2 =
      2 ^ j * (n' + 1) ^ (j + 1) + n' := by
    have h1 : n' + 2 - 1 = n' + 1 := by omega
    rw [Nat.add_sub_cancel, h1]
    omega
  rw [hcoef, hrhs, ← erH_closed n' j]
  exact Nat.mul_le_mul_left _ hk

/-- **Larson–Mitchell** ([LaMi97]), archived: `k(n,3) ≤ n²`. -/
theorem larson_mitchell (n : ℕ) (hn : 2 ≤ n) :
    kDigraph n 3 ≤ n ^ 2 := by
  classical
  have hR : RamseyDigraph (n ^ 2) n 3 :=
    ramseyDigraph_of_forall _ _ _ fun r hirr =>
      larson_mitchell_finset r hirr n (by omega) Finset.univ (by simp)
  exact Nat.sInf_le hR

/-- A directed path on `s` vertices in `S`, given by an injection realizing
    consecutive forward arcs. Extra ambient arcs are allowed. -/
def DirPathOn (r : V → V → Prop) (s : ℕ) (S : Finset V) : Prop :=
  ∃ e : Fin s ↪ V, (∀ i, e i ∈ S) ∧ S.card = s ∧
    ∀ i : ℕ, ∀ h : i + 1 < s,
      r (e ⟨i, by omega⟩) (e ⟨i + 1, h⟩)

/-- Adding one arc `(u, v)` to an arc set: a walk of the enlarged relation
    either avoids the new arc, or passes through it, giving walks `x ⇝ u`
    and `v ⇝ y` in the old relation. -/
private theorem transGen_insert_arc [DecidableEq V] {A : Finset (V × V)} {u v x y : V}
    (h : Relation.TransGen (fun a b => (a, b) ∈ insert (u, v) A) x y) :
    Relation.TransGen (fun a b => (a, b) ∈ A) x y ∨
      (Relation.ReflTransGen (fun a b => (a, b) ∈ A) x u ∧
        Relation.ReflTransGen (fun a b => (a, b) ∈ A) v y) := by
  induction h with
  | single hab =>
    rcases Finset.mem_insert.mp hab with heq | hA
    · obtain ⟨hx, hy⟩ := Prod.mk.inj heq
      subst hx hy
      exact Or.inr ⟨.refl, .refl⟩
    · exact Or.inl (.single hA)
  | tail _ hbc ih =>
    rcases Finset.mem_insert.mp hbc with heq | hA
    · obtain ⟨hb, hc⟩ := Prod.mk.inj heq
      subst hb hc
      rcases ih with ih | ⟨hxu, _⟩
      · exact Or.inr ⟨ih.to_reflTransGen, .refl⟩
      · exact Or.inr ⟨hxu, .refl⟩
    · rcases ih with ih | ⟨hxu, hvb⟩
      · exact Or.inl (ih.tail hA)
      · exact Or.inr ⟨hxu, hvb.tail hA⟩

/-- A walk in an acyclic relation repeats no vertex. -/
private theorem nodup_of_isChain_acyclic {R : V → V → Prop}
    (hacyc : ∀ v, ¬ Relation.TransGen R v v) {l : List V} (hl : l.IsChain R) :
    l.Nodup := by
  have hpw : l.Pairwise (Relation.TransGen R) :=
    List.isChain_iff_pairwise.mp (hl.imp fun _ _ h => Relation.TransGen.single h)
  exact hpw.imp fun {a _} hab => by rintro rfl; exact hacyc a hab

/-- A repetition-free walk with at least `m` vertices yields a directed path
    on `m` vertices. -/
private theorem dirPathOn_of_isChain [DecidableEq V] {r : V → V → Prop} {m : ℕ}
    {l : List V} (hl : l.IsChain r) (hnd : l.Nodup) (hlen : m ≤ l.length) :
    ∃ S : Finset V, DirPathOn r m S := by
  have hlen' : (l.take m).length = m := by simp [hlen]
  have hc : (l.take m).IsChain r := hl.take m
  have hnd' : (l.take m).Nodup := hnd.sublist (List.take_sublist m l)
  generalize l.take m = l' at hlen' hc hnd'
  subst hlen'
  let e : Fin l'.length ↪ V := ⟨l'.get, List.nodup_iff_injective_get.mp hnd'⟩
  refine ⟨Finset.univ.map e, e, ?_, ?_, ?_⟩
  · intro i
    exact Finset.mem_map_of_mem e (Finset.mem_univ i)
  · simp
  · intro i hi
    exact hc.getElem i hi

/-- Gallai–Roy pigeonhole form: an irreflexive digraph on more than
    `(n-1)(m-1)` vertices has an independent `n`-set or a directed path on
    `m` vertices. A maximum acyclic arc set `A ⊆ r` is chosen; the longest
    `A`-walk ending at a vertex is strictly increasing along `A`, and every
    other arc of `r` closes an `A`-walk backwards, so its fibres are
    independent. -/
private theorem exists_indep_or_dirPath [Fintype V] [DecidableEq V] (r : V → V → Prop)
    (hirr : ∀ v, ¬ r v v) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : (n - 1) * (m - 1) < Fintype.card V) :
    (∃ S : Finset V, S.card = n ∧ IndepSet r S) ∨ ∃ S : Finset V, DirPathOn r m S := by
  classical
  by_cases hpath : ∃ S : Finset V, DirPathOn r m S
  · exact Or.inr hpath
  left
  let C : Finset (Finset (V × V)) := (Finset.univ : Finset (V × V)).powerset.filter
    (fun A => (∀ p ∈ A, r p.1 p.2) ∧ ∀ w, ¬ Relation.TransGen (fun a b => (a, b) ∈ A) w w)
  have hC : C.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp, ?_⟩⟩
    intro w hw
    obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp hw
    simp at hc
  obtain ⟨A, hAC, hAmax⟩ := Finset.exists_max_image C Finset.card hC
  have hAr : ∀ p ∈ A, r p.1 p.2 := (Finset.mem_filter.mp hAC).2.1
  have hAacyc : ∀ w, ¬ Relation.TransGen (fun a b => (a, b) ∈ A) w w :=
    (Finset.mem_filter.mp hAC).2.2
  -- every arc of `r` outside `A` is closed backwards by an `A`-walk
  have hback : ∀ u v, r u v → (u, v) ∉ A →
      Relation.TransGen (fun a b => (a, b) ∈ A) v u := by
    intro u v huv hA
    by_contra hvu
    have hins : insert (u, v) A ∈ C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact huv
        · exact hAr p hp
      · intro w hw
        rcases transGen_insert_arc hw with hw | ⟨hwu, hvw⟩
        · exact hAacyc w hw
        · rcases Relation.reflTransGen_iff_eq_or_transGen.mp (hvw.trans hwu) with heq | htg
          · rw [heq] at huv
            exact hirr v huv
          · exact hvu htg
    have hle := hAmax _ hins
    rw [Finset.card_insert_of_notMem hA] at hle
    omega
  -- `W v k`: an `A`-walk with `k + 1` vertices ending at `v`, listed backwards
  let W : V → ℕ → Prop := fun v k =>
    ∃ l : List V, l.length = k ∧ (v :: l).IsChain (fun a b => (b, a) ∈ A)
  have hWbound : ∀ v k, W v k → k ≤ m - 2 := by
    rintro v k ⟨l, hlen, hch⟩
    by_contra hk
    apply hpath
    have hch' : (v :: l).reverse.IsChain (fun a b => (a, b) ∈ A) :=
      List.isChain_reverse.mpr hch
    have hchr : (v :: l).reverse.IsChain r := hch'.imp fun a b h => hAr (a, b) h
    exact dirPathOn_of_isChain hchr (nodup_of_isChain_acyclic hAacyc hch')
      (by simp only [List.length_reverse, List.length_cons]; omega)
  let f : V → ℕ := fun v => Nat.findGreatest (W v) (m - 2)
  have hfW : ∀ v, W v (f v) := fun v =>
    Nat.findGreatest_spec (Nat.zero_le _) ⟨[], rfl, List.isChain_singleton v⟩
  have hfle : ∀ v, f v ≤ m - 2 := fun v => Nat.findGreatest_le _
  have hmono : ∀ u v, (u, v) ∈ A → f u < f v := by
    intro u v huv
    obtain ⟨l, hlen, hch⟩ := hfW u
    have hW : W v (f u + 1) := ⟨u :: l, by simp [hlen], List.IsChain.cons_cons huv hch⟩
    exact Nat.lt_of_succ_le (Nat.le_findGreatest (hWbound v _ hW) hW)
  have hmono' : ∀ u v, Relation.TransGen (fun a b => (a, b) ∈ A) u v → f u < f v := by
    intro u v h
    induction h with
    | single h => exact hmono _ _ h
    | tail _ h ih => exact ih.trans (hmono _ _ h)
  have hne : ∀ u v, r u v → f u ≠ f v := by
    intro u v huv
    by_cases hA : (u, v) ∈ A
    · exact (hmono u v hA).ne
    · exact (hmono' v u (hback u v huv hA)).ne'
  -- pigeonhole over the `m - 1` heights
  have hmaps : ∀ v ∈ (Finset.univ : Finset V), f v ∈ Finset.range (m - 1) := fun v _ =>
    Finset.mem_range.mpr (by have := hfle v; omega)
  have hlt : (Finset.range (m - 1)).card * (n - 1) < (Finset.univ : Finset V).card := by
    rw [Finset.card_range, Finset.card_univ, Nat.mul_comm]
    exact hcard
  obtain ⟨y, -, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ.filter fun x => f x = y).card by omega)
  refine ⟨T, hTcard, ?_⟩
  intro a ha b hb hab
  have hfa := (Finset.mem_filter.mp (hT ha)).2
  have hfb := (Finset.mem_filter.mp (hT hb)).2
  exact hne a b hab (hfa.trans hfb.symm)

/-- Lower construction for the path variant: on `N ≤ (n-1)(m-1)` vertices,
    the bidirected disjoint union of the blocks `i / (m-1)` (at most `n - 1`
    blocks of at most `m - 1` vertices each) has no independent `n`-set and
    no directed path on `m` vertices. -/
private theorem exists_bad_digraph (n m N : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hN : N ≤ (n - 1) * (m - 1)) :
    ∃ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) ∧
      (¬ ∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∧
      ¬ ∃ S : Finset (Fin N), DirPathOn r m S := by
  classical
  refine ⟨fun i j => i ≠ j ∧ (i : ℕ) / (m - 1) = (j : ℕ) / (m - 1),
    fun v h => h.1 rfl, ?_, ?_⟩
  · rintro ⟨S, hcard, hind⟩
    have hmaps : ∀ i ∈ S, (i : ℕ) / (m - 1) ∈ Finset.range (n - 1) := by
      intro i _
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul (by omega)]
      exact lt_of_lt_of_le i.2 hN
    have hlt : (Finset.range (n - 1)).card < S.card := by
      rw [Finset.card_range, hcard]
      omega
    obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    exact hind a ha b hb ⟨hab, heq⟩
  · rintro ⟨S, e, -, -, hpath⟩
    have hblock : ∀ i : Fin m, ((e i : Fin N) : ℕ) / (m - 1) =
        ((e ⟨0, by omega⟩ : Fin N) : ℕ) / (m - 1) := by
      rintro ⟨i, hi⟩
      induction i with
      | zero => rfl
      | succ i ih => exact ((hpath i hi).2).symm.trans (ih (by omega))
    have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        ((e i : Fin N) : ℕ) % (m - 1) ∈ Finset.range (m - 1) := fun i _ =>
      Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
    have hlt : (Finset.range (m - 1)).card < (Finset.univ : Finset (Fin m)).card := by
      rw [Finset.card_range, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨a, -, b, -, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    apply hab
    apply e.injective
    apply Fin.ext
    rw [← Nat.div_add_mod ((e a : Fin N) : ℕ) (m - 1),
      ← Nat.div_add_mod ((e b : Fin N) : ℕ) (m - 1), hblock a, hblock b, heq]

/-- Hunter–Steiner path variant: the vertex-count threshold is
    `(n-1)*(m-1)+1`, so n=m=2 gives 2.

    The completed upper proof uses a maximal acyclic arc set, its height coloring, and
    pigeonhole to obtain either an independent `n`-set or a directed path on `m` vertices.
    The completed lower proof uses `(n-1)` bidirected blocks of size `(m-1)`; an independent
    set meets each block at most once, while an injective directed path cannot leave its block.
    This is the non-induced directed-path convention of `DirPathOn`; it does not identify
    induced and non-induced extremal functions. -/
theorem hunter_steiner_path_exact (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    sInf {N : ℕ | ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
        (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
        (∃ S : Finset (Fin N), DirPathOn r m S)} =
      (n - 1) * (m - 1) + 1 := by
  classical
  have hmem : (n - 1) * (m - 1) + 1 ∈ {N : ℕ | ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
      (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
      (∃ S : Finset (Fin N), DirPathOn r m S)} := fun r hirr =>
    exists_indep_or_dirPath r hirr n m hn hm (by simp)
  have hlow : ∀ N ∈ {N : ℕ | ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
      (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
      (∃ S : Finset (Fin N), DirPathOn r m S)}, (n - 1) * (m - 1) + 1 ≤ N := by
    intro N hN
    by_contra hlt
    obtain ⟨r, hirr, hind, hpath⟩ := exists_bad_digraph n m N hn hm (by omega)
    rcases hN r hirr with h | h
    · exact hind h
    · exact hpath h
  exact le_antisymm (Nat.sInf_le hmem) (hlow _ (Nat.sInf_mem ⟨_, hmem⟩))

end ErdosCandidates.E112

/- AMENDED REVIEW
   The path theorem uses the vertex-count boundary correction `+1`: in particular, `n = m = 2`
   requires two vertices. `hunter_steiner_path_exact` is formally proved above from the completed
   upper and lower constructions. `TransTournamentOn` and `DirPathOn` both have non-induced
   forward-arc meanings, with reverse ambient arcs permitted; no equivalence with an induced
   extremal function is asserted. The Erdős–Rado and Larson–Mitchell source attributions remain
   subject to the graph-convention uncertainty recorded in the module header.
-/
