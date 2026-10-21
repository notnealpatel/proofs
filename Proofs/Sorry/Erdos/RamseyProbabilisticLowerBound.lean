/-
# Erdős 1947 — probabilistic lower bound for diagonal Ramsey numbers

## Source

P. Erdős, "Some remarks on the theory of graphs", Bull. Amer. Math. Soc. 53
(1947), 292–294 (the counting argument giving `R(k) > 2^{k/2}`); textbook form:
N. Alon and J. Spencer, *The Probabilistic Method*, Proposition 1.1.1
("If `C(n,k) · 2^{1 - C(k,2)} < 1` then `R(k,k) > n`; thus `R(k,k) > ⌊2^{k/2}⌋`
for all `k ≥ 3`").

## Informal statement (target spec, verbatim)

  For every k ≥ 3, 2^(k/2) ≤ R(k): if n ≤ 2^(k/2) (equivalently
  C(n,k)·2^(1−C(k,2)) < 1) there is a graph on n vertices with no k-clique and
  no k-independent set.

Recorded 2026-10-21.

## Definition layer

No new definitions.  The diagonal Ramsey number is the repository's production
definition from `Proofs/Erdos/Erdos77/ClassicalBounds.lean`:

* `HasRamseyProperty n k := ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree k ∨ ¬ Gᶜ.CliqueFree k`
* `R k := sInf {n | HasRamseyProperty n k}`, with the threshold lemma `R_le_iff`.

A 2-colouring of the edges of `K_n` is a graph `G` on `Fin n` (colour 1 = edges of
`G`, colour 2 = edges of `Gᶜ`).  Mathlib has no Ramsey number (leandoc searches
"ramsey number lower bound", "diagonal Ramsey probabilistic",
`SimpleGraph.ramseyNumber` → miss; `grep -ri ramsey Mathlib` hits only
Hales–Jewett, Hindman and coalgebra files), so nothing here duplicates Mathlib.

## Proof

Union bound by counting (the probabilistic argument with the uniform measure
replaced by cardinalities).  For a fixed `k`-set `s`, the graphs in which `s` is
independent inject, via `edgeFinset`, into subsets of the `C(n,2) - C(k,2)` edges
of `K_n` not inside `s`; complementation transfers the bound to cliques.  Summing
over the `C(n,k)` sets `s` bounds the bad graphs by
`C(n,k) · 2 · 2^{C(n,2)-C(k,2)}`, which is below the `2^{C(n,2)}` graphs on `Fin n`
when `2 · C(n,k) < 2^{C(k,2)}`.  The arithmetic `n² ≤ 2^k ⇒ 2·C(n,k) < 2^{C(k,2)}`
for `k ≥ 3` uses `k!·C(n,k) ≤ n^k` and `4·2^k < (k!)²`; the real form takes
`n = ⌊2^{k/2}⌋`.
-/
import Mathlib
import Erdos.Erdos77.ClassicalBounds

set_option autoImplicit false

namespace ErdosCandidates.RamseyProbabilisticLowerBound

open SimpleGraph Finset ErdosCandidates.E77

open Classical in
/-- At most `2^{C(n,2) - C(|s|,2)}` graphs on `Fin n` have `s` as an independent set
(a clique of the complement): their edge sets avoid the `C(|s|,2)` pairs inside `s`. -/
theorem card_graphs_indep_le (n : ℕ) (s : Finset (Fin n)) :
    #(univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s)) ≤
      2 ^ (n.choose 2 - (#s).choose 2) := by
  classical
  set Es : Finset (Sym2 (Fin n)) := s.offDiag.image Sym2.mk.uncurry with hEs
  have hEs_sub : Es ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    have hne : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
    simpa [SimpleGraph.mem_edgeFinset] using hne
  have hmaps : ∀ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s),
      G.edgeFinset ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ Es).powerset := by
    intro G hG
    have hcl := (Finset.mem_filter.mp hG).2
    rw [Finset.mem_powerset]
    intro e he
    rw [Finset.mem_sdiff]
    refine ⟨edgeFinset_mono le_top he, ?_⟩
    intro heEs
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp heEs
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    have hadj : G.Adj a b := by simpa using he
    have hcadj : Gᶜ.Adj a b := hcl.isClique ha hb hne
    exact ((G.compl_adj a b).mp hcadj).2 hadj
  have hinj : Set.InjOn (fun G : SimpleGraph (Fin n) => G.edgeFinset)
      (univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s)) := by
    intro G₁ _ G₂ _ h
    exact edgeFinset_inj.mp h
  calc #(univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s))
      ≤ #(((⊤ : SimpleGraph (Fin n)).edgeFinset \ Es).powerset) :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 ^ (n.choose 2 - (#s).choose 2) := by
        rw [Finset.card_powerset, Finset.card_sdiff_of_subset hEs_sub,
          card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, hEs,
          Sym2.card_image_offDiag]


open Classical in
/-- At most `2^{C(n,2) - C(|s|,2)}` graphs on `Fin n` have `s` as a clique;
complementation reduces this to `card_graphs_indep_le`. -/
theorem card_graphs_clique_le (n : ℕ) (s : Finset (Fin n)) :
    #(univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique #s s)) ≤
      2 ^ (n.choose 2 - (#s).choose 2) := by
  have himage : univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique #s s) =
      (univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s)).image compl := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hG
      exact ⟨Gᶜ, by rwa [compl_compl], compl_compl G⟩
    · rintro ⟨H, hH, rfl⟩
      exact hH
  rw [himage]
  exact (Finset.card_image_le).trans (card_graphs_indep_le n s)

/-- There are at least `2^{C(n,2)}` simple graphs on `Fin n`: every set of edges of
`K_n` is the edge set of a distinct graph. -/
theorem two_pow_le_card_graphs (n : ℕ) :
    2 ^ n.choose 2 ≤ Fintype.card (SimpleGraph (Fin n)) := by
  classical
  have hmaps : ∀ A ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset,
      SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n))) ∈ (univ : Finset (SimpleGraph (Fin n))) :=
    fun _ _ => Finset.mem_univ _
  have hinj : Set.InjOn (fun A : Finset (Sym2 (Fin n)) =>
      SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n))))
      ((⊤ : SimpleGraph (Fin n)).edgeFinset.powerset) := by
    have hedge : ∀ A ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset,
        (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).edgeSet = A := by
      intro A hA
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_sdiff, Finset.mem_coe, and_iff_left_iff_imp]
      intro he
      have hetop := Finset.mem_powerset.mp hA he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] at hetop
      exact hetop
    intro A hA B hB hAB
    have h := congrArg SimpleGraph.edgeSet hAB
    simp only at h
    rw [hedge A hA, hedge B hB] at h
    exact Finset.coe_injective h
  calc 2 ^ n.choose 2 = #(⊤ : SimpleGraph (Fin n)).edgeFinset.powerset := by
        rw [Finset.card_powerset, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    _ ≤ #(univ : Finset (SimpleGraph (Fin n))) := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Fintype.card (SimpleGraph (Fin n)) := Finset.card_univ


/-- **Erdős 1947, counting form** (Alon–Spencer Prop. 1.1.1): if
`C(n,k) · 2^{1 - C(k,2)} < 1`, written without division as `2 · C(n,k) < 2^{C(k,2)}`,
then some graph on `n` vertices has neither a `k`-clique nor a `k`-independent set,
i.e. `HasRamseyProperty n k` fails. -/
theorem not_hasRamseyProperty_of_two_mul_choose_lt (n k : ℕ)
    (h : 2 * n.choose k < 2 ^ k.choose 2) : ¬ HasRamseyProperty n k := by
  classical
  intro hR
  let bad : Finset (Fin n) → Finset (SimpleGraph (Fin n)) := fun s =>
    univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique #s s) ∪
      univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique #s s)
  have hcover : (univ : Finset (SimpleGraph (Fin n))) ⊆ (powersetCard k univ).biUnion bad := by
    intro G _
    rw [Finset.mem_biUnion]
    rcases hR G with hG | hG
    · obtain ⟨s, hs⟩ := (not_cliqueFree_iff_exists G k).mp hG
      refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs.card_eq⟩, ?_⟩
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ G, ?_⟩)
      rwa [hs.card_eq]
    · obtain ⟨s, hs⟩ := (not_cliqueFree_iff_exists Gᶜ k).mp hG
      refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs.card_eq⟩, ?_⟩
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ G, ?_⟩)
      rwa [hs.card_eq]
  have hbad : ∀ s ∈ powersetCard k (univ : Finset (Fin n)),
      #(bad s) ≤ 2 * 2 ^ (n.choose 2 - k.choose 2) := by
    intro s hs
    have hsk : #s = k := (Finset.mem_powersetCard.mp hs).2
    calc #(bad s) ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 ^ (n.choose 2 - (#s).choose 2) + 2 ^ (n.choose 2 - (#s).choose 2) :=
          Nat.add_le_add (card_graphs_clique_le n s) (card_graphs_indep_le n s)
      _ = 2 * 2 ^ (n.choose 2 - k.choose 2) := by rw [hsk, two_mul]
  have hupper : Fintype.card (SimpleGraph (Fin n)) ≤
      n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
    calc Fintype.card (SimpleGraph (Fin n)) = #(univ : Finset (SimpleGraph (Fin n))) :=
          Finset.card_univ.symm
      _ ≤ #((powersetCard k univ).biUnion bad) := Finset.card_le_card hcover
      _ ≤ ∑ s ∈ powersetCard k (univ : Finset (Fin n)), #(bad s) := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ powersetCard k (univ : Finset (Fin n)), 2 * 2 ^ (n.choose 2 - k.choose 2) :=
          Finset.sum_le_sum hbad
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  have hlt : n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) < 2 ^ n.choose 2 := by
    rcases Nat.lt_or_ge n k with hnk | hkn
    · rw [Nat.choose_eq_zero_of_lt hnk, Nat.zero_mul]
      exact Nat.two_pow_pos _
    · have hchoose : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
      have hsplit : 2 ^ n.choose 2 = 2 ^ (n.choose 2 - k.choose 2) * 2 ^ k.choose 2 := by
        rw [← pow_add, Nat.sub_add_cancel hchoose]
      rw [hsplit]
      calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
          = 2 ^ (n.choose 2 - k.choose 2) * (2 * n.choose k) := by ring
        _ < 2 ^ (n.choose 2 - k.choose 2) * 2 ^ k.choose 2 :=
          Nat.mul_lt_mul_of_pos_left h (Nat.two_pow_pos _)
  exact absurd ((two_pow_le_card_graphs n).trans hupper) (Nat.not_le.mpr hlt)


/-- `2 · C(k,2) + k = k²`. -/
theorem two_mul_choose_two_add_self (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

/-- For `k ≥ 3`, `4 · 2^k < (k!)²` (equality-tight start: `32 < 36` at `k = 3`). -/
theorem four_mul_two_pow_lt_factorial_sq (k : ℕ) (hk : 3 ≤ k) :
    4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hfac : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    have hk2 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    calc 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by ring
      _ < 2 * k.factorial ^ 2 := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ ≤ (k + 1) ^ 2 * k.factorial ^ 2 := Nat.mul_le_mul_right _ hk2
      _ = ((k + 1).factorial) ^ 2 := by rw [hfac, mul_pow]

/-- For `k ≥ 3` and `n² ≤ 2^k` (i.e. `n ≤ 2^{k/2}`), the Erdős counting condition
`2 · C(n,k) < 2^{C(k,2)}` holds. -/
theorem two_mul_choose_lt_of_sq_le (n k : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  have hdesc : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hsq : (2 * n ^ k) ^ 2 < (k.factorial * 2 ^ k.choose 2) ^ 2 := by
    calc (2 * n ^ k) ^ 2 = 4 * (n ^ 2) ^ k := by ring
      _ ≤ 4 * (2 ^ k) ^ k := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hn k)
      _ = 4 * 2 ^ k * 2 ^ (2 * k.choose 2) := by
          rw [← pow_mul, mul_assoc, ← pow_add, Nat.add_comm k, two_mul_choose_two_add_self,
            sq]
      _ < k.factorial ^ 2 * 2 ^ (2 * k.choose 2) :=
          Nat.mul_lt_mul_of_pos_right (four_mul_two_pow_lt_factorial_sq k hk) (Nat.two_pow_pos _)
      _ = (k.factorial * 2 ^ k.choose 2) ^ 2 := by ring
  have hlt : 2 * n ^ k < k.factorial * 2 ^ k.choose 2 :=
    (Nat.pow_lt_pow_iff_left (by norm_num)).mp hsq
  have hmul : k.factorial * (2 * n.choose k) < k.factorial * 2 ^ k.choose 2 := by
    calc k.factorial * (2 * n.choose k) = 2 * (k.factorial * n.choose k) := by ring
      _ ≤ 2 * n ^ k := Nat.mul_le_mul_left 2 hdesc
      _ < k.factorial * 2 ^ k.choose 2 := hlt
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Erdős 1947, natural-number form**: for `k ≥ 3`, every `n` with `n² ≤ 2^k`
satisfies `n < R(k)`. -/
theorem lt_R_of_sq_le_two_pow (n k : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) : n < R k := by
  by_contra hle
  exact not_hasRamseyProperty_of_two_mul_choose_lt n k (two_mul_choose_lt_of_sq_le n k hk hn)
    ((R_le_iff n k).mp (Nat.not_lt.mp hle))

/-- **Erdős 1947 lower bound** for diagonal Ramsey numbers: for every `k ≥ 3`,
`2^{k/2} ≤ R(k)` (real exponent `k/2`, no natural-number division). -/
theorem R_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (R k : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hxsq : x ^ 2 = (2 : ℝ) ^ k := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  set n : ℕ := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hnsq : n ^ 2 ≤ 2 ^ k := by
    have hreal : ((n ^ 2 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      push_cast
      rw [← hxsq]
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) hnx 2
    exact_mod_cast hreal
  have hlt : n < R k := lt_R_of_sq_le_two_pow n k hk hnsq
  calc x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    _ ≤ (R k : ℝ) := by exact_mod_cast hlt

/-! ## Non-vacuity and ground truth -/

/-- The counting hypothesis is satisfiable: `2 · C(5,4) = 10 < 64 = 2^{C(4,2)}`. -/
example : 2 * Nat.choose 5 4 < 2 ^ Nat.choose 4 2 := by decide

/-- The counting form recovers `5 < R 4` (true value `R 4 = 18`). -/
example : ¬ HasRamseyProperty 5 4 :=
  not_hasRamseyProperty_of_two_mul_choose_lt 5 4 (by decide)

/-- The square form at the boundary `n² = 2^k`: `4 < R 4`. -/
example : 4 < R 4 := lt_R_of_sq_le_two_pow 4 4 (by norm_num) (by norm_num)

/-- At `k = 3` the bound gives `2 < R 3` (true value `R 3 = 6`). -/
example : 2 < R 3 := lt_R_of_sq_le_two_pow 2 3 le_rfl (by norm_num)

end ErdosCandidates.RamseyProbabilisticLowerBound
