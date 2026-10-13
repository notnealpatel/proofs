import Combinatorics.ChordalBasics

set_option autoImplicit false

namespace ErdosCandidates.E81

open SimpleGraph
open scoped BigOperators

/-- The complete split graph with clique side `A`; its complement is independent. -/
def splitGraph {V : Type*} [DecidableEq V] (A : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (u ∈ A ∨ v ∈ A)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [DecidableEq V] (A : Finset V) :
    DecidableRel (splitGraph A).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

example : (splitGraph ({0} : Finset (Fin 3))).Adj 0 1 := by decide
example : ¬ (splitGraph ({0} : Finset (Fin 3))).Adj 1 2 := by decide

/-- Every complete split graph has no induced cycle of length at least four. -/
theorem chordal_splitGraph {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) : Chordal (splitGraph A) := by
  classical
  intro s hs
  constructor
  intro f
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ s.card by omega)
  have hk' : s.card = k + 3 := by omega
  let f' : ((splitGraph A).induce (s : Set V)) ≃g cycleGraph (k + 3) := hk' ▸ f
  have hdeg (x : (s : Set V)) : ((splitGraph A).induce (s : Set V)).degree x = 2 := by
    rw [← f'.degree_eq x]
    exact cycleGraph_degree_three_le
  by_cases hA : ∃ u ∈ s, u ∈ A
  · obtain ⟨u, hu, huA⟩ := hA
    let x : (s : Set V) := ⟨u, hu⟩
    have hneighbors : ((splitGraph A).induce (s : Set V)).neighborFinset x =
        Finset.univ.erase x := by
      ext y
      rw [mem_neighborFinset]
      change (x.val ≠ y.val ∧ (x.val ∈ A ∨ y.val ∈ A)) ↔ y ∈ Finset.univ.erase x
      rw [Finset.mem_erase]
      simp only [Finset.mem_univ, and_true]
      constructor
      · intro h
        exact fun he => h.1 (congrArg Subtype.val he.symm)
      · intro h
        exact ⟨fun he => h (Subtype.ext he.symm), Or.inl huA⟩
    have hcard : ((splitGraph A).induce (s : Set V)).degree x = s.card - 1 := by
      rw [← card_neighborFinset_eq_degree, hneighbors]
      simp
    have hd := hdeg x
    omega
  · let x := f'.symm (0 : Fin (k + 3))
    have hneighbors : ((splitGraph A).induce (s : Set V)).neighborFinset x = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      have hadj := (mem_neighborFinset _ _ _).mp hy
      change x.val ≠ y.val ∧ (x.val ∈ A ∨ y.val ∈ A) at hadj
      rcases hadj.2 with hx | hy
      · exact hA ⟨x.val, x.property, hx⟩
      · exact hA ⟨y.val, y.property, hy⟩
    have hd := hdeg x
    rw [← card_neighborFinset_eq_degree, hneighbors, Finset.card_empty] at hd
    omega

example : Chordal (splitGraph ({0} : Finset (Fin 3))) := chordal_splitGraph _

private theorem partition_eq_of_pair {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {P : Finset (Finset V)} (hP : CliqueEdgePartition G P)
    {Q R : Finset V} (hQ : Q ∈ P) (hR : R ∈ P)
    {x y : V} (hxy : G.Adj x y) (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hxR : x ∈ R) (hyR : y ∈ R) : Q = R := by
  classical
  obtain ⟨S, hS, huniq⟩ := hP.2 s(x, y) (by simpa using hxy)
  have hQS : Q = S := huniq Q ⟨hQ, by simpa using And.intro hxQ hyQ⟩
  have hRS : R = S := huniq R ⟨hR, by simpa using And.intro hxR hyR⟩
  exact hQS.trans hRS.symm

private theorem partition_covers_pair {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {P : Finset (Finset V)} (hP : CliqueEdgePartition G P)
    {x y : V} (hxy : G.Adj x y) : ∃ Q ∈ P, x ∈ Q ∧ y ∈ Q := by
  classical
  obtain ⟨Q, hQ, _⟩ := hP.2 s(x, y) (by simpa using hxy)
  exact ⟨Q, hQ.1, by simpa using hQ.2⟩

private theorem split_clique_sdiff_card_le_one {V : Type*} [DecidableEq V]
    (A Q : Finset V) (hQ : (splitGraph A).IsClique (Q : Set V)) :
    (Q \ A).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have h := hQ (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
  exact h.2.elim (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2

private theorem split_internal_pair_count {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (P : Finset (Finset V)) (hP : CliqueEdgePartition (splitGraph A) P) :
    (∑ Q ∈ P, (Q ∩ A).card.choose 2) ≤ A.card.choose 2 := by
  classical
  let pairs := fun Q : Finset V => (Q ∩ A).powersetCard 2
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint pairs := by
    intro Q hQ R hR hne
    apply Finset.disjoint_left.mpr
    intro T hTQ hTR
    have hTQ' := Finset.mem_powersetCard.mp hTQ
    have hTR' := Finset.mem_powersetCard.mp hTR
    obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp hTQ'.2
    have hxT : x ∈ T := by simp [hT]
    have hyT : y ∈ T := by simp [hT]
    have hxQ := Finset.mem_inter.mp (hTQ'.1 hxT)
    have hyQ := Finset.mem_inter.mp (hTQ'.1 hyT)
    have hxR := Finset.mem_inter.mp (hTR'.1 hxT)
    have hyR := Finset.mem_inter.mp (hTR'.1 hyT)
    exact hne (partition_eq_of_pair hP hQ hR ⟨hxy, Or.inl hxQ.2⟩
      hxQ.1 hyQ.1 hxR.1 hyR.1)
  have hsub : P.biUnion pairs ⊆ A.powersetCard 2 := by
    intro T hT
    obtain ⟨Q, _, hTQ⟩ := Finset.mem_biUnion.mp hT
    exact Finset.powersetCard_mono Finset.inter_subset_right hTQ
  calc
    (∑ Q ∈ P, (Q ∩ A).card.choose 2) = (P.biUnion pairs).card := by
      rw [Finset.card_biUnion hdisj]
      simp [pairs, Finset.card_powersetCard]
    _ ≤ (A.powersetCard 2).card := Finset.card_le_card hsub
    _ = A.card.choose 2 := Finset.card_powersetCard _ _

private theorem split_cross_pair_count {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (P : Finset (Finset V)) (hP : CliqueEdgePartition (splitGraph A) P) :
    A.card * (Finset.univ \ A).card = ∑ Q ∈ P, (Q ∩ A).card * (Q \ A).card := by
  classical
  let cross := fun Q : Finset V => (Q ∩ A) ×ˢ (Q \ A)
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint cross := by
    intro Q hQ R hR hne
    apply Finset.disjoint_left.mpr
    intro z hzQ hzR
    have hzQ' := Finset.mem_product.mp hzQ
    have hzR' := Finset.mem_product.mp hzR
    have hxQ := Finset.mem_inter.mp hzQ'.1
    have hyQ := Finset.mem_sdiff.mp hzQ'.2
    have hxR := Finset.mem_inter.mp hzR'.1
    have hyR := Finset.mem_sdiff.mp hzR'.2
    have hxy : z.1 ≠ z.2 := fun he => hyQ.2 (he ▸ hxQ.2)
    exact hne (partition_eq_of_pair hP hQ hR ⟨hxy, Or.inl hxQ.2⟩
      hxQ.1 hyQ.1 hxR.1 hyR.1)
  have heq : P.biUnion cross = A ×ˢ (Finset.univ \ A) := by
    ext z
    constructor
    · intro hz
      obtain ⟨Q, _, hzQ⟩ := Finset.mem_biUnion.mp hz
      have hzQ' := Finset.mem_product.mp hzQ
      exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hzQ'.1).2,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hzQ'.2).2⟩⟩
    · intro hz
      have hz' := Finset.mem_product.mp hz
      have hyA := (Finset.mem_sdiff.mp hz'.2).2
      have hxy : z.1 ≠ z.2 := fun he => hyA (he ▸ hz'.1)
      obtain ⟨Q, hQ, hxQ, hyQ⟩ := partition_covers_pair hP ⟨hxy, Or.inl hz'.1⟩
      exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_product.mpr
        ⟨Finset.mem_inter.mpr ⟨hxQ, hz'.1⟩, Finset.mem_sdiff.mpr ⟨hyQ, hyA⟩⟩⟩
  calc
    A.card * (Finset.univ \ A).card = (A ×ˢ (Finset.univ \ A)).card :=
      (Finset.card_product _ _).symm
    _ = (P.biUnion cross).card := congrArg Finset.card heq.symm
    _ = ∑ Q ∈ P, (Q ∩ A).card * (Q \ A).card := by
      rw [Finset.card_biUnion hdisj]
      simp [cross, Finset.card_product]

private theorem self_le_one_add_choose_two (t : ℕ) : t ≤ 1 + t.choose 2 := by
  cases t with
  | zero => decide
  | succ t =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- In any edge partition of a complete split graph, the cross edges require
at least `|A|·|B| − choose(|A|,2)` cliques, stated without truncated subtraction. -/
theorem splitGraph_clique_partition_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (P : Finset (Finset V)) (hP : CliqueEdgePartition (splitGraph A) P) :
    A.card * (Finset.univ \ A).card ≤ P.card + A.card.choose 2 := by
  classical
  have hlocal (Q : Finset V) (hQ : Q ∈ P) :
      (Q ∩ A).card * (Q \ A).card ≤ 1 + (Q ∩ A).card.choose 2 := by
    calc
      _ ≤ (Q ∩ A).card * 1 := Nat.mul_le_mul_left _
        (split_clique_sdiff_card_le_one A Q (hP.1 Q hQ).1)
      _ = (Q ∩ A).card := Nat.mul_one _
      _ ≤ _ := self_le_one_add_choose_two _
  calc
    _ = ∑ Q ∈ P, (Q ∩ A).card * (Q \ A).card := split_cross_pair_count A P hP
    _ ≤ ∑ Q ∈ P, (1 + (Q ∩ A).card.choose 2) := Finset.sum_le_sum hlocal
    _ = P.card + ∑ Q ∈ P, (Q ∩ A).card.choose 2 := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left (split_internal_pair_count A P hP) _

example : CliqueEdgePartition (splitGraph (Finset.univ : Finset (Fin 3)))
    {(Finset.univ : Finset (Fin 3))} := by
  have heq : splitGraph (Finset.univ : Finset (Fin 3)) = ⊤ := by
    ext x y
    simp [splitGraph]
  rw [heq]
  exact cliqueEdgePartition_top_fin3

/-- The explicit `floor(n/3)`-clique split graph gives the quadratic lower
bound with linear error `2n`, for each nondegenerate size `n ≥ 3`. -/
theorem splitGraph_sharpness_witness (n : ℕ) (hn : 3 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      Chordal G ∧ ∀ P : Finset (Finset (Fin n)), CliqueEdgePartition G P →
        n ^ 2 ≤ 6 * P.card + 2 * n := by
  classical
  let a := n / 3
  let r := n % 3
  let A : Finset (Fin n) := Finset.univ.filter (fun x => x.val < a)
  have ha : a ≤ n := Nat.div_le_self n 3
  have hA : A.card = a := by
    have hbij : (Finset.univ : Finset (Fin a)).card = A.card := by
      apply Finset.card_bij (fun x _ => (⟨x.val, lt_of_lt_of_le x.isLt ha⟩ : Fin n))
      · intro x hx
        simp [A, x.isLt]
      · intro x hx y hy heq
        exact Fin.ext (congrArg (@Fin.val n) heq)
      · intro y hy
        have hy' : y.val < a := (Finset.mem_filter.mp hy).2
        exact ⟨⟨y.val, hy'⟩, Finset.mem_univ _, Fin.ext rfl⟩
    simpa using hbij.symm
  let b := (Finset.univ \ A).card
  have hab : b + a = n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simpa only [Finset.card_univ, Fintype.card_fin, hA] using h
  have hnr : r + 3 * a = n := Nat.mod_add_div n 3
  have hr : r ≤ 2 := by
    have h := Nat.mod_lt n (show 0 < 3 by decide)
    omega
  refine ⟨splitGraph A, inferInstance, chordal_splitGraph A, ?_⟩
  intro P hP
  have hcount : a * b ≤ P.card + a.choose 2 := by
    simpa only [hA] using splitGraph_clique_partition_lower_bound A P hP
  have hcountQ : (a : ℚ) * b ≤ (P.card : ℚ) + (a : ℚ) * ((a : ℚ) - 1) / 2 := by
    have h : (a : ℚ) * b ≤ (P.card : ℚ) + (a.choose 2 : ℚ) := by exact_mod_cast hcount
    simpa only [Nat.cast_choose_two] using h
  have hnrQ : (n : ℚ) = 3 * (a : ℚ) + r := by exact_mod_cast hnr.symm.trans (Nat.add_comm _ _)
  have habQ : (b : ℚ) = 2 * (a : ℚ) + r := by
    have h : (b : ℚ) + a = n := by exact_mod_cast hab
    linarith
  have hidentity : (n : ℚ) ^ 2 = 6 * (a : ℚ) * b -
      3 * (a : ℚ) * ((a : ℚ) - 1) + (r : ℚ) ^ 2 - 3 * a := by
    rw [hnrQ, habQ]
    ring
  have hrQ : (r : ℚ) ≤ 2 := by exact_mod_cast hr
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have hr2 : (r : ℚ) ^ 2 ≤ 4 := by nlinarith
  have hnQ : (3 : ℚ) ≤ n := by exact_mod_cast hn
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
  have hfinal : (n : ℚ) ^ 2 ≤ 6 * (P.card : ℚ) + 2 * n := by
    nlinarith [hidentity]
  exact_mod_cast hfinal

example : (Finset.univ.filter (fun x : Fin 3 => x.val < 3 / 3)) = {0} := by decide

example : 3 ≤ (3 : ℕ) ∧ Chordal (splitGraph ({0} : Finset (Fin 3))) ∧
    CliqueEdgePartition (splitGraph ({0} : Finset (Fin 3)))
      {({0, 1} : Finset (Fin 3)), {0, 2}} := by
  refine ⟨by decide, chordal_splitGraph _, ?_⟩
  constructor
  · intro Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    all_goals constructor
    all_goals decide
  · intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hadj : (splitGraph ({0} : Finset (Fin 3))).Adj x y := by simpa using he
      fin_cases x <;> fin_cases y <;> simp [splitGraph] at hadj
      all_goals
        first
        | (refine ⟨{0, 1}, ?_, ?_⟩
           · simp
           · intro Q hQ
             rcases (Finset.mem_insert.mp hQ.1) with h | h
             · exact h
             · have hval := hQ.2
               simp only [Finset.mem_singleton] at h
               subst Q
               simp at hval)
        | (refine ⟨{0, 2}, ?_, ?_⟩
           · simp
           · intro Q hQ
             rcases (Finset.mem_insert.mp hQ.1) with h | h
             · have hval := hQ.2
               subst Q
               simp at hval
             · exact Finset.mem_singleton.mp h)

end ErdosCandidates.E81
