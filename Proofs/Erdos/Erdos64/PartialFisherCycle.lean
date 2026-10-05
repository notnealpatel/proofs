import Erdos.Erdos64.Basic
import Erdos.Erdos64.PartialFisherCore
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex
import Erdos.Erdos64.UniqueCubicClawCenterCycleList
import Erdos.Erdos64.UniqueCubicClawCenterBlockInsertion

set_option autoImplicit false

namespace Erdos64.PartialFisherCycle

open PartialFisherCore

/-- Incoming incidences of an injectively indexed root cycle never collide with a
spare incidence, even if the spare edge is contracted off the cycle. -/
theorem incoming_ne_spare {V : Type*} (K M : SimpleGraph V) (z : V)
    {m : ℕ} (c : Fin (m + 1) → V) (hc : Function.Injective c)
    (hcycle : ∀ i, K.Adj (c i) (c (i + 1)))
    (i j : Fin (m + 1)) (hi : c i ≠ z) (hj : c j ≠ z)
    (s : V) (hs : K.Adj (c j) s)
    (hprev : s ≠ c (j - 1)) (hnext : s ≠ c (j + 1)) :
    q K z M (some ⟨(c i, c (i - 1)), hi, by
      simpa using (hcycle (i - 1)).symm⟩) ≠
    q K z M (some ⟨(c j, s), hj, hs⟩) := by
  intro heq
  rcases (q_eq_iff K z M _ _).mp heq with heq | hrev
  · have hp := congrArg (fun a : Port K z => a.map Subtype.val) heq
    have hp' := Option.some.inj hp
    have hij : i = j := hc (congrArg Prod.fst hp')
    have he : c (i - 1) = s := congrArg Prod.snd hp'
    exact hprev (by simpa only [hij] using he.symm)
  · have hij : i - 1 = j := hc hrev.2.1
    have he : i = j + 1 := by
      rw [← hij]
      simp
    exact hnext (by simpa only [he] using hrev.1.symm)

/-- A contracted outgoing cycle edge forces both the incoming edge and the spare
edge at its tail to be uncontracted, by root matching. -/
theorem tail_edges_not_matching {V : Type*} (M : SimpleGraph V)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (x prev next spare : V) (hused : M.Adj x next)
    (hp : prev ≠ next) (hs : spare ≠ next) :
    ¬M.Adj x prev ∧ ¬M.Adj x spare := by
  constructor
  · intro h
    exact hp (hmatch x prev next h hused)
  · intro h
    exact hs (hmatch x spare next h hused)

/-- At a contracted cycle edge, the spare-to-outgoing local edge becomes the
boundary edge to the incoming incidence at the next actual root. -/
theorem contracted_tail_boundary {V : Type*} (K M : SimpleGraph V) (z : V)
    (x y s : V) (hx : x ≠ z) (hy : y ≠ z)
    (hxy : K.Adj x y) (hxs : K.Adj x s) (hsy : s ≠ y)
    (hused : M.Adj x y) :
    (G K z M).Adj (q K z M (some ⟨(x,s), hx, hxs⟩))
      (q K z M (some ⟨(y,x), hy, hxy.symm⟩)) := by
  rw [← (connector_q_eq_iff K z M x y hx hy hxy).mpr hused]
  apply quotienttriangleedge K z M x _ _ rfl rfl
  intro heq
  exact hsy (congrArg (fun p : OrdinaryPort K z => p.val.2) heq)

/-- A cubic root has a neighbor other than its two specified cycle neighbors. -/
theorem exists_spare {V : Type*} [Fintype V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (x prev next : V) (hdegree : K.degree x = 3) :
    ∃ s, K.Adj x s ∧ s ≠ prev ∧ s ≠ next := by
  classical
  by_contra! hn
  have hsub : K.neighborFinset x ⊆ {prev, next} := by
    intro s hs
    have hadj := (K.mem_neighborFinset x s).mp hs
    by_cases hp : s = prev
    · simp [hp]
    · have hnext := hn s hadj hp
      simp [hnext]
  have hcard := (Finset.card_le_card hsub).trans (show ({prev, next} : Finset V).card ≤ 2 from Finset.card_le_two)
  rw [K.card_neighborFinset_eq_degree, hdegree] at hcard
  omega

private theorem collision_roots {V : Type*} (K M : SimpleGraph V) (z : V)
    {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → V)
    (hc : Function.Injective c) (i j : Fin (m + 1))
    (p r : OrdinaryPort K z) (hp : p.val.1 = c i) (hr : r.val.1 = c j)
    (hps : p.val.2 = c (i - 1) ∨ ¬M.Adj p.val.1 p.val.2)
    (hrs : r.val.2 = c (j - 1) ∨ ¬M.Adj r.val.1 r.val.2)
    (heq : q K z M (some p) = q K z M (some r)) : i = j := by
  rcases (q_eq_iff K z M _ _).mp heq with heq | hrev
  · exact hc (hp.symm.trans ((congrArg (fun a : Port K z =>
      a.map (fun b => b.val.1)) heq |> Option.some.inj).trans hr))
  · have hM : M.Adj r.val.1 r.val.2 := by
      simpa only [← hrev.1, ← hrev.2.1] using hrev.2.2.symm
    rcases hps with hps | hps
    · rcases hrs with hrs | hrs
      · have hij : i = j - 1 := hc (by simpa only [hp, hrs] using hrev.1)
        have hji : j = i - 1 := hc (by simpa only [hr, hps] using hrev.2.1.symm)
        have hs : (i + 1) + 1 = i := by
          have h1 : i + 1 = j := by rw [hij]; simp
          have h2 : j + 1 = i := by rw [hji]; simp
          rw [h1, h2]
        exact False.elim (UniqueCubicClawCenter.CycleIndex.succ_succ_ne m
          (by omega) i hs)
      · exact False.elim (hrs hM)
    · exact False.elim (hps hrev.2.2)

/-- An injectively indexed actual root cycle avoiding the pole lifts to a cycle
of exactly twice its length, including when cycle edges are contracted. -/
theorem exists_exact_cycle_avoiding_pole {V : Type*} [Fintype V]
    (K M : SimpleGraph V) [DecidableRel K.Adj] (z : V)
    (hdegree : ∀ x, x ≠ z → K.degree x = 3)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → V)
    (hc : Function.Injective c) (havoid : ∀ i, c i ≠ z)
    (hcycle : ∀ i, K.Adj (c i) (c (i + 1))) :
    ∃ a, ∃ p : (G K z M).Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  have hex : ∀ i, ∃ s, K.Adj (c i) s ∧ s ≠ c (i - 1) ∧ s ≠ c (i + 1) :=
    fun i => exists_spare K (c i) (c (i - 1)) (c (i + 1))
      (hdegree (c i) (havoid i))
  choose s hs using hex
  let t := fun i => if M.Adj (c i) (c (i + 1)) then s i else c (i + 1)
  have htadj : ∀ i, K.Adj (c i) (t i) := by
    intro i
    dsimp only [t]
    split_ifs
    · exact (hs i).1
    · exact hcycle i
  have htM : ∀ i, ¬M.Adj (c i) (t i) := by
    intro i
    dsimp only [t]
    split_ifs with h
    · intro he
      exact (hs i).2.2 (hmatch _ _ _ he h)
    · exact h
  have htprev : ∀ i, c (i - 1) ≠ t i := by
    intro i
    dsimp only [t]
    split_ifs
    · exact (hs i).2.1.symm
    · intro he
      have hi := hc he
      have hreturn : ((i - 1) + 1) + 1 = i - 1 := by
        simpa using hi.symm
      exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m (by omega) (i - 1) hreturn
  let pin : Fin (m + 1) → OrdinaryPort K z := fun i =>
    ⟨(c i, c (i - 1)), havoid i, by simpa using (hcycle (i - 1)).symm⟩
  let pout : Fin (m + 1) → OrdinaryPort K z := fun i =>
    ⟨(c i, t i), havoid i, htadj i⟩
  let a := fun i => q K z M (some (pin i))
  let b := fun i => q K z M (some (pout i))
  have hab : ∀ i, a i ≠ b i := by
    intro i he
    have heport := (qInjectiveWithinOrdinaryFirst K z M (c i) (pin i) (pout i)
      rfl rfl).mp he
    exact htprev i (congrArg (fun p : OrdinaryPort K z => p.val.2) heport)
  have hroots : ∀ i j x, x ∈ [a i, b i] → x ∈ [a j, b j] → i = j := by
    intro i j x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    · exact collision_roots K M z hm c hc i j (pin i) (pin j) rfl rfl
        (Or.inl rfl) (Or.inl rfl) hy
    · exact collision_roots K M z hm c hc i j (pin i) (pout j) rfl rfl
        (Or.inl rfl) (Or.inr (htM j)) hy
    · exact collision_roots K M z hm c hc i j (pout i) (pin j) rfl rfl
        (Or.inr (htM i)) (Or.inl rfl) hy
    · exact collision_roots K M z hm c hc i j (pout i) (pout j) rfl rfl
        (Or.inr (htM i)) (Or.inr (htM j)) hy
  let blocks := fun i => [a i, b i]
  have hnodup : (List.ofFn blocks).flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      simpa [blocks] using hab i
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      apply List.disjoint_left.mpr
      intro x hx hy
      exact (ne_of_lt hij) (hroots i j x hx hy)
  have hlocal : ∀ i, (blocks i).IsChain (G K z M).Adj := by
    intro i
    have hadj : (G K z M).Adj (a i) (b i) := by
      apply quotienttriangleedge K z M (c i) (pin i) (pout i) rfl rfl
      intro he
      exact htprev i (congrArg (fun p : OrdinaryPort K z => p.val.2) he)
    simpa [blocks] using hadj
  have hboundary : ∀ i, (G K z M).Adj (b i) (a (i + 1)) := by
    intro i
    change (G K z M).Adj (q K z M (some ⟨(c i,t i), havoid i, htadj i⟩))
      (q K z M (some ⟨(c (i+1),c ((i+1)-1)), havoid (i+1),
        by simpa using (hcycle i).symm⟩))
    by_cases h : M.Adj (c i) (c (i + 1))
    · simpa only [t, if_pos h, add_sub_cancel_right] using
        contracted_tail_boundary K M z (c i) (c (i + 1)) (s i)
          (havoid i) (havoid (i + 1)) (hcycle i) (hs i).1 (hs i).2.2 h
    · simpa only [t, if_neg h, add_sub_cancel_right] using
        noncontracted_connector_edge K z M (c i) (c (i + 1))
          (havoid i) (havoid (i + 1)) (hcycle i) h
  have hne : ∀ i, blocks i ≠ [] := by intro i; simp [blocks]
  have hchain := UniqueCubicClawCenter.BlockInsertion.cyclic_chain (G K z M)
    blocks hne hlocal (by
      intro i x hx y hy
      simp only [blocks, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hx
      simp only [blocks, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst x
      subst y
      exact hboundary i)
  have hlen : (List.ofFn blocks).flatten.length = 2 * (m + 1) := by
    simp only [blocks, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply, List.length_cons, List.length_nil, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  obtain ⟨v, p, hp, hl⟩ := UniqueCubicClawCenter.exists_cycle_of_nodup_list
    (G K z M) _ (UniqueCubicClawCenter.BlockInsertion.nonempty blocks hne)
    hnodup (by rw [hlen]; omega) hchain
  exact ⟨v, p, hp, hl.trans hlen⟩

/-- A cycle meeting the pole has an ordinary index whose outgoing cycle edge
is not contracted. A used matching edge supplies its head; otherwise the
successor of the pole supplies the index for the extra spare insertion. -/
theorem exists_augmentation_index {V : Type*} (K M : SimpleGraph V) (z : V)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (hpole : ∀ x, ¬M.Adj z x)
    {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → V)
    (hc : Function.Injective c) (hcycle : ∀ i, K.Adj (c i) (c (i + 1)))
    (hhit : ∃ k, c k = z) :
    ∃ j, c j ≠ z ∧ ¬M.Adj (c j) (c (j + 1)) := by
  classical
  by_cases hused : ∃ i, M.Adj (c i) (c (i + 1))
  · obtain ⟨i, hi⟩ := hused
    refine ⟨i + 1, ?_, ?_⟩
    · intro he
      exact hpole (c i) (by simpa only [he] using hi.symm)
    · intro he
      have hvertices := hmatch _ _ _ hi.symm he
      have hindices := hc hvertices
      exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m (by omega) i hindices.symm
  · obtain ⟨k, hk⟩ := hhit
    refine ⟨k + 1, ?_, ?_⟩
    · intro he
      exact (hcycle k).ne (hk.trans he.symm)
    · intro he
      exact hused ⟨k + 1, he⟩

/-- An injectively indexed actual root cycle meeting the pole lifts to a cycle
of exactly twice its length. One ordinary block receives the extra spare port. -/
theorem exists_exact_cycle_meeting_pole {V : Type*} [Fintype V]
    (K M : SimpleGraph V) [DecidableRel K.Adj] (z : V)
    (hdegree : ∀ x, x ≠ z → K.degree x = 3)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (hpole : ∀ x, ¬M.Adj z x)
    {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → V)
    (hc : Function.Injective c) (hcycle : ∀ i, K.Adj (c i) (c (i + 1)))
    (hhit : ∃ k, c k = z) :
    ∃ a, ∃ p : (G K z M).Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  obtain ⟨k, hk⟩ := hhit
  obtain ⟨j, hj, hjM⟩ := exists_augmentation_index K M z hmatch hpole hm c hc hcycle ⟨k, hk⟩
  have hkj : k ≠ j := fun he => hj (he ▸ hk)
  have hpole_iff : ∀ i, c i = z ↔ i = k := by
    intro i
    exact ⟨fun he => hc (he.trans hk.symm), fun he => he ▸ hk⟩
  have hex : ∀ i, ∃ s, c i ≠ z →
      K.Adj (c i) s ∧ s ≠ c (i - 1) ∧ s ≠ c (i + 1) := by
    intro i
    by_cases hi : c i = z
    · exact ⟨c i, fun hn => (hn hi).elim⟩
    · obtain ⟨s, hs⟩ := exists_spare K (c i) (c (i - 1)) (c (i + 1))
        (hdegree (c i) hi)
      exact ⟨s, fun _ => hs⟩
  choose s hs using hex
  let t := fun i => if M.Adj (c i) (c (i + 1)) then s i else c (i + 1)
  have htadj : ∀ i, c i ≠ z → K.Adj (c i) (t i) := by
    intro i hi
    dsimp only [t]
    split_ifs
    · exact (hs i hi).1
    · exact hcycle i
  have htM : ∀ i, c i ≠ z → ¬M.Adj (c i) (t i) := by
    intro i hi
    dsimp only [t]
    split_ifs with h
    · intro he
      exact (hs i hi).2.2 (hmatch _ _ _ he h)
    · exact h
  have htprev : ∀ i, c i ≠ z → c (i - 1) ≠ t i := by
    intro i hi
    dsimp only [t]
    split_ifs
    · exact (hs i hi).2.1.symm
    · intro he
      have hindices := hc he
      have hreturn : ((i - 1) + 1) + 1 = i - 1 := by simpa using hindices.symm
      exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m (by omega) (i - 1) hreturn
  let pin := fun i (hi : c i ≠ z) =>
    (⟨(c i, c (i - 1)), hi, by simpa using (hcycle (i - 1)).symm⟩ : OrdinaryPort K z)
  let pout := fun i (hi : c i ≠ z) =>
    (⟨(c i, t i), hi, htadj i hi⟩ : OrdinaryPort K z)
  let pole := q K z M none
  let a := fun i => if hi : c i = z then pole else q K z M (some (pin i hi))
  let b := fun i => if hi : c i = z then pole else q K z M (some (pout i hi))
  have ha : ∀ i (hi : c i ≠ z), a i = q K z M (some (pin i hi)) := by
    intro i hi
    simp only [a, dif_neg hi]
  have hb : ∀ i (hi : c i ≠ z), b i = q K z M (some (pout i hi)) := by
    intro i hi
    simp only [b, dif_neg hi]
  have hapole : ∀ i, c i = z → a i = pole := by intro i hi; simp [a, hi]
  have hbpole : ∀ i, c i = z → b i = pole := by intro i hi; simp [b, hi]
  have hab : ∀ i, c i ≠ z → a i ≠ b i := by
    intro i hi he
    rw [ha i hi, hb i hi] at he
    have heport := (qInjectiveWithinOrdinaryFirst K z M (c i) (pin i hi) (pout i hi)
      rfl rfl).mp he
    exact htprev i hi (congrArg (fun p : OrdinaryPort K z => p.val.2) heport)
  have hroots : ∀ i j, c i ≠ z → c j ≠ z →
      ∀ x, x ∈ [a i, b i] → x ∈ [a j, b j] → i = j := by
    intro i j hi hj x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    · rw [ha i hi, ha j hj] at hy
      exact collision_roots K M z hm c hc i j (pin i hi) (pin j hj) rfl rfl
        (Or.inl rfl) (Or.inl rfl) hy
    · rw [ha i hi, hb j hj] at hy
      exact collision_roots K M z hm c hc i j (pin i hi) (pout j hj) rfl rfl
        (Or.inl rfl) (Or.inr (htM j hj)) hy
    · rw [hb i hi, ha j hj] at hy
      exact collision_roots K M z hm c hc i j (pout i hi) (pin j hj) rfl rfl
        (Or.inr (htM i hi)) (Or.inl rfl) hy
    · rw [hb i hi, hb j hj] at hy
      exact collision_roots K M z hm c hc i j (pout i hi) (pout j hj) rfl rfl
        (Or.inr (htM i hi)) (Or.inr (htM j hj)) hy
  let base := fun i => if c i = z then [pole] else [a i, b i]
  let spare : OrdinaryPort K z := ⟨(c j,s j), hj, (hs j hj).1⟩
  let extra := q K z M (some spare)
  let blocks := fun i => if i = j then [a i, extra, b i] else base i
  have hnotpole : ∀ i, c i ≠ z → pole ≠ a i ∧ pole ≠ b i := by
    intro i hi
    rw [ha i hi, hb i hi]
    exact ⟨q_none_ne_some K z M _, q_none_ne_some K z M _⟩
  have hbaseRoots : ∀ i l x, x ∈ base i → x ∈ base l → i = l := by
    intro i l x hx hy
    by_cases hi : c i = z <;> by_cases hl : c l = z
    · exact ((hpole_iff i).mp hi).trans ((hpole_iff l).mp hl).symm
    · simp only [base, if_pos hi, List.mem_singleton] at hx
      subst x
      simp only [base, if_neg hl, List.mem_cons, List.not_mem_nil, or_false] at hy
      exact False.elim (hy.elim (hnotpole l hl).1 (hnotpole l hl).2)
    · simp only [base, if_pos hl, List.mem_singleton] at hy
      subst x
      simp only [base, if_neg hi, List.mem_cons, List.not_mem_nil, or_false] at hx
      exact False.elim (hx.elim (hnotpole i hi).1 (hnotpole i hi).2)
    · simp only [base, if_neg hi, if_neg hl] at hx hy
      exact hroots i l hi hl x hx hy
  have hbaseNodup : ∀ i, (base i).Nodup := by
    intro i
    by_cases hi : c i = z
    · simp [base, hi]
    · simpa [base, hi] using hab i hi
  have hfresh : ∀ i, extra ∉ base i := by
    intro i he
    by_cases hi : c i = z
    · simp only [base, if_pos hi, List.mem_singleton] at he
      exact q_none_ne_some K z M spare he.symm
    · simp only [base, if_neg hi, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he
      · apply incoming_ne_spare K M z c hc hcycle i j hi hj (s j)
          (hs j hj).1 (hs j hj).2.1 (hs j hj).2.2
        simpa only [ha i hi, extra, spare, pin] using he.symm
      · rw [hb i hi] at he
        rcases (q_eq_iff K z M _ _).mp he with hport | hrev
        · have hports := Option.some.inj hport
          have hji : j = i := hc (congrArg (fun p : OrdinaryPort K z => p.val.1) hports)
          have hseconds : s j = t i := congrArg (fun p : OrdinaryPort K z => p.val.2) hports
          exact (hs j hj).2.2 (by simpa only [← hji, t, if_neg hjM] using hseconds)
        · have hM : M.Adj (pout i hi).val.1 (pout i hi).val.2 := by
            simpa only [← hrev.1, ← hrev.2.1] using hrev.2.2.symm
          exact htM i hi hM
  have hax : a j ≠ extra := by
    intro he
    apply hfresh j
    simp [base, hj, ← he]
  have hxb : extra ≠ b j := by
    intro he
    apply hfresh j
    simp [base, hj, he]
  have hmem : ∀ i x, x ∈ blocks i → x ∈ base i ∨ i = j ∧ x = extra := by
    intro i x hx
    by_cases hij : i = j
    · subst i
      simp only [blocks, if_pos rfl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · exact Or.inl (by simp [base, hj, hx])
      · exact Or.inr ⟨rfl, hx⟩
      · exact Or.inl (by simp [base, hj, hx])
    · exact Or.inl (by simpa only [blocks, if_neg hij] using hx)
  have hnodup : (List.ofFn blocks).flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      by_cases hij : i = j
      · subst i
        simp [blocks, hax, hxb, hab j hj]
      · simpa only [blocks, if_neg hij] using hbaseNodup i
    · apply List.pairwise_ofFn.mpr
      intro i l hil
      apply List.disjoint_left.mpr
      intro x hx hy
      rcases hmem i x hx with hx | hx <;> rcases hmem l x hy with hy | hy
      · exact (ne_of_lt hil) (hbaseRoots i l x hx hy)
      · exact hfresh i (by simpa only [hy.2] using hx)
      · exact hfresh l (by simpa only [hx.2] using hy)
      · exact (ne_of_lt hil) (hx.1.trans hy.1.symm)
  have hlocal : ∀ i, (blocks i).IsChain (G K z M).Adj := by
    intro i
    by_cases hij : i = j
    · subst i
      have hin : (G K z M).Adj (a j) extra := by
        rw [ha j hj]
        apply quotienttriangleedge K z M (c j) (pin j hj) spare rfl rfl
        intro he
        exact (hs j hj).2.1
          (congrArg (fun p : OrdinaryPort K z => p.val.2) he).symm
      have hout : (G K z M).Adj extra (b j) := by
        rw [hb j hj]
        apply quotienttriangleedge K z M (c j) spare (pout j hj) rfl rfl
        intro he
        have hseconds : s j = t j := congrArg (fun p : OrdinaryPort K z => p.val.2) he
        exact (hs j hj).2.2 (by simpa only [t, if_neg hjM] using hseconds)
      simpa [blocks] using (show (G K z M).Adj (a j) extra ∧
        (G K z M).Adj extra (b j) from ⟨hin, hout⟩)
    · by_cases hi : c i = z
      · simp [blocks, hij, base, hi]
      · have hadj : (G K z M).Adj (a i) (b i) := by
          rw [ha i hi, hb i hi]
          apply quotienttriangleedge K z M (c i) (pin i hi) (pout i hi) rfl rfl
          intro he
          exact htprev i hi (congrArg (fun p : OrdinaryPort K z => p.val.2) he)
        simpa [blocks, hij, base, hi] using hadj
  have hboundary : ∀ i, (G K z M).Adj (b i) (a (i + 1)) := by
    intro i
    by_cases hi : c i = z
    · have hn : c (i + 1) ≠ z := by
        intro he
        exact (hcycle i).ne (hi.trans he.symm)
      rw [hbpole i hi, ha (i + 1) hn]
      simpa only [pole, pin, add_sub_cancel_right, hi] using
        pole_spoke K z M (c (i + 1)) (by simpa only [hi] using hcycle i)
    · by_cases hn : c (i + 1) = z
      · have hnotM : ¬M.Adj (c i) (c (i + 1)) := by
          intro he
          exact hpole (c i) (by simpa only [hn] using he.symm)
        have ht : t i = z := by
          dsimp only [t]
          rw [if_neg hnotM, hn]
        rw [hb i hi, hapole (i + 1) hn]
        simpa only [pole, pout, ht] using
          (pole_spoke K z M (c i) (by simpa only [hn] using (hcycle i).symm)).symm
      · rw [hb i hi, ha (i + 1) hn]
        by_cases h : M.Adj (c i) (c (i + 1))
        · simpa only [pout, pin, t, if_pos h, add_sub_cancel_right] using
            contracted_tail_boundary K M z (c i) (c (i + 1)) (s i)
              hi hn (hcycle i) (hs i hi).1 (hs i hi).2.2 h
        · simpa only [pout, pin, t, if_neg h, add_sub_cancel_right] using
            noncontracted_connector_edge K z M (c i) (c (i + 1)) hi hn (hcycle i) h
  have hhead : ∀ i, (blocks i).head? = some (a i) := by
    intro i
    by_cases hij : i = j
    · simp [blocks, hij]
    · by_cases hi : c i = z
      · simp [blocks, hij, base, hi, hapole i hi]
      · simp [blocks, hij, base, hi]
  have hlast : ∀ i, (blocks i).getLast? = some (b i) := by
    intro i
    by_cases hij : i = j
    · simp [blocks, hij]
    · by_cases hi : c i = z
      · simp [blocks, hij, base, hi, hbpole i hi]
      · simp [blocks, hij, base, hi]
  have hne : ∀ i, blocks i ≠ [] := by
    intro i
    by_cases hij : i = j <;> by_cases hi : c i = z <;> simp [blocks, base, hij, hi]
  have hchain := UniqueCubicClawCenter.BlockInsertion.cyclic_chain (G K z M)
    blocks hne hlocal (by
      intro i x hx y hy
      rw [hlast i] at hx
      rw [hhead (i + 1)] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst x
      subst y
      exact hboundary i)
  have hpoint : ∀ i, (blocks i).length + (if i = k then 1 else 0) =
      2 + (if i = j then 1 else 0) := by
    intro i
    by_cases hik : i = k
    · subst i
      simp [blocks, base, hk, hkj]
    · by_cases hij : i = j
      · subst i
        simp [blocks, hik]
      · have hi : c i ≠ z := fun he => hik ((hpole_iff i).mp he)
        simp [blocks, base, hik, hij, hi]
  have hsum : (∑ i, ((blocks i).length + (if i = k then 1 else 0))) =
      ∑ i, (2 + (if i = j then 1 else 0)) :=
    Finset.sum_congr rfl (fun i _ => hpoint i)
  have hsum' : (∑ i, (blocks i).length) + 1 = 2 * (m + 1) + 1 := by
    simpa [Finset.sum_add_distrib, mul_comm] using hsum
  have hlen : (List.ofFn blocks).flatten.length = 2 * (m + 1) := by
    simpa only [List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply] using Nat.add_right_cancel hsum'
  obtain ⟨v, p, hp, hl⟩ := UniqueCubicClawCenter.exists_cycle_of_nodup_list
    (G K z M) _ (UniqueCubicClawCenter.BlockInsertion.nonempty blocks hne)
    hnodup (by rw [hlen]; omega) hchain
  exact ⟨v, p, hp, hl.trans hlen⟩

/-- Every injectively indexed actual root cycle has an exact double-length cycle
in the partial Fisher quotient, whether or not the root cycle meets the pole. -/
theorem exists_exact_cycle {V : Type*} [Fintype V]
    (K M : SimpleGraph V) [DecidableRel K.Adj] (z : V)
    (hdegree : ∀ x, x ≠ z → K.degree x = 3)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (hpole : ∀ x, ¬M.Adj z x)
    {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → V)
    (hc : Function.Injective c) (hcycle : ∀ i, K.Adj (c i) (c (i + 1))) :
    ∃ a, ∃ p : (G K z M).Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  by_cases hhit : ∃ k, c k = z
  · exact exists_exact_cycle_meeting_pole K M z hdegree hmatch hpole hm c hc hcycle hhit
  · have havoid : ∀ i, c i ≠ z := fun i hi => hhit ⟨i, hi⟩
    exact exists_exact_cycle_avoiding_pole K M z hdegree hmatch hm c hc havoid hcycle

/-- A simple closed walk has an injective cyclic indexing of its actual vertices. -/
private theorem cycle_index_of_walk {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ m : ℕ, p.length = m + 1 ∧ 3 ≤ m + 1 ∧
      ∃ c : Fin (m + 1) → V, Function.Injective c ∧
        ∀ i, G.Adj (c i) (c (i + 1)) := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  let d : Fin p.length → V := fun i => p.getVert i.val
  have hd : Function.Injective d := by
    intro i j hij
    apply Fin.ext
    have hdrop := hp.nodup_dropLast_support
    apply (hdrop.getElem_inj_iff).mp
    · have hi' : i.val < p.support.dropLast.length := by simpa [p.length_support] using i.isLt
      have hj' : j.val < p.support.dropLast.length := by simpa [p.length_support] using j.isLt
      have hiP : i.val < p.support.length := by simpa [p.length_support] using Nat.lt_succ_of_lt i.isLt
      have hjP : j.val < p.support.length := by simpa [p.length_support] using Nat.lt_succ_of_lt j.isLt
      have hs : p.support[i.val]'hiP = p.support[j.val]'hjP := by
        rw [p.support_getElem_eq_getVert, p.support_getElem_eq_getVert]
        exact hij
      simpa only [List.getElem_dropLast hi', List.getElem_dropLast hj'] using hs
    · simpa [p.length_support] using i.isLt
    · simpa [p.length_support] using j.isLt
  let m := p.length - 1
  have hm : p.length = m + 1 := by dsimp only [m]; omega
  let c : Fin (m + 1) → V := fun i => d ⟨i.val, by omega⟩
  have hc : Function.Injective c := by
    intro i j hij
    have hdij : d ⟨i.val, by omega⟩ = d ⟨j.val, by omega⟩ := by
      simpa [c] using hij
    have hval : (⟨i.val, by omega⟩ : Fin p.length) = ⟨j.val, by omega⟩ := hd hdij
    have hval' : (⟨i.val, by omega⟩ : Fin p.length).val =
        (⟨j.val, by omega⟩ : Fin p.length).val :=
      congrArg (fun z : Fin p.length => z.val) hval
    exact Fin.ext hval'
  refine ⟨m, hm, hm ▸ hlen, c, hc, ?_⟩
  intro i
  have hi : i.val < p.length := by omega
  by_cases hn : i.val + 1 < p.length
  · have ha := p.adj_getVert_succ (i := i.val) hi
    change G.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa [c, d, Fin.val_add, Nat.mod_eq_of_lt (show i.val + 1 < m + 1 by omega)] using ha
  · have he : i.val + 1 = p.length := by omega
    have hz : (i + 1 : Fin (m + 1)).val = 0 := by
      simp [Fin.val_add, ← hm, he]
    have ha := p.adj_getVert_succ hi
    change G.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa [c, d, hz, p.getVert_zero, he] using ha


/-- Every ordinary root walk cycle lifts to an actual cycle in the partial Fisher
quotient of exactly twice the original walk length, regardless of pole incidence. -/
theorem exists_exact_cycle_of_walk {V : Type*} [Fintype V]
    (K M : SimpleGraph V) [DecidableRel K.Adj] (z : V)
    (hdegree : ∀ x, x ≠ z → K.degree x = 3)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (hpole : ∀ x, ¬M.Adj z x)
    {a : V} (p : K.Walk a a) (hp : p.IsCycle) :
    ∃ b, ∃ q : (G K z M).Walk b b, q.IsCycle ∧ q.length = 2 * p.length := by
  classical
  obtain ⟨m, hlen, hm, c, hc, hcycle⟩ := cycle_index_of_walk p hp
  have hmin : 2 ≤ m := by omega
  obtain ⟨b, q, hq, hq_len⟩ := exists_exact_cycle K M z hdegree hmatch hpole hmin c hc hcycle
  exact ⟨b, q, hq, by simpa only [hlen] using hq_len⟩

/-- A power-of-two root cycle lifts to a power-of-two cycle in the partial Fisher
quotient, with its exponent increased by one. -/
theorem hasPowerOfTwoCycle_lift {V : Type*} [Fintype V]
    (K M : SimpleGraph V) [DecidableRel K.Adj] (z : V)
    (hdegree : ∀ x, x ≠ z → K.degree x = 3)
    (hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w)
    (hpole : ∀ x, ¬M.Adj z x) (hcycle : HasPowerOfTwoCycle K) :
    HasPowerOfTwoCycle (G K z M) := by
  obtain ⟨n, hn, a, p, hp, hplen⟩ := hcycle
  obtain ⟨b, q, hq, hlen⟩ := exists_exact_cycle_of_walk K M z hdegree hmatch hpole p hp
  refine ⟨n + 1, by omega, b, q, hq, ?_⟩
  calc
    q.length = 2 * p.length := hlen
    _ = 2 * 2 ^ n := by rw [hplen]
    _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

end Erdos64.PartialFisherCycle
