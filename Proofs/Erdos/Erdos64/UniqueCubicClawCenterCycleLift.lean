import Erdos.Erdos64.UniqueCubicClawCenterSuppression
import Erdos.Erdos64.UniqueCubicClawCenterCycleList

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- At an ordinary cubic root node there is at most one direct cubic neighbor
other than the pole root. This is the matching property derived from independence
of the original high-degree vertices, not an additional assumption on the root. -/
theorem nonpole_direct_neighbors_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z C D E : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    (hCz : C ≠ z) (hDz : D ≠ z) (hEz : E ≠ z)
    (hC3 : (cliqueRoot (completion G v)).degree C = 3)
    (hD3 : (cliqueRoot (completion G v)).degree D = 3)
    (hE3 : (cliqueRoot (completion G v)).degree E = 3)
    (hCD : (cliqueRoot (completion G v)).Adj C D)
    (hCE : (cliqueRoot (completion G v)).Adj C E) : D = E := by
  obtain ⟨p, hpC, hpD⟩ := hCD.2
  obtain ⟨q, hqC, hqE⟩ := hCE.2
  have hp4 := old_degree_four_of_cubic_root_edge G hG hv hclaw hunique hz
    hCz hDz hCD.1 hC3 hD3 hpC hpD
  have hq4 := old_degree_four_of_cubic_root_edge G hG hv hclaw hunique hz
    hCz hEz hCE.1 hC3 hE3 hqC hqE
  have hpq : p = q := by
    by_contra hne
    exact old_high_labels_not_same_root_angle G hG hHIGH hv hz hCz hpC hqC hne hp4 hq4
  rw [← hpq] at hqE
  have hD := completion_strongDiamondFree G hG hv
  have hcf := completion_claw_free G hunique
  have hmin := completion_min_degree G hG hv hclaw
  obtain ⟨A, B, hAB, hpA, hpB, hinc⟩ :=
    exactly_two_root_nodes (completion G v) hD hcf hmin p
  rcases (hinc C).mp hpC with rfl | rfl
  · have hDB : D = B := by
      rcases (hinc D).mp hpD with hDA | hDB
      · exact False.elim (hCD.1 hDA.symm)
      · exact hDB
    have hEB : E = B := by
      rcases (hinc E).mp hqE with hEA | hEB
      · exact False.elim (hCE.1 hEA.symm)
      · exact hEB
    exact hDB.trans hEB.symm
  · have hDA : D = A := by
      rcases (hinc D).mp hpD with hDA | hDB
      · exact hDA
      · exact False.elim (hCD.1 hDB.symm)
    have hEA : E = A := by
      rcases (hinc E).mp hqE with hEA | hEB
      · exact hEA
      · exact False.elim (hCE.1 hEB.symm)
    exact hDA.trans hEA.symm

/-- A cubic root clique has a unique third label after two distinct incident
labels have been specified. This label is outside both used incidences. -/
theorem existsUnique_third_root_label {W : Type u} [Fintype W]
    (R : SimpleGraph W) [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ x, ¬ Claw R x) (hmin : ∀ x, 3 ≤ R.degree x)
    {C : RootNode R} (hC3 : (cliqueRoot R).degree C = 3)
    {p q : W} (hp : p ∈ C.val) (hq : q ∈ C.val) (hpq : p ≠ q) :
    ∃! a : W, a ∈ C.val ∧ a ≠ p ∧ a ≠ q := by
  classical
  have hc : C.val.toFinset.card = 3 := by
    rw [Set.toFinset_card, ← cliqueRoot_degree_eq_card R hD hcf hmin C, hC3]
  have hp' : p ∈ C.val.toFinset := by simpa using hp
  have hq' : q ∈ C.val.toFinset.erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, by simpa using hq⟩
  have hcard : ((C.val.toFinset.erase p).erase q).card = 1 := by
    rw [Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hp', hc]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have ha' : a ∈ (C.val.toFinset.erase p).erase q := by
    rw [ha]
    exact Finset.mem_singleton_self a
  have hs : ∀ x : W, x ∈ (C.val.toFinset.erase p).erase q ↔
      x ∈ C.val ∧ x ≠ p ∧ x ≠ q := by
    intro x
    simp only [Finset.mem_erase, Set.mem_toFinset]
    tauto
  refine ⟨a, (hs a).mp ha', ?_⟩
  intro b hb
  have hb' := (hs b).mpr hb
  rw [ha] at hb'
  exact Finset.mem_singleton.mp hb'

/-- The image of chosen incident labels has at least half as many elements as
its source nodes, because a root label belongs to exactly two nodes. -/
theorem cycle_lift_label_image_bound {W : Type u} [Fintype W] [DecidableEq W]
    (R : SimpleGraph W) [DecidableRel R.Adj] (hD : StrongDiamondFree R)
    (hcf : ∀ x, ¬ Claw R x) (hmin : ∀ x, 3 ≤ R.degree x)
    (s : Finset (RootNode R)) (f : RootNode R → W)
    (hf : ∀ C ∈ s, f C ∈ C.val) : s.card ≤ 2 * (s.image f).card := by
  classical
  apply Finset.card_le_mul_card_image s 2
  intro x hx
  obtain ⟨A, B, hAB, hxA, hxB, hinc⟩ := exactly_two_root_nodes R hD hcf hmin x
  have hsub : s.filter (fun C => f C = x) ⊆ {A, B} := by
    intro C hC
    obtain ⟨hCs, hfx⟩ := Finset.mem_filter.mp hC
    have hxC : x ∈ C.val := by rw [← hfx]; exact hf C hCs
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (hinc C).mp hxC
  have hle := Finset.card_le_card hsub
  simpa [hAB] using hle

/-- A finite image large enough for the insertion budget admits a subset of
representatives with precisely that cardinality and no repeated label. -/
theorem cycle_lift_exists_injective_subset {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A → B) (n : ℕ) (hn : n ≤ (s.image f).card) :
    ∃ t ⊆ s, t.card = n ∧ Set.InjOn f (t : Set A) := by
  classical
  obtain ⟨q, hqs, hqn⟩ := Finset.exists_subset_card_eq hn
  have hsurj : Set.SurjOn f (s : Set A) (q : Set B) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (hqs hy)
    exact ⟨x, hx, hxy⟩
  obtain ⟨t, hts, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (s : Set A) q hsurj
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage, hqn] at hcard
  exact ⟨t, hts, hcard.symm, hinj⟩

/-- Matching endpoint counts and incidence-two give enough distinct candidates;
for an odd ordinary-node count they give one additional candidate. -/
theorem cycle_lift_exists_candidates {W : Type u} [Fintype W]
    (R : SimpleGraph W) [DecidableRel R.Adj] (hD : StrongDiamondFree R)
    (hcf : ∀ x, ¬ Claw R x) (hmin : ∀ x, 3 ≤ R.degree x)
    (s : Finset (RootNode R)) (f : RootNode R → W)
    (hf : ∀ C ∈ s, f C ∈ C.val) (b : ℕ) (hbudget : 2 * b ≤ s.card) :
    (∃ t ⊆ s, t.card = b ∧ Set.InjOn f (t : Set (RootNode R))) ∧
    (Odd s.card → ∃ t ⊆ s, t.card = b + 1 ∧ Set.InjOn f (t : Set (RootNode R))) := by
  classical
  have hcount := cycle_lift_label_image_bound R hD hcf hmin s f hf
  constructor
  · apply cycle_lift_exists_injective_subset
    omega
  · rintro ⟨k, hk⟩
    apply cycle_lift_exists_injective_subset
    omega

/-- Every ordinary cycle of length at least three has an injective cyclic
indexing whose consecutive indices follow graph edges, including the closing edge. -/
theorem exists_indexed_cycle {A : Type*} (H : SimpleGraph A) {a : A}
    (p : H.Walk a a) (hp : p.IsCycle) (m : ℕ) (hlen : p.length = m + 1)
    (hn : 3 ≤ m + 1) :
    ∃ c : Fin (m + 1) → A, Function.Injective c ∧ ∀ i, H.Adj (c i) (c (i + 1)) := by
  let c : Fin (m + 1) → A := fun i => p.getVert i.val
  have hinj : Function.Injective c := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)
    exact hij
  refine ⟨c, hinj, ?_⟩
  intro i
  change H.Adj (p.getVert i.val) (p.getVert (i + 1).val)
  rw [Fin.val_add_one]
  split_ifs with hi
  · subst i
    have hedge := p.adj_getVert_succ (i := m) (by omega)
    have hend : p.getVert (m + 1) = a := hlen ▸ p.getVert_length
    simpa only [Fin.val_last, hend, p.getVert_zero] using hedge
  · exact p.adj_getVert_succ (by omega)

/-- A family of used oriented matching edges cannot occupy both an index and
its cyclic successor. Injectivity of the successor then bounds its size by half
the available ordinary endpoints. -/
theorem cycle_matching_endpoint_bound {A : Type*} [DecidableEq A]
    (s r : Finset A) (next : A → A) (hinj : Function.Injective next)
    (hs : s ⊆ r) (ht : ∀ i ∈ s, next i ∈ r)
    (hgap : ∀ i ∈ s, next i ∉ s) : 2 * s.card ≤ r.card := by
  have hdisj : Disjoint s (s.image next) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, hjs, hji⟩ := Finset.mem_image.mp hj
    exact hgap j hjs (hji ▸ hi)
  have hsub : s ∪ s.image next ⊆ r := by
    intro i hi
    rcases Finset.mem_union.mp hi with his | hit
    · exact hs his
    · obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hit
      exact ht j hjs
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective s hinj] at hcard
  omega

/-- A suppressed edge determines a unique incident half-edge at its first
retained endpoint. A split corridor is distinguished from a direct edge by the
intermediate vertex's degree; triangles and parallel corridors exclude ambiguity. -/
theorem existsUnique_suppression_first_neighbor {W : Type u} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hparallel : ∀ a b p q, H.degree a = 3 → H.degree b = 3 → a ≠ b →
      H.degree p = 2 → H.degree q = 2 → p ≠ q →
      H.Adj a p → H.Adj p b → H.Adj a q → H.Adj q b → False)
    {x y : SuppressionNode H} (hxy : (suppression H).Adj x y) :
    ∃! m : W, H.Adj x.val m ∧
      ((m = y.val ∧ H.degree m = 3) ∨ (H.degree m = 2 ∧ H.Adj m y.val)) := by
  have hex : ∃ m : W, H.Adj x.val m ∧
      ((m = y.val ∧ H.degree m = 3) ∨ (H.degree m = 2 ∧ H.Adj m y.val)) := by
    rcases hxy.2 with hdir | ⟨m, hm, hxm, hmy⟩
    · exact ⟨y.val, hdir, Or.inl ⟨rfl, y.property⟩⟩
    · exact ⟨m, hxm, Or.inr ⟨hm, hmy⟩⟩
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, hm, ?_⟩
  intro n hn
  rcases hm.2 with ⟨hmy, hm3⟩ | ⟨hm2, hmy⟩
  · rcases hn.2 with ⟨hny, hn3⟩ | ⟨hn2, hny⟩
    · exact hny.trans hmy.symm
    · have hxy' : H.Adj x.val y.val := hmy ▸ hm.1
      exact False.elim (htri x.val y.val n hxy' hny.symm hn.1.symm)
  · rcases hn.2 with ⟨hny, hn3⟩ | ⟨hn2, hny⟩
    · have hxy' : H.Adj x.val y.val := hny ▸ hn.1
      exact False.elim (htri x.val y.val m hxy' hmy.symm hm.1.symm)
    · by_contra hnm
      have hvals : x.val ≠ y.val := fun heq => hxy.1 (Subtype.ext heq)
      exact hparallel x.val y.val n m x.property y.property hvals hn2 hm2 hnm
        hn.1 hny hm.1 hmy

/-- The label on a root edge determines its unordered pair of endpoints.
Thus label collisions are edge collisions, rather than merely shared corridors. -/
theorem root_edge_label_eq_iff {W : Type u} [Fintype W]
    (R : SimpleGraph W) [DecidableRel R.Adj] (hD : StrongDiamondFree R)
    (hcf : ∀ x, ¬ Claw R x) (hmin : ∀ x, 3 ≤ R.degree x)
    {A B C D : RootNode R} (hAB : A ≠ B) (hCD : C ≠ D)
    {p q : W} (hpA : p ∈ A.val) (hpB : p ∈ B.val)
    (hqC : q ∈ C.val) (hqD : q ∈ D.val) :
    p = q ↔ (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  constructor
  · intro hpq
    subst q
    have hC := root_incidence_exhausted R hD hcf hmin hAB hpA hpB hqC
    have hE := root_incidence_exhausted R hD hcf hmin hAB hpA hpB hqD
    rcases hC with hCA | hCB
    · rcases hE with hDA | hDB
      · exact False.elim (hCD (hCA.trans hDA.symm))
      · exact Or.inl ⟨hCA.symm, hDB.symm⟩
    · rcases hE with hDA | hDB
      · exact Or.inr ⟨hDA.symm, hCB.symm⟩
      · exact False.elim (hCD (hCB.trans hDB.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact root_intersection_unique R hD hAB hpA hpB hqC hqD
    · exact root_intersection_unique R hD hAB hpA hpB hqD hqC

example : ∃ t ⊆ ({0, 1, 2} : Finset ℕ), t.card = 2 ∧
    Set.InjOn (fun x : ℕ => x + 3) (t : Set ℕ) := by
  exact cycle_lift_exists_injective_subset {0, 1, 2} (fun x => x + 3) 2 (by decide)

/-- A common used root-edge label identifies the unordered retained endpoints
of its suppression corridor. This handles direct and split corridors uniformly. -/
theorem suppressed_label_collision {W : Type u} [Fintype W]
    (R : SimpleGraph W) [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {x y s t : SuppressionNode (cliqueRoot R)} {m n : RootNode R}
    (hxy : (suppression (cliqueRoot R)).Adj x y)
    (hst : (suppression (cliqueRoot R)).Adj s t)
    (hxm : (cliqueRoot R).Adj x.val m) (hsn : (cliqueRoot R).Adj s.val n)
    (hmy : (m = y.val ∧ (cliqueRoot R).degree m = 3) ∨
      ((cliqueRoot R).degree m = 2 ∧ (cliqueRoot R).Adj m y.val))
    (hnt : (n = t.val ∧ (cliqueRoot R).degree n = 3) ∨
      ((cliqueRoot R).degree n = 2 ∧ (cliqueRoot R).Adj n t.val))
    {p : W} (hpx : p ∈ x.val.val) (hpm : p ∈ m.val)
    (hps : p ∈ s.val.val) (hpn : p ∈ n.val) :
    (x = s ∧ y = t) ∨ (x = t ∧ y = s) := by
  have hpair := (root_edge_label_eq_iff R hD hcf hmin hxm.1 hsn.1
    hpx hpm hps hpn).mp rfl
  rcases hpair with ⟨hxs, hmn⟩ | ⟨hxn, hms⟩
  · have hxs' : x = s := Subtype.ext hxs
    subst s
    rw [← hmn] at hnt
    exact Or.inl ⟨rfl, suppression_endpoint_unique (cliqueRoot R) hxm hxy hst hmy hnt⟩
  · have hm3 : (cliqueRoot R).degree m = 3 := hms ▸ s.property
    have hn3 : (cliqueRoot R).degree n = 3 := hxn ▸ x.property
    have hmy' : m = y.val := by
      rcases hmy with hm | hm
      · exact hm.1
      · omega
    have hnt' : n = t.val := by
      rcases hnt with hn | hn
      · exact hn.1
      · omega
    exact Or.inr ⟨Subtype.ext (hxn.trans hnt'), Subtype.ext (hmy'.symm.trans hms)⟩

end Erdos64.UniqueCubicClawCenter
