import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false

namespace ErdosCandidates.E77

open SimpleGraph

private theorem extend_clique {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {t : Finset V} {v : V} {k : ℕ} (h : G.IsNClique k t)
    (hv : v ∉ t) (ha : ∀ x ∈ t, G.Adj v x) :
    G.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert, G.isClique_insert]
    exact ⟨h.isClique, fun x hx _ => ha x hx⟩
  · rw [Finset.card_insert_of_notMem hv, h.card_eq]

/-- The classical off-diagonal binomial bound, with exact-sized clique witnesses
contained in any vertex finset of at least `choose (m+n) m` vertices. -/
theorem offDiagonal_cliques {V : Type*} (m n : ℕ)
    (G : SimpleGraph V) (s : Finset V) (hs : (m + n).choose m ≤ s.card) :
    (∃ t : Finset V, t ⊆ s ∧ G.IsNClique (m + 1) t) ∨
    (∃ t : Finset V, t ⊆ s ∧ Gᶜ.IsNClique (n + 1) t) := by
  classical
  induction m generalizing n s with
  | zero =>
    have hpos : 0 < s.card := by simpa using hs
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
  | succ m ihm =>
    induction n generalizing s with
    | zero =>
      have hpos : 0 < s.card := by simpa using hs
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      exact Or.inr ⟨{v}, by simpa using hv, by simp⟩
    | succ n ihn =>
      have hpos : 0 < s.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hs
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      let u := s.erase v
      let A := u.filter (G.Adj v)
      let B := u.filter (fun x => ¬G.Adj v x)
      have hsum : A.card + B.card = s.card - 1 := by
        change (u.filter (G.Adj v)).card + (u.filter (fun x => ¬G.Adj v x)).card = _
        rw [Finset.card_filter_add_card_filter_not]
        exact Finset.card_erase_of_mem hv
      have hpascal : (m + 1 + (n + 1)).choose (m + 1) =
          (m + (n + 1)).choose m + (m + 1 + n).choose (m + 1) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.choose_succ_succ (m + n + 1) m
      have hsplit : (m + (n + 1)).choose m ≤ A.card ∨
          (m + 1 + n).choose (m + 1) ≤ B.card := by
        rw [hpascal] at hs
        omega
      rcases hsplit with hA | hB
      · rcases ihm (n + 1) A hA with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
        · have hmem : ∀ x ∈ t, x ∈ s ∧ x ≠ v ∧ G.Adj v x := by
            intro x hx
            have hxa := Finset.mem_filter.mp (ht hx)
            have hxu := Finset.mem_erase.mp hxa.1
            exact ⟨hxu.2, hxu.1, hxa.2⟩
          have hvt : v ∉ t := by
            intro hvt
            exact (hmem v hvt).2.1 rfl
          exact Or.inl ⟨insert v t, Finset.insert_subset hv (fun x hx => (hmem x hx).1),
            extend_clique G hc hvt (fun x hx => (hmem x hx).2.2)⟩
        · exact Or.inr ⟨t, fun x hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp (ht hx)).1).2, hc⟩
      · rcases ihn B hB with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
        · exact Or.inl ⟨t, fun x hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp (ht hx)).1).2, hc⟩
        · have hmem : ∀ x ∈ t, x ∈ s ∧ x ≠ v ∧ ¬G.Adj v x := by
            intro x hx
            have hxb := Finset.mem_filter.mp (ht hx)
            have hxu := Finset.mem_erase.mp hxb.1
            exact ⟨hxu.2, hxu.1, hxb.2⟩
          have hvt : v ∉ t := by
            intro hvt
            exact (hmem v hvt).2.1 rfl
          exact Or.inr ⟨insert v t, Finset.insert_subset hv (fun x hx => (hmem x hx).1),
            extend_clique Gᶜ hc hvt (fun x hx =>
              (G.compl_adj v x).mpr ⟨(hmem x hx).2.1.symm, (hmem x hx).2.2⟩)⟩

/-- Every graph on `Fin n` contains a `k`-clique in it or its complement. -/
def HasRamseyProperty (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree k ∨ ¬ Gᶜ.CliqueFree k

/-- The least vertex count with the diagonal Ramsey property. Finiteness below
ensures this natural infimum is taken over a nonempty set. -/
noncomputable def R (k : ℕ) : ℕ := sInf {n : ℕ | HasRamseyProperty n k}

/-- Exact clique witnesses are equivalent to failure of clique-freeness. -/
theorem not_cliqueFree_iff_exists {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    ¬G.CliqueFree k ↔ ∃ s : Finset V, G.IsNClique k s := by
  classical
  simp [SimpleGraph.CliqueFree]

/-- Zero-sized cliques exist even on the empty vertex type. -/
theorem hasRamseyProperty_zero (n : ℕ) : HasRamseyProperty n 0 := by
  intro G
  left
  exact (not_cliqueFree_iff_exists G 0).mpr ⟨∅, by simp⟩

example : HasRamseyProperty 0 0 := hasRamseyProperty_zero 0
example (k : ℕ) : R k = sInf {n : ℕ | HasRamseyProperty n k} := rfl

/-- The off-diagonal binomial bound in positive clique-size parameters. -/
theorem offDiagonal_bound {V : Type*} [Fintype V] (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (G : SimpleGraph V)
    (hV : (a + b - 2).choose (a - 1) ≤ Fintype.card V) :
    ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b := by
  classical
  have hab : a - 1 + (b - 1) = a + b - 2 := by omega
  have hcard : (a - 1 + (b - 1)).choose (a - 1) ≤
      (Finset.univ : Finset V).card := by simpa only [hab, Finset.card_univ] using hV
  rcases offDiagonal_cliques (a - 1) (b - 1) G Finset.univ hcard with
    ⟨t, _, ht⟩ | ⟨t, _, ht⟩
  · left
    apply (not_cliqueFree_iff_exists G a).mpr
    exact ⟨t, by simpa only [Nat.sub_add_cancel ha] using ht⟩
  · right
    apply (not_cliqueFree_iff_exists Gᶜ b).mpr
    exact ⟨t, by simpa only [Nat.sub_add_cancel hb] using ht⟩

/-- The classical binomial vertex count has the diagonal Ramsey property. -/
theorem hasRamseyProperty_choose (k : ℕ) (hk : 1 ≤ k) :
    HasRamseyProperty ((2 * k - 2).choose (k - 1)) k := by
  intro G
  apply offDiagonal_bound k k hk hk G
  simp [Fintype.card_fin, two_mul]

/-- Finite diagonal Ramsey theorem, including the empty-clique boundary `k = 0`. -/
theorem ramsey_finite (k : ℕ) : {n : ℕ | HasRamseyProperty n k}.Nonempty := by
  cases k with
  | zero => exact ⟨0, hasRamseyProperty_zero 0⟩
  | succ k => exact ⟨_, hasRamseyProperty_choose (k + 1) (by omega)⟩

private theorem clique_comap_lift {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (G : SimpleGraph W) {k : ℕ} {s : Finset V}
    (h : (G.comap f).IsNClique k s) : G.IsNClique k (s.map f) := by
  refine ⟨?_, by rw [Finset.card_map, h.card_eq]⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
  exact h.isClique ha hb (fun hab => hxy (congrArg f hab))

private theorem compl_comap_embedding {V W : Type*} (f : V ↪ W)
    (G : SimpleGraph W) : (G.comap f)ᶜ = Gᶜ.comap f := by
  ext x y
  change (x ≠ y ∧ ¬G.Adj (f x) (f y)) ↔ (f x ≠ f y ∧ ¬G.Adj (f x) (f y))
  simp only [f.injective.ne_iff]

/-- The diagonal Ramsey property is upward closed in the vertex count. -/
theorem hasRamseyProperty_of_le {n m k : ℕ} (hnm : n ≤ m)
    (h : HasRamseyProperty n k) : HasRamseyProperty m k := by
  classical
  intro G
  let f : Fin n ↪ Fin m := ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩
  rcases h (G.comap f) with hr | hb
  · obtain ⟨t, ht⟩ := (not_cliqueFree_iff_exists (G.comap f) k).mp hr
    exact Or.inl ((not_cliqueFree_iff_exists G k).mpr ⟨t.map f, clique_comap_lift f G ht⟩)
  · rw [compl_comap_embedding] at hb
    obtain ⟨t, ht⟩ := (not_cliqueFree_iff_exists (Gᶜ.comap f) k).mp hb
    exact Or.inr ((not_cliqueFree_iff_exists Gᶜ k).mpr ⟨t.map f, clique_comap_lift f Gᶜ ht⟩)

/-- Original one-step monotonicity signature, as a corollary of upward closure. -/
theorem hasRamseyProperty_mono (n k : ℕ) (h : HasRamseyProperty n k) :
    HasRamseyProperty (n + 1) k :=
  hasRamseyProperty_of_le (Nat.le_succ n) h

/-- The least Ramsey vertex count itself has the Ramsey property. -/
theorem hasRamseyProperty_R (k : ℕ) : HasRamseyProperty (R k) k :=
  Nat.sInf_mem (ramsey_finite k)

/-- The natural infimum is a genuine threshold, not an empty-set default. -/
theorem R_le_iff (n k : ℕ) : R k ≤ n ↔ HasRamseyProperty n k := by
  constructor
  · intro h
    exact hasRamseyProperty_of_le h (hasRamseyProperty_R k)
  · intro h
    exact Nat.sInf_le h

/-- The classical diagonal binomial upper bound. -/
theorem R_le_choose (k : ℕ) (hk : 1 ≤ k) :
    R k ≤ (2 * k - 2).choose (k - 1) :=
  (R_le_iff _ k).mpr (hasRamseyProperty_choose k hk)

/-- Erdős–Szekeres' classical exponential upper bound for diagonal Ramsey numbers. -/
theorem R_upper_bound (k : ℕ) (hk : 1 ≤ k) : R k ≤ 4 ^ k := by
  calc
    R k ≤ (2 * k - 2).choose (k - 1) := R_le_choose k hk
    _ ≤ 2 ^ (2 * k - 2) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    _ = 4 ^ k := by rw [pow_mul]; rfl

/-- The zero-clique Ramsey number is zero. -/
theorem R_zero : R 0 = 0 := by
  exact Nat.eq_zero_of_le_zero ((R_le_iff 0 0).mpr (hasRamseyProperty_zero 0))

end ErdosCandidates.E77
