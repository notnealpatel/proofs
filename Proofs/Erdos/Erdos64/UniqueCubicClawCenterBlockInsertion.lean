import Mathlib

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter.BlockInsertion

/-- Simultaneously prepending fresh, index-unique optional labels preserves nodup. -/
theorem nodup {V : Type*} {n : ℕ} (blocks : Fin n → List V)
    (insert : Fin n → Option V)
    (hbase : (List.ofFn blocks).flatten.Nodup)
    (hfresh : ∀ i x, insert i = some x → x ∉ (List.ofFn blocks).flatten)
    (hunique : ∀ i j x, insert i = some x → insert j = some x → i = j) :
    (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.Nodup := by
  have hmem (i : Fin n) {x : V} (hx : x ∈ blocks i) :
      x ∈ (List.ofFn blocks).flatten :=
    List.mem_flatten.mpr ⟨blocks i, List.mem_ofFn.mpr ⟨i, rfl⟩, hx⟩
  have hb := List.nodup_flatten.mp hbase
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    have hi := hb.1 (blocks i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    cases he : insert i with
    | none => simpa using hi
    | some x =>
      simpa using List.nodup_cons.mpr ⟨(fun hx => hfresh i x he (hmem i hx)), hi⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hy
    have hd := List.disjoint_left.mp (List.pairwise_ofFn.mp hb.2 hij)
    simp only [List.mem_append, Option.mem_toList] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (ne_of_lt hij) (hunique i j x hx hy)
    · exact hfresh i x hx (hmem j hy)
    · exact hfresh j x hy (hmem i hx)
    · exact hd hx hy

/-- The flattened length increases by exactly the number of selected indices. -/
theorem length {V : Type*} {n : ℕ} (blocks : Fin n → List V)
    (insert : Fin n → Option V) :
    (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.length =
      (List.ofFn blocks).flatten.length +
        (Finset.univ.filter (fun i => (insert i).isSome)).card := by
  classical
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    List.length_append]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases insert i <;> simp

private theorem head_flatten_cons {V : Type*} (b : List V) (bs : List (List V))
    (hb : b ≠ []) : (b :: bs).flatten.head? = b.head? := by
  simpa only [List.flatten_cons] using List.head?_append_of_ne_nil b hb

private theorem chain_flatten {V : Type*} (R : V → V → Prop)
    (bs : List (List V))
    (hne : ∀ b ∈ bs, b ≠ [])
    (hlocal : ∀ b ∈ bs, b.IsChain R)
    (hboundary : bs.IsChain (fun a b => ∀ x ∈ a.getLast?, ∀ y ∈ b.head?, R x y)) :
    bs.flatten.IsChain R := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb := hne b (by simp)
    have hc := hlocal b (by simp)
    have ht := ih (fun c hc => hne c (by simp [hc]))
      (fun c hc => hlocal c (by simp [hc])) hboundary.tail
    rw [List.flatten_cons, List.isChain_append]
    refine ⟨hc, ht, ?_⟩
    cases bs with
    | nil => simp
    | cons c cs =>
      rw [head_flatten_cons c cs (hne c (by simp))]
      exact (List.isChain_cons_cons.mp hboundary).1

/-- Flattening nonempty indexed blocks has the first block's first endpoint. -/
theorem head_flatten {V : Type*} {m : ℕ} (blocks : Fin (m + 1) → List V)
    (hne : ∀ i, blocks i ≠ []) :
    (List.ofFn blocks).flatten.head? = (blocks 0).head? := by
  rw [List.ofFn_succ]
  exact head_flatten_cons _ _ (hne 0)

/-- Flattening nonempty indexed blocks has the last block's last endpoint. -/
theorem getLast_flatten {V : Type*} {m : ℕ} (blocks : Fin (m + 1) → List V)
    (hne : ∀ i, blocks i ≠ []) :
    (List.ofFn blocks).flatten.getLast? = (blocks (Fin.last m)).getLast? := by
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
  simpa using List.getLast?_append_of_ne_nil
    (List.ofFn (fun i : Fin m => blocks i.castSucc)).flatten (hne (Fin.last m))

/-- Flattening nonempty indexed blocks is nonempty, including at one block. -/
theorem nonempty {V : Type*} {m : ℕ} (blocks : Fin (m + 1) → List V)
    (hne : ∀ i, blocks i ≠ []) : (List.ofFn blocks).flatten ≠ [] := by
  rw [List.ofFn_succ, List.flatten_cons]
  intro he
  exact hne 0 (List.append_eq_nil_iff.mp he).1

/-- Local chains and cyclic adjacent-block boundaries give a closed flattened chain. -/
theorem cyclic_chain {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (blocks : Fin (m + 1) → List V)
    (hne : ∀ i, blocks i ≠ [])
    (hlocal : ∀ i, (blocks i).IsChain G.Adj)
    (hboundary : ∀ i a, a ∈ (blocks i).getLast? →
      ∀ b, b ∈ (blocks (i + 1)).head? → G.Adj a b) :
    ((List.ofFn blocks).flatten ++
      [(List.ofFn blocks).flatten.head (nonempty blocks hne)]).IsChain G.Adj := by
  apply List.isChain_append.mpr
  refine ⟨chain_flatten G.Adj _ ?_ ?_ ?_, by simp, ?_⟩
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact hne i
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact hlocal i
  · apply List.isChain_ofFn.mpr
    intro i hi
    have hs : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (m + 1)) + 1 = ⟨i + 1, hi⟩ := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hi]
    simpa only [hs] using hboundary ⟨i, Nat.lt_of_succ_lt hi⟩
  · intro a ha b hb
    have he : (Fin.last m : Fin (m + 1)) + 1 = 0 := by
      apply Fin.ext
      simp [Fin.val_add, Fin.last]
    have hfirst : b ∈ (blocks 0).head? := by
      rw [← head_flatten blocks hne, List.head?_eq_some_head (nonempty blocks hne)]
      simpa using hb
    rw [getLast_flatten blocks hne] at ha
    apply hboundary (Fin.last m) a ha b
    simpa only [he] using hfirst

/-- A prefix insertion cannot empty an originally nonempty block. -/
theorem modified_nonempty {V : Type*} {n : ℕ} (blocks : Fin n → List V)
    (insert : Fin n → Option V) (hne : ∀ i, blocks i ≠ []) :
    ∀ i, (insert i).toList ++ blocks i ≠ [] := by
  intro i he
  exact hne i (List.append_eq_nil_iff.mp he).2

/-- Simultaneous indexed insertion yields nonemptiness, nodup, exact insertion count,
and a closed adjacency chain using only the modified blocks' local adjacencies. -/
theorem certificates {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (blocks : Fin (m + 1) → List V) (insert : Fin (m + 1) → Option V)
    (hne : ∀ i, blocks i ≠ [])
    (hbase : (List.ofFn blocks).flatten.Nodup)
    (hfresh : ∀ i x, insert i = some x → x ∉ (List.ofFn blocks).flatten)
    (hunique : ∀ i j x, insert i = some x → insert j = some x → i = j)
    (hlocal : ∀ i, ((insert i).toList ++ blocks i).IsChain G.Adj)
    (hboundary : ∀ i a, a ∈ ((insert i).toList ++ blocks i).getLast? →
      ∀ b, b ∈ ((insert (i + 1)).toList ++ blocks (i + 1)).head? → G.Adj a b) :
    ∃ hfinal : (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten ≠ [],
      (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.Nodup ∧
      (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.length =
        (List.ofFn blocks).flatten.length +
          (Finset.univ.filter (fun i => (insert i).isSome)).card ∧
      ((List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten ++
        [(List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.head hfinal]).IsChain
          G.Adj := by
  let modified := fun i => (insert i).toList ++ blocks i
  have hmodified : ∀ i, modified i ≠ [] := modified_nonempty blocks insert hne
  refine ⟨nonempty modified hmodified, nodup blocks insert hbase hfresh hunique,
    length blocks insert, ?_⟩
  exact cyclic_chain G modified hmodified hlocal hboundary

end Erdos64.UniqueCubicClawCenter.BlockInsertion
