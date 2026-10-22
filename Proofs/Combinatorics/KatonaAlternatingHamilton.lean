/-
# Katona's conjecture: alternating Hamilton cycles in the Boolean lattice

Yuxian Dong and Jianxi Mao, *Alternating Hamilton Paths and Cycles in
Poset Products*, arXiv:2610.18152, Conjecture 1.1 (Katona, Discrete Appl.
Math. 2013, Section 8) and Corollary 1.3: the Boolean lattice `B_n`
admits an alternating Hamilton cycle for every `n ≥ 3`. Such a cycle
is a cyclic enumeration alternating strict increases and decreases.
The construction below uses Lemma 2.2, Section 2.

## Route

The paper deduces the conjecture from `B_n ≅ B_1 × B_{n-1}` and Theorem 1.2(i)
for all `r ≥ 2`.  We use only the `r = 2` step (Lemma 2.2, even case) and
induct by two: `B_{k+2} ≅ B_k × B_2`, where `B_1` and `B_2` have explicit
alternating Hamilton paths and `B_k` (`k ≥ 3`) inherits one from its cycle.
The even-`|P|` gadget of Lemma 2.2 also covers `|P| = 2` (it then produces an
AHC of `B_3`), so no separate `B_3` base case is needed.

Alternating walks are encoded as lists of elements labelled `false` (valley)
or `true` (peak); `AltStep` is symmetric, so reversing a segment is free.
-/
import Mathlib

set_option autoImplicit false

namespace KatonaAlternatingHamilton

open List

/-! ## The statement -/

section Statement

variable {α : Type*} [Preorder α]

/-- `IsAltHamCycle x` says that the enumeration `x : Fin N ≃ α` of all elements of `α` is an
alternating Hamilton cycle `x 0 < x 1 > x 2 < ⋯ < x (N - 1) > x 0` in the comparability graph:
from an even position the cyclic successor (`finRotate`) is strictly larger, and from an odd
position it is strictly smaller.  This is the paper's first pattern
`x_1 < x_2 > x_3 < ⋯ < x_{|P|} > x_1`, indexed from `0`. -/
def IsAltHamCycle {N : ℕ} (x : Fin N ≃ α) : Prop :=
  ∀ i : Fin N, (Even (i : ℕ) → x i < x (finRotate N i)) ∧ (Odd (i : ℕ) → x (finRotate N i) < x i)

/-- `0 < 2 > 1 < 3 > 0` is an alternating Hamilton cycle of the chain `Fin 4`. -/
example : IsAltHamCycle (Equiv.swap (1 : Fin 4) 2) := by
  unfold IsAltHamCycle
  decide

/-- The identity enumeration `0 < 1 < 2 < 3` of `Fin 4` is not alternating. -/
example : ¬ IsAltHamCycle (Equiv.refl (Fin 4)) := by
  unfold IsAltHamCycle
  decide

end Statement

/-! ## Labelled alternating walks -/

section Generic

variable {α : Type*}

/-- One step of an alternating walk between labelled elements: a valley (label `false`) is
followed by a strictly larger peak (label `true`), or a peak by a strictly smaller valley. -/
def AltStep [Preorder α] (u v : α × Bool) : Prop :=
  (u.2 = false ∧ v.2 = true ∧ u.1 < v.1) ∨ (u.2 = true ∧ v.2 = false ∧ v.1 < u.1)

instance instDecidableRelAltStep [Preorder α] [DecidableLT α] :
    DecidableRel (AltStep (α := α)) := fun u v => by
  unfold AltStep
  infer_instance

/-- `AltStep` is symmetric. -/
lemma AltStep.symm [Preorder α] {u v : α × Bool} (h : AltStep u v) : AltStep v u := by
  unfold AltStep at *
  tauto

/-- Along an `AltStep` the label flips. -/
lemma AltStep.label [Preorder α] {u v : α × Bool} (h : AltStep u v) : v.2 = !u.2 := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> simp [h1, h2]

/-- Reversing an alternating walk gives an alternating walk. -/
lemma isChain_altStep_reverse [Preorder α] {l : List (α × Bool)}
    (h : List.IsChain AltStep l) : List.IsChain AltStep l.reverse :=
  isChain_reverse.2 (h.imp fun _ _ hab => hab.symm)

/-- A labelled alternating Hamilton path: an alternating walk whose underlying elements list
every element of `α` exactly once. -/
def IsLabelledAHP [Preorder α] (l : List (α × Bool)) : Prop :=
  List.IsChain AltStep l ∧ (l.map Prod.fst).Nodup ∧ ∀ x : α, x ∈ l.map Prod.fst

/-- A labelled alternating Hamilton cycle: a list starting at a valley `c₀`, listing every element
of `α` exactly once, which stays an alternating walk after closing it up with `c₀`. -/
def IsLabelledAHC [Preorder α] (C : List (α × Bool)) : Prop :=
  ∃ c₀ : α, ∃ M : List (α × Bool), C = (c₀, false) :: M ∧
    List.IsChain AltStep (C ++ [(c₀, false)]) ∧ (C.map Prod.fst).Nodup ∧
      ∀ x : α, x ∈ C.map Prod.fst

/-- A duplicate-free list of all elements of a finite type has length the cardinality. -/
lemma length_eq_card_of_nodup_of_forall_mem [Fintype α] {l : List α} (hnd : l.Nodup)
    (hcov : ∀ x, x ∈ l) : l.length = Fintype.card α := by
  classical
  rw [← Fintype.card_fin l.length]
  exact Fintype.card_congr (hnd.getEquivOfForallMemList l hcov)

/-- Pigeonhole: a list containing every element of a finite type, of length at most the
cardinality, has no duplicates. -/
lemma nodup_of_forall_mem_of_length_le [Fintype α] {l : List α} (hcov : ∀ x, x ∈ l)
    (hlen : l.length ≤ Fintype.card α) : l.Nodup := by
  classical
  have hcov' : ∀ x, x ∈ l.dedup := fun x => List.mem_dedup.2 (hcov x)
  have hd : l.dedup.length = Fintype.card α :=
    length_eq_card_of_nodup_of_forall_mem (List.nodup_dedup l) hcov'
  have hle := (List.dedup_sublist l).length_le
  have heq : l.dedup = l := (List.dedup_sublist l).eq_of_length (by omega)
  rw [← heq]
  exact List.nodup_dedup l

/-- Gluing two chains that share the element `c`. -/
lemma isChain_glue {R : α → α → Prop} {l₁ l₂ : List α} {c : α}
    (h₁ : List.IsChain R (l₁ ++ [c])) (h₂ : List.IsChain R (c :: l₂)) :
    List.IsChain R (l₁ ++ c :: l₂) :=
  isChain_split.2 ⟨h₁, h₂⟩

end Generic

/-! ## Lemma 2.2: from an AHP of `P` to an AHC of `P × B_2` -/

section Product

variable {P : Type*}

/-- Put the labelled element `p` into the copy `P × {A}` of `P` inside `P × B_2`. -/
def tagAt (A : Finset (Fin 2)) (p : P × Bool) : (P × Finset (Fin 2)) × Bool := ((p.1, A), p.2)

/-- Put the labelled element `p` into the copy `P × {σ p}`, the copy depending on `p`. -/
def lift (σ : P × Bool → Finset (Fin 2)) (p : P × Bool) : (P × Finset (Fin 2)) × Bool :=
  ((p.1, σ p), p.2)

/-- The cycle of Lemma 2.2 (even case) built from an alternating Hamilton path
`a < x₁ > x₂ < ⋯ > x_{N-2} < z` of `P` whose inner part is `M`.  Writing `{0}`, `{1}` for the
paper's `{1}`, `{2}`, the cycle is
`(a,∅) < I_∅ < (z,{0}) > (z,∅) < (z,{1}) > rev I_{1} > (a,{1}) < (a,univ) > (a,{0}) < I_univ
 < (z,univ) > rev I_{0} > (a,∅)`. -/
def prodCycle (a z : P) (M : List (P × Bool)) : List ((P × Finset (Fin 2)) × Bool) :=
  ((a, ∅), false) :: (M.map (tagAt ∅) ++ ((z, {0}), true) :: ((z, ∅), false) :: ((z, {1}), true) ::
    ((M.map (tagAt {1})).reverse ++ ((a, {1}), false) :: ((a, Finset.univ), true) ::
      ((a, {0}), false) ::
      (M.map (tagAt Finset.univ) ++ ((z, Finset.univ), true) :: (M.map (tagAt {0})).reverse)))

/-- Lifting an alternating walk into `P × B_2` keeps it alternating, provided the copy chosen
for a valley is always below the copy chosen for a peak. -/
lemma isChain_map_lift [PartialOrder P] (σ : P × Bool → Finset (Fin 2))
    (hσ : ∀ u v : P, σ (u, false) ≤ σ (v, true)) {l : List (P × Bool)}
    (h : List.IsChain AltStep l) : List.IsChain AltStep (l.map (lift σ)) := by
  rw [isChain_map]
  refine h.imp ?_
  rintro ⟨x, b⟩ ⟨y, c⟩ hxy
  rcases hxy with ⟨hb, hc, hlt⟩ | ⟨hb, hc, hlt⟩
  · simp only at hb hc hlt
    subst hb hc
    exact Or.inl ⟨rfl, rfl, Prod.mk_lt_mk_of_lt_of_le hlt (hσ x y)⟩
  · simp only at hb hc hlt
    subst hb hc
    exact Or.inr ⟨rfl, rfl, Prod.mk_lt_mk_of_lt_of_le hlt (hσ y x)⟩

/-- Computing a lift that is constant on the inner part of a path. -/
lemma map_lift_eq (σ : P × Bool → Finset (Fin 2)) (A : Finset (Fin 2)) (a z : P)
    (M : List (P × Bool)) (hM : ∀ p ∈ M, σ p = A) :
    ((a, false) :: M ++ [(z, true)]).map (lift σ) =
      ((a, σ (a, false)), false) :: M.map (tagAt A) ++ [((z, σ (z, true)), true)] := by
  have hmap : M.map (lift σ) = M.map (tagAt A) :=
    map_congr_left fun p hp => by simp only [lift, tagAt, hM p hp]
  simp only [cons_append, map_cons, map_append, map_nil, hmap, lift]

/-- The closed-up cycle of Lemma 2.2 is an alternating walk. -/
lemma prodCycle_chain [PartialOrder P] (a z : P) (M : List (P × Bool))
    (ha : a ∉ M.map Prod.fst) (hz : z ∉ M.map Prod.fst)
    (h : List.IsChain AltStep ((a, false) :: M ++ [(z, true)])) :
    List.IsChain AltStep (prodCycle a z M ++ [((a, ∅), false)]) := by
  classical
  have hMa : ∀ p ∈ M, p.1 ≠ a := fun p hp hpa => ha (mem_map.2 ⟨p, hp, hpa⟩)
  have hMz : ∀ p ∈ M, p.1 ≠ z := fun p hp hpz => hz (mem_map.2 ⟨p, hp, hpz⟩)
  -- the copy `I_∅`, entered from `(a, ∅)` and left towards `(z, {0})`
  have c1 : List.IsChain AltStep (((a, ∅), false) :: M.map (tagAt ∅) ++ [((z, {0}), true)]) := by
    have key := isChain_map_lift (fun p => if p.1 = z ∧ p.2 = true then {0} else ∅)
      (fun u v => by simp) h
    rw [map_lift_eq _ ∅ a z M (fun p hp => by simp [hMz p hp])] at key
    simpa using key
  -- the right gadget `(z, {0}) > (z, ∅) < (z, {1})`
  have c2 : List.IsChain AltStep
      ([((z, {0}), true), ((z, ∅), false), ((z, {1}), true)] :
        List ((P × Finset (Fin 2)) × Bool)) := by
    refine .cons_cons (Or.inr ⟨rfl, rfl, ?_⟩) (.cons_cons (Or.inl ⟨rfl, rfl, ?_⟩) (.singleton _)) <;>
      exact Prod.mk_lt_mk_iff_right.2 (by decide)
  -- the copy `I_{1}` traversed backwards
  have c3 : List.IsChain AltStep (((z, {1}), true) :: (M.map (tagAt {1})).reverse ++
      [((a, {1}), false)]) := by
    have key := isChain_altStep_reverse (isChain_map_lift (fun _ => {1}) (fun u v => le_rfl) h)
    rw [map_lift_eq _ {1} a z M (fun p hp => rfl)] at key
    simpa using key
  -- the left gadget `(a, {1}) < (a, univ) > (a, {0})`
  have c4 : List.IsChain AltStep
      ([((a, {1}), false), ((a, Finset.univ), true), ((a, {0}), false)] :
        List ((P × Finset (Fin 2)) × Bool)) := by
    refine .cons_cons (Or.inl ⟨rfl, rfl, ?_⟩) (.cons_cons (Or.inr ⟨rfl, rfl, ?_⟩) (.singleton _)) <;>
      exact Prod.mk_lt_mk_iff_right.2 (by decide)
  -- the copy `I_univ`, entered from `(a, {0})` and left towards `(z, univ)`
  have c5 : List.IsChain AltStep (((a, {0}), false) :: M.map (tagAt Finset.univ) ++
      [((z, Finset.univ), true)]) := by
    have key := isChain_map_lift (fun p => if p.1 = a ∧ p.2 = false then {0} else Finset.univ)
      (fun u v => by simp) h
    rw [map_lift_eq _ Finset.univ a z M (fun p hp => by simp [hMa p hp])] at key
    simpa using key
  -- the copy `I_{0}` traversed backwards, closing up at `(a, ∅)`
  have c6 : List.IsChain AltStep (((z, Finset.univ), true) :: (M.map (tagAt {0})).reverse ++
      [((a, ∅), false)]) := by
    have key := isChain_altStep_reverse (isChain_map_lift
      (fun p => if p.2 = true then (if p.1 = z then Finset.univ else {0})
        else (if p.1 = a then ∅ else {0}))
      (fun u v => by simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> decide) h)
    rw [map_lift_eq _ {0} a z M (fun p hp => by
      rcases p with ⟨x, b⟩
      cases b <;> simp [hMa _ hp, hMz _ hp])] at key
    simpa using key
  simp only [prodCycle, cons_append, append_assoc]
  exact isChain_glue (l₁ := ((a, ∅), false) :: M.map (tagAt ∅)) c1 <|
    isChain_glue (l₁ := [((z, {0}), true), ((z, ∅), false)]) c2 <|
    isChain_glue (l₁ := ((z, {1}), true) :: (M.map (tagAt {1})).reverse) c3 <|
    isChain_glue (l₁ := [((a, {1}), false), ((a, Finset.univ), true)]) c4 <|
    isChain_glue (l₁ := ((a, {0}), false) :: M.map (tagAt Finset.univ)) c5 c6

/-- The cycle of Lemma 2.2 visits every element of `P × B_2`. -/
lemma prodCycle_cover (a z : P) (M : List (P × Bool))
    (hcov : ∀ x : P, x ∈ ((a, false) :: M ++ [(z, true)]).map Prod.fst) :
    ∀ q : P × Finset (Fin 2), q ∈ (prodCycle a z M).map Prod.fst := by
  rintro ⟨x, A⟩
  have hA : A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Finset.univ := by
    revert A
    decide
  have hx := hcov x
  simp only [cons_append, map_cons, map_append, map_nil, mem_cons, mem_append, mem_map,
    Prod.exists, exists_and_right, exists_eq_right, not_mem_nil, or_false] at hx
  rcases hx with rfl | ⟨b, hb⟩ | rfl
  · rcases hA with rfl | rfl | rfl | rfl <;> simp [prodCycle]
  · cases b <;> rcases hA with rfl | rfl | rfl | rfl <;> simp [prodCycle, tagAt, hb]
  · rcases hA with rfl | rfl | rfl | rfl <;> simp [prodCycle]

/-- The cycle of Lemma 2.2 has `4 |P|` entries. -/
lemma length_prodCycle (a z : P) (M : List (P × Bool)) :
    (prodCycle a z M).length = 4 * (M.length + 2) := by
  simp only [prodCycle, length_cons, length_append, length_map, length_reverse]
  ring

/-- **Lemma 2.2, even case** (labelled form).  If `a < x₁ > ⋯ < z` is an alternating Hamilton
path of `P` (starting at a valley, ending at a peak), then `prodCycle a z M` is an alternating
Hamilton cycle of `P × B_2`.  The inner part `M` may be empty (`|P| = 2`). -/
theorem prodCycle_isLabelledAHC [PartialOrder P] [Fintype P] (a z : P) (M : List (P × Bool))
    (h : IsLabelledAHP ((a, false) :: M ++ [(z, true)])) : IsLabelledAHC (prodCycle a z M) := by
  obtain ⟨hch, hnd, hcov⟩ := h
  have hnd' : (a :: (M.map Prod.fst ++ [z])).Nodup := by simpa using hnd
  have ha : a ∉ M.map Prod.fst := fun hm => (List.nodup_cons.1 hnd').1 (mem_append_left _ hm)
  have hz : z ∉ M.map Prod.fst := fun hm =>
    (List.disjoint_of_nodup_append (List.nodup_cons.1 hnd').2) hm (mem_singleton_self z)
  have hcard : M.length + 2 = Fintype.card P := by
    have := length_eq_card_of_nodup_of_forall_mem hnd hcov
    simpa using this
  have hcovC := prodCycle_cover a z M hcov
  refine ⟨(a, ∅), _, rfl, prodCycle_chain a z M ha hz hch, ?_, hcovC⟩
  refine nodup_of_forall_mem_of_length_le hcovC ?_
  rw [length_map, length_prodCycle, Fintype.card_prod, ← hcard]
  simp
  omega

end Product

/-! ## Transport along order isomorphisms, and paths from cycles -/

section Transfer

variable {α β : Type*} [Preorder α] [Preorder β]

/-- A bijective strictly monotone map carries labelled AHCs to labelled AHCs. -/
lemma IsLabelledAHC.map {g : α → β} (hg : Function.Bijective g) (hmono : StrictMono g)
    {C : List (α × Bool)} (h : IsLabelledAHC C) : IsLabelledAHC (C.map (Prod.map g id)) := by
  obtain ⟨c₀, M, rfl, hch, hnd, hcov⟩ := h
  have hfst : (Prod.fst ∘ Prod.map g id : α × Bool → β) = g ∘ Prod.fst := rfl
  refine ⟨g c₀, M.map (Prod.map g id), by simp, ?_, ?_, ?_⟩
  · have key : List.IsChain AltStep
        ((((c₀, false) :: M) ++ [(c₀, false)]).map (Prod.map g id)) := by
      rw [isChain_map]
      refine hch.imp ?_
      rintro ⟨x, b⟩ ⟨y, c⟩ hxy
      rcases hxy with ⟨hb, hc, hlt⟩ | ⟨hb, hc, hlt⟩
      · exact Or.inl ⟨hb, hc, hmono hlt⟩
      · exact Or.inr ⟨hb, hc, hmono hlt⟩
    simpa using key
  · rw [map_map, hfst, ← map_map]
    exact hnd.map hg.1
  · intro y
    obtain ⟨x, rfl⟩ := hg.2 y
    rw [map_map, hfst, ← map_map]
    exact mem_map_of_mem (hcov x)

/-- Lemma 2.1(i): an alternating Hamilton cycle with at least two entries yields an alternating
Hamilton path starting at a valley and ending at a peak. -/
lemma IsLabelledAHC.exists_path {C : List (α × Bool)} (h : IsLabelledAHC C)
    (hlen : 2 ≤ C.length) :
    ∃ a z : α, ∃ M : List (α × Bool), IsLabelledAHP ((a, false) :: M ++ [(z, true)]) := by
  obtain ⟨c₀, M, rfl, hch, hnd, hcov⟩ := h
  rcases List.eq_nil_or_concat' M with rfl | ⟨M', w, rfl⟩
  · simp at hlen
  · have hw : AltStep w (c₀, false) := by
      have := (isChain_append.1 hch).2.2
      exact this w (show (((c₀, false) :: M') ++ [w]).getLast? = some w from getLast?_concat)
        (c₀, false) (by simp)
    have hw2 : w.2 = true := by
      rcases hw with ⟨-, h2, -⟩ | ⟨h1, -, -⟩
      · simp at h2
      · exact h1
    refine ⟨c₀, w.1, M', ?_, ?_, ?_⟩
    · have hw' : w = (w.1, true) := by rw [← hw2]
      rw [← hw']
      exact hch.left_of_append
    · simpa using hnd
    · intro x
      simpa using hcov x

end Transfer

/-! ## From labelled cycles to `IsAltHamCycle` -/

section Bridge

variable {α : Type*} [Preorder α]

/-- The value of `finRotate N i`: the cyclic successor of `i`. -/
lemma val_finRotate {N : ℕ} (i : Fin N) :
    (finRotate N i : ℕ) = if (i : ℕ) + 1 = N then 0 else (i : ℕ) + 1 := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    simp [Fin.ext_iff]

/-- Reindexing along `finCongr` commutes with the cyclic successor. -/
lemma finRotate_finCongr {N M : ℕ} (h : N = M) (i : Fin N) :
    finRotate M (finCongr h i) = finCongr h (finRotate N i) := by
  subst h
  rfl

/-- In an alternating walk starting at a valley, the entry at position `i` is a peak exactly
when `i` is odd. -/
lemma label_eq_decide_odd {L : List (α × Bool)} (hch : List.IsChain AltStep L)
    (h0 : ∀ hL : 0 < L.length, L[0].2 = false) :
    ∀ (i : ℕ) (hi : i < L.length), L[i].2 = decide (Odd i) := by
  intro i
  induction i with
  | zero => intro hi; simp [h0 hi]
  | succ i ih =>
    intro hi
    rw [(hch.getElem i hi).label, ih (by omega)]
    simp [Nat.odd_add_one, ← Nat.not_even_iff_odd]

/-- A labelled alternating Hamilton cycle gives an enumeration satisfying `IsAltHamCycle`. -/
theorem IsLabelledAHC.exists_isAltHamCycle [Fintype α] {C : List (α × Bool)}
    (h : IsLabelledAHC C) : ∃ x : Fin (Fintype.card α) ≃ α, IsAltHamCycle x := by
  classical
  obtain ⟨c₀, M, hC, hch, hnd, hcov⟩ := h
  have hlen : (C.map Prod.fst).length = Fintype.card α :=
    length_eq_card_of_nodup_of_forall_mem hnd hcov
  rw [length_map] at hlen
  let e : Fin (Fintype.card α) ≃ α :=
    (finCongr (by rw [length_map, hlen])).trans (hnd.getEquivOfForallMemList _ hcov)
  have he : ∀ (j : Fin (Fintype.card α)) (m : ℕ) (hm : m < C.length), (j : ℕ) = m →
      e j = C[m].1 := by
    rintro j m hm rfl
    simp [e]
  have hD : ∀ (m : ℕ) (hm : m < C.length),
      (C ++ [(c₀, false)])[m]'(by simp; omega) = C[m] :=
    fun m hm => getElem_append_left hm
  have hlab := label_eq_decide_odd hch.left_of_append (fun hL => by simp [hC])
  have h0 : 0 < C.length := by rw [hC]; simp
  have hc₀ : C[0] = (c₀, false) := by simp [hC]
  refine ⟨e, fun i => ?_⟩
  have hi : (i : ℕ) < C.length := by have := i.2; omega
  have hli := hlab i hi
  have hxi := he i i hi rfl
  by_cases hlast : (i : ℕ) + 1 = Fintype.card α
  · have hstep : AltStep C[(i : ℕ)] (c₀, false) := by
      have := hch.getElem i (by simp; omega)
      rw [hD i hi, getElem_append_right (by omega)] at this
      simpa only [getElem_singleton] using this
    have hrot : e (finRotate _ i) = c₀ := by
      rw [he _ 0 h0 (by rw [val_finRotate, if_pos hlast]), hc₀]
    rcases hstep with ⟨-, h2, -⟩ | ⟨h1, -, hlt⟩
    · simp at h2
    · rw [h1] at hli
      have hodd : Odd (i : ℕ) := by simpa using hli.symm
      refine ⟨fun hev => absurd hodd (Nat.not_odd_iff_even.2 hev), fun _ => ?_⟩
      rw [hrot, hxi]
      exact hlt
  · have hi1 : (i : ℕ) + 1 < C.length := by have := i.2; omega
    have hstep : AltStep C[(i : ℕ)] C[(i : ℕ) + 1] := hch.left_of_append.getElem i hi1
    have hrot : e (finRotate _ i) = C[(i : ℕ) + 1].1 :=
      he _ _ hi1 (by rw [val_finRotate, if_neg hlast])
    rw [hrot, hxi]
    rcases hstep with ⟨h1, -, hlt⟩ | ⟨h1, -, hlt⟩
    · rw [h1] at hli
      have hev : ¬ Odd (i : ℕ) := by simpa using hli.symm
      exact ⟨fun _ => hlt, fun hodd => absurd hodd hev⟩
    · rw [h1] at hli
      have hodd : Odd (i : ℕ) := by simpa using hli.symm
      exact ⟨fun hev => absurd hodd (Nat.not_odd_iff_even.2 hev), fun _ => hlt⟩

end Bridge

/-! ## The Boolean lattices -/

section Boolean

/-- The order isomorphism `B_k × B_2 → B_{k+2}` (as a map): `(s, A) ↦ s ⊔ (A shifted by k)`. -/
def boolEmb (k : ℕ) (p : Finset (Fin k) × Finset (Fin 2)) : Finset (Fin (k + 2)) :=
  (p.1.disjSum p.2).map finSumFinEquiv.toEmbedding

/-- `boolEmb` is injective. -/
lemma boolEmb_injective (k : ℕ) : Function.Injective (boolEmb k) := by
  rintro ⟨s, A⟩ ⟨t, B⟩ hst
  have h := Finset.map_injective _ hst
  have h1 := congrArg Finset.toLeft h
  have h2 := congrArg Finset.toRight h
  simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum] at h1 h2
  rw [h1, h2]

/-- `boolEmb` is surjective. -/
lemma boolEmb_surjective (k : ℕ) : Function.Surjective (boolEmb k) := by
  intro S
  refine ⟨((S.map finSumFinEquiv.symm.toEmbedding).toLeft,
    (S.map finSumFinEquiv.symm.toEmbedding).toRight), ?_⟩
  simp only [boolEmb, Finset.toLeft_disjSum_toRight, Finset.map_map]
  ext x
  simp

/-- `boolEmb` is strictly monotone. -/
lemma boolEmb_strictMono (k : ℕ) : StrictMono (boolEmb k) := by
  refine Monotone.strictMono_of_injective ?_ (boolEmb_injective k)
  rintro ⟨s, A⟩ ⟨t, B⟩ ⟨hst, hAB⟩
  exact Finset.map_subset_map.2 (Finset.disjSum_mono hst hAB)

/-- `B_1` has the alternating Hamilton path `∅ < {0}`. -/
lemma isLabelledAHP_one :
    IsLabelledAHP ([(∅, false), (Finset.univ, true)] : List (Finset (Fin 1) × Bool)) := by
  unfold IsLabelledAHP
  decide

/-- `B_2` has the alternating Hamilton path `{0} < {0,1} > ∅ < {1}`. -/
lemma isLabelledAHP_two : IsLabelledAHP
    ([({0}, false), (Finset.univ, true), (∅, false), ({1}, true)] :
      List (Finset (Fin 2) × Bool)) := by
  unfold IsLabelledAHP
  decide

/-- `boolEmb` sends `({0}, {1})` to `{0} ∪ {1 + 1} = {0, 2}` in `B_3`. -/
example : boolEmb 1 ({0}, {1}) = {0, 2} := by decide

/-- The explicit AHC of `B_3` printed in the proof of Lemma 2.2,
`∅ < {1,2,3} > {1} < {1,2} > {2} < {2,3} > {3} < {1,3} > ∅` (shifted to `Fin 3`). -/
example : IsLabelledAHC ([(∅, false), ({0, 1, 2}, true), ({0}, false), ({0, 1}, true),
    ({1}, false), ({1, 2}, true), ({2}, false), ({0, 2}, true)] :
      List (Finset (Fin 3) × Bool)) :=
  ⟨∅, _, rfl, by decide, by decide, by decide⟩

/-- The Lemma 2.2 cycle built from the path `0 < 1` of the chain `Fin 2`
(the case `|P| = 2`) is an AHC of `Fin 2 × B_2`. -/
example : IsLabelledAHC (prodCycle (0 : Fin 2) 1 []) :=
  prodCycle_isLabelledAHC 0 1 [] ⟨by decide, by decide, by decide⟩

/-- Every `B_n` with `n ≥ 3` has a labelled alternating Hamilton cycle (induction `n ↦ n + 2`). -/
theorem exists_isLabelledAHC (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : List (Finset (Fin n) × Bool), IsLabelledAHC C := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hpath : ∃ a z : Finset (Fin k), ∃ M : List (Finset (Fin k) × Bool),
      IsLabelledAHP ((a, false) :: M ++ [(z, true)]) := by
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk
    · exact ⟨∅, Finset.univ, [], isLabelledAHP_one⟩
    · exact ⟨{0}, {1}, [(Finset.univ, true), (∅, false)], isLabelledAHP_two⟩
    · obtain ⟨C, hC⟩ := ih k (by omega) hk
      refine hC.exists_path ?_
      obtain ⟨c₀, M, rfl, -, hnd, hcov⟩ := hC
      have := length_eq_card_of_nodup_of_forall_mem hnd hcov
      simp only [length_map, Fintype.card_finset, Fintype.card_fin] at this
      rw [this]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  obtain ⟨a, z, M, hP⟩ := hpath
  exact ⟨_, (prodCycle_isLabelledAHC a z M hP).map
    ⟨boolEmb_injective k, boolEmb_surjective k⟩ (boolEmb_strictMono k)⟩

/-- **Katona's conjecture** (arXiv:2610.18152, Conjecture 1.1, proved there as Corollary 1.3):
for every `n ≥ 3` the Boolean lattice `B_n = Finset (Fin n)` admits an alternating Hamilton
cycle, i.e. an enumeration `x 0, …, x (2^n - 1)` of all subsets of `Fin n` with
`x 0 ⊂ x 1 ⊃ x 2 ⊂ ⋯ ⊂ x (2^n - 1) ⊃ x 0`. -/
theorem katona_conjecture (n : ℕ) (hn : 3 ≤ n) :
    ∃ x : Fin (2 ^ n) ≃ Finset (Fin n), IsAltHamCycle x := by
  obtain ⟨C, hC⟩ := exists_isLabelledAHC n hn
  obtain ⟨x, hx⟩ := hC.exists_isAltHamCycle
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp
  exact ⟨(finCongr hcard.symm).trans x, fun i => by
    have := hx (finCongr hcard.symm i)
    rw [finRotate_finCongr] at this
    exact this⟩

/-- Paper alias: Corollary 1.3 of arXiv:2610.18152 (Katona's conjecture holds). -/
theorem cor_1_3 (n : ℕ) (hn : 3 ≤ n) :
    ∃ x : Fin (2 ^ n) ≃ Finset (Fin n), IsAltHamCycle x :=
  katona_conjecture n hn

/-- At the smallest case, `B_3` has an alternating Hamilton cycle. -/
example : ∃ x : Fin (2 ^ 3) ≃ Finset (Fin 3), IsAltHamCycle x := katona_conjecture 3 le_rfl

end Boolean

end KatonaAlternatingHamilton
