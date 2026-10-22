/-
# Counting finite partitions by Stirling and Bell numbers

R. P. Stanley, "Enumerative Combinatorics", Vol. 1, 2nd ed. (2012), §1.9;
D. E. Knuth, "The Art of Computer Programming", Vol. 1, §1.2.6.
For a finite set `s`, the number of its finpartitions into `k` blocks is
`S₂(s.card,k)`, and the total number is `Bell(s.card)`.
Deleting one element and reinserting it into an existing block or a new
singleton gives the Stirling recurrence. Summing its row gives the Bell
identity. The statements include the empty set and specialize to `Fin n`.
-/
import Mathlib

set_option autoImplicit false

namespace StirlingBellCombinatorial

open Finset

variable {α : Type*} [DecidableEq α]

/-- Two finpartitions of the same finset are equal once their `part` functions agree on it. -/
theorem finpartition_ext_part {s : Finset α} {P Q : Finpartition s}
    (h : ∀ x ∈ s, P.part x = Q.part x) : P = Q := by
  have key : ∀ (P Q : Finpartition s), (∀ x ∈ s, P.part x = Q.part x) →
      ∀ u ∈ P.parts, u ∈ Q.parts := by
    intro P Q h u hu
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hu
    have hxs : x ∈ s := P.le hu hx
    rw [← P.part_eq_of_mem hu hx, h x hxs]
    exact Q.part_mem.2 hxs
  ext u
  exact ⟨key P Q h u, key Q P (fun x hx => (h x hx).symm) u⟩

/-- Delete the point `a` from a finpartition of `insert a s` (with `a ∉ s`), discarding the
part that becomes empty. -/
def eraseElem {a : α} {s : Finset α} (ha : a ∉ s) (P : Finpartition (insert a s)) :
    Finpartition s :=
  (P.avoid {a}).copy (by
    rw [insert_sdiff_of_mem _ (mem_singleton_self a), sdiff_singleton_eq_erase,
      erase_eq_of_notMem ha])

/-- Example: deleting `2` from the one-block partition of `{2, 0, 1}` leaves `{{0, 1}}`. -/
example : (eraseElem (a := (2 : ℕ)) (s := {0, 1}) (by decide) ⊤).parts = {{0, 1}} := by decide

/-- Example: deleting `2` from `{{2}, {0, 1}}` drops the emptied block. -/
example :
    (eraseElem (a := (2 : ℕ)) (s := {0, 1}) (by decide)
      ((⊤ : Finpartition ({0, 1} : Finset ℕ)).extend (b := {2}) (by decide) (by decide)
        (by decide))).parts = {{0, 1}} := by decide

/-- After deleting `a`, the part of `x ∈ s` is the old part of `x` with `a` removed. -/
theorem eraseElem_part {a : α} {s : Finset α} (ha : a ∉ s) (P : Finpartition (insert a s))
    {x : α} (hx : x ∈ s) : (eraseElem ha P).part x = P.part x \ {a} := by
  have hxa : x ≠ a := fun h => ha (h ▸ hx)
  have hxs : x ∈ insert a s := mem_insert_of_mem hx
  apply Finpartition.part_eq_of_mem
  · simp only [eraseElem, Finpartition.copy_parts, Finpartition.mem_avoid]
    refine ⟨P.part x, P.part_mem.2 hxs, ?_, rfl⟩
    intro hle
    exact hxa (mem_singleton.1 (hle (P.mem_part hxs)))
  · simp [hxa, P.mem_part hxs]

/-- A part of a finpartition of `s` does not contain a point `a ∉ s`. -/
theorem not_mem_of_mem_parts {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    {u : Finset α} (hu : u ∈ Q.parts) : a ∉ u :=
  fun hau => ha (Q.le hu hau)

/-- An element of `insert ∅ Q.parts` is a subset of `s`. -/
theorem subset_of_mem_insert_empty {s : Finset α} (Q : Finpartition s) {t : Finset α}
    (ht : t ∈ insert ∅ Q.parts) : t ⊆ s := by
  rcases mem_insert.1 ht with rfl | ht'
  · exact empty_subset s
  · exact Q.le ht'

/-- Insert the new point `a` into a finpartition `Q` of `s`: if `t = ∅` the singleton `{a}`
becomes a new part, otherwise `a` joins the part `t ∈ Q.parts`. -/
def insertElem {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s) (t : Finset α)
    (ht : t ∈ insert ∅ Q.parts) : Finpartition (insert a s) :=
  Finpartition.ofExistsUnique (insert (insert a t) (Q.parts.erase t))
    (by
      intro p hp
      rcases mem_insert.1 hp with rfl | hp'
      · exact insert_subset_insert a (subset_of_mem_insert_empty Q ht)
      · exact (Q.le (mem_of_mem_erase hp')).trans (subset_insert a s))
    (by
      intro x hx
      by_cases hxt : x ∈ insert a t
      · refine ⟨insert a t, ⟨mem_insert_self _ _, hxt⟩, ?_⟩
        rintro u ⟨hu, hxu⟩
        rcases mem_insert.1 hu with rfl | hu'
        · rfl
        · exfalso
          have hut : u ≠ t := ne_of_mem_erase hu'
          have huQ : u ∈ Q.parts := mem_of_mem_erase hu'
          rcases mem_insert.1 hxt with rfl | hxt'
          · exact not_mem_of_mem_parts ha Q huQ hxu
          · have htQ : t ∈ Q.parts := by
              rcases mem_insert.1 ht with rfl | ht'
              · simp at hxt'
              · exact ht'
            exact hut (Q.eq_of_mem_parts huQ htQ hxu hxt')
      · have hxa : x ≠ a := fun h => hxt (h ▸ mem_insert_self _ _)
        have hxs : x ∈ s := (mem_insert.1 hx).resolve_left hxa
        have hxt' : x ∉ t := fun h => hxt (mem_insert_of_mem h)
        refine ⟨Q.part x, ⟨?_, Q.mem_part hxs⟩, ?_⟩
        · refine mem_insert_of_mem (mem_erase.2 ⟨?_, Q.part_mem.2 hxs⟩)
          rintro hpt
          exact hxt' (hpt ▸ Q.mem_part hxs)
        · rintro u ⟨hu, hxu⟩
          rcases mem_insert.1 hu with rfl | hu'
          · exact absurd hxu hxt
          · exact (Q.part_eq_of_mem (mem_of_mem_erase hu') hxu).symm)
    (by
      intro h
      rcases mem_insert.1 h with h' | h'
      · exact insert_ne_empty a t h'.symm
      · exact Q.bot_notMem (mem_of_mem_erase h'))

/-- The parts of `insertElem`. -/
theorem insertElem_parts {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) :
    (insertElem ha Q t ht).parts = insert (insert a t) (Q.parts.erase t) := rfl

/-- Example: inserting `2` as a new singleton block into `{{0}, {1}}`. -/
example : (insertElem (a := (2 : ℕ)) (s := {0, 1}) (by decide) ⊥ ∅ (by decide)).parts =
    {{2}, {0}, {1}} := by decide

/-- Example: inserting `2` into the block `{0}` of `{{0}, {1}}`. -/
example : (insertElem (a := (2 : ℕ)) (s := {0, 1}) (by decide) ⊥ {0} (by decide)).parts =
    {{2, 0}, {1}} := by decide

/-- In `insertElem`, the part of `a`, and of every point of `t`, is `insert a t`. -/
theorem insertElem_part_of_mem {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) {x : α} (hx : x ∈ insert a t) :
    (insertElem ha Q t ht).part x = insert a t :=
  Finpartition.part_eq_of_mem _ (by rw [insertElem_parts]; exact mem_insert_self _ _) hx

/-- In `insertElem`, the part of a point `x ∈ s \ t` is unchanged. -/
theorem insertElem_part_of_not_mem {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    (insertElem ha Q t ht).part x = Q.part x := by
  apply Finpartition.part_eq_of_mem _ _ (Q.mem_part hxs)
  rw [insertElem_parts]
  refine mem_insert_of_mem (mem_erase.2 ⟨?_, Q.part_mem.2 hxs⟩)
  rintro hpt
  exact hxt (hpt ▸ Q.mem_part hxs)

/-- Number of parts of `insertElem`: one more than `Q` exactly when `t = ∅`. -/
theorem card_insertElem_parts {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) :
    #(insertElem ha Q t ht).parts = if t = ∅ then #Q.parts + 1 else #Q.parts := by
  have hnot : insert a t ∉ Q.parts.erase t := fun h =>
    not_mem_of_mem_parts ha Q (mem_of_mem_erase h) (mem_insert_self a t)
  rw [insertElem_parts, card_insert_of_notMem hnot]
  split_ifs with h0
  · subst h0
    rw [erase_eq_of_notMem Q.empty_notMem_parts]
  · have htQ : t ∈ Q.parts := (mem_insert.1 ht).resolve_left h0
    rw [card_erase_of_mem htQ]
    have hpos : 0 < #Q.parts := card_pos.2 ⟨t, htQ⟩
    omega

/-- Removing a point not in `t` after inserting it gives back `t`. -/
theorem insert_sdiff_singleton_of_not_mem {a : α} {t : Finset α} (hat : a ∉ t) :
    insert a t \ {a} = t := by
  rw [insert_sdiff_of_mem _ (mem_singleton_self a), sdiff_singleton_eq_erase,
    erase_eq_of_notMem hat]

/-- Deleting `a` undoes `insertElem`. -/
theorem eraseElem_insertElem {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) : eraseElem ha (insertElem ha Q t ht) = Q := by
  have hat : a ∉ t := fun h => ha (subset_of_mem_insert_empty Q ht h)
  apply finpartition_ext_part
  intro x hxs
  rw [eraseElem_part ha _ hxs]
  by_cases hxt : x ∈ t
  · rw [insertElem_part_of_mem ha Q t ht (mem_insert_of_mem hxt),
      insert_sdiff_singleton_of_not_mem hat]
    have htQ : t ∈ Q.parts := by
      rcases mem_insert.1 ht with rfl | ht'
      · simp at hxt
      · exact ht'
    exact (Q.part_eq_of_mem htQ hxt).symm
  · rw [insertElem_part_of_not_mem ha Q t ht hxs hxt]
    have hap : a ∉ Q.part x := not_mem_of_mem_parts ha Q (Q.part_mem.2 hxs)
    rw [sdiff_singleton_eq_erase, erase_eq_of_notMem hap]

/-- The block that `a` joined in `insertElem` is recovered as its part minus `a`. -/
theorem insertElem_part_self_sdiff {a : α} {s : Finset α} (ha : a ∉ s) (Q : Finpartition s)
    (t : Finset α) (ht : t ∈ insert ∅ Q.parts) :
    (insertElem ha Q t ht).part a \ {a} = t := by
  have hat : a ∉ t := fun h => ha (subset_of_mem_insert_empty Q ht h)
  rw [insertElem_part_of_mem ha Q t ht (mem_insert_self a t),
    insert_sdiff_singleton_of_not_mem hat]

/-- The part of `a` minus `a` is either empty or a part of the deleted partition. -/
theorem part_sdiff_mem_insert_empty {a : α} {s : Finset α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) : P.part a \ {a} ∈ insert ∅ (eraseElem ha P).parts := by
  by_cases h0 : P.part a \ {a} = ∅
  · rw [h0]; exact mem_insert_self _ _
  · refine mem_insert_of_mem ?_
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 h0
    have hxp : x ∈ P.part a := (mem_sdiff.1 hx).1
    have hxa : x ≠ a := fun h => (mem_sdiff.1 hx).2 (mem_singleton.2 h)
    have hxs : x ∈ s := (mem_insert.1 (P.part_subset a hxp)).resolve_left hxa
    have has : a ∈ insert a s := mem_insert_self a s
    have hpx : P.part x = P.part a := P.part_eq_of_mem (P.part_mem.2 has) hxp
    have hmem := (eraseElem ha P).part_mem.2 hxs
    rwa [eraseElem_part ha P hxs, hpx] at hmem

/-- Reinserting `a` into the block it came from undoes `eraseElem`. -/
theorem insertElem_eraseElem {a : α} {s : Finset α} (ha : a ∉ s)
    (P : Finpartition (insert a s)) :
    insertElem ha (eraseElem ha P) (P.part a \ {a}) (part_sdiff_mem_insert_empty ha P) = P := by
  have has : a ∈ insert a s := mem_insert_self a s
  have hpa : insert a (P.part a \ {a}) = P.part a := by
    rw [sdiff_singleton_eq_erase, insert_erase (P.mem_part has)]
  apply finpartition_ext_part
  intro y hy
  by_cases hyt : y ∈ insert a (P.part a \ {a})
  · rw [insertElem_part_of_mem ha _ _ _ hyt, hpa]
    rw [hpa] at hyt
    exact (P.part_eq_of_mem (P.part_mem.2 has) hyt).symm
  · have hya : y ≠ a := by rintro rfl; exact hyt (mem_insert_self _ _)
    have hys : y ∈ s := (mem_insert.1 hy).resolve_left hya
    have hyt' : y ∉ P.part a \ {a} := fun h => hyt (mem_insert_of_mem h)
    rw [insertElem_part_of_not_mem ha _ _ _ hys hyt', eraseElem_part ha P hys]
    have hap : a ∉ P.part y := by
      intro hay
      have hpy : P.part a = P.part y := P.part_eq_of_mem (P.part_mem.2 hy) hay
      exact hyt' (mem_sdiff.2 ⟨hpy ▸ P.mem_part hy, fun h => hya (mem_singleton.1 h)⟩)
    rw [sdiff_singleton_eq_erase, erase_eq_of_notMem hap]

/-- For a fixed partition `Q` of `s`, the number of admissible blocks `t ∈ insert ∅ Q.parts`
for which `insertElem Q t` has `k + 1` parts. -/
theorem card_filter_insert_empty {s : Finset α} (Q : Finpartition s) (k : ℕ) :
    #((insert ∅ Q.parts).filter
        (fun t => (if t = ∅ then #Q.parts + 1 else #Q.parts) = k + 1)) =
      (if #Q.parts = k then 1 else 0) + (if #Q.parts = k + 1 then k + 1 else 0) := by
  have hcongr : Q.parts.filter (fun t => (if t = ∅ then #Q.parts + 1 else #Q.parts) = k + 1) =
      Q.parts.filter (fun _ => #Q.parts = k + 1) := by
    apply filter_congr
    intro t ht
    rw [if_neg (Q.ne_empty ht)]
  rw [filter_insert, if_pos rfl, hcongr]
  by_cases hk : #Q.parts = k
  · have hk' : ¬ #Q.parts = k + 1 := by omega
    rw [if_pos hk, if_pos (by omega), filter_false_of_mem (fun _ _ => hk'), if_neg hk']
    simp
  · rw [if_neg hk, if_neg (by omega)]
    by_cases hk1 : #Q.parts = k + 1
    · rw [filter_true_of_mem (fun _ _ => hk1), if_pos hk1, hk1]
      simp
    · rw [filter_false_of_mem (fun _ _ => hk1), if_neg hk1]
      simp

/-- Combinatorial Stirling recurrence: for `a ∉ s`, the finpartitions of `insert a s` into
`k + 1` parts number those of `s` into `k` parts plus `k + 1` times those of `s` into `k + 1`
parts. -/
theorem card_finpartition_insert {a : α} {s : Finset α} (ha : a ∉ s) (k : ℕ) :
    #{P : Finpartition (insert a s) | #P.parts = k + 1} =
      #{Q : Finpartition s | #Q.parts = k} + (k + 1) * #{Q : Finpartition s | #Q.parts = k + 1}
    := by
  let T : Finset (Σ _ : Finpartition s, Finset α) := univ.sigma fun Q =>
    (insert ∅ Q.parts).filter (fun t => (if t = ∅ then #Q.parts + 1 else #Q.parts) = k + 1)
  have hT : ∀ b ∈ T, b.2 ∈ insert ∅ b.1.parts := by
    intro b hb
    simp only [T, mem_sigma, mem_univ, mem_filter, true_and] at hb
    exact hb.1
  have hbij : #{P : Finpartition (insert a s) | #P.parts = k + 1} = #T := by
    refine card_bij' (fun P _ => ⟨eraseElem ha P, P.part a \ {a}⟩)
      (fun b hb => insertElem ha b.1 b.2 (hT b hb)) ?_ ?_ ?_ ?_
    · intro P hP
      simp only [mem_filter, mem_univ, true_and] at hP
      have hcard := card_insertElem_parts ha (eraseElem ha P) (P.part a \ {a})
        (part_sdiff_mem_insert_empty ha P)
      rw [insertElem_eraseElem, hP] at hcard
      simp only [T, mem_sigma, mem_univ, mem_filter, true_and]
      exact ⟨part_sdiff_mem_insert_empty ha P, hcard.symm⟩
    · intro b hb
      have hb' := hb
      simp only [T, mem_sigma, mem_univ, mem_filter, true_and] at hb'
      simp only [mem_filter, mem_univ, true_and]
      rw [card_insertElem_parts]
      exact hb'.2
    · intro P _
      exact insertElem_eraseElem ha P
    · intro b hb
      rw [eraseElem_insertElem, insertElem_part_self_sdiff]
  rw [hbij, card_sigma]
  simp_rw [card_filter_insert_empty, sum_add_distrib, sum_boole]
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  simp

/-- The empty finset has exactly one finpartition with `0` parts. -/
theorem card_finpartition_empty_zero :
    #{P : Finpartition (∅ : Finset α) | #P.parts = 0} = 1 := by
  have hparts : ∀ P : Finpartition (∅ : Finset α), P.parts = ∅ :=
    fun P => P.parts_eq_empty_iff.2 rfl
  rw [card_eq_one]
  refine ⟨⊥, ?_⟩
  ext P
  simp only [mem_filter, mem_univ, true_and, mem_singleton, card_eq_zero]
  constructor
  · intro hP
    ext u
    rw [hP, hparts ⊥]
  · intro hP
    exact hparts P

/-- The empty finset has no finpartition with `k + 1` parts. -/
theorem card_finpartition_empty_succ (k : ℕ) :
    #{P : Finpartition (∅ : Finset α) | #P.parts = k + 1} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro P _
  rw [P.parts_eq_empty_iff.2 rfl, card_empty]
  omega

/-- A nonempty finset has no finpartition with `0` parts. -/
theorem card_finpartition_zero_of_nonempty {s : Finset α} (hs : s.Nonempty) :
    #{P : Finpartition s | #P.parts = 0} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro P _
  rw [card_eq_zero]
  exact fun h => hs.ne_empty (P.parts_eq_empty_iff.1 h)

/-- **Combinatorial meaning of `Nat.stirlingSecond`.** For every finset `s` and every `k`, the
number of finpartitions of `s` into exactly `k` parts is the Stirling number of the second kind
`S(#s, k)`. -/
theorem card_finpartition_parts_eq_stirlingSecond_finset (s : Finset α) (k : ℕ) :
    #{P : Finpartition s | #P.parts = k} = (#s).stirlingSecond k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => rw [card_finpartition_empty_zero, card_empty, Nat.stirlingSecond_zero]
    | succ k => rw [card_finpartition_empty_succ, card_empty, Nat.stirlingSecond_zero_succ]
  | insert a s ha ih =>
    rw [card_insert_of_notMem ha]
    cases k with
    | zero =>
      rw [card_finpartition_zero_of_nonempty (insert_nonempty a s),
        Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [card_finpartition_insert ha k, ih k, ih (k + 1), Nat.stirlingSecond_succ_succ]
      ring

/-- Pascal's rule applied inside a binomial sum. -/
theorem sum_range_choose_succ_mul (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (n + 2), (n + 1).choose i * f i =
      ∑ i ∈ range (n + 1), n.choose i * f i + ∑ i ∈ range (n + 1), n.choose i * f (i + 1) := by
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, add_mul, sum_add_distrib]
  rw [sum_range_succ (fun k => n.choose (k + 1) * f (k + 1)) n, Nat.choose_succ_self,
    sum_range_succ' (fun i => n.choose i * f i) n]
  simp only [Nat.choose_zero_right, zero_mul, add_zero]
  ring

/-- The binomial recurrence `S(n+1, k+1) = ∑_{i ≤ n} C(n, i) S(i, k)` for Stirling numbers of
the second kind. -/
theorem stirlingSecond_succ_succ_eq_sum (n k : ℕ) :
    (n + 1).stirlingSecond (k + 1) = ∑ i ∈ range (n + 1), n.choose i * i.stirlingSecond k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [Nat.stirlingSecond_self]
    | succ k => simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ n ih =>
    rw [sum_range_choose_succ_mul, Nat.stirlingSecond_succ_succ]
    cases k with
    | zero =>
      have h2 : ∑ i ∈ range (n + 1), n.choose i * (i + 1).stirlingSecond 0 = 0 := by
        simp [Nat.stirlingSecond_succ_zero]
      rw [h2, Nat.stirlingSecond_succ_zero, ← ih 0]
      ring
    | succ k =>
      have h2 : ∑ i ∈ range (n + 1), n.choose i * (i + 1).stirlingSecond (k + 1) =
          (k + 1) * ∑ i ∈ range (n + 1), n.choose i * i.stirlingSecond (k + 1) +
            ∑ i ∈ range (n + 1), n.choose i * i.stirlingSecond k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl ?_
        intro i _
        rw [Nat.stirlingSecond_succ_succ]
        ring
      rw [h2, ← ih k, ← ih (k + 1)]
      ring

/-- `∑_{k ≤ n} S(n, k) = B(n)`: the Bell number is the row sum of Stirling numbers of the second
kind. -/
theorem sum_stirlingSecond_eq_bell (n : ℕ) :
    ∑ k ∈ range (n + 1), n.stirlingSecond k = n.bell := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Nat.stirlingSecond_zero]
    | succ n =>
      have hext : ∀ i ∈ range (n + 1),
          ∑ k ∈ range (n + 1), i.stirlingSecond k = i.bell := by
        intro i hi
        have hin : i < n + 1 := mem_range.1 hi
        rw [← ih i (by omega)]
        symm
        apply sum_subset (range_subset_range.2 (by omega))
        intro k _ hk
        exact Nat.stirlingSecond_eq_zero_of_lt (by simpa using hk)
      have hreflect : ∑ i ∈ range (n + 1), n.choose i * i.bell =
          ∑ i ∈ range (n + 1), n.choose i * (n - i).bell := by
        rw [← sum_range_reflect (fun i => n.choose i * i.bell) (n + 1)]
        refine sum_congr rfl ?_
        intro i hi
        have hin : i < n + 1 := mem_range.1 hi
        have hsub : n + 1 - 1 - i = n - i := by omega
        rw [hsub, Nat.choose_symm (by omega)]
      rw [sum_range_succ', Nat.stirlingSecond_succ_zero, add_zero]
      simp_rw [stirlingSecond_succ_succ_eq_sum]
      rw [sum_comm]
      simp_rw [← mul_sum]
      rw [sum_congr rfl (fun i hi => by rw [hext i hi]), hreflect, Nat.bell_succ,
        Nat.range_succ_eq_Iic]

/-- **Combinatorial meaning of `Nat.bell`.** A finset `s` has exactly `B(#s)` finpartitions. -/
theorem card_finpartition_eq_bell_finset (s : Finset α) :
    Fintype.card (Finpartition s) = (#s).bell := by
  rw [← card_univ, ← sum_stirlingSecond_eq_bell,
    card_eq_sum_card_fiberwise (f := fun P : Finpartition s => #P.parts) (t := range (#s + 1))
      (fun P _ => mem_range.2 (Nat.lt_succ_of_le P.card_parts_le_card))]
  exact sum_congr rfl (fun k _ => card_finpartition_parts_eq_stirlingSecond_finset s k)

/-- **Stirling numbers of the second kind count set partitions** (Stanley, EC1 §1.9): the
number of partitions of `{0, …, n-1}` into exactly `k` nonempty blocks is `S(n, k)`. -/
theorem card_finpartition_parts_eq_stirlingSecond (n k : ℕ) :
    #{P : Finpartition (univ : Finset (Fin n)) | #P.parts = k} = n.stirlingSecond k := by
  rw [card_finpartition_parts_eq_stirlingSecond_finset, card_univ, Fintype.card_fin]

/-- **Bell numbers count set partitions** (Stanley, EC1 §1.9): the set `{0, …, n-1}` has
exactly `B(n)` partitions into nonempty blocks. -/
theorem card_finpartition_eq_bell (n : ℕ) :
    Fintype.card (Finpartition (univ : Finset (Fin n))) = n.bell := by
  rw [card_finpartition_eq_bell_finset, card_univ, Fintype.card_fin]

/-- Example (independent of the proof): `{0, 1}` has exactly `2 = B(2)` partitions, one of
them with a single block. -/
example : Fintype.card (Finpartition (univ : Finset (Fin 2))) = 2 := by decide

/-- Example (independent of the proof): `{0, 1}` has exactly `1 = S(2, 1)` partition into
one block. -/
example : #{P : Finpartition (univ : Finset (Fin 2)) | #P.parts = 1} = 1 := by decide

/-- Instance of the main theorem: `S(3, 2) = 3` partitions of `{0, 1, 2}` into two blocks. -/
example : #{P : Finpartition (univ : Finset (Fin 3)) | #P.parts = 2} = 3 := by
  rw [card_finpartition_parts_eq_stirlingSecond]; decide

/-- Instance of the Bell corollary: `{0, 1, 2}` has `B(3) = 5` partitions. -/
example : Fintype.card (Finpartition (univ : Finset (Fin 3))) = 5 := by
  rw [card_finpartition_eq_bell]
  simp [Nat.bell_succ, sum_range_succ, ← Nat.range_succ_eq_Iic]

end StirlingBellCombinatorial
