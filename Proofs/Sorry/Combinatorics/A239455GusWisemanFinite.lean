/-
# A239455 — Wiseman: Look-and-Say iff some ordering has distinct run-lengths

## OEIS source (retrieved with `oeis show A239455`, 2026-10-21)

```
NAME:     Number of Look-and-Say partitions of n; see Comments.
TERMS:    0,1,2,2,4,5,7,10,13,16,21,28,33,45,55,65,83,105,121,155,180,217,
          259,318,362,445,512,614,707,850,958,1155,1309,1543,1754,2079,...
COMMENT (the definition):
  Suppose that p = x(1) >= x(2) >= ... >= x(k) is a partition of n. Let
  y(1) > y(2) > ... > y(h) be the distinct parts of p, and let m(i) be the
  multiplicity of y(i) for 1 <= i <= h. Then we can "look" at p as "m(1)
  y(1)'s and m(2) y(2)'s and ... m(h) y(h)'s". Reversing the m's and y's, we
  can then "say" the Look-and-Say partition of p, denoted by LS(p). [...]
COMMENT (the conjecture):
  Conjecture: a partition is Look-and-Say iff it has a permutation with all
  distinct run-lengths. For example, the partition y = (2,2,2,1,1,1) has the
  permutation (2,2,1,1,1,2), with run-lengths (2,3,1), which are all
  distinct, so y is counted under a(9). - _Gus Wiseman_, Aug 11 2025
COMMENT (the equivalent definition used here):
  Also the number of integer partitions y of n such that there is a pairwise
  disjoint way to choose a strict integer partition of each multiplicity (or
  run-length) of y. - _Gus Wiseman_, Aug 11 2025
```

## Status

Open in the entry (stated as a conjecture, Aug 2025); proved below.  The triage found no
proof in the entry, in A351293, A351294, A351295, A386580, or in one web
search; that coverage is limited and does not establish novelty.

## Formalization

The statement is proved for every finite multiset `s` over a type with
decidable equality (integer partitions are the case `α = ℕ`, `s = y.parts`).

* `runLengths l` — lengths of the maximal runs of the word `l`, computed with
  Mathlib's `List.splitBy (· == ·)` (consecutive equal letters).
* `HasDistinctRunOrdering s` — some word `l` with `(l : Multiset α) = s` has
  pairwise distinct run lengths.
* `IsLookAndSay s` — Wiseman's second comment: for each distinct value `a` of
  `s` there is a strict partition `P a` (a finset of positive integers) of
  the multiplicity `s.count a`, and these finsets are pairwise disjoint.

Proof.  (⇒) the runs of one letter have distinct lengths summing to its
multiplicity.  (⇐) all blocks `(length n, colour c n)` have distinct lengths;
while some colour occupies more than half of the blocks, merge its largest
block `m` with a block `j` of the same colour such that `m + j` is not a length
in use (`exists_balanced`); then order the blocks with no two adjacent of equal
colour (`exists_arrangement`) and flatten.  The entry's own definition (the
image of the map `LS`) is bridged in `isLookAndSay_iff_exists_lookAndSay`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A239455GusWisemanFinite

variable {α : Type*} [DecidableEq α]

/-! ## Definitions -/

/-- The lengths of the maximal runs (maximal blocks of consecutive equal
letters) of the word `l`, from left to right. -/
def runLengths (l : List α) : List ℕ :=
  (l.splitBy (· == ·)).map List.length

/-- The multiset `s` has an ordering (a word with letter multiset `s`) whose
maximal runs have pairwise distinct lengths. -/
def HasDistinctRunOrdering (s : Multiset α) : Prop :=
  ∃ l : List α, (l : Multiset α) = s ∧ (runLengths l).Nodup

/-- The multiset `s` is Look-and-Say (Wiseman's equivalent definition in
A239455): one can choose, for every distinct value `a` of `s`, a strict
partition `P a` of the multiplicity `s.count a` (a finset of positive integers
summing to it) so that these strict partitions are pairwise disjoint. -/
def IsLookAndSay (s : Multiset α) : Prop :=
  ∃ P : α → Finset ℕ, (∀ a ∈ s.toFinset, 0 ∉ P a ∧ ∑ i ∈ P a, i = s.count a) ∧
    (s.toFinset : Set α).PairwiseDisjoint P

/-- Membership in `HasDistinctRunOrdering` for a multiset given by a list is a
finite check over the permutations of that list. -/
theorem hasDistinctRunOrdering_coe_iff (l : List α) :
    HasDistinctRunOrdering (l : Multiset α) ↔ ∃ l' ∈ l.permutations', (runLengths l').Nodup := by
  constructor
  · rintro ⟨l', hl', hnd⟩
    exact ⟨l', List.mem_permutations'.2 (Multiset.coe_eq_coe.1 hl'), hnd⟩
  · rintro ⟨l', hl', hnd⟩
    exact ⟨l', Multiset.coe_eq_coe.2 (List.mem_permutations'.1 hl'), hnd⟩

/-! ## Ground truth -/

/-- Wiseman's example: the word `(2,2,1,1,1,2)` has run lengths `(2,3,1)`. -/
example : runLengths [2, 2, 1, 1, 1, 2] = [2, 3, 1] := by decide

/-- Wiseman's example: `(2,2,2,1,1,1)` has an ordering with distinct run lengths. -/
example : HasDistinctRunOrdering ({2, 2, 2, 1, 1, 1} : Multiset ℕ) :=
  ⟨[2, 2, 1, 1, 1, 2], by decide, by decide⟩

/-- `(3,1)` (not Look-and-Say, `a(4) = 4` omits it) has no ordering with
distinct run lengths. -/
example : ¬ HasDistinctRunOrdering ((([3, 1] : List ℕ)) : Multiset ℕ) := by
  rw [hasDistinctRunOrdering_coe_iff]; decide

/-- `(2,2,2,1,1,1)` is Look-and-Say: `P 1 = {3}`, `P 2 = {1, 2}`. -/
example : IsLookAndSay ({2, 2, 2, 1, 1, 1} : Multiset ℕ) := by
  refine ⟨fun a => if a = 1 then {3} else {1, 2}, by decide, ?_⟩
  rw [show ({2, 2, 2, 1, 1, 1} : Multiset ℕ).toFinset = {1, 2} by decide]
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | exact absurd rfl hab | decide

/-! ## Forward direction: distinct run lengths give a Look-and-Say family -/

/-- Every maximal run of a word is a nonempty constant block `b^n`. -/
theorem exists_replicate_of_mem_splitBy {l r : List α} (hr : r ∈ l.splitBy (· == ·)) :
    ∃ b n, 0 < n ∧ r = List.replicate n b := by
  have hne : r ≠ [] := List.ne_nil_of_mem_splitBy hr
  have hc : r.IsChain (fun x y => x = y) :=
    (List.isChain_of_mem_splitBy hr).imp (fun x y h => by simpa using h)
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hp : (b :: t).Pairwise (fun x y => x = y) := List.isChain_iff_pairwise.1 hc
  refine ⟨b, (b :: t).length, by simp, List.eq_replicate_iff.2 ⟨rfl, fun x hx => ?_⟩⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · rfl
  · exact ((List.pairwise_cons.1 hp).1 x hx).symm

/-- In a concatenation of nonempty constant blocks, the number of copies of `a`
is the total length of the blocks whose letter is `a`. -/
theorem count_flatten_of_replicate (a : α) : ∀ R : List (List α),
    (∀ r ∈ R, ∃ b n, 0 < n ∧ r = List.replicate n b) →
    R.flatten.count a = ((R.filter (fun r => r.head? == some a)).map List.length).sum
  | [], _ => by simp
  | r :: R, h => by
    obtain ⟨b, n, hn, rfl⟩ := h r List.mem_cons_self
    have ih := count_flatten_of_replicate a R (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    rw [List.flatten_cons, List.count_append, ih, List.filter_cons]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    by_cases hab : b = a
    · subst hab; simp [List.replicate_succ]
    · simp [List.replicate_succ, List.count_replicate, hab]

/-- (⇒) If some ordering of `s` has pairwise distinct run lengths, then `s` is
Look-and-Say: the run lengths of the letter `a` form the strict partition
`P a` of its multiplicity. -/
theorem isLookAndSay_of_hasDistinctRunOrdering {s : Multiset α}
    (h : HasDistinctRunOrdering s) : IsLookAndSay s := by
  obtain ⟨w, rfl, hnd⟩ := h
  rw [runLengths] at hnd
  set R := w.splitBy (· == ·) with hR
  have hrun : ∀ r ∈ R, ∃ b n, 0 < n ∧ r = List.replicate n b :=
    fun r hr => exists_replicate_of_mem_splitBy hr
  refine ⟨fun a => ((R.filter (fun r => r.head? == some a)).map List.length).toFinset,
    fun a _ => ⟨?_, ?_⟩, ?_⟩
  · simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
    rintro ⟨r, ⟨hr, -⟩, hlen⟩
    obtain ⟨b, n, hn, rfl⟩ := hrun r hr
    simp only [List.length_replicate] at hlen
    omega
  · have hnd' : ((R.filter (fun r => r.head? == some a)).map List.length).Nodup :=
      hnd.sublist (List.filter_sublist.map _)
    rw [List.sum_toFinset _ hnd', List.map_id', Multiset.coe_count,
      ← count_flatten_of_replicate a R hrun, hR, List.flatten_splitBy]
  · intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro n hna hnb
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hna hnb
    obtain ⟨r1, ⟨hr1, h1⟩, rfl⟩ := hna
    obtain ⟨r2, ⟨hr2, h2⟩, hl⟩ := hnb
    have heq : r2 = r1 := List.inj_on_of_nodup_map hnd hr2 hr1 hl
    subst heq
    simp only [beq_iff_eq] at h1 h2
    rw [h1] at h2
    exact hab (Option.some_injective _ h2)

/-! ## Backward direction, step 1: arranging coloured blocks -/

/-- **Arrangement lemma.** Let `L` be a finite set of blocks coloured by `c`.
If no colour occupies more than `(|L| + 1) / 2` blocks, and the forbidden first
colour `x` (if any) occupies at most `|L| / 2` blocks, then `L` can be listed
without repetition so that adjacent blocks have different colours and the
first block does not have colour `x`. -/
theorem exists_arrangement (c : ℕ → α) (N : ℕ) : ∀ (L : Finset ℕ), L.card = N →
    ∀ (x : Option α),
    (∀ v, 2 * (L.filter (fun n => c n = v)).card ≤ L.card + 1) →
    (∀ v, x = some v → 2 * (L.filter (fun n => c n = v)).card ≤ L.card) →
    ∃ l : List ℕ, l.Nodup ∧ l.toFinset = L ∧ l.IsChain (fun a b => c a ≠ c b) ∧
      ∀ y ∈ l.head?, some (c y) ≠ x := by
  induction N with
  | zero =>
    intro L hL x _ _
    refine ⟨[], List.nodup_nil, ?_, List.isChain_nil, by simp⟩
    simp [Finset.card_eq_zero.1 hL]
  | succ N ih =>
    intro L hL x hbal hx
    set L₀ := L.filter (fun n => some (c n) ≠ x) with hL₀
    have hL₀ne : L₀.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      have hall : ∀ n ∈ L, some (c n) = x := by
        intro n hn
        by_contra hne
        have hmem : n ∈ L₀ := Finset.mem_filter.2 ⟨hn, hne⟩
        rw [h0] at hmem
        exact Finset.notMem_empty n hmem
      obtain ⟨n0, hn0⟩ : L.Nonempty := Finset.card_pos.1 (by omega)
      have hxv : x = some (c n0) := (hall n0 hn0).symm
      have hsub : L.filter (fun n => c n = c n0) = L :=
        Finset.filter_true_of_mem (fun n hn => Option.some_injective _ ((hall n hn).trans hxv))
      have hle := hx (c n0) hxv
      rw [hsub] at hle
      omega
    obtain ⟨a, haL₀, hamax⟩ :=
      Finset.exists_max_image L₀ (fun n => (L.filter (fun m => c m = c n)).card) hL₀ne
    obtain ⟨haL, hax⟩ := Finset.mem_filter.1 haL₀
    have hka : a ∈ L.filter (fun m => c m = c a) := Finset.mem_filter.2 ⟨haL, rfl⟩
    have hcard' : (L.erase a).card = N := by
      rw [Finset.card_erase_of_mem haL]
      omega
    have hfy : ((L.erase a).filter (fun n => c n = c a)).card + 1 =
        (L.filter (fun n => c n = c a)).card := by
      rw [Finset.filter_erase, Finset.card_erase_add_one hka]
    have hfv : ∀ v, v ≠ c a →
        (L.erase a).filter (fun n => c n = v) = L.filter (fun n => c n = v) := by
      intro v hv
      rw [Finset.filter_erase]
      exact Finset.erase_eq_of_notMem (fun h => hv (Finset.mem_filter.1 h).2.symm)
    have hsum : ∀ v, v ≠ c a →
        (L.filter (fun n => c n = v)).card + (L.filter (fun n => c n = c a)).card ≤ L.card := by
      intro v hv
      rw [← Finset.card_union_of_disjoint]
      · exact Finset.card_le_card
          (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      · exact Finset.disjoint_filter.2 (fun n _ h1 h2 => hv (h1.symm.trans h2))
    have hbal' : ∀ v, 2 * ((L.erase a).filter (fun n => c n = v)).card ≤ (L.erase a).card + 1 := by
      intro v
      rw [hcard']
      by_cases hv : v = c a
      · rw [hv]
        have hb := hbal (c a)
        omega
      · rw [hfv v hv]
        by_cases hxv : x = some v
        · have hb := hx v hxv
          omega
        · rcases (L.filter (fun n => c n = v)).eq_empty_or_nonempty with he | ⟨b, hb⟩
          · rw [he, Finset.card_empty]
            omega
          · obtain ⟨hbL, hbv⟩ := Finset.mem_filter.1 hb
            have hbL₀ : b ∈ L₀ :=
              Finset.mem_filter.2 ⟨hbL, by rw [hbv]; exact fun h => hxv h.symm⟩
            have hle := hamax b hbL₀
            simp only [hbv] at hle
            have hs := hsum v hv
            omega
    have hx' : ∀ v, some (c a) = some v →
        2 * ((L.erase a).filter (fun n => c n = v)).card ≤ (L.erase a).card := by
      intro v hv
      rw [Option.some_inj] at hv
      rw [← hv, hcard']
      have hb := hbal (c a)
      omega
    obtain ⟨l', hnd', hl', hch', hhd'⟩ := ih (L.erase a) hcard' (some (c a)) hbal' hx'
    refine ⟨a :: l', ?_, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun ha => ?_, hnd'⟩
      rw [← List.mem_toFinset, hl'] at ha
      exact Finset.notMem_erase a L ha
    · rw [List.toFinset_cons, hl', Finset.insert_erase haL]
    · refine List.isChain_cons.2 ⟨fun b hb hab => ?_, hch'⟩
      exact hhd' b hb (by rw [hab])
    · intro b hb
      rw [List.head?_cons, Option.mem_some_iff] at hb
      subst hb
      exact hax

/-! ## Backward direction, step 2: merging blocks of an over-represented colour -/

/-- **Balancing lemma.** If `s` is the disjoint union of blocks `c n ^ n`,
`n ∈ L`, with distinct positive lengths, then (after merging blocks of a common
colour) `s` is also such a union in which no colour occupies more than
`(|L'| + 1) / 2` blocks.  An over-represented colour `v` with largest block `m`
has more blocks `j ≠ m` than there are blocks of other colours, so some sum
`m + j` is not a length in use; merge `m` and `j` into `m + j`. -/
theorem exists_balanced (s : Multiset α) (N : ℕ) : ∀ (L : Finset ℕ) (c : ℕ → α),
    L.card ≤ N → 0 ∉ L → s = ∑ n ∈ L, Multiset.replicate n (c n) →
    ∃ (L' : Finset ℕ) (c' : ℕ → α), 0 ∉ L' ∧ s = ∑ n ∈ L', Multiset.replicate n (c' n) ∧
      ∀ v, 2 * (L'.filter (fun n => c' n = v)).card ≤ L'.card + 1 := by
  induction N with
  | zero =>
    intro L c hL h0 hs
    refine ⟨L, c, h0, hs, fun v => ?_⟩
    have hle := Finset.card_le_card (Finset.filter_subset (fun n => c n = v) L)
    omega
  | succ N ih =>
    intro L c hL h0 hs
    by_cases hbal : ∀ v, 2 * (L.filter (fun n => c n = v)).card ≤ L.card + 1
    · exact ⟨L, c, h0, hs, hbal⟩
    push Not at hbal
    obtain ⟨v, hv⟩ := hbal
    set V := L.filter (fun n => c n = v) with hV
    set F := L.filter (fun n => ¬ c n = v) with hF
    have hVF : V.card + F.card = L.card := Finset.card_filter_add_card_filter_not _
    have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
    set m := V.max' hVne with hm
    have hmV : m ∈ V := Finset.max'_mem V hVne
    have hex : ∃ j ∈ V.erase m, m + j ∉ F := by
      by_contra hcon
      push Not at hcon
      have hsub : (V.erase m).image (fun j => m + j) ⊆ F := by
        intro t ht
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
        exact hcon j hj
      have hc1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (add_right_injective m),
        Finset.card_erase_of_mem hmV] at hc1
      omega
    obtain ⟨j, hjV', hjF⟩ := hex
    have hjm : j ≠ m := Finset.ne_of_mem_erase hjV'
    have hjV : j ∈ V := Finset.mem_of_mem_erase hjV'
    obtain ⟨hjL, hjc⟩ := Finset.mem_filter.1 hjV
    obtain ⟨hmL, hmc⟩ := Finset.mem_filter.1 hmV
    have hjpos : 0 < j := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hjL))
    have htL : m + j ∉ L := by
      intro htL
      by_cases htc : c (m + j) = v
      · have hle : m + j ≤ m := Finset.le_max' V (m + j) (Finset.mem_filter.2 ⟨htL, htc⟩)
        omega
      · exact hjF (Finset.mem_filter.2 ⟨htL, htc⟩)
    have htL' : m + j ∉ (L.erase m).erase j :=
      fun h => htL (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    have hjLm : j ∈ L.erase m := Finset.mem_erase.2 ⟨hjm, hjL⟩
    have hcardL' : (insert (m + j) ((L.erase m).erase j)).card + 1 = L.card := by
      rw [Finset.card_insert_of_notMem htL', Finset.card_erase_of_mem hjLm,
        Finset.card_erase_of_mem hmL]
      omega
    refine ih (insert (m + j) ((L.erase m).erase j)) (Function.update c (m + j) v)
      (by omega) ?_ ?_
    · intro h
      rcases Finset.mem_insert.1 h with h | h
      · omega
      · exact h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    · have hrest : ∑ n ∈ (L.erase m).erase j,
          Multiset.replicate n (Function.update c (m + j) v n) =
          ∑ n ∈ (L.erase m).erase j, Multiset.replicate n (c n) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hnt : n ≠ m + j := fun h => htL' (h ▸ hn)
        rw [Function.update_of_ne hnt]
      rw [hs, ← Finset.add_sum_erase L _ hmL, ← Finset.add_sum_erase (L.erase m) _ hjLm,
        Finset.sum_insert htL', hrest, ← add_assoc, Function.update_self, hmc, hjc,
        Multiset.replicate_add]

/-! ## Backward direction, step 3: flattening an arrangement into a word -/

/-- The maximal runs of the word obtained by writing each block `n` of an
arrangement as `c n ^ n` are exactly these blocks, provided all lengths are
positive and adjacent blocks have different colours. -/
theorem splitBy_flatMap_replicate (c : ℕ → α) (l : List ℕ) (h0 : 0 ∉ l)
    (hch : l.IsChain (fun a b => c a ≠ c b)) :
    (l.flatMap (fun n => List.replicate n (c n))).splitBy (· == ·) =
      l.map (fun n => List.replicate n (c n)) := by
  rw [List.splitBy_eq_iff]
  refine ⟨List.flatMap_def, ?_, ?_, ?_⟩
  · simp only [List.mem_map, not_exists, not_and]
    intro n hn hrep
    rw [List.replicate_eq_nil_iff] at hrep
    exact h0 (hrep ▸ hn)
  · intro r hr
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hr
    exact List.isChain_replicate_of_rel n (by simp)
  · rw [List.isChain_map]
    refine hch.imp_of_mem_imp (fun a b ha hb hab => ?_)
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    refine ⟨by simpa using ha0, by simpa using hb0, ?_⟩
    simp [List.getLast_replicate, List.head_replicate, hab]

/-- The run lengths of the flattened arrangement are the arrangement itself. -/
theorem runLengths_flatMap_replicate (c : ℕ → α) (l : List ℕ) (h0 : 0 ∉ l)
    (hch : l.IsChain (fun a b => c a ≠ c b)) :
    runLengths (l.flatMap (fun n => List.replicate n (c n))) = l := by
  have hid : (List.length ∘ fun n => List.replicate n (c n)) = id :=
    funext fun n => List.length_replicate
  rw [runLengths, splitBy_flatMap_replicate c l h0 hch, List.map_map, hid, List.map_id]

omit [DecidableEq α] in
/-- The letter multiset of the flattened arrangement is the sum of its blocks. -/
theorem coe_flatMap_replicate (c : ℕ → α) (l : List ℕ) :
    ((l.flatMap (fun n => List.replicate n (c n)) : List α) : Multiset α) =
      (l.map (fun n => Multiset.replicate n (c n))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ← Multiset.coe_add, ih, Multiset.coe_replicate]

/-! ## Backward direction and the conjecture -/

/-- (⇐) A Look-and-Say multiset has an ordering whose maximal runs have
pairwise distinct lengths. -/
theorem hasDistinctRunOrdering_of_isLookAndSay {s : Multiset α} (h : IsLookAndSay s) :
    HasDistinctRunOrdering s := by
  obtain ⟨P, hP, hdisj⟩ := h
  rcases eq_or_ne s 0 with rfl | hs0
  · exact ⟨[], rfl, by simp [runLengths]⟩
  obtain ⟨a0, -⟩ := Multiset.exists_mem_of_ne_zero hs0
  classical
  let L : Finset ℕ := s.toFinset.biUnion P
  let c : ℕ → α := fun n => if hn : ∃ a ∈ s.toFinset, n ∈ P a then hn.choose else a0
  have hc : ∀ a ∈ s.toFinset, ∀ n ∈ P a, c n = a := by
    intro a ha n hn
    have hex : ∃ a ∈ s.toFinset, n ∈ P a := ⟨a, ha, hn⟩
    simp only [c, dif_pos hex]
    obtain ⟨hb, hnb⟩ := hex.choose_spec
    by_contra hne
    exact Finset.disjoint_left.1 (hdisj hb ha hne) hnb hn
  have hL0 : 0 ∉ L := by
    simp only [L, Finset.mem_biUnion, not_exists, not_and]
    intro a ha
    exact (hP a ha).1
  have hsL : s = ∑ n ∈ L, Multiset.replicate n (c n) := by
    rw [Finset.sum_biUnion hdisj]
    conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq s]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← (hP a ha).2, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hc a ha n hn, Multiset.nsmul_singleton]
  obtain ⟨L', c', hL'0, hsL', hbal⟩ := exists_balanced s L.card L c le_rfl hL0 hsL
  obtain ⟨l, hnd, hl, hch, -⟩ :=
    exists_arrangement c' L'.card L' rfl none hbal (fun v hv => absurd hv (by simp))
  have h0 : 0 ∉ l := by
    rw [← List.mem_toFinset, hl]
    exact hL'0
  refine ⟨l.flatMap (fun n => List.replicate n (c' n)), ?_, ?_⟩
  · rw [coe_flatMap_replicate, hsL', ← hl, List.sum_toFinset _ hnd]
  · rw [runLengths_flatMap_replicate c' l h0 hch]
    exact hnd

/-- **Wiseman's conjecture (A239455, Gus Wiseman, Aug 11 2025), proved for all
finite multisets.**  A finite multiset `s` has an ordering whose maximal runs
have pairwise distinct lengths if and only if `s` is Look-and-Say, i.e. one can
choose pairwise disjoint strict partitions of the multiplicities of its
distinct values. -/
theorem hasDistinctRunOrdering_iff_isLookAndSay (s : Multiset α) :
    HasDistinctRunOrdering s ↔ IsLookAndSay s :=
  ⟨isLookAndSay_of_hasDistinctRunOrdering, hasDistinctRunOrdering_of_isLookAndSay⟩

/-- **Wiseman's conjecture for integer partitions (A239455, Aug 11 2025).**
A partition `y` of `n` has a permutation with all distinct run lengths iff `y`
is Look-and-Say (in the disjoint-strict-partitions form of the entry). -/
theorem partition_hasDistinctRunOrdering_iff_isLookAndSay {n : ℕ} (y : Nat.Partition n) :
    HasDistinctRunOrdering y.parts ↔ IsLookAndSay y.parts :=
  hasDistinctRunOrdering_iff_isLookAndSay y.parts

/-! ## The entry's own definition: the Look-and-Say map `LS` -/

/-- The Look-and-Say partition `LS(p)` of the entry's first comment: each
distinct part `y` of `p` with multiplicity `m` contributes `y` copies of `m`. -/
def lookAndSay (p : Multiset ℕ) : Multiset ℕ :=
  ∑ y ∈ p.toFinset, Multiset.replicate y (p.count y)

/-- The entry's example: `LS(3,3,2,1) = (2,2,2,1,1,1)`. -/
example : lookAndSay {3, 3, 2, 1} = {2, 2, 2, 1, 1, 1} := by decide

/-- `a(4) = 4`: the images under `LS` of the five partitions of `4` are the four
distinct partitions `(1,1,1,1)`, `(2,2)`, `(2,1,1)`, `(4)`. -/
example : (([[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]] : List (List ℕ)).map
    (fun l => lookAndSay (l : Multiset ℕ))).dedup.length = 4 := by decide

/-- `a(6) = 7`: the images under `LS` of the eleven partitions of `6`. -/
example : (([[6], [5, 1], [4, 2], [4, 1, 1], [3, 3], [3, 2, 1], [3, 1, 1, 1], [2, 2, 2],
    [2, 2, 1, 1], [2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]] : List (List ℕ)).map
    (fun l => lookAndSay (l : Multiset ℕ))).dedup.length = 7 := by decide

/-- `LS` preserves the sum, so it maps partitions of `n` to partitions of `n`. -/
theorem sum_lookAndSay (p : Multiset ℕ) : (lookAndSay p).sum = p.sum := by
  rw [lookAndSay, Multiset.sum_sum, Finset.sum_multiset_count p]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Multiset.sum_replicate, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The multiplicity of `k` in `LS(p)` is the sum of the distinct parts of `p`
of multiplicity `k`. -/
theorem count_lookAndSay (p : Multiset ℕ) (k : ℕ) :
    (lookAndSay p).count k = ∑ y ∈ p.toFinset.filter (fun y => p.count y = k), y := by
  rw [lookAndSay, Multiset.count_sum', Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Multiset.count_replicate]

/-- For a multiset `q` of positive integers, Wiseman's disjoint-strict-partition
form of Look-and-Say agrees with the entry's definition: `q = LS(p)` for some
multiset `p` of positive integers. -/
theorem isLookAndSay_iff_exists_lookAndSay {q : Multiset ℕ} (hq : 0 ∉ q) :
    IsLookAndSay q ↔ ∃ p : Multiset ℕ, 0 ∉ p ∧ lookAndSay p = q := by
  constructor
  · rintro ⟨P, hP, hdisj⟩
    let p : Multiset ℕ := ∑ m ∈ q.toFinset, ∑ y ∈ P m, Multiset.replicate m y
    have hcp : ∀ z, p.count z = ∑ m ∈ q.toFinset, if z ∈ P m then m else 0 := by
      intro z
      simp only [p, Multiset.count_sum', Multiset.count_replicate]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      exact Finset.sum_ite_eq' (P m) z (fun _ => m)
    have hcount : ∀ m ∈ q.toFinset, ∀ z ∈ P m, p.count z = m := by
      intro m hm z hz
      rw [hcp z, Finset.sum_eq_single m]
      · rw [if_pos hz]
      · intro b hb hbm
        rw [if_neg (Finset.disjoint_left.1 (hdisj hm hb (Ne.symm hbm)) hz)]
      · intro hm'
        exact absurd hm hm'
    have hpos : ∀ m ∈ q.toFinset, m ≠ 0 := fun m hm h0 => hq (h0 ▸ Multiset.mem_toFinset.1 hm)
    have htoF : p.toFinset = q.toFinset.biUnion P := by
      ext z
      rw [Multiset.mem_toFinset, ← Multiset.count_ne_zero, hcp z, Finset.mem_biUnion]
      constructor
      · intro hne
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        refine ⟨m, hm, ?_⟩
        by_contra hz
        exact hm0 (if_neg hz)
      · rintro ⟨m, hm, hz⟩
        rw [← hcp z, hcount m hm z hz]
        exact hpos m hm
    refine ⟨p, ?_, ?_⟩
    · intro h0
      have h0' : (0 : ℕ) ∈ p.toFinset := Multiset.mem_toFinset.2 h0
      rw [htoF, Finset.mem_biUnion] at h0'
      obtain ⟨m, hm, h0m⟩ := h0'
      exact (hP m hm).1 h0m
    · rw [lookAndSay, htoF, Finset.sum_biUnion hdisj]
      conv_rhs => rw [← Multiset.toFinset_sum_count_nsmul_eq q]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [← (hP m hm).2, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [hcount m hm z hz, Multiset.nsmul_singleton]
  · rintro ⟨p, hp0, rfl⟩
    refine ⟨fun k => p.toFinset.filter (fun y => p.count y = k), fun k _ => ⟨?_, ?_⟩, ?_⟩
    · intro h0
      exact hp0 (Multiset.mem_toFinset.1 (Finset.mem_filter.1 h0).1)
    · rw [count_lookAndSay]
    · intro a _ b _ hab
      exact Finset.disjoint_filter.2 (fun y _ h1 h2 => hab (h1.symm.trans h2))

/-- **Wiseman's conjecture in the entry's own terms (A239455, Gus Wiseman,
Aug 11 2025).**  A partition `y` of `n` has a permutation with all distinct run
lengths iff `y` is a Look-and-Say partition of `n`, i.e. `y = LS(p)` for some
partition `p` of `n`. -/
theorem partition_hasDistinctRunOrdering_iff_exists_lookAndSay {n : ℕ} (y : Nat.Partition n) :
    HasDistinctRunOrdering y.parts ↔ ∃ p : Nat.Partition n, lookAndSay p.parts = y.parts := by
  have hy0 : 0 ∉ y.parts := fun h => (lt_irrefl 0) (y.parts_pos h)
  rw [hasDistinctRunOrdering_iff_isLookAndSay, isLookAndSay_iff_exists_lookAndSay hy0]
  constructor
  · rintro ⟨p, hp0, hpy⟩
    refine ⟨⟨p, fun {i} hi => Nat.pos_of_ne_zero (fun h => hp0 (h ▸ hi)), ?_⟩, hpy⟩
    rw [← sum_lookAndSay, hpy, y.parts_sum]
  · rintro ⟨p, hpy⟩
    exact ⟨p.parts, fun h => (lt_irrefl 0) (p.parts_pos h), hpy⟩

end Candidates.A239455GusWisemanFinite
