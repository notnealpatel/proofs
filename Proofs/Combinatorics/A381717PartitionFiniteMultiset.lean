/-
# A381717 — distinct run-sums and constant-block partitions

Gus Wiseman (OEIS A381717, Mar 2025; also A381636) conjectured that an
integer partition has a permutation with distinct run-sums iff it has a
multiset partition into constant blocks with distinct block-sums. Run-sums
are sums of maximal constant runs. The equivalence and its counting form
are established below for multisets of positive integers.

## Proof outline

(i) ⇒ (ii): the maximal runs of the permutation are constant blocks and their
sums are the run-sums.

(ii) ⇒ (i): strong induction on the number `B` of blocks.  If some value `v`
owns `c` blocks with `B + 1 < 2c`, the `v`-block sizes are distinct (positive
`v`, distinct sums); let `m` be the largest.  The `c - 1` merged sums
`v (m + k)` are distinct and exceed every `v`-block sum, while only
`B - c < c - 1` blocks of other values exist, so some merge keeps all sums
distinct and lowers `B`.  Otherwise every value owns at most `(B + 1) / 2`
blocks, and a greedy arrangement (`exists_isChain_ne`) orders the blocks with no
two equal values adjacent; the runs of the concatenation are then exactly the
blocks.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A381717PartitionFiniteMultiset

/-! ## Definitions -/

/-- The run-sums of a sequence: split it into maximal constant runs and sum
each run (`Split` and `Total` in the entry's Mathematica). -/
def runSums (l : List ℕ) : List ℕ := (l.splitBy (· == ·)).map List.sum

/-- A constant block: a nonempty multiset all of whose elements are equal. -/
def IsConstantBlock (b : Multiset ℕ) : Prop :=
  b ≠ 0 ∧ ∃ v : ℕ, b = Multiset.replicate (Multiset.card b) v

/-- Condition (i): some permutation of `y` has pairwise distinct run-sums. -/
def HasDistinctRunSumPerm (y : Multiset ℕ) : Prop :=
  ∃ l : List ℕ, (l : Multiset ℕ) = y ∧ (runSums l).Nodup

/-- Condition (ii): `y` has a multiset partition into constant blocks with
pairwise distinct block-sums (the property whose failure A381717 counts). -/
def HasDistinctConstantBlockSplit (y : Multiset ℕ) : Prop :=
  ∃ P : Multiset (Multiset ℕ), P.join = y ∧ (∀ b ∈ P, IsConstantBlock b) ∧
    (P.map Multiset.sum).Nodup

/-! ## Examples -/

example : runSums [1, 1, 2, 1] = [2, 2, 1] := by decide

example : runSums [3, 3, 3, 1, 1, 2] = [9, 2, 2] := by decide

-- The entry's example: `(3,2,2,1)` splits as `{{3},{2,2},{1}}`.
example : HasDistinctConstantBlockSplit {3, 2, 2, 1} := by
  refine ⟨{{3}, {2, 2}, {1}}, by decide, ?_, by decide⟩
  intro b hb
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨by decide, 3, by decide⟩
  · exact ⟨by decide, 2, by decide⟩
  · exact ⟨by decide, 1, by decide⟩

-- The permutation `(3,2,2,1)` has run-sums `3,4,1`, which are distinct, while
-- the permutation `(2,3,2,1)` has run-sums `2,3,2,1`, which repeat.
example : HasDistinctRunSumPerm {3, 2, 2, 1} := ⟨[3, 2, 2, 1], rfl, by decide⟩

example : ¬ (runSums [2, 3, 2, 1]).Nodup := by decide

/-! ## (i) ⇒ (ii) -/

/-- Every maximal run of a list of naturals is a nonempty constant list. -/
theorem eq_replicate_of_mem_splitBy {l m : List ℕ} (hm : m ∈ l.splitBy (· == ·)) :
    m ≠ [] ∧ ∃ v : ℕ, m = List.replicate m.length v := by
  have hne : m ≠ [] := List.ne_nil_of_mem_splitBy hm
  have hchain : m.IsChain (· = ·) :=
    (List.isChain_of_mem_splitBy hm).imp (fun a b h => by simpa using h)
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨hne, a, ?_⟩
  exact List.isChain_eq_iff_eq_replicate.mp hchain a (by simp)

/-- (i) ⇒ (ii): the maximal runs of a permutation with distinct run-sums form a
constant split with distinct block-sums. -/
theorem hasDistinctConstantBlockSplit_of_hasDistinctRunSumPerm (y : Multiset ℕ)
    (h : HasDistinctRunSumPerm y) : HasDistinctConstantBlockSplit y := by
  obtain ⟨l, rfl, hnd⟩ := h
  refine ⟨((l.splitBy (· == ·)).map (fun m : List ℕ => (m : Multiset ℕ)) : List (Multiset ℕ)),
    ?_, ?_, ?_⟩
  · rw [Multiset.coe_join, List.flatten_splitBy]
  · intro b hb
    rw [Multiset.mem_coe, List.mem_map] at hb
    obtain ⟨m, hm, rfl⟩ := hb
    obtain ⟨hne, v, hv⟩ := eq_replicate_of_mem_splitBy hm
    refine ⟨by simpa using hne, v, ?_⟩
    rw [hv, Multiset.coe_card, List.length_replicate, Multiset.coe_replicate]
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    have hfun : (Multiset.sum ∘ fun m : List ℕ => (m : Multiset ℕ)) = List.sum := by
      funext m
      simp
    rw [hfun]
    exact hnd

/-! ## Blocks as `(value, size)` pairs -/

/-- The constant list with `p.2` copies of the value `p.1`. -/
def blk (p : ℕ × ℕ) : List ℕ := List.replicate p.2 p.1

/-- The constant multiset with `p.2` copies of the value `p.1`. -/
def blkM (p : ℕ × ℕ) : Multiset ℕ := Multiset.replicate p.2 p.1

example : blk (3, 2) = [3, 3] := rfl

example : blkM (3, 2) = {3, 3} := rfl

/-- The list block and the multiset block agree. -/
theorem coe_blk (p : ℕ × ℕ) : ((blk p : List ℕ) : Multiset ℕ) = blkM p := by
  simp only [blk, blkM, Multiset.coe_replicate]

/-- The sum of the block `(v, k)` is `v * k`. -/
theorem sum_blk (p : ℕ × ℕ) : (blk p).sum = p.1 * p.2 := by
  simp [blk, mul_comm]

/-- If consecutive blocks carry different values and every block is nonempty,
the maximal runs of the concatenation are exactly the blocks. -/
theorem splitBy_flatten_blk (L : List (ℕ × ℕ)) (hpos : ∀ p ∈ L, 0 < p.2)
    (hchain : L.IsChain (fun a b => a.1 ≠ b.1)) :
    (L.map blk).flatten.splitBy (· == ·) = L.map blk := by
  rw [List.splitBy_eq_iff]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have hp2 := hpos p hp
    simp only [blk, List.replicate_eq_nil_iff] at hpe
    omega
  · intro m hm
    rw [List.mem_map] at hm
    obtain ⟨p, -, rfl⟩ := hm
    exact List.isChain_replicate_of_rel _ (by simp)
  · rw [List.isChain_map]
    refine hchain.imp_of_mem_imp ?_
    intro a b ha hb hab
    have ha' : blk a ≠ [] := by
      simpa [blk, List.replicate_eq_nil_iff] using (hpos a ha).ne'
    have hb' : blk b ≠ [] := by
      simpa [blk, List.replicate_eq_nil_iff] using (hpos b hb).ne'
    refine ⟨ha', hb', ?_⟩
    simp only [blk, List.getLast_replicate, List.head_replicate]
    simpa using hab

/-! ## The arrangement lemma -/

/-- Two disjoint predicates count at most the whole multiset. -/
theorem countP_add_countP_le_card {α : Type*} (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (hpq : ∀ a, p a → ¬q a) (s : Multiset α) :
    s.countP p + s.countP q ≤ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
    have h := hpq a
    split_ifs with h1 h2 h2 <;> first | omega | exact absurd h2 (h h1)

/-- **Arrangement lemma.**  If no colour occupies more than `(card s + 1) / 2`
items of `s` (and the forbidden first colour `d`, if any, at most
`card s / 2`), then `s` can be listed with no two adjacent items of the same
colour, starting with a colour other than `d`. -/
theorem exists_isChain_ne {α β : Type*} [DecidableEq β] (f : α → β) (n : ℕ) :
    ∀ (s : Multiset α) (d : Option β), Multiset.card s = n →
      (∀ c, 2 * s.countP (fun a => f a = c) ≤ Multiset.card s + 1) →
      (∀ c, d = some c → 2 * s.countP (fun a => f a = c) ≤ Multiset.card s) →
      ∃ l : List α, (l : Multiset α) = s ∧ l.IsChain (fun a b => f a ≠ f b) ∧
        ∀ a ∈ l.head?, d ≠ some (f a) := by
  induction n with
  | zero =>
    intro s d hs _ _
    refine ⟨[], ?_, List.IsChain.nil, by simp⟩
    rw [Multiset.card_eq_zero] at hs
    simp [hs]
  | succ n ih =>
    intro s d hs hall hd
    -- choose the first element `a`
    have hchoice : ∃ a ∈ s, d ≠ some (f a) ∧
        ∀ c, c ≠ f a → 2 * s.countP (fun x => f x = c) ≤ Multiset.card s := by
      by_cases hbig : ∃ a ∈ s, 2 * s.countP (fun x => f x = f a) = Multiset.card s + 1
      · obtain ⟨a, ha, hbig⟩ := hbig
        refine ⟨a, ha, ?_, ?_⟩
        · intro hda
          have hda' := hd (f a) hda
          omega
        · intro c hc
          have hdisj := countP_add_countP_le_card (fun x => f x = c) (fun x => f x = f a)
            (fun x hx hx' => hc (hx.symm.trans hx')) s
          omega
      · push Not at hbig
        have hsmall : ∀ c, 2 * s.countP (fun x => f x = c) ≤ Multiset.card s := by
          intro c
          by_contra hlt
          have heq : 2 * s.countP (fun x => f x = c) = Multiset.card s + 1 := by
            have hc := hall c
            omega
          have hpos : 0 < s.countP (fun x => f x = c) := by omega
          obtain ⟨b, hb, rfl⟩ := Multiset.countP_pos.mp hpos
          exact hbig b hb heq
        have hex : ∃ a ∈ s, d ≠ some (f a) := by
          by_contra hnone
          push Not at hnone
          have hne : s ≠ 0 := by
            intro h0
            rw [h0, Multiset.card_zero] at hs
            omega
          obtain ⟨a0, ha0⟩ := Multiset.exists_mem_of_ne_zero hne
          have hda0 := hnone a0 ha0
          have hcard : s.countP (fun x => f x = f a0) = Multiset.card s := by
            rw [Multiset.countP_eq_card]
            intro x hx
            exact Option.some_injective _ ((hnone x hx).symm.trans hda0)
          have hda0' := hd (f a0) hda0
          omega
        obtain ⟨a, ha, hda⟩ := hex
        exact ⟨a, ha, hda, fun c _ => hsmall c⟩
    obtain ⟨a, ha, hda, hother⟩ := hchoice
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    have hcount : ∀ c, (a ::ₘ t).countP (fun x => f x = c) =
        t.countP (fun x => f x = c) + if f a = c then 1 else 0 :=
      fun c => Multiset.countP_cons _ a t
    rw [Multiset.card_cons] at hs hall hother
    obtain ⟨l, hl, hchain, hhead⟩ := ih t (some (f a)) (by omega)
      (by
        intro c
        by_cases hc : c = f a
        · subst hc
          have h1 := hall (f a)
          rw [hcount, if_pos rfl] at h1
          omega
        · have h1 := hother c hc
          rw [hcount, if_neg (Ne.symm hc)] at h1
          omega)
      (by
        intro c hc
        rw [Option.some_inj] at hc
        subst hc
        have h1 := hall (f a)
        rw [hcount, if_pos rfl] at h1
        omega)
    refine ⟨a :: l, by rw [← Multiset.cons_coe, hl], ?_, ?_⟩
    · refine hchain.cons ?_
      intro y hy hfy
      exact hhead y hy (by rw [hfy])
    · intro x hx
      rw [List.head?_cons, Option.mem_some_iff] at hx
      subst hx
      exact hda

/-! ## The merge step -/

/-- **Merge step.**  Let `Q` list blocks as positive `(value, size)` pairs with
pairwise distinct sums `value * size`.  If some value `v` owns more than
`(card Q + 1) / 2` blocks, two `v`-blocks can be merged so that the sums stay
pairwise distinct; the multiset of entries is unchanged and the number of blocks
drops. -/
theorem exists_merge (Q : Multiset (ℕ × ℕ)) (hpos : ∀ p ∈ Q, 0 < p.1 ∧ 0 < p.2)
    (hnd : (Q.map (fun p => p.1 * p.2)).Nodup) (v : ℕ)
    (hbig : Multiset.card Q + 1 < 2 * Q.countP (fun p => p.1 = v)) :
    ∃ Q' : Multiset (ℕ × ℕ), Multiset.card Q' < Multiset.card Q ∧
      (∀ p ∈ Q', 0 < p.1 ∧ 0 < p.2) ∧ (Q'.map (fun p => p.1 * p.2)).Nodup ∧
      (Q'.map blkM).join = (Q.map blkM).join := by
  classical
  set V := Q.filter (fun p => p.1 = v) with hV
  set O := Q.filter (fun p => ¬p.1 = v) with hO
  have hcardVO : Multiset.card V + Multiset.card O = Multiset.card Q := by
    rw [hV, hO, ← Multiset.card_add, Multiset.filter_add_not]
  have hcountV : Q.countP (fun p => p.1 = v) = Multiset.card V := by
    rw [hV, Multiset.countP_eq_card_filter]
  rw [hcountV, ← hcardVO] at hbig
  have hVnd : V.Nodup := by
    have h1 : (V.map (fun p => p.1 * p.2)).Nodup :=
      Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ Q)) hnd
    exact h1.of_map _
  have hVne : V ≠ 0 := by
    have hVpos : 0 < Multiset.card V := by omega
    exact Multiset.card_pos.mp hVpos
  obtain ⟨pm, hpmV, hpmmax⟩ := Multiset.exists_max_image (fun p : ℕ × ℕ => p.2) hVne
  have hpmQ : pm ∈ Q := Multiset.mem_of_mem_filter hpmV
  have hpm1 : pm.1 = v := (Multiset.mem_filter.mp hpmV).2
  have hvpos : 0 < v := hpm1 ▸ (hpos pm hpmQ).1
  -- the merged sums
  set f : ℕ × ℕ → ℕ := fun q => v * (pm.2 + q.2) with hf
  have hex : ∃ q ∈ V.erase pm, ∀ o ∈ O, o.1 * o.2 ≠ f q := by
    by_contra hnone
    push Not at hnone
    have hsub : ((V.erase pm).map f).toFinset ⊆ (O.map (fun p => p.1 * p.2)).toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Multiset.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨o, ho, hoeq⟩ := hnone q hq
      rw [Multiset.mem_toFinset, Multiset.mem_map]
      exact ⟨o, ho, hoeq⟩
    have hfnd : ((V.erase pm).map f).Nodup := by
      refine (Multiset.Nodup.erase pm hVnd).map_on ?_
      intro x hx y hy hxy
      have hx1 : x.1 = v := (Multiset.mem_filter.mp (Multiset.mem_of_mem_erase hx)).2
      have hy1 : y.1 = v := (Multiset.mem_filter.mp (Multiset.mem_of_mem_erase hy)).2
      have h2 : pm.2 + x.2 = pm.2 + y.2 := Nat.eq_of_mul_eq_mul_left hvpos hxy
      exact Prod.ext (hx1.trans hy1.symm) (by omega)
    have hc1 := Finset.card_le_card hsub
    rw [Multiset.toFinset_card_of_nodup hfnd, Multiset.card_map,
      Multiset.card_erase_of_mem hpmV, Nat.pred_eq_sub_one] at hc1
    have hc2 := Multiset.toFinset_card_le (O.map (fun p => p.1 * p.2))
    rw [Multiset.card_map] at hc2
    omega
  obtain ⟨q, hqVe, hqfree⟩ := hex
  have hqV : q ∈ V := Multiset.mem_of_mem_erase hqVe
  have hq1 : q.1 = v := (Multiset.mem_filter.mp hqV).2
  have hqQ' : q ∈ Q.erase pm :=
    Multiset.mem_of_le (Multiset.erase_le_erase pm (Multiset.filter_le _ Q)) hqVe
  obtain ⟨Q1, hQ1⟩ := Multiset.exists_cons_of_mem hpmQ
  rw [hQ1, Multiset.erase_cons_head] at hqQ'
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hqQ'
  have hQ : Q = pm ::ₘ q ::ₘ R := by rw [hQ1, hR]
  have hq2 : 0 < q.2 := (hpos q (hQ ▸ by simp)).2
  refine ⟨(v, pm.2 + q.2) ::ₘ R, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    simp
  · intro p hp
    rw [Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hvpos, by omega⟩
    · exact hpos p (by rw [hQ]; simp [hp])
  · have hndQ := hnd
    rw [hQ, Multiset.map_cons, Multiset.map_cons, Multiset.nodup_cons, Multiset.nodup_cons]
      at hndQ
    rw [Multiset.map_cons, Multiset.nodup_cons]
    refine ⟨?_, hndQ.2.2⟩
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨r, hr, hreq⟩ := hmem
    have hrQ : r ∈ Q := by rw [hQ]; simp [hr]
    by_cases hr1 : r.1 = v
    · have hrV : r ∈ V := Multiset.mem_filter.mpr ⟨hrQ, hr1⟩
      have hle : r.2 ≤ pm.2 := hpmmax r hrV
      rw [hr1] at hreq
      have hlt : v * r.2 < v * (pm.2 + q.2) := Nat.mul_lt_mul_of_pos_left (by omega) hvpos
      dsimp only at hreq
      omega
    · have hrO : r ∈ O := Multiset.mem_filter.mpr ⟨hrQ, hr1⟩
      exact hqfree r hrO hreq
  · rw [hQ]
    simp only [Multiset.map_cons, Multiset.join_cons, blkM]
    rw [Multiset.replicate_add, hpm1, hq1, add_assoc]

/-! ## (ii) ⇒ (i) -/

/-- If no value owns more than `(card Q + 1) / 2` blocks, the blocks can be
concatenated into a permutation whose run-sums are the (distinct) block sums. -/
theorem exists_perm_of_balanced (Q : Multiset (ℕ × ℕ)) (hpos : ∀ p ∈ Q, 0 < p.1 ∧ 0 < p.2)
    (hnd : (Q.map (fun p => p.1 * p.2)).Nodup)
    (hbal : ∀ v, 2 * Q.countP (fun p => p.1 = v) ≤ Multiset.card Q + 1) :
    ∃ l : List ℕ, (l : Multiset ℕ) = (Q.map blkM).join ∧ (runSums l).Nodup := by
  obtain ⟨L, hL, hchain, -⟩ := exists_isChain_ne Prod.fst (Multiset.card Q) Q none rfl hbal
    (by simp)
  have hposL : ∀ p ∈ L, 0 < p.2 := fun p hp => (hpos p (by rw [← hL]; exact hp)).2
  refine ⟨(L.map blk).flatten, ?_, ?_⟩
  · rw [← hL, ← Multiset.coe_join, Multiset.map_coe, List.map_map]
    congr 2
  · rw [runSums, splitBy_flatten_blk L hposL hchain, List.map_map]
    have hfun : (List.sum ∘ blk) = fun p : ℕ × ℕ => p.1 * p.2 := by
      funext p
      exact sum_blk p
    rw [hfun, ← Multiset.coe_nodup, ← Multiset.map_coe, hL]
    exact hnd

/-- (ii) ⇒ (i) in pair form, by strong induction on the number of blocks: merge
while some value is over-represented, then arrange. -/
theorem exists_perm_of_pairs (n : ℕ) : ∀ Q : Multiset (ℕ × ℕ), Multiset.card Q = n →
    (∀ p ∈ Q, 0 < p.1 ∧ 0 < p.2) → (Q.map (fun p => p.1 * p.2)).Nodup →
    ∃ l : List ℕ, (l : Multiset ℕ) = (Q.map blkM).join ∧ (runSums l).Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hpos hnd
    by_cases hbal : ∀ v, 2 * Q.countP (fun p => p.1 = v) ≤ Multiset.card Q + 1
    · exact exists_perm_of_balanced Q hpos hnd hbal
    · push Not at hbal
      obtain ⟨v, hv⟩ := hbal
      obtain ⟨Q', hcard, hpos', hnd', hjoin⟩ := exists_merge Q hpos hnd v hv
      obtain ⟨l, hl, hlnd⟩ := ih (Multiset.card Q') (hQn ▸ hcard) Q' rfl hpos' hnd'
      exact ⟨l, hl.trans hjoin, hlnd⟩

/-- Lift a multiset through a map: if every element of `P` has a preimage under
`g` satisfying `R`, then `P` is the image of a multiset of such preimages. -/
theorem exists_pairs_of_forall {β γ : Type*} (g : β → γ) (R : β → Prop) (P : Multiset γ)
    (h : ∀ b ∈ P, ∃ p, g p = b ∧ R p) : ∃ Q : Multiset β, Q.map g = P ∧ ∀ p ∈ Q, R p := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | cons b P ih =>
    obtain ⟨Q, hQ, hR⟩ := ih (fun c hc => h c (Multiset.mem_cons_of_mem hc))
    obtain ⟨p, hp, hRp⟩ := h b (Multiset.mem_cons_self b P)
    refine ⟨p ::ₘ Q, by rw [Multiset.map_cons, hp, hQ], ?_⟩
    intro x hx
    rw [Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hRp
    · exact hR x hx

/-- (ii) ⇒ (i): a partition with a constant split with distinct block-sums has a
permutation with distinct run-sums. -/
theorem hasDistinctRunSumPerm_of_hasDistinctConstantBlockSplit (y : Multiset ℕ)
    (hy : ∀ x ∈ y, 0 < x) (h : HasDistinctConstantBlockSplit y) : HasDistinctRunSumPerm y := by
  obtain ⟨P, hjoin, hconst, hnd⟩ := h
  obtain ⟨Q, hQ, hRQ⟩ := exists_pairs_of_forall blkM (fun p => 0 < p.1 ∧ 0 < p.2) P (by
    intro b hb
    obtain ⟨hne, v, hv⟩ := hconst b hb
    have hcard : 0 < Multiset.card b := Multiset.card_pos.mpr hne
    have hvb : v ∈ b := by
      rw [hv]
      exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
    have hvy : v ∈ y := by
      rw [← hjoin]
      exact Multiset.mem_join.mpr ⟨b, hb, hvb⟩
    exact ⟨(v, Multiset.card b), hv.symm, hy v hvy, hcard⟩)
  have hndQ : (Q.map (fun p => p.1 * p.2)).Nodup := by
    rw [← hQ, Multiset.map_map] at hnd
    have hfun : (Multiset.sum ∘ blkM) = fun p : ℕ × ℕ => p.1 * p.2 := by
      funext p
      simp [blkM, mul_comm]
    rw [hfun] at hnd
    exact hnd
  obtain ⟨l, hl, hlnd⟩ := exists_perm_of_pairs (Multiset.card Q) Q rfl hRQ hndQ
  exact ⟨l, by rw [hl, hQ, hjoin], hlnd⟩

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A381717, Gus Wiseman, Mar 2025; also A381636).**

For every integer partition `y` (a finite multiset of positive integers),
(i) some permutation of `y` has pairwise distinct run-sums iff (ii) `y` can be
split into constant multisets with pairwise distinct block-sums. -/
theorem hasDistinctRunSumPerm_iff_hasDistinctConstantBlockSplit (y : Multiset ℕ)
    (hy : ∀ x ∈ y, 0 < x) :
    HasDistinctRunSumPerm y ↔ HasDistinctConstantBlockSplit y :=
  ⟨hasDistinctConstantBlockSplit_of_hasDistinctRunSumPerm y,
    hasDistinctRunSumPerm_of_hasDistinctConstantBlockSplit y hy⟩

open Classical in
/-- **Counting form (A381717 comment).**  For every `n`, the number of integer
partitions of `n` having no permutation with all distinct run-sums equals the
number of integer partitions of `n` that cannot be partitioned into constant
multisets with distinct block-sums, i.e. A381717(n). -/
theorem card_not_hasDistinctRunSumPerm_eq (n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ¬HasDistinctRunSumPerm p.parts)).card =
      (Finset.univ.filter
        (fun p : n.Partition => ¬HasDistinctConstantBlockSplit p.parts)).card := by
  congr 1
  refine Finset.filter_congr ?_
  intro p _
  rw [hasDistinctRunSumPerm_iff_hasDistinctConstantBlockSplit p.parts
    (fun x hx => p.parts_pos hx)]

/-! ## Examples -/

-- The positivity hypothesis is satisfiable: the theorem applies to `(3,2,2,1)`.
example : HasDistinctRunSumPerm {3, 2, 2, 1} ↔ HasDistinctConstantBlockSplit {3, 2, 2, 1} :=
  hasDistinctRunSumPerm_iff_hasDistinctConstantBlockSplit _ (by decide)

-- The entry's counted example: `(3,2,1,1,1)` has no permutation with distinct
-- run-sums (checked over all permutations), hence no constant split with
-- distinct block-sums.  Both sides of the equivalence occur.
set_option maxRecDepth 100000 in
example : ¬ HasDistinctRunSumPerm {3, 2, 1, 1, 1} ∧
    ¬ HasDistinctConstantBlockSplit {3, 2, 1, 1, 1} := by
  have hrun : ¬ HasDistinctRunSumPerm {3, 2, 1, 1, 1} := by
    rintro ⟨l, hl, hnd⟩
    have hperm : l ∈ ([3, 2, 1, 1, 1] : List ℕ).permutations' :=
      List.mem_permutations'.mpr (Multiset.coe_eq_coe.mp hl)
    have hall : ∀ m ∈ ([3, 2, 1, 1, 1] : List ℕ).permutations', ¬ (runSums m).Nodup := by
      decide +kernel
    exact hall l hperm hnd
  refine ⟨hrun, ?_⟩
  rwa [← hasDistinctRunSumPerm_iff_hasDistinctConstantBlockSplit _ (by decide)]

end Candidates.A381717PartitionFiniteMultiset
