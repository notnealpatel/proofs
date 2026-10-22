/-
# Beck's A229816 partition identity

Philip Cuthbertson, "A requested analytic proof of an identity of Dixit,
Kumar, and Srivastava", arXiv:2608.30180, Section 4; OEIS A229816,
George Beck (Jun 23 2019).
For every `n`, partitions of `n` whose length is not a part are counted by
the total number of distinct part sizes among partitions of `2n+2` with
rank `n+1`. Rank is largest part minus length.
The proof is bijective. The formulas involving partition numbers are stated
at `n+2`, avoiding negative indices; the main equality holds for all `n`.
-/
import Mathlib

set_option autoImplicit false

namespace BeckA229816

open Finset

/-! ## Definitions mirroring the source -/

/-- `e(n)`: the number of partitions of `n` whose length (number of parts) is
not a part ("unrestricted non-Rascoe partitions" of Dixit-Kumar-Srivastava). -/
def nonRascoeCount (n : ℕ) : ℕ :=
  (univ.filter (fun l : n.Partition => Multiset.card l.parts ∉ l.parts)).card

/-- The (Dyson) rank of a partition: largest part minus number of parts,
computed in `ℤ`.  The largest part is `l.parts.sup` (which is `0` only for the
empty partition of `0`). -/
def rank {n : ℕ} (l : n.Partition) : ℤ :=
  (l.parts.sup : ℤ) - (Multiset.card l.parts : ℤ)

/-- `f(n)`: the sum, over all partitions of `2n + 2` with rank `n + 1`, of the
number of distinct part sizes. -/
def beckF (n : ℕ) : ℕ :=
  ∑ l ∈ univ.filter (fun l : (2 * n + 2).Partition => rank l = n + 1),
    l.parts.toFinset.card

/-! ## Examples on small instances -/

/-- The partition `(2)` of `2` has rank `1 = 0 + 1`, so it contributes to `f(0)`. -/
example : rank (⟨{2}, by decide, by decide⟩ : (2 : ℕ).Partition) = 0 + 1 := by decide

/-- The partition `(1, 1)` of `2` has rank `-1`. -/
example : rank (⟨{1, 1}, by decide, by decide⟩ : (2 : ℕ).Partition) = -1 := by decide

/-- The partition `(5, 1)` of `6 = 2 * 2 + 2` has rank `3 = 2 + 1` and two part
sizes; `(4, 1, 1)` has rank `1`. -/
example : rank (⟨{5, 1}, by decide, by decide⟩ : (6 : ℕ).Partition) = 2 + 1 ∧
    (({5, 1} : Multiset ℕ).toFinset.card = 2) ∧
    rank (⟨{4, 1, 1}, by decide, by decide⟩ : (6 : ℕ).Partition) = 1 := by decide

/-- `(2, 1)` has length `2`, which is a part (a Rascoe partition), while
`(3, 1)` has length `2`, which is not a part (non-Rascoe). -/
example : Multiset.card ({2, 1} : Multiset ℕ) ∈ ({2, 1} : Multiset ℕ) ∧
    Multiset.card ({3, 1} : Multiset ℕ) ∉ ({3, 1} : Multiset ℕ) := by decide

/-! ## Transport to multisets of parts -/

/-- The multisets of parts of all partitions of `n`. -/
def partsSet (n : ℕ) : Finset (Multiset ℕ) :=
  univ.map ⟨fun l : n.Partition => l.parts, fun _ _ h => Nat.Partition.ext h⟩

/-- A multiset is the multiset of parts of a partition of `n` iff its elements
are positive and sum to `n`. -/
theorem mem_partsSet {n : ℕ} {m : Multiset ℕ} :
    m ∈ partsSet n ↔ (∀ i ∈ m, 0 < i) ∧ m.sum = n := by
  constructor
  · intro h
    obtain ⟨l, -, rfl⟩ := Finset.mem_map.1 h
    exact ⟨fun i hi => l.parts_pos hi, l.parts_sum⟩
  · rintro ⟨hpos, hsum⟩
    exact Finset.mem_map.2 ⟨⟨m, fun hi => hpos _ hi, hsum⟩, Finset.mem_univ _, rfl⟩

/-- `p(n) = #partsSet n`. -/
theorem card_partsSet (n : ℕ) : (partsSet n).card = Fintype.card n.Partition := by
  rw [partsSet, Finset.card_map, Finset.card_univ]

/-- Counting partitions by a property of their parts is counting `partsSet`. -/
theorem card_filter_univ_eq {n : ℕ} (p : Multiset ℕ → Prop) [DecidablePred p] :
    (univ.filter (fun l : n.Partition => p l.parts)).card = ((partsSet n).filter p).card := by
  rw [partsSet, Finset.filter_map, Finset.card_map]
  rfl

/-- Weighted sums over partitions filtered by a property of their parts are
sums over `partsSet`. -/
theorem sum_filter_univ_eq {n : ℕ} (p : Multiset ℕ → Prop) [DecidablePred p]
    (w : Multiset ℕ → ℕ) :
    ∑ l ∈ univ.filter (fun l : n.Partition => p l.parts), w l.parts =
      ∑ m ∈ (partsSet n).filter p, w m := by
  rw [partsSet, Finset.filter_map, Finset.sum_map]
  rfl

/-! ## Multiset helpers -/

/-- Adding `1` to every element raises the sum by the cardinality. -/
theorem sum_map_add_one (s : Multiset ℕ) :
    (s.map (· + 1)).sum = s.sum + Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons]
    ring

/-- Subtracting `1` after adding `1` is the identity. -/
theorem map_sub_one_map_add_one (s : Multiset ℕ) :
    (s.map (· + 1)).map (· - 1) = s := by
  simp [Multiset.map_map]

/-- Adding `1` after subtracting `1` is the identity on positive elements. -/
theorem map_add_one_map_sub_one {s : Multiset ℕ} (h : ∀ i ∈ s, 0 < i) :
    (s.map (· - 1)).map (· + 1) = s := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl fun i hi => Nat.sub_add_cancel (h i hi)

/-- Sum after subtracting `1` from positive elements. -/
theorem sum_map_sub_one_add_card {s : Multiset ℕ} (h : ∀ i ∈ s, 0 < i) :
    (s.map (· - 1)).sum + Multiset.card s = s.sum := by
  conv_rhs => rw [← map_add_one_map_sub_one h]
  rw [sum_map_add_one, Multiset.card_map]

/-- The supremum of a nonempty multiset of naturals is one of its elements. -/
theorem sup_mem_of_ne_zero {s : Multiset ℕ} (h : s ≠ 0) : s.sup ∈ s := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl h
  | cons a s ih =>
    rw [Multiset.sup_cons]
    by_cases hs : s = 0
    · subst hs
      simp
    · rcases le_total a s.sup with hle | hle
      · rw [sup_eq_right.2 hle]
        exact Multiset.mem_cons_of_mem (ih hs)
      · rw [sup_eq_left.2 hle]
        exact Multiset.mem_cons_self a s

/-- Distinct values are preserved by adding `1`. -/
theorem card_toFinset_map_add_one (s : Multiset ℕ) :
    (s.map (· + 1)).toFinset.card = s.toFinset.card := by
  rw [Multiset.toFinset_map]
  exact Finset.card_image_of_injective _ (add_left_injective 1)


/-! ## Bijection (A): partitions with a part `1` -/

/-- (A) Partitions of `n + 1` containing a part `1` are equinumerous with
partitions of `n`: remove one part `1`. -/
theorem card_filter_one_mem (n : ℕ) :
    ((partsSet (n + 1)).filter (fun m => 1 ∈ m)).card = (partsSet n).card := by
  refine Finset.card_nbij' (fun m => m.erase 1) (fun m => 1 ::ₘ m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet] at hm
    obtain ⟨⟨hpos, hsum⟩, h1⟩ := hm
    rw [Finset.mem_coe, mem_partsSet]
    refine ⟨fun i hi => hpos i (Multiset.mem_of_mem_erase hi), ?_⟩
    have hs := Multiset.sum_erase h1
    show (m.erase 1).sum = n
    omega
  · intro m hm
    rw [Finset.mem_coe, mem_partsSet] at hm
    obtain ⟨hpos, hsum⟩ := hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet]
    refine ⟨⟨fun i hi => ?_, ?_⟩, Multiset.mem_cons_self 1 m⟩
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact Nat.one_pos
      · exact hpos i hi
    · rw [Multiset.sum_cons, hsum, add_comm]
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter] at hm
    exact Multiset.cons_erase hm.2
  · intro m _
    exact Multiset.erase_cons_head 1 m

/-! ## Bijection (B): Rascoe partitions -/

/-- Forward map of (B): remove one part equal to the length, add `1` to every
remaining part. -/
def rascoeFwd (m : Multiset ℕ) : Multiset ℕ :=
  (m.erase (Multiset.card m)).map (· + 1)

/-- Backward map of (B): subtract `1` from every part, then add a part equal to
the new length. -/
def rascoeBwd (m : Multiset ℕ) : Multiset ℕ :=
  (Multiset.card m + 1) ::ₘ m.map (· - 1)

/-- `1` is never an element of a multiset of the form `s.map (· + 1)` with
positive `s`. -/
theorem one_not_mem_map_add_one {s : Multiset ℕ} (h : ∀ i ∈ s, 0 < i) :
    1 ∉ s.map (· + 1) := by
  intro h1
  obtain ⟨a, ha, hEq⟩ := Multiset.mem_map.1 h1
  have := h a ha
  omega

/-- (B) Partitions of `n + 1` whose length is a part are equinumerous with
partitions of `n` with no part `1`. -/
theorem card_filter_card_mem (n : ℕ) :
    ((partsSet (n + 1)).filter (fun m => Multiset.card m ∈ m)).card =
      ((partsSet n).filter (fun m => 1 ∉ m)).card := by
  refine Finset.card_nbij' rascoeFwd rascoeBwd ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet] at hm
    obtain ⟨⟨hpos, hsum⟩, hL⟩ := hm
    have hposE : ∀ i ∈ m.erase (Multiset.card m), 0 < i :=
      fun i hi => hpos i (Multiset.mem_of_mem_erase hi)
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet]
    refine ⟨⟨fun i hi => ?_, ?_⟩, one_not_mem_map_add_one hposE⟩
    · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hi
      exact Nat.succ_pos a
    · have hs := Multiset.sum_erase hL
      have hc := Multiset.card_erase_of_mem hL
      rw [Nat.pred_eq_sub_one] at hc
      have hLpos := hpos _ hL
      rw [rascoeFwd, sum_map_add_one, hc]
      omega
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet] at hm
    obtain ⟨⟨hpos, hsum⟩, h1⟩ := hm
    have hpos2 : ∀ i ∈ m, 1 < i := fun i hi => by
      have := hpos i hi
      have hne : i ≠ 1 := fun h => h1 (h ▸ hi)
      omega
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet]
    refine ⟨⟨fun i hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact Nat.succ_pos _
      · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hi
        have := hpos2 a ha
        omega
    · have hs := sum_map_sub_one_add_card hpos
      rw [rascoeBwd, Multiset.sum_cons]
      omega
    · rw [rascoeBwd, Multiset.card_cons, Multiset.card_map]
      exact Multiset.mem_cons_self _ _
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet] at hm
    obtain ⟨⟨hpos, -⟩, hL⟩ := hm
    have hc := Multiset.card_erase_of_mem hL
    rw [Nat.pred_eq_sub_one] at hc
    have hLpos := hpos _ hL
    have hcard : Multiset.card (rascoeFwd m) + 1 = Multiset.card m := by
      rw [rascoeFwd, Multiset.card_map, hc]
      omega
    rw [rascoeBwd, hcard, rascoeFwd, map_sub_one_map_add_one, Multiset.cons_erase hL]
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_partsSet] at hm
    obtain ⟨⟨hpos, -⟩, -⟩ := hm
    have hcard : Multiset.card (rascoeBwd m) = Multiset.card m + 1 := by
      rw [rascoeBwd, Multiset.card_cons, Multiset.card_map]
    rw [rascoeFwd, hcard, rascoeBwd, Multiset.erase_cons_head, map_add_one_map_sub_one hpos]


/-! ## Bijection (C): part sizes of partitions with no part `1` -/

/-- Forward map of (C): from a pair `(λ, k)` remove one part `k` and add
`k - 2` parts equal to `1`. -/
def sizeFwd (x : Σ _ : Multiset ℕ, ℕ) : Multiset ℕ :=
  x.1.erase x.2 + Multiset.replicate (x.2 - 2) 1

/-- Backward map of (C): replace all `m₁` parts `1` by a single part `m₁ + 2`,
remembering that part size. -/
def sizeBwd (m : Multiset ℕ) : Σ _ : Multiset ℕ, ℕ :=
  ⟨(m.count 1 + 2) ::ₘ m.filter (fun a => ¬ a = 1), m.count 1 + 2⟩

/-- Splitting off the parts equal to `1`. -/
theorem filter_ne_one_add_replicate (m : Multiset ℕ) :
    m.filter (fun a => ¬ a = 1) + Multiset.replicate (m.count 1) 1 = m := by
  rw [← Multiset.filter_eq' m 1, add_comm]
  exact Multiset.filter_add_not _ m

/-- (C) The total number of part sizes over all partitions of `n + 2` with no
part `1` equals `p(n)`. -/
theorem sum_card_toFinset_filter_one_not_mem (n : ℕ) :
    ∑ m ∈ (partsSet (n + 2)).filter (fun m => 1 ∉ m), m.toFinset.card =
      (partsSet n).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_nbij' sizeFwd sizeBwd ?_ ?_ ?_ ?_
  · rintro ⟨m, k⟩ hx
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, mem_partsSet,
      Multiset.mem_toFinset] at hx
    obtain ⟨⟨⟨hpos, hsum⟩, h1⟩, hk⟩ := hx
    dsimp only at hpos hsum h1 hk
    have hk2 : 2 ≤ k := by
      have := hpos k hk
      have hne : k ≠ 1 := fun h => h1 (h ▸ hk)
      omega
    rw [Finset.mem_coe, mem_partsSet]
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hi with hi | hi
      · exact hpos i (Multiset.mem_of_mem_erase hi)
      · rw [Multiset.eq_of_mem_replicate hi]
        exact Nat.one_pos
    · have hs := Multiset.sum_erase hk
      rw [sizeFwd, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
      dsimp only
      omega
  · intro m hm
    rw [Finset.mem_coe, mem_partsSet] at hm
    obtain ⟨hpos, hsum⟩ := hm
    have hsplit := congrArg Multiset.sum (filter_ne_one_add_replicate m)
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one] at hsplit
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, mem_partsSet,
      Multiset.mem_toFinset, sizeBwd]
    refine ⟨⟨⟨fun i hi => ?_, ?_⟩, ?_⟩, Multiset.mem_cons_self _ _⟩
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact Nat.succ_pos _
      · exact hpos i (Multiset.mem_of_mem_filter hi)
    · rw [Multiset.sum_cons]
      omega
    · intro h1
      rcases Multiset.mem_cons.1 h1 with h | h
      · omega
      · exact (Multiset.of_mem_filter h) rfl
  · rintro ⟨m, k⟩ hx
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, mem_partsSet,
      Multiset.mem_toFinset] at hx
    obtain ⟨⟨⟨hpos, -⟩, h1⟩, hk⟩ := hx
    dsimp only at hpos h1 hk
    have hk2 : 2 ≤ k := by
      have := hpos k hk
      have hne : k ≠ 1 := fun h => h1 (h ▸ hk)
      omega
    have h1E : 1 ∉ m.erase k := fun h => h1 (Multiset.mem_of_mem_erase h)
    have hcount : (sizeFwd ⟨m, k⟩).count 1 + 2 = k := by
      rw [sizeFwd, Multiset.count_add, Multiset.count_eq_zero.2 h1E,
        Multiset.count_replicate_self]
      dsimp only
      omega
    have hfilter : (sizeFwd ⟨m, k⟩).filter (fun a => ¬ a = 1) = m.erase k := by
      rw [sizeFwd, Multiset.filter_add, Multiset.filter_eq_self.2, Multiset.filter_eq_nil.2,
        add_zero]
      · intro a ha
        rw [Multiset.eq_of_mem_replicate ha]
        exact not_not.2 rfl
      · intro a ha hEq
        exact h1E (hEq ▸ ha)
    rw [sizeBwd, hcount, hfilter, Multiset.cons_erase hk]
  · intro m _
    rw [sizeBwd, sizeFwd]
    dsimp only
    rw [Multiset.erase_cons_head, Nat.add_sub_cancel]
    exact filter_ne_one_add_replicate m


/-! ## Bijection (D): partitions of `2n + 2` with rank `n + 1` -/

/-- The rank `sup − card` of a multiset of parts, in `ℤ`. -/
def rankParts (m : Multiset ℕ) : ℤ :=
  (m.sup : ℤ) - (Multiset.card m : ℤ)

/-- Forward map of (D): remove the largest part, add `1` to the others. -/
def rankFwd (m : Multiset ℕ) : Multiset ℕ :=
  (m.erase m.sup).map (· + 1)

/-- Backward map of (D) at level `n`: subtract `1` from every part and add a
largest part `n + ℓ + 2`, where `ℓ` is the original length. -/
def rankBwd (n : ℕ) (m : Multiset ℕ) : Multiset ℕ :=
  (n + Multiset.card m + 2) ::ₘ m.map (· - 1)

/-- Every element of a multiset of naturals is at most its sum. -/
theorem le_of_mem_of_sum_eq {m : Multiset ℕ} {n i : ℕ} (hsum : m.sum = n) (hi : i ∈ m) :
    i ≤ n :=
  hsum ▸ Multiset.le_sum_of_mem hi

/-- The new part `n + ℓ + 2` of `rankBwd n μ` is strictly larger than every
other part when `μ ⊢ n`. -/
theorem lt_of_mem_map_sub_one {μ : Multiset ℕ} {n i : ℕ} (hsum : μ.sum = n)
    (hi : i ∈ μ.map (· - 1)) : i < n + Multiset.card μ + 2 := by
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hi
  have := le_of_mem_of_sum_eq hsum ha
  omega

/-- The largest part of `rankBwd n μ` is the new part. -/
theorem sup_rankBwd {μ : Multiset ℕ} {n : ℕ} (hsum : μ.sum = n) :
    (rankBwd n μ).sup = n + Multiset.card μ + 2 := by
  rw [rankBwd, Multiset.sup_cons, sup_eq_left]
  exact Multiset.sup_le.2 fun i hi => (lt_of_mem_map_sub_one hsum hi).le

/-- `rankBwd n μ` has exactly one more part size than `μ` when `μ ⊢ n` has
positive parts. -/
theorem card_toFinset_rankBwd {μ : Multiset ℕ} {n : ℕ} (hpos : ∀ i ∈ μ, 0 < i)
    (hsum : μ.sum = n) :
    (rankBwd n μ).toFinset.card = μ.toFinset.card + 1 := by
  have hnot : n + Multiset.card μ + 2 ∉ μ.map (· - 1) :=
    fun h => lt_irrefl _ (lt_of_mem_map_sub_one hsum h)
  rw [rankBwd, Multiset.toFinset_cons, Finset.card_insert_of_notMem
    (fun h => hnot (Multiset.mem_toFinset.1 h))]
  congr 1
  conv_rhs => rw [← map_add_one_map_sub_one hpos]
  rw [card_toFinset_map_add_one]

/-- (D) `f(n)` is the sum over partitions `μ ⊢ n` with no part `1` of
(number of part sizes of `μ`) `+ 1`. -/
theorem beckF_eq_sum (n : ℕ) :
    beckF n = ∑ m ∈ (partsSet n).filter (fun m => 1 ∉ m), (m.toFinset.card + 1) := by
  have hF : beckF n = ∑ l ∈ univ.filter (fun l : (2 * n + 2).Partition =>
      rankParts l.parts = n + 1), l.parts.toFinset.card := rfl
  rw [hF, sum_filter_univ_eq (fun m => rankParts m = n + 1) (fun m => m.toFinset.card)]
  -- membership in the source: positive parts, sum `2n + 2`, rank `n + 1`
  have hsrc : ∀ m ∈ (partsSet (2 * n + 2)).filter (fun m => rankParts m = n + 1),
      (∀ i ∈ m, 0 < i) ∧ m.sum = 2 * n + 2 ∧ m.sup ∈ m ∧
        m.sup = n + 1 + Multiset.card m := by
    intro m hm
    rw [Finset.mem_filter, mem_partsSet, rankParts] at hm
    obtain ⟨⟨hpos, hsum⟩, hrank⟩ := hm
    have hne : m ≠ 0 := by
      rintro rfl
      simp at hsum
    exact ⟨hpos, hsum, sup_mem_of_ne_zero hne, by omega⟩
  have htgt : ∀ μ ∈ (partsSet n).filter (fun m => 1 ∉ m),
      (∀ i ∈ μ, 0 < i) ∧ μ.sum = n ∧ 1 ∉ μ := by
    intro μ hμ
    rw [Finset.mem_filter, mem_partsSet] at hμ
    exact ⟨hμ.1.1, hμ.1.2, hμ.2⟩
  have hleft : ∀ m ∈ (partsSet (2 * n + 2)).filter (fun m => rankParts m = n + 1),
      rankBwd n (rankFwd m) = m := by
    intro m hm
    obtain ⟨hpos, -, hmem, hsup⟩ := hsrc m hm
    have hc := Multiset.card_erase_of_mem hmem
    rw [Nat.pred_eq_sub_one] at hc
    have hLpos : 0 < Multiset.card m := Multiset.card_pos_iff_exists_mem.2 ⟨_, hmem⟩
    have hhead : n + Multiset.card (rankFwd m) + 2 = m.sup := by
      rw [rankFwd, Multiset.card_map, hc]
      omega
    rw [rankBwd, hhead, rankFwd, map_sub_one_map_add_one, Multiset.cons_erase hmem]
  have hmaps : ∀ m ∈ (partsSet (2 * n + 2)).filter (fun m => rankParts m = n + 1),
      rankFwd m ∈ (partsSet n).filter (fun m => 1 ∉ m) := by
    intro m hm
    obtain ⟨hpos, hsum, hmem, hsup⟩ := hsrc m hm
    have hposE : ∀ i ∈ m.erase m.sup, 0 < i :=
      fun i hi => hpos i (Multiset.mem_of_mem_erase hi)
    rw [Finset.mem_filter, mem_partsSet]
    refine ⟨⟨fun i hi => ?_, ?_⟩, one_not_mem_map_add_one hposE⟩
    · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hi
      exact Nat.succ_pos a
    · have hs := Multiset.sum_erase hmem
      have hc := Multiset.card_erase_of_mem hmem
      rw [Nat.pred_eq_sub_one] at hc
      have hLpos : 0 < Multiset.card m := Multiset.card_pos_iff_exists_mem.2 ⟨_, hmem⟩
      rw [rankFwd, sum_map_add_one, hc]
      omega
  refine Finset.sum_nbij' rankFwd (rankBwd n) hmaps ?_ hleft ?_ ?_
  · intro μ hμ
    obtain ⟨hpos, hsum, h1⟩ := htgt μ hμ
    have hpos2 : ∀ i ∈ μ, 1 < i := fun i hi => by
      have := hpos i hi
      have hne : i ≠ 1 := fun h => h1 (h ▸ hi)
      omega
    rw [Finset.mem_filter, mem_partsSet, rankParts, sup_rankBwd hsum]
    refine ⟨⟨fun i hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact Nat.succ_pos _
      · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hi
        have := hpos2 a ha
        omega
    · have hs := sum_map_sub_one_add_card hpos
      rw [rankBwd, Multiset.sum_cons]
      omega
    · rw [rankBwd, Multiset.card_cons, Multiset.card_map]
      push_cast
      ring
  · intro μ hμ
    obtain ⟨hpos, hsum, -⟩ := htgt μ hμ
    rw [rankFwd, sup_rankBwd hsum, rankBwd, Multiset.erase_cons_head,
      map_add_one_map_sub_one hpos]
  · intro m hm
    obtain ⟨hpos, -, -, -⟩ := hsrc m hm
    have hfwd := Finset.mem_filter.1 (hmaps m hm)
    rw [mem_partsSet] at hfwd
    conv_lhs => rw [← hleft m hm]
    exact card_toFinset_rankBwd hfwd.1.1 hfwd.1.2


/-! ## Assembly -/

/-- The only partition of `0` is the empty one. -/
theorem partsSet_zero : partsSet 0 = {0} := by
  ext m
  rw [mem_partsSet, Finset.mem_singleton]
  constructor
  · rintro ⟨hpos, hsum⟩
    refine Multiset.eq_zero_of_forall_notMem fun i hi => ?_
    have := hpos i hi
    have := le_of_mem_of_sum_eq hsum hi
    omega
  · rintro rfl
    simp

/-- Every partition of `1` has a part `1`. -/
theorem filter_one_not_mem_partsSet_one :
    (partsSet 1).filter (fun m => 1 ∉ m) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun m hm h1 => h1 ?_
  rw [mem_partsSet] at hm
  obtain ⟨hpos, hsum⟩ := hm
  have hne : m ≠ 0 := by
    rintro rfl
    simp at hsum
  obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hne
  have := hpos i hi
  have := le_of_mem_of_sum_eq hsum hi
  have hi1 : i = 1 := by omega
  exact hi1 ▸ hi

/-- `e(n)` plus the number of (unrestricted) Rascoe partitions of `n` is `p(n)`. -/
theorem nonRascoeCount_add_card_filter (n : ℕ) :
    nonRascoeCount n + ((partsSet n).filter (fun m => Multiset.card m ∈ m)).card =
      (partsSet n).card := by
  have he : nonRascoeCount n = ((partsSet n).filter (fun m => Multiset.card m ∉ m)).card :=
    card_filter_univ_eq (fun m => Multiset.card m ∉ m)
  rw [he, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- Partitions of `n` split by whether they contain a part `1`. -/
theorem card_filter_one_mem_add (n : ℕ) :
    ((partsSet n).filter (fun m => 1 ∈ m)).card +
      ((partsSet n).filter (fun m => 1 ∉ m)).card = (partsSet n).card :=
  Finset.card_filter_add_card_filter_not _

/-- **Beck's A229816 conjecture** (arXiv:2608.30180, Section 4, Theorem; OEIS
A229816, G. Beck 2019): for every `n`, the number `e(n)` of partitions of `n`
whose length is not a part equals `f(n)`, the total number of distinct part
sizes over all partitions of `2n + 2` with rank (largest part minus number of
parts) equal to `n + 1`. -/
theorem nonRascoeCount_eq_beckF (n : ℕ) : nonRascoeCount n = beckF n := by
  rw [beckF_eq_sum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have he := nonRascoeCount_add_card_filter n
  rcases n with _ | _ | n
  · rw [partsSet_zero] at he ⊢
    simpa [Finset.filter_singleton] using he
  · have hB := card_filter_card_mem 0
    have hA := card_filter_one_mem 0
    have hsplit := card_filter_one_mem_add 1
    simp only [show (0 : ℕ) + 1 = 1 from rfl] at he hB hA ⊢
    rw [partsSet_zero] at hB hA
    rw [Finset.card_singleton] at hA
    rw [filter_one_not_mem_partsSet_one] at hsplit ⊢
    simp only [Finset.card_empty, Finset.sum_empty, add_zero] at hsplit ⊢
    have hN0 : (({0} : Finset (Multiset ℕ)).filter (fun m => 1 ∉ m)).card = 1 := by
      simp [Finset.filter_singleton]
    omega
  · have hB := card_filter_card_mem (n + 1)
    have hA1 := card_filter_one_mem n
    have hA2 := card_filter_one_mem (n + 1)
    have hs1 := card_filter_one_mem_add (n + 1)
    have hs2 := card_filter_one_mem_add (n + 2)
    have hC := sum_card_toFinset_filter_one_not_mem n
    simp only [show n + 1 + 1 = n + 2 from rfl] at he hB hA2 hs1 ⊢
    omega

/-- The first equality of the paper's Theorem (Section 4), for `n ≥ 2`:
`e(n) = p(n) - p(n - 1) + p(n - 2)`, stated at `n + 2` and in `ℤ`. -/
theorem nonRascoeCount_add_two (n : ℕ) :
    (nonRascoeCount (n + 2) : ℤ) =
      (Fintype.card (n + 2).Partition : ℤ) - (Fintype.card (n + 1).Partition : ℤ) +
        (Fintype.card n.Partition : ℤ) := by
  have he := nonRascoeCount_add_card_filter (n + 2)
  have hB := card_filter_card_mem (n + 1)
  have hA1 := card_filter_one_mem n
  have hs1 := card_filter_one_mem_add (n + 1)
  simp only [show n + 1 + 1 = n + 2 from rfl] at hB
  rw [← card_partsSet, ← card_partsSet, ← card_partsSet]
  omega

/-- `f(n) = p(n) - p(n - 1) + p(n - 2)` for `n ≥ 2`, stated at `n + 2` and in `ℤ`. -/
theorem beckF_add_two (n : ℕ) :
    (beckF (n + 2) : ℤ) =
      (Fintype.card (n + 2).Partition : ℤ) - (Fintype.card (n + 1).Partition : ℤ) +
        (Fintype.card n.Partition : ℤ) := by
  rw [← nonRascoeCount_eq_beckF]
  exact nonRascoeCount_add_two n

/-- Non-vacuity check: `e(0) = f(0) = 1` (the empty partition of `0` is
non-Rascoe; `(2)` is the unique partition of `2` with rank `1`). -/
example : nonRascoeCount 0 = 1 ∧ beckF 0 = 1 := by
  have he := nonRascoeCount_add_card_filter 0
  rw [partsSet_zero] at he
  have he0 : nonRascoeCount 0 = 1 := by simpa [Finset.filter_singleton] using he
  exact ⟨he0, nonRascoeCount_eq_beckF 0 ▸ he0⟩

end BeckA229816
