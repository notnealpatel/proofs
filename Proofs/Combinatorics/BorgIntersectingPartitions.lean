/-
# Borg's t-intersecting partition conjecture fails at `(n, k, t) = (29, 8, 1)`

Yury Person and Thomas Schweser, *Intersecting integer partitions: star
bounds and counterexamples at every scale*, arXiv:2610.01747, Theorem 1.2
and the remark before Section 6, refute Borg's Conjecture 1.6 (2016).
The conjecture compares `t`-intersecting families of partitions of `n`
into `k` positive parts with the canonical star, for `1 ≤ t < k ≤ n`
except `(n,k) = (t+7,t+2)`; common parts are counted with multiplicity.

This file applies the remark's Hilton–Milner construction at `(29,8,1)`,
rather than the paper's `(31,8,1)`. The family
`H = {λ ∈ P_{29,8} : 1 ∈ λ, supp λ ∩ {2,3,4} ≠ ∅} ∪ {λ ∈ P_{29,8} : {2,3,4} ⊆ supp λ}`
is intersecting and has 439 members, exceeding the star's
`p(28,7) = 436` members.

## Method

Partitions of `n` into `k` parts with all parts `≥ m` are enumerated as
nondecreasing lists by `gen n k m`; `mem_gen` characterises its members
and `card_filter_partition_eq_length` transports a cardinality of a filter of
`Finset.univ : Finset (Nat.Partition n)` to the length of a filtered `gen`
list.  The three numbers 439, 436, 436 are then checked by `decide +kernel`
over 525 (resp. 436) lists; `Fintype (Nat.Partition 29)` (4565 elements) is
never enumerated.  The intersecting property of `H` is structural.
-/
import Mathlib

set_option autoImplicit false

namespace BorgIntersectingPartitions

/-! ## Definitions mirroring the source -/

/-- A family `F` of partitions of `n` is `t`-intersecting if every two members
(not necessarily distinct) have at least `t` common parts, counted with
multiplicity: `|λ ∩ μ| = ∑_a min(m_λ(a), m_μ(a)) ≥ t`.  Multiset intersection
`∩` takes the minimum of multiplicities. -/
def IsTIntersecting {n : ℕ} (t : ℕ) (F : Finset (Nat.Partition n)) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, t ≤ (p.parts ∩ q.parts).card

/-- `P_{n,k}`: the partitions of `n` into exactly `k` positive parts. -/
def partitionsWithParts (n k : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun p => p.parts.card = k

/-- The canonical `t`-star `T_{n,k,t} = {λ ∈ P_{n,k} : m_λ(1) ≥ t}`: the
partitions of `n` into `k` parts having at least `t` parts equal to `1`. -/
def canonicalStar (n k t : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun p => p.parts.card = k ∧ t ≤ p.parts.count 1

/-- Borg's Conjecture 1.6 (Borg 2016), as quoted in arXiv:2610.01747: for
`1 ≤ t < k ≤ n` with `(n, k) ≠ (t + 7, t + 2)`, every `t`-intersecting family
`F ⊆ P_{n,k}` has at most `p(n - t, k - t)` members, i.e. no more than the
canonical star.  The subtraction `n - t` is guarded by `t < k ≤ n`. -/
def BorgConjecture : Prop :=
  ∀ n k t : ℕ, 1 ≤ t → t < k → k ≤ n → (n, k) ≠ (t + 7, t + 2) →
    ∀ F : Finset (Nat.Partition n), (∀ p ∈ F, p.parts.card = k) →
      IsTIntersecting t F → F.card ≤ (partitionsWithParts (n - t) (k - t)).card

/-- The membership predicate of the Hilton–Milner-type family of the paper's
remark before Section 6: either `1` is a part and some part lies in
`{2, 3, 4}`, or each of `2, 3, 4` is a part. -/
def hmPred (s : Multiset ℕ) : Prop :=
  (1 ∈ s ∧ (2 ∈ s ∨ 3 ∈ s ∨ 4 ∈ s)) ∨ (2 ∈ s ∧ 3 ∈ s ∧ 4 ∈ s)

/-- `hmPred` is decidable: it is a Boolean combination of multiset memberships. -/
instance : DecidablePred hmPred := fun s => by unfold hmPred; infer_instance

/-- The family `H ⊆ P_{n,k}` of the paper's remark (there with
`(n,k) = (31,8)`): `{λ : 1 ∈ λ, supp λ ∩ {2,3,4} ≠ ∅} ∪ S_{{2,3,4}}(n,k)`. -/
def hmFamily (n k : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun p => p.parts.card = k ∧ hmPred p.parts

/-! ## Enumerating partitions with a fixed number of parts -/

/-- `gen n k m` lists the nondecreasing lists of length `k`, with all entries
`≥ m`, summing to `n`.  The first entry `a` ranges over `m ≤ a ≤ n / k`. -/
def gen : ℕ → ℕ → ℕ → List (List ℕ)
  | n, 0, _ => if n = 0 then [[]] else []
  | n, k + 1, m =>
      (List.range' m (n / (k + 1) + 1 - m)).flatMap fun a => (gen (n - a) k a).map (a :: ·)

example : gen 8 3 1 = [[1, 1, 6], [1, 2, 5], [1, 3, 4], [2, 2, 4], [2, 3, 3]] := by
  decide

example : gen 5 2 2 = [[2, 3]] := by decide

/-- If every entry of `l` is at least `a`, then `l.length * a ≤ l.sum`. -/
lemma length_mul_le_sum {a : ℕ} :
    ∀ l : List ℕ, (∀ x ∈ l, a ≤ x) → l.length * a ≤ l.sum
  | [], _ => by simp
  | x :: l, h => by
    have hx : a ≤ x := h x (by simp)
    have hl : l.length * a ≤ l.sum := length_mul_le_sum l fun y hy => h y (by simp [hy])
    simp only [List.length_cons, List.sum_cons]
    nlinarith

/-- Characterisation of `gen`: `l ∈ gen n k m` iff `l` is nondecreasing, has
all entries `≥ m`, has length `k` and sums to `n`. -/
lemma mem_gen : ∀ (k n m : ℕ) (l : List ℕ),
    l ∈ gen n k m ↔
      l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, m ≤ x) ∧ l.length = k ∧ l.sum = n := by
  intro k
  induction k with
  | zero =>
    intro n m l
    by_cases hn : n = 0
    · subst hn
      cases l with
      | nil => simp [gen]
      | cons x l => simp [gen]
    · cases l with
      | nil => simp [gen, hn, eq_comm]
      | cons x l => simp [gen, hn]
  | succ k ih =>
    intro n m l
    constructor
    · intro hl
      simp only [gen, List.mem_flatMap, List.mem_range', List.mem_map, one_mul] at hl
      obtain ⟨a, ⟨i, hi, rfl⟩, l', hl', rfl⟩ := hl
      obtain ⟨hsort, hge, hlen, hsum⟩ := (ih (n - (m + i)) (m + i) l').1 hl'
      have hdiv : n / (k + 1) ≤ n := Nat.div_le_self n (k + 1)
      refine ⟨List.pairwise_cons.2 ⟨hge, hsort⟩, ?_, by simp [hlen], ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact le_trans (by omega) (hge x hx)
      · simp only [List.sum_cons, hsum]
        omega
    · rintro ⟨hsort, hge, hlen, hsum⟩
      obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
        cases l with
        | nil => simp at hlen
        | cons a l' => exact ⟨a, l', rfl⟩
      obtain ⟨hal', hsort'⟩ := List.pairwise_cons.1 hsort
      have hma : m ≤ a := hge a (by simp)
      have hlen' : l'.length = k := by simpa using hlen
      have hsum' : a + l'.sum = n := by simpa using hsum
      have hbound : l'.length * a ≤ l'.sum := length_mul_le_sum l' hal'
      have hka : (k + 1) * a ≤ n := by
        rw [hlen'] at hbound
        nlinarith
      have hadiv : a ≤ n / (k + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).2 (by linarith)
      simp only [gen, List.mem_flatMap, List.mem_range', List.mem_map, one_mul]
      refine ⟨a, ⟨a - m, by omega, by omega⟩, l', ?_, rfl⟩
      exact (ih (n - a) a l').2 ⟨hsort', hal', hlen', by omega⟩

/-- `gen n k m` has no duplicates: distinct first entries give disjoint
blocks. -/
lemma nodup_gen : ∀ (k n m : ℕ), (gen n k m).Nodup := by
  intro k
  induction k with
  | zero =>
    intro n m
    by_cases hn : n = 0 <;> simp [gen, hn]
  | succ k ih =>
    intro n m
    simp only [gen]
    refine List.nodup_flatMap.2 ⟨fun a _ => (ih (n - a) a).map List.cons_injective, ?_⟩
    refine (List.nodup_range' (step := 1) (by norm_num)).imp ?_
    intro a b hab
    simp only [Function.onFun]
    intro x hxa hxb
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hxa
    obtain ⟨v, -, hv⟩ := List.mem_map.1 hxb
    exact hab (List.cons.inj hv).1.symm

/-- The sorted parts of a partition of `n` into `k` parts form a member of
`gen n k 1`. -/
lemma sort_mem_gen {n k : ℕ} (p : Nat.Partition n) (hk : p.parts.card = k) :
    p.parts.sort (· ≤ ·) ∈ gen n k 1 := by
  have hsort : ((p.parts.sort (· ≤ ·) : List ℕ) : Multiset ℕ) = p.parts :=
    Multiset.sort_eq p.parts (· ≤ ·)
  refine (mem_gen k n 1 _).2 ⟨Multiset.pairwise_sort p.parts (· ≤ ·), ?_, ?_, ?_⟩
  · intro x hx
    exact p.parts_pos ((Multiset.mem_sort (· ≤ ·)).1 hx)
  · rw [Multiset.length_sort, hk]
  · rw [← Multiset.sum_coe, hsort, p.parts_sum]

/-- Counting bridge: the number of partitions `p` of `n` with exactly `k` parts
whose multiset of parts satisfies `P` equals the number of lists in
`gen n k 1` whose underlying multiset satisfies `P`.  The bijection sends a
partition to its parts sorted in nondecreasing order. -/
lemma card_filter_partition_eq_length (n k : ℕ) (P : Multiset ℕ → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun p : Nat.Partition n => p.parts.card = k ∧ P p.parts).card =
      ((gen n k 1).filter fun l : List ℕ => decide (P (l : Multiset ℕ))).length := by
  rw [← List.toFinset_card_of_nodup ((nodup_gen k n 1).filter _)]
  refine Finset.card_bij (fun p _ => p.parts.sort (· ≤ ·)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hcard, hP⟩ := (Finset.mem_filter.1 hp).2
    have hsort : ((p.parts.sort (· ≤ ·) : List ℕ) : Multiset ℕ) = p.parts :=
      Multiset.sort_eq p.parts (· ≤ ·)
    simp only [List.mem_toFinset, List.mem_filter, hsort, decide_eq_true_eq]
    exact ⟨sort_mem_gen p hcard, hP⟩
  · intro p _ q _ hpq
    apply Nat.Partition.ext
    rw [← Multiset.sort_eq p.parts (· ≤ ·), ← Multiset.sort_eq q.parts (· ≤ ·)]
    exact congrArg _ hpq
  · intro l hl
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hl
    obtain ⟨hgen, hP⟩ := hl
    obtain ⟨hsort, hge, hlen, hsum⟩ := (mem_gen k n 1 l).1 hgen
    let p : Nat.Partition n :=
      { parts := (l : Multiset ℕ)
        parts_pos := fun {i} hi => hge i (Multiset.mem_coe.1 hi)
        parts_sum := by rw [Multiset.sum_coe, hsum] }
    refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, by simp [p, hlen], hP⟩, ?_⟩
    change (l : Multiset ℕ).sort (· ≤ ·) = l
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) hsort

/-- `P_{n,k}` written as a filter of the shape used by
`card_filter_partition_eq_length`. -/
lemma partitionsWithParts_eq_filter (n k : ℕ) :
    partitionsWithParts n k =
      Finset.univ.filter fun p : Nat.Partition n => p.parts.card = k ∧ True := by
  simp [partitionsWithParts]

/-! ## Examples on small instances from the paper -/

/-- `|P_{8,3}| = 5`: `611, 521, 431, 422, 332`. -/
example : (partitionsWithParts 8 3).card = 5 := by
  rw [partitionsWithParts_eq_filter]
  exact (card_filter_partition_eq_length 8 3 fun _ => True).trans (by decide)

/-- Borg's exceptional case `(n,k,t) = (8,3,1)`: the canonical star has
`p(7,2) = 3` members. -/
example : (canonicalStar 8 3 1).card = 3 :=
  (card_filter_partition_eq_length 8 3 fun s => 1 ≤ s.count 1).trans (by decide)

/-- Borg's exceptional example `{(1,2,5), (1,3,4), (2,2,4), (2,3,3)} ⊆ P_{8,3}`
(the partitions of `8` into `3` parts with at most one part equal to `1`) is
intersecting and has `4 > 3 = |T_{8,3,1}|` members; this is why the
conjecture excludes `(n, k) = (t + 7, t + 2)`. -/
example :
    IsTIntersecting 1
        (Finset.univ.filter fun p : Nat.Partition 8 => p.parts.card = 3 ∧ p.parts.count 1 ≤ 1) ∧
      (Finset.univ.filter fun p : Nat.Partition 8 =>
        p.parts.card = 3 ∧ p.parts.count 1 ≤ 1).card = 4 := by
  refine ⟨?_, (card_filter_partition_eq_length 8 3 fun s => s.count 1 ≤ 1).trans (by decide)⟩
  intro p hp q hq
  obtain ⟨hp3, hp1⟩ := (Finset.mem_filter.1 hp).2
  obtain ⟨hq3, hq1⟩ := (Finset.mem_filter.1 hq).2
  have hpg := sort_mem_gen p hp3
  have hqg := sort_mem_gen q hq3
  rw [← Multiset.sort_eq p.parts (· ≤ ·)] at hp1 ⊢
  rw [← Multiset.sort_eq q.parts (· ≤ ·)] at hq1 ⊢
  generalize p.parts.sort (· ≤ ·) = lp at hpg hp1 ⊢
  generalize q.parts.sort (· ≤ ·) = lq at hqg hq1 ⊢
  revert lp lq
  decide

/-- The paper's value `p(30, 7) = 618` (the star at `(31, 8, 1)`). -/
example : (partitionsWithParts 30 7).card = 618 := by
  rw [partitionsWithParts_eq_filter]
  exact (card_filter_partition_eq_length 30 7 fun _ => True).trans (by decide +kernel)

/-- The paper's remark before Section 6: the family `H` in `P_{31,8}` has
`626` members. -/
example : (hmFamily 31 8).card = 626 := by
  rw [hmFamily, card_filter_partition_eq_length]
  decide +kernel

/-! ## The counterexample at `(n, k, t) = (29, 8, 1)` -/

/-- The Hilton–Milner-type family `H` is intersecting (`t = 1`) for every
`n, k`: two members of the first branch share the part `1`, two members of
the second branch share `2`, and a member of each branch shares a part in
`{2, 3, 4}`. -/
theorem isTIntersecting_one_hmFamily (n k : ℕ) : IsTIntersecting 1 (hmFamily n k) := by
  intro p hp q hq
  have hp' : hmPred p.parts := (Finset.mem_filter.1 hp).2.2
  have hq' : hmPred q.parts := (Finset.mem_filter.1 hq).2.2
  suffices hcommon : ∃ a, a ∈ p.parts ∧ a ∈ q.parts by
    obtain ⟨a, hap, haq⟩ := hcommon
    exact Multiset.card_pos_iff_exists_mem.2 ⟨a, Multiset.mem_inter.2 ⟨hap, haq⟩⟩
  unfold hmPred at hp' hq'
  rcases hp' with ⟨hp1, hp2 | hp3 | hp4⟩ | ⟨hp2, hp3, hp4⟩ <;>
    rcases hq' with ⟨hq1, hq2 | hq3 | hq4⟩ | ⟨hq2, hq3, hq4⟩
  all_goals first
    | exact ⟨1, hp1, hq1⟩
    | exact ⟨2, hp2, hq2⟩
    | exact ⟨3, hp3, hq3⟩
    | exact ⟨4, hp4, hq4⟩

/-- `|H| = 439` for `H ⊆ P_{29,8}`. -/
theorem card_hmFamily_29_8 : (hmFamily 29 8).card = 439 := by
  rw [hmFamily, card_filter_partition_eq_length]
  decide +kernel

/-- The canonical star `T_{29,8,1}` has `436` members. -/
theorem card_canonicalStar_29_8_1 : (canonicalStar 29 8 1).card = 436 :=
  (card_filter_partition_eq_length 29 8 fun s => 1 ≤ s.count 1).trans (by decide +kernel)

/-- `p(28, 7) = 436`, the bound `p(n - t, k - t)` of Borg's conjecture at
`(n, k, t) = (29, 8, 1)`. -/
theorem card_partitionsWithParts_28_7 : (partitionsWithParts 28 7).card = 436 := by
  rw [partitionsWithParts_eq_filter]
  exact (card_filter_partition_eq_length 28 7 fun _ => True).trans (by decide +kernel)

/-- An intersecting family of partitions of `29` into `8` parts that is
strictly larger than the canonical star `T_{29,8,1}`: `439 > 436`. -/
theorem exists_intersecting_gt_canonicalStar :
    ∃ F : Finset (Nat.Partition 29), (∀ p ∈ F, p.parts.card = 8) ∧
      IsTIntersecting 1 F ∧ (canonicalStar 29 8 1).card < F.card := by
  refine ⟨hmFamily 29 8, fun p hp => (Finset.mem_filter.1 hp).2.1,
    isTIntersecting_one_hmFamily 29 8, ?_⟩
  rw [card_hmFamily_29_8, card_canonicalStar_29_8_1]
  norm_num

/-- **Borg's Conjecture 1.6 is false** (arXiv:2610.01747 disproves it; this is
an explicit instance at `(n, k, t) = (29, 8, 1)`, smaller than the paper's
stated `(31, 8, 1)`): the intersecting family `H ⊆ P_{29,8}` has `439`
members, exceeding `p(28, 7) = 436`. -/
theorem not_borgConjecture : ¬ BorgConjecture := by
  intro hBorg
  have hle := hBorg 29 8 1 le_rfl (by norm_num) (by norm_num) (by decide) (hmFamily 29 8)
    (fun p hp => (Finset.mem_filter.1 hp).2.1) (isTIntersecting_one_hmFamily 29 8)
  rw [card_hmFamily_29_8] at hle
  change 439 ≤ (partitionsWithParts 28 7).card at hle
  rw [card_partitionsWithParts_28_7] at hle
  norm_num at hle

end BorgIntersectingPartitions
