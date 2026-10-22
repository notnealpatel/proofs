/-
# A344611 — partitions of 2n with reverse-alternating sum ≥ 0 vs. A160786

OEIS A344611, Gus Wiseman (2021): the number of partitions of `2n` with
nonnegative reverse-alternating sum is at most A160786(n). Here
`A160786(n) = A027193(2n+1)` counts partitions of `2n+1` into an odd
number of parts, and the reverse-alternating sum of `(y₁,…,yₖ)` is
`Σᵢ (-1)^(k-i) yᵢ`.

## Proof

Sort the parts `y_1 ≥ ⋯ ≥ y_k`.  For even `k` the reverse-alternating sum is
`-((y_1 - y_2) + (y_3 - y_4) + ⋯) ≤ 0`, with equality only when the parts pair
up, i.e. the multiset of parts is `μ + μ`.  Map an odd-length partition of
`2n` to the partition of `2n+1` obtained by adding `1` to a largest part (its
largest part becomes unique), and a doubled partition `μ + μ` to `μ + μ + {1}`
(every part other than `1` occurs an even number of times).  Both maps land in
odd-length partitions of `2n+1`, are injective, and have disjoint images, since
the bumped largest part `≥ 2` occurs exactly once.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A344611PartitionsWhoseReverse

open Multiset

/-- The reverse-alternating sum of a list `y = (y_1, ..., y_k)`:
`∑_i (-1)^(k-i) y_i`, i.e. the alternating sum `y_k - y_{k-1} + y_{k-2} - ⋯`
of the reversed list. -/
def revAltSum (y : List ℕ) : ℤ :=
  (y.reverse.map (fun x : ℕ => (x : ℤ))).alternatingSum

/-- **A344611.** `a344611 n` is the number of integer partitions of `2n`
whose reverse-alternating sum (of the parts sorted in weakly decreasing order)
is `≥ 0`. -/
def a344611 (n : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun p : Nat.Partition (2 * n) => 0 ≤ revAltSum (p.parts.sort (· ≥ ·)))).card

/-- **A027193.** `a027193 m` is the number of partitions of `m` into an odd
number of parts. -/
def a027193 (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition m => Odd p.parts.card)).card

/-- **A160786.** `a160786 n = A027193(2n+1)`, the number of partitions of
`2n+1` into an odd number of parts. -/
def a160786 (n : ℕ) : ℕ := a027193 (2 * n + 1)

/-! ## Examples for `revAltSum` -/

/-- `(3,2,1)` has reverse-alternating sum `1 - 2 + 3 = 2`. -/
example : revAltSum [3, 2, 1] = 2 := by decide

/-- `(3,1)` has reverse-alternating sum `1 - 3 = -2`. -/
example : revAltSum [3, 1] = -2 := by decide

/-- `(2,2)` has reverse-alternating sum `0`. -/
example : revAltSum [2, 2] = 0 := by decide


/-! ## Count examples

`Finset.univ : Finset (Nat.Partition m)` does not reduce in the kernel, so the
first terms are checked against a verified computable enumeration
`boundedParts` of multisets with parts in `[1, k]` and given sum. -/

/-- `boundedParts k m` is the finset of multisets with all elements in `[1, k]`
summing to `m` (enumerated by the multiplicity of the part `k`). -/
def boundedParts : ℕ → ℕ → Finset (Multiset ℕ)
  | 0, m => if m = 0 then {0} else ∅
  | k + 1, m => (Finset.range (m / (k + 1) + 1)).biUnion
      (fun j => (boundedParts k (m - j * (k + 1))).image (fun s => s + replicate j (k + 1)))

/-- Membership in `boundedParts k m`: all elements lie in `[1, k]` and the sum
is `m`. -/
theorem mem_boundedParts : ∀ (k m : ℕ) (s : Multiset ℕ),
    s ∈ boundedParts k m ↔ (∀ x ∈ s, 0 < x ∧ x ≤ k) ∧ s.sum = m
  | 0, m, s => by
    simp only [boundedParts]
    constructor
    · intro h
      split_ifs at h with hm
      · rw [Finset.mem_singleton] at h
        subst h
        simp [hm]
      · simp at h
    · rintro ⟨h, hsum⟩
      have hs0 : s = 0 := Multiset.eq_zero_of_forall_notMem (fun x hx => by
        have := h x hx
        omega)
      subst hs0
      simp only [Multiset.sum_zero] at hsum
      subst hsum
      simp
  | k + 1, m, s => by
    simp only [boundedParts, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      mem_boundedParts k]
    constructor
    · rintro ⟨j, hj, t, ⟨ht, htsum⟩, rfl⟩
      have hjm : j * (k + 1) ≤ m :=
        (Nat.le_div_iff_mul_le (by omega)).mp (Nat.lt_succ_iff.mp hj)
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases Multiset.mem_add.mp hx with hx | hx
        · have := ht x hx
          omega
        · rw [Multiset.eq_of_mem_replicate hx]
          omega
      · rw [Multiset.sum_add, htsum, Multiset.sum_replicate, smul_eq_mul]
        omega
    · rintro ⟨h, hsum⟩
      have hs : s.filter (· ≠ k + 1) + replicate (count (k + 1) s) (k + 1) = s := by
        rw [← Multiset.filter_eq' s (k + 1)]
        conv_rhs => rw [← Multiset.filter_add_not (· ≠ k + 1) s]
        congr 1
        exact Multiset.filter_congr (fun x _ => not_not.symm)
      have hsum' : (s.filter (· ≠ k + 1)).sum + count (k + 1) s * (k + 1) = m := by
        rw [← hsum]
        conv_rhs => rw [← hs]
        rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      refine ⟨count (k + 1) s, ?_, s.filter (· ≠ k + 1), ⟨fun x hx => ?_, ?_⟩, hs⟩
      · exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
      · obtain ⟨hxs, hxne⟩ := Multiset.mem_filter.mp hx
        have := h x hxs
        omega
      · omega

/-- Counting partitions of `m` by a predicate on their parts equals counting
the multisets in `boundedParts m m` satisfying it. -/
theorem card_filter_eq_boundedParts (m : ℕ) (P : Multiset ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun p : Nat.Partition m => P p.parts)).card =
      ((boundedParts m m).filter P).card := by
  have himg : (Finset.univ : Finset (Nat.Partition m)).image Nat.Partition.parts =
      boundedParts m m := by
    ext s
    rw [Finset.mem_image, mem_boundedParts]
    constructor
    · rintro ⟨p, -, rfl⟩
      exact ⟨fun x hx => ⟨p.parts_pos hx, Nat.Partition.le_of_mem_parts hx⟩, p.parts_sum⟩
    · rintro ⟨h, hsum⟩
      exact ⟨⟨s, fun hx => (h _ hx).1, hsum⟩, Finset.mem_univ _, rfl⟩
  rw [← himg, Finset.filter_image,
    Finset.card_image_of_injective _ (fun p q h => Nat.Partition.ext h)]

/-- Weakly decreasing sort of a multiset via insertion sort (kernel-reducible). -/
def sortDesc (s : Multiset ℕ) : List ℕ :=
  Quot.liftOn s (fun l => l.insertionSort (· ≥ ·)) (fun l₁ l₂ h => by
    have h' := congrArg (fun u : Multiset ℕ => u.sort (· ≥ ·))
      (Multiset.coe_eq_coe.mpr h)
    rwa [Multiset.coe_sort, Multiset.coe_sort, List.mergeSort_eq_insertionSort,
      List.mergeSort_eq_insertionSort] at h')

/-- `sortDesc` agrees with Mathlib's `Multiset.sort (· ≥ ·)`. -/
theorem sortDesc_eq (s : Multiset ℕ) : sortDesc s = s.sort (· ≥ ·) :=
  Quot.inductionOn s (fun l => by
    show l.insertionSort (· ≥ ·) = (l : Multiset ℕ).sort (· ≥ ·)
    rw [Multiset.coe_sort, List.mergeSort_eq_insertionSort])

/-- `a344611 n` as a count over the computable enumeration. -/
theorem a344611_eq_card_boundedParts (n : ℕ) :
    a344611 n = ((boundedParts (2 * n) (2 * n)).filter
      (fun s => 0 ≤ revAltSum (sortDesc s))).card := by
  simp only [sortDesc_eq]
  unfold a344611
  exact card_filter_eq_boundedParts (2 * n) (fun s => 0 ≤ revAltSum (s.sort (· ≥ ·)))

/-- `a160786 n` as a count over the computable enumeration. -/
theorem a160786_eq_card_boundedParts (n : ℕ) :
    a160786 n = ((boundedParts (2 * n + 1) (2 * n + 1)).filter
      (fun s => Odd (card s))).card := by
  unfold a160786 a027193
  exact card_filter_eq_boundedParts (2 * n + 1) (fun s => Odd (card s))

/-- A344611 terms `a(0..4) = 1, 2, 4, 8, 15`. -/
example : a344611 0 = 1 ∧ a344611 1 = 2 ∧ a344611 2 = 4 ∧ a344611 3 = 8 ∧
    a344611 4 = 15 := by
  simp only [a344611_eq_card_boundedParts]
  decide +kernel

/-- A160786 terms `A160786(0..4) = 1, 2, 4, 8, 16`; the first strict
inequality `a(4) = 15 < 16` matches the listed differences `0, 0, 0, 0, 1`. -/
example : a160786 0 = 1 ∧ a160786 1 = 2 ∧ a160786 2 = 4 ∧ a160786 3 = 8 ∧
    a160786 4 = 16 := by
  simp only [a160786_eq_card_boundedParts]
  decide +kernel

/-! ## The even-length structure lemma -/

/-- For a weakly increasing list `L` of even length, the alternating sum
`L_1 - L_2 + L_3 - ⋯` is `≤ 0`, and if it is `≥ 0` then `L` (as a multiset)
is a doubled multiset `μ + μ`. -/
theorem altSum_even_sorted :
    ∀ (L : List ℕ), L.Pairwise (· ≤ ·) → Even L.length →
      (L.map (fun x : ℕ => (x : ℤ))).alternatingSum ≤ 0 ∧
      (0 ≤ (L.map (fun x : ℕ => (x : ℤ))).alternatingSum →
        ∃ μ : Multiset ℕ, (L : Multiset ℕ) = μ + μ)
  | [], _, _ => ⟨by simp, fun _ => ⟨0, by simp⟩⟩
  | [_], _, hev => absurd hev (by simp)
  | a :: b :: L, hsort, hev => by
    have hab : a ≤ b := List.rel_of_pairwise_cons hsort (by simp)
    have hL : L.Pairwise (· ≤ ·) := (List.pairwise_cons.mp
      (List.pairwise_cons.mp hsort).2).2
    have hevL : Even L.length := by
      simpa [List.length_cons, Nat.even_add_one] using hev
    obtain ⟨hle, hdbl⟩ := altSum_even_sorted L hL hevL
    have hsum : ((a :: b :: L).map (fun x : ℕ => (x : ℤ))).alternatingSum =
        (a : ℤ) - b + (L.map (fun x : ℕ => (x : ℤ))).alternatingSum := by
      rw [List.map_cons, List.map_cons, List.alternatingSum_cons_cons]
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    refine ⟨by rw [hsum]; linarith, fun h0 => ?_⟩
    rw [hsum] at h0
    have hba : (a : ℤ) = b := by linarith
    have hba' : a = b := by exact_mod_cast hba
    obtain ⟨μ, hμ⟩ := hdbl (by linarith)
    refine ⟨a ::ₘ μ, ?_⟩
    subst hba'
    rw [← Multiset.cons_coe, ← Multiset.cons_coe, hμ, Multiset.cons_add,
      Multiset.add_cons]

/-- A partition of even length whose reverse-alternating sum is `≥ 0` has
parts of the form `μ + μ`. -/
theorem exists_double_of_even_of_nonneg (s : Multiset ℕ) (hev : Even (card s))
    (h : 0 ≤ revAltSum (s.sort (· ≥ ·))) : ∃ μ : Multiset ℕ, s = μ + μ := by
  set L := (s.sort (· ≥ ·)).reverse with hLdef
  have hsort : L.Pairwise (· ≤ ·) :=
    List.pairwise_reverse.mpr (Multiset.pairwise_sort s (· ≥ ·))
  have hlen : L.length = card s := by
    rw [hLdef, List.length_reverse, Multiset.length_sort]
  have hcoe : (L : Multiset ℕ) = s := by
    rw [hLdef, Multiset.coe_reverse, Multiset.sort_eq]
  rw [← hlen] at hev
  obtain ⟨-, hdbl⟩ := altSum_even_sorted L hsort hev
  rw [← hcoe]
  exact hdbl h

/-! ## The bump map: increment the largest part -/

/-- The maximum of a nonempty multiset of naturals belongs to it. -/
theorem sup_mem_of_ne_zero : ∀ (s : Multiset ℕ), s ≠ 0 → s.sup ∈ s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    rw [Multiset.sup_cons]
    by_cases ht : t = 0
    · subst ht; simp
    · rcases le_total a t.sup with hle | hle
      · rw [sup_eq_right.mpr hle]; exact Multiset.mem_cons_of_mem (ih ht)
      · rw [sup_eq_left.mpr hle]; exact Multiset.mem_cons_self a t

/-- Replace the largest part `m` of `s` by `m + 1`. -/
def bump (s : Multiset ℕ) : Multiset ℕ := (s.sup + 1) ::ₘ s.erase s.sup

/-- Bumping a nonempty multiset raises its sum by one. -/
theorem sum_bump {s : Multiset ℕ} (hs : s ≠ 0) : (bump s).sum = s.sum + 1 := by
  rw [bump, Multiset.sum_cons, ← Multiset.sum_erase (sup_mem_of_ne_zero s hs)]
  ring

/-- Bumping a nonempty multiset preserves its cardinality. -/
theorem card_bump {s : Multiset ℕ} (hs : s ≠ 0) : card (bump s) = card s := by
  rw [bump, Multiset.card_cons, Multiset.card_erase_add_one (sup_mem_of_ne_zero s hs)]

/-- The new largest part `max s + 1` occurs exactly once in `bump s`. -/
theorem count_bump (s : Multiset ℕ) : count (s.sup + 1) (bump s) = 1 := by
  rw [bump, Multiset.count_cons_self, Multiset.count_eq_zero.mpr]
  intro hmem
  have := Multiset.le_sup (Multiset.mem_of_mem_erase hmem)
  omega

/-- `bump` is injective on nonempty multisets. -/
theorem bump_inj {s t : Multiset ℕ} (hs : s ≠ 0) (ht : t ≠ 0) (h : bump s = bump t) :
    s = t := by
  have key : ∀ {u v : Multiset ℕ}, bump u = bump v → u.sup ≤ v.sup := by
    intro u v huv
    have hmem : u.sup + 1 ∈ bump v := huv ▸ Multiset.mem_cons_self _ _
    rcases Multiset.mem_cons.mp hmem with heq | hmem'
    · omega
    · have := Multiset.le_sup (Multiset.mem_of_mem_erase hmem')
      omega
  have hsup : s.sup = t.sup := le_antisymm (key h) (key h.symm)
  have herase : s.erase s.sup = t.erase t.sup := by
    have h' := h
    rw [bump, bump, hsup] at h'
    rw [hsup]
    exact (Multiset.cons_inj_right _).mp h'
  rw [← Multiset.cons_erase (sup_mem_of_ne_zero s hs),
    ← Multiset.cons_erase (sup_mem_of_ne_zero t ht), herase, hsup]

/-- A bumped multiset of positive parts is never of the form `1 + μ + μ`. -/
theorem bump_ne_cons_one_double {s : Multiset ℕ} (hs : s ≠ 0) (hpos : ∀ x ∈ s, 0 < x)
    (μ : Multiset ℕ) : bump s ≠ 1 ::ₘ (μ + μ) := by
  intro h
  have hsup : 0 < s.sup := hpos _ (sup_mem_of_ne_zero s hs)
  have hc := count_bump s
  rw [h, Multiset.count_cons_of_ne (by omega), Multiset.count_add] at hc
  omega

/-! ## The injection -/

/-- Image of an odd-length partition of `m`: bump its largest part. -/
def bumpPartition {m : ℕ} (p : Nat.Partition m) (hp : p.parts ≠ 0) :
    Nat.Partition (m + 1) where
  parts := bump p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi'
    · omega
    · exact p.parts_pos (Multiset.mem_of_mem_erase hi')
  parts_sum := by rw [sum_bump hp, p.parts_sum]

/-- Image of an even-length partition of `m`: add a part `1`. -/
def consOnePartition {m : ℕ} (p : Nat.Partition m) : Nat.Partition (m + 1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi'
    · omega
    · exact p.parts_pos hi'
  parts_sum := by rw [Multiset.sum_cons, p.parts_sum]; ring

/-- The injection from partitions of `m` into partitions of `m + 1`: bump the
largest part of an odd-length partition, add a part `1` to an even-length one. -/
noncomputable def toOdd {m : ℕ} (p : Nat.Partition m) : Nat.Partition (m + 1) :=
  if hp : Odd (card p.parts) then
    bumpPartition p (by rintro h; rw [h] at hp; simp at hp)
  else consOnePartition p

/-- An odd-cardinality multiset is nonzero. -/
theorem ne_zero_of_odd_card {s : Multiset ℕ} (h : Odd (card s)) : s ≠ 0 := by
  rintro rfl; simp at h

/-- **Conjecture (A344611, Gus Wiseman, May 30 2021), proved here.**

For all `n ≥ 0`, the number of
integer partitions of `2n` whose reverse-alternating sum is `≥ 0` is at most
`A160786(n) = A027193(2n+1)`, the number of partitions of `2n+1` into an odd
number of parts. -/
theorem a344611_le_a160786 (n : ℕ) : a344611 n ≤ a160786 n := by
  unfold a344611 a160786 a027193
  refine Finset.card_le_card_of_injOn toOdd ?_ ?_
  · intro p _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    unfold toOdd
    split_ifs with hp
    · simpa [bumpPartition, card_bump (ne_zero_of_odd_card hp)] using hp
    · simp only [consOnePartition, Multiset.card_cons]
      exact (Nat.not_odd_iff_even.mp hp).add_one
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    have hparts := congrArg Nat.Partition.parts hpq
    unfold toOdd at hparts
    apply Nat.Partition.ext
    split_ifs at hparts with hpo hqo hqo
    · exact bump_inj (ne_zero_of_odd_card hpo) (ne_zero_of_odd_card hqo) hparts
    · obtain ⟨μ, hμ⟩ := exists_double_of_even_of_nonneg q.parts
        (Nat.not_odd_iff_even.mp hqo) hq
      exact absurd (hμ ▸ hparts) (bump_ne_cons_one_double (ne_zero_of_odd_card hpo)
        (fun x hx => p.parts_pos hx) μ)
    · obtain ⟨μ, hμ⟩ := exists_double_of_even_of_nonneg p.parts
        (Nat.not_odd_iff_even.mp hpo) hp
      exact absurd (hμ ▸ hparts.symm) (bump_ne_cons_one_double (ne_zero_of_odd_card hqo)
        (fun x hx => q.parts_pos hx) μ)
    · exact (Multiset.cons_inj_right 1).mp hparts

end Candidates.A344611PartitionsWhoseReverse
