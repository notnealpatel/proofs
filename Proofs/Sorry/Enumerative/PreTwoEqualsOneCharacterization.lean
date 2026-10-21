/-
# `pre_2(n) = 1` exactly for `n ∈ {1, 2, 4}`

## Source

arXiv:2604.17424, Aman Devnani and Pramod Eyyunni, "Elementary symmetric
polynomials and a potentially injective family of maps on partitions".

Definitions (Introduction, after equation (1.1)): following Ballantine, Beck
and Merca, for `λ = (λ_1, …, λ_ℓ)` the partition `pre_k(λ)` has the multiset of
parts `{λ_{i_1} ⋯ λ_{i_k} | 1 ≤ i_1 < ⋯ < i_k ≤ ℓ}` if `ℓ ≥ k`, and is the
empty partition if `ℓ < k`.  Before Theorem 1.6 (`pre2nsize`): "Let `Pre_2(n)`
be the set of partitions of `n` which are in the image of `pre_2`. Set
`pre_2(n) := |Pre_2(n)|`. ... we have that `pre_2(n) ≥ 1` for all `n ≥ 1`."

Verbatim question (Concluding Remarks, Problem 3):

  "In the course of the proof of Case 1 of Theorem \ref{pre2nsize}, we saw
   that if `n+1` is a prime, then `pre_2(n) ≥ 1`. We thus ask
   Does there exist an `n ≥ 1` such that `pre_2(n) = 1`?"

## Claim formalized here

For `n ≥ 1`, `pre_2(n) = 1` iff `n ∈ {1, 2, 4}`.  Equivalently, `n` is the
second elementary symmetric function `e_2` of a multiset of at least three
positive integers iff `n ∉ {0, 1, 2, 4}`.  In particular the answer to
Problem 3 is "yes", and exactly three such `n` exist.

## Status

Open in the paper (posed as Problem 3; no answer given).  The characterization
and its proof below are new elementary arguments (date: 2026-10-21):

* a length-2 partition `(a, b)` maps to the single-part partition `(ab)`, and
  `(n) = pre_2(n, 1)` is always in the image;
* a partition with `ℓ ≥ 3` parts maps to a partition with `choose ℓ 2 ≥ 3`
  parts; such a partition of `n` exists iff `n ∉ {0, 1, 2, 4}`:
  writing `2n = j k` with `2 ≤ j < k` of opposite parity gives
  `e_2(a, 1^j) = n` for `a = (k - j + 1)/2`, which covers every `n` that is not
  a power of two; `e_2(2, 2, 2^{e-2} - 1) = 2^e` covers `e ≥ 3`; and
  `e_2 ∈ {1, 2, 4}` is impossible for three or more positive parts.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.PreTwoEqualsOneCharacterization

/-! ## Definitions -/

/-- `pre2 s` is the multiset of all products `s_i s_j` over the two-element
sub-multisets of `s` (indices `i < j`): the parts of the partition `pre_2(λ)` of
Ballantine–Beck–Merca when `s` is the multiset of parts of `λ`.  For fewer than
two parts it is the empty multiset, matching the empty partition. -/
def pre2 (s : Multiset ℕ) : Multiset ℕ :=
  (s.powersetCard 2).map Multiset.prod

/-- `Pre2Set n` is the set `Pre_2(n)` of partitions `μ` of `n` lying in the
image of `pre_2`, i.e. `μ = pre_2(λ)` for some partition `λ` of some `m`. -/
def Pre2Set (n : ℕ) : Set (Nat.Partition n) :=
  {μ | ∃ m : ℕ, ∃ l : Nat.Partition m, pre2 l.parts = μ.parts}

/-- `pre2Count n = pre_2(n) = |Pre_2(n)|`, the number of partitions of `n` in
the image of `pre_2`. -/
noncomputable def pre2Count (n : ℕ) : ℕ :=
  (Pre2Set n).ncard

/-! ## Ground truth -/

/-- The paper's example: `pre_2(7, 4, 4) = (28, 28, 16)`. -/
example : pre2 {7, 4, 4} = {28, 28, 16} := by decide

/-- The paper's example `14 + 7 + 2 = pre_2(7 + 2 + 1)`. -/
example : pre2 {7, 2, 1} = {14, 7, 2} := by decide

/-- A single part maps to the empty partition. -/
example : pre2 {5} = 0 := by decide

/-! ## Basic lemmas on `pre2` -/

/-- `e_2` is the sum of the parts of `pre_2`. -/
theorem sum_pre2 (s : Multiset ℕ) : (pre2 s).sum = s.esymm 2 := rfl

/-- Recursion: `pre_2(a :: s) = pre_2(s) + a · s`. -/
theorem pre2_cons (a : ℕ) (s : Multiset ℕ) :
    pre2 (a ::ₘ s) = pre2 s + s.map (a * ·) := by
  unfold pre2
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.map_map]
  congr 1
  rw [Multiset.powersetCard_one, Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => by simp

/-- `pre_2(λ)` has `choose ℓ 2` parts. -/
theorem card_pre2 (s : Multiset ℕ) :
    Multiset.card (pre2 s) = (Multiset.card s).choose 2 := by
  simp [pre2]

/-- Products of positive parts are positive. -/
theorem pos_of_mem_pre2 {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) :
    ∀ y ∈ pre2 s, 0 < y := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  have hts : t ≤ s := (Multiset.mem_powersetCard.mp ht).1
  exact Multiset.prod_pos fun x hx => hs x (Multiset.mem_of_le hts hx)

/-- For positive parts, `choose ℓ 2 ≤ e_2`, since each of the `choose ℓ 2`
products is at least `1`. -/
theorem choose_card_le_sum_pre2 {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) :
    (Multiset.card s).choose 2 ≤ (pre2 s).sum := by
  rw [← card_pre2]
  simpa using Multiset.card_nsmul_le_sum (s := pre2 s) (a := 1)
    (fun y hy => pos_of_mem_pre2 hs y hy)

/-- `pre_2` of a two-element multiset is the single product. -/
theorem pre2_pair (a b : ℕ) : pre2 {a, b} = {a * b} := by
  rw [Multiset.insert_eq_cons, pre2_cons]
  simp [pre2]

/-- `2 · choose j 2 + j = j²`. -/
theorem two_mul_choose_two_add (j : ℕ) : 2 * j.choose 2 + j = j * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    linarith

/-- `e_2(a, 1^j) = a j + choose j 2`. -/
theorem sum_pre2_cons_replicate (a j : ℕ) :
    (pre2 (a ::ₘ Multiset.replicate j 1)).sum = a * j + j.choose 2 := by
  induction j with
  | zero => simp [pre2]
  | succ j ih =>
    rw [Multiset.replicate_succ, Multiset.cons_swap, pre2_cons, Multiset.sum_add, ih]
    simp only [one_mul, Multiset.map_cons, Multiset.map_replicate, Multiset.sum_cons,
      Multiset.sum_replicate, smul_eq_mul, mul_one, Nat.choose_succ_succ, Nat.choose_one_right,
      Nat.succ_eq_add_one, Nat.reduceAdd]
    ring

/-! ## Representability by three or more positive parts -/

/-- `n` is `e_2` of a multiset of at least three positive integers. -/
def E2Rep (n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ x ∈ s, 0 < x) ∧ 3 ≤ Multiset.card s ∧ s.esymm 2 = n

/-- If `2n = j k` with `2 ≤ j < k` and `j + k` odd, then `n = e_2(a, 1^j)` with
`a = (k - j + 1)/2`. -/
theorem e2Rep_of_two_mul_eq {n j k : ℕ} (hj : 2 ≤ j) (hjk : j < k) (hodd : Odd (j + k))
    (hn : 2 * n = j * k) : E2Rep n := by
  obtain ⟨c, hc⟩ : Odd (k - j) := by
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r - j, by omega⟩
  have hk : k = j + 2 * c + 1 := by omega
  refine ⟨(c + 1) ::ₘ Multiset.replicate j 1, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · omega
    · rw [Multiset.eq_of_mem_replicate hx]; omega
  · simp only [Multiset.card_cons, Multiset.card_replicate]
    omega
  · rw [← sum_pre2, sum_pre2_cons_replicate]
    have hch := two_mul_choose_two_add j
    subst hk
    nlinarith

/-- `2^e = e_2(2, 2, 2^{e-2} - 1)` for `e ≥ 3`. -/
theorem e2Rep_two_pow (f : ℕ) : E2Rep (2 ^ (f + 3)) := by
  have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
  refine ⟨{2, 2, 2 * 2 ^ f - 1}, ?_, by simp, ?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    omega
  · rw [← sum_pre2, Multiset.insert_eq_cons, Multiset.insert_eq_cons, pre2_cons, pre2_cons]
    simp only [pre2, Multiset.card_singleton, Order.lt_two_iff, Std.le_refl,
      Multiset.powersetCard_eq_empty, Multiset.map_zero, Multiset.map_singleton, Multiset.zero_add,
      Multiset.map_cons, Nat.reduceMul, Multiset.add_cons, Multiset.singleton_add, Multiset.sum_cons,
      Multiset.sum_singleton, pow_succ]
    omega

/-- Every `n ∉ {0, 1, 2, 4}` is `e_2` of at least three positive integers. -/
theorem e2Rep_of_not_mem {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    E2Rep n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h0
  obtain ⟨r, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- `n = 2^e`
    have he : 3 ≤ e := by
      by_contra hlt
      interval_cases e <;> simp_all
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
    simpa using e2Rep_two_pow f
  · have hpe : 0 < 2 ^ e := pow_pos (by norm_num) e
    have hn : 2 * (2 ^ e * (2 * r + 1)) = (2 * 2 ^ e) * (2 * r + 1) := by ring
    rcases lt_or_gt_of_ne (show 2 * 2 ^ e ≠ 2 * r + 1 by omega) with hlt | hgt
    · exact e2Rep_of_two_mul_eq (by omega) hlt ⟨2 ^ e + r, by ring⟩ hn
    · exact e2Rep_of_two_mul_eq (by omega) hgt ⟨2 ^ e + r, by ring⟩ (by rw [hn, mul_comm])

/-- Three or more positive parts never give `e_2 ∈ {1, 2, 4}`. -/
theorem not_e2Rep {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 4) : ¬ E2Rep n := by
  rintro ⟨s, hs, hcard, hsum⟩
  rw [← sum_pre2] at hsum
  have hle := choose_card_le_sum_pre2 hs
  rcases Nat.lt_or_ge (Multiset.card s) 4 with h3 | h4
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp (show Multiset.card s = 3 by omega)
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hc := hs c (by simp)
    rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, pre2_cons, pre2_cons] at hsum
    simp only [pre2, Multiset.card_singleton, Order.lt_two_iff, Std.le_refl,
      Multiset.powersetCard_eq_empty, Multiset.map_zero, Multiset.map_singleton, Multiset.zero_add,
      Multiset.map_cons, Multiset.add_cons, Multiset.singleton_add, Multiset.sum_cons,
      Multiset.sum_singleton] at hsum
    have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hac : 1 ≤ a * c := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hbc : 1 ≤ b * c := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hn4 : n ≤ 4 := by omega
    have ha4 : a ≤ 4 := (Nat.le_mul_of_pos_right a hb).trans (by omega)
    have hb4 : b ≤ 4 := (Nat.le_mul_of_pos_right b hc).trans (by omega)
    have hc4 : c ≤ 4 := (Nat.le_mul_of_pos_left c ha).trans (by omega)
    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
  · have h6 : 6 ≤ (Multiset.card s).choose 2 :=
      (Nat.choose_le_choose 2 h4).trans' (by decide)
    omega

/-- **Representability.** `n` is `e_2` of a multiset of at least three positive
integers iff `n ∉ {0, 1, 2, 4}`. -/
theorem e2Rep_iff (n : ℕ) : E2Rep n ↔ n ∉ ({0, 1, 2, 4} : Finset ℕ) := by
  constructor
  · rintro hrep hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | hmem
    · obtain ⟨s, hs, hcard, hsum⟩ := hrep
      rw [← sum_pre2] at hsum
      have hle := choose_card_le_sum_pre2 hs
      have h3 : 3 ≤ (Multiset.card s).choose 2 :=
        (Nat.choose_le_choose 2 hcard).trans' (by decide)
      omega
    · exact not_e2Rep hmem hrep
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact e2Rep_of_not_mem h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ## The partition count `pre_2(n)` -/

/-- For `n ≠ 0` the single-part partition `(n)` has parts `{n}`. -/
theorem indiscrete_parts {n : ℕ} (hn : n ≠ 0) : (Nat.Partition.indiscrete n).parts = {n} := by
  simp [Nat.Partition.indiscrete, Nat.Partition.ofSums, hn]

/-- The single-part partition `(n) = pre_2(n, 1)` lies in `Pre_2(n)` for `n ≥ 1`. -/
theorem indiscrete_mem_pre2Set {n : ℕ} (hn : 0 < n) :
    Nat.Partition.indiscrete n ∈ Pre2Set n := by
  refine ⟨n + 1, ⟨{n, 1}, ?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
    omega
  · simp
  · rw [pre2_pair, mul_one, indiscrete_parts hn.ne']

/-- A multiset of at least three positive integers with `e_2 = n` yields a
partition in `Pre_2(n)` other than `(n)`. -/
theorem exists_ne_indiscrete_of_e2Rep {n : ℕ} (hrep : E2Rep n) :
    ∃ μ ∈ Pre2Set n, μ ≠ Nat.Partition.indiscrete n := by
  obtain ⟨s, hs, hcard, hsum⟩ := hrep
  let μ : Nat.Partition n := ⟨pre2 s, fun hy => pos_of_mem_pre2 hs _ hy, hsum⟩
  refine ⟨μ, ⟨s.sum, ⟨s, fun hx => hs _ hx, rfl⟩, rfl⟩, ?_⟩
  intro hμ
  have hn : n ≠ 0 := by
    rintro rfl
    have hle := choose_card_le_sum_pre2 hs
    have h3 : 3 ≤ (Multiset.card s).choose 2 :=
      (Nat.choose_le_choose 2 hcard).trans' (by decide)
    rw [sum_pre2] at hle
    omega
  have hparts : pre2 s = {n} := by
    rw [← indiscrete_parts hn, ← hμ]
  have hc := congrArg Multiset.card hparts
  rw [card_pre2, Multiset.card_singleton] at hc
  have h3 : 3 ≤ (Multiset.card s).choose 2 :=
    (Nat.choose_le_choose 2 hcard).trans' (by decide)
  omega

/-- For `n ∈ {1, 2, 4}` every partition in `Pre_2(n)` is `(n)`. -/
theorem eq_indiscrete_of_mem_pre2Set {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 4)
    {μ : Nat.Partition n} (hμ : μ ∈ Pre2Set n) : μ = Nat.Partition.indiscrete n := by
  obtain ⟨m, l, hl⟩ := hμ
  have hsum : (pre2 l.parts).sum = n := by rw [hl, μ.parts_sum]
  have hpos : ∀ x ∈ l.parts, 0 < x := fun x hx => l.parts_pos hx
  rcases lt_trichotomy (Multiset.card l.parts) 2 with hlt | h2 | hgt
  · have hzero : pre2 l.parts = 0 := by
      rw [← Multiset.card_eq_zero, card_pre2]
      exact Nat.choose_eq_zero_of_lt hlt
    rw [hzero, Multiset.sum_zero] at hsum
    omega
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp h2
    rw [hab, pre2_pair] at hl hsum
    rw [Multiset.sum_singleton] at hsum
    have hn0 : n ≠ 0 := by omega
    ext1
    rw [indiscrete_parts hn0, ← hl, hsum]
  · exact absurd ⟨l.parts, hpos, hgt, by rw [← sum_pre2, hsum]⟩ (not_e2Rep hn)

/-- **Characterization (answer to Problem 3 of arXiv:2604.17424).** For
`n ≥ 1`, `pre_2(n) = 1`, i.e. the only partition of `n` in the image of `pre_2`
is `(n)`, iff `n ∈ {1, 2, 4}`. -/
theorem pre2Count_eq_one_iff {n : ℕ} (hn : 0 < n) :
    pre2Count n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 4 := by
  constructor
  · intro h
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨μ, hμ, hne'⟩ :=
      exists_ne_indiscrete_of_e2Rep (e2Rep_of_not_mem hn.ne' hne.1 hne.2.1 hne.2.2)
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
    have h1 : μ = a := by
      rw [ha] at hμ
      exact hμ
    have h2 : Nat.Partition.indiscrete n = a := by
      have hmem := indiscrete_mem_pre2Set hn
      rw [ha] at hmem
      exact hmem
    exact hne' (h1.trans h2.symm)
  · intro h
    rw [pre2Count, Set.ncard_eq_one]
    exact ⟨Nat.Partition.indiscrete n, Set.eq_singleton_iff_unique_mem.mpr
      ⟨indiscrete_mem_pre2Set hn, fun μ hμ => eq_indiscrete_of_mem_pre2Set h hμ⟩⟩

/-- **Problem 3 of arXiv:2604.17424, answered.** There exists `n ≥ 1` with
`pre_2(n) = 1`; for instance `n = 4`. -/
theorem exists_pre2Count_eq_one : ∃ n : ℕ, 1 ≤ n ∧ pre2Count n = 1 :=
  ⟨4, by norm_num, (pre2Count_eq_one_iff (by norm_num)).mpr (by norm_num)⟩

/-- Non-vacuity check of the converse direction: `pre_2(3) ≠ 1`
(`pre_2(1, 1, 1) = (1, 1, 1)` is a second partition of `3` in the image). -/
example : pre2Count 3 ≠ 1 := by
  rw [Ne, pre2Count_eq_one_iff (by norm_num)]
  omega

end Candidates.PreTwoEqualsOneCharacterization
