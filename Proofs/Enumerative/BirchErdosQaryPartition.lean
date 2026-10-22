/-
# Birch–Erdős representations and q-ary partitions

Yuchen Ding, Honghu Liu and Zi Wang, *Note on a theorem of Birch–Erdős and
m-ary partitions*, arXiv:2503.11676, Section 1: Theorem 2, Corollaries 4, 6, 7
and Proposition 1.
For odd `q > 1`, the number `f_{2,q}(n)` of representations as a sum of distinct
`2^a q^b` equals the q-ary partition count. Both counts satisfy
`F(n)=Σ_{k≤n/q} F(k)`. This gives the successor recursion, monotonicity in `n`,
the block partial-sum identity and antitonicity in `q`.
The recurrence and the latter two identities include `n=0` (and block index 0),
extending the paper's positive-index statements. Asymptotic, density and
parity results and conjectures for bases `p>2` are outside this module.
-/
import Mathlib

set_option autoImplicit false

namespace BirchErdosQaryPartition

open Finset

/-- `x` is of the form `2^a q^b` for some `a, b ∈ ℕ`. -/
def IsTwoQ (q x : ℕ) : Prop := ∃ a b : ℕ, x = 2 ^ a * q ^ b

/-- Bounded form of `IsTwoQ`, used only to decide it. -/
lemma isTwoQ_iff_bdd (q x : ℕ) :
    IsTwoQ q x ↔ ∃ a < x + 1, ∃ b < x + 2, x = 2 ^ a * q ^ b := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · exact ⟨a, by simpa using (Nat.lt_two_pow_self (n := a)).le, 0, by simp, rfl⟩
      · exact ⟨0, by simp, 1, by simp [zero_pow hb.ne'], by simp [zero_pow hb.ne']⟩
    · rcases Nat.lt_or_ge q 2 with hq1 | hq2
      · obtain rfl : q = 1 := by omega
        exact ⟨a, by simpa using (Nat.lt_two_pow_self (n := a)).le, 0, by simp, by simp⟩
      · refine ⟨a, ?_, b, ?_, rfl⟩
        · have h1 : a < 2 ^ a := Nat.lt_two_pow_self
          have h2 : 1 ≤ q ^ b := Nat.one_le_pow _ _ hq
          nlinarith
        · have h1 : b < q ^ b := Nat.lt_pow_self hq2
          have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
          nlinarith
  · rintro ⟨a, -, b, -, h⟩
    exact ⟨a, b, h⟩

/-- `IsTwoQ q` is decidable via the bounded form `isTwoQ_iff_bdd`. -/
instance (q : ℕ) : DecidablePred (IsTwoQ q) := fun x =>
  decidable_of_iff _ (isTwoQ_iff_bdd q x).symm

/-- The finsets of numbers of the form `2^a q^b` (distinct terms) whose sum is `n`.
Every such term is `≤ n`, so the finsets range over subsets of `{0, …, n}`. -/
def f2qSet (q n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (n + 1)).powerset.filter (fun S => (∀ x ∈ S, IsTwoQ q x) ∧ ∑ x ∈ S, x = n)

/-- Membership in `f2qSet` without the ambient bound `S ⊆ {0, …, n}`. -/
lemma mem_f2qSet {q n : ℕ} {S : Finset ℕ} :
    S ∈ f2qSet q n ↔ (∀ x ∈ S, IsTwoQ q x) ∧ ∑ x ∈ S, x = n := by
  classical
  unfold f2qSet
  rw [mem_filter, mem_powerset, and_iff_right_iff_imp]
  rintro ⟨-, hsum⟩ x hx
  rw [mem_range, Nat.lt_succ_iff, ← hsum]
  exact single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx

/-- An odd `q > 1` divides no power of two. -/
lemma not_dvd_two_pow {q : ℕ} (hq : Odd q) (h1 : 1 < q) (a : ℕ) : ¬ q ∣ 2 ^ a := by
  intro h
  have hc : Nat.Coprime q (2 ^ a) := (Nat.coprime_two_right.mpr hq).pow_right a
  have : q = 1 := Nat.Coprime.eq_one_of_dvd hc h
  omega

/-- A term `2^a q^b` divisible by `q` is `q` times a term `2^a q^(b-1)`. -/
lemma isTwoQ_div {q x : ℕ} (hq : Odd q) (h1 : 1 < q) (hx : IsTwoQ q x) (hd : q ∣ x) :
    IsTwoQ q (x / q) ∧ q * (x / q) = x := by
  obtain ⟨a, b, rfl⟩ := hx
  refine ⟨?_, Nat.mul_div_cancel' hd⟩
  rcases b with _ | c
  · exact absurd (by simpa using hd) (not_dvd_two_pow hq h1 a)
  · refine ⟨a, c, ?_⟩
    rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by omega)]

/-- A term `2^a q^b` not divisible by `q` is a power of two. -/
lemma isTwoQ_pow_two_of_not_dvd {q x : ℕ} (hx : IsTwoQ q x) (hd : ¬ q ∣ x) :
    ∃ a, x = 2 ^ a := by
  obtain ⟨a, b, rfl⟩ := hx
  rcases b with _ | c
  · exact ⟨a, by simp⟩
  · exact absurd (Dvd.dvd.mul_left (dvd_pow_self q (Nat.succ_ne_zero c)) _) hd

/-- A finset of powers of two is the image of its set of exponents. -/
lemma pow_two_finset_eq_image {S : Finset ℕ} (hS : ∀ x ∈ S, ∃ a, x = 2 ^ a) :
    (S.image (Nat.log 2)).image (2 ^ ·) = S := by
  ext x
  simp only [mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hS y hy
    rwa [Nat.log_pow (by norm_num)]
  · intro hx
    obtain ⟨a, rfl⟩ := hS x hx
    exact ⟨2 ^ a, hx, by rw [Nat.log_pow (by norm_num)]⟩

/-- The sum of a finset of powers of two as a sum over exponents. -/
lemma sum_pow_two_finset {S : Finset ℕ} (hS : ∀ x ∈ S, ∃ a, x = 2 ^ a) :
    ∑ x ∈ S, x = ∑ a ∈ S.image (Nat.log 2), 2 ^ a := by
  conv_lhs => rw [← pow_two_finset_eq_image hS]
  rw [sum_image (fun a _ b _ h => Nat.pow_right_injective le_rfl h)]

/-- Uniqueness of binary expansion: a finset of powers of two is determined by its sum. -/
lemma pow_two_finset_eq_of_sum_eq {S T : Finset ℕ} (hS : ∀ x ∈ S, ∃ a, x = 2 ^ a)
    (hT : ∀ x ∈ T, ∃ a, x = 2 ^ a) (h : ∑ x ∈ S, x = ∑ x ∈ T, x) : S = T := by
  rw [sum_pow_two_finset hS, sum_pow_two_finset hT] at h
  have := Finset.geomSum_injective le_rfl h
  rw [← pow_two_finset_eq_image hS, ← pow_two_finset_eq_image hT, this]

/-- `f_{2,q}(n)`: the number of ways to write `n` as a sum of distinct terms
`2^a q^b` (`a, b ∈ ℕ`), the order of the terms being immaterial. -/
def f2q (q n : ℕ) : ℕ := (f2qSet q n).card

/-- The members of `f2qSet q n` sum to `n`. -/
lemma sum_eq_of_mem_f2qSet {q n : ℕ} {S : Finset ℕ} (h : S ∈ f2qSet q n) : ∑ x ∈ S, x = n :=
  (mem_f2qSet.mp h).2

/-- Bottom-level recursion: `f_{2,q}(n) = ∑_{k ≤ n/q} f_{2,q}(k)` for odd `q > 1`. -/
lemma f2q_rec {q : ℕ} (hq : Odd q) (h1 : 1 < q) (n : ℕ) :
    f2q q n = ∑ k ∈ range (n / q + 1), f2q q k := by
  classical
  have hq0 : 0 < q := by omega
  unfold f2q
  rw [← card_biUnion]
  swap
  · intro k _ k' _ hkk'
    refine Finset.disjoint_left.mpr fun S hS hS' => hkk' ?_
    rw [← sum_eq_of_mem_f2qSet hS, ← sum_eq_of_mem_f2qSet hS']
  -- the two auxiliary sums
  have hsumP : ∀ m : ℕ, ∑ x ∈ m.bitIndices.toFinset.image (2 ^ ·), x = m := by
    intro m
    rw [sum_image (fun a _ b _ h => Nat.pow_right_injective le_rfl h)]
    exact Finset.sum_toFinset_bitIndices_two_pow m
  have hP2 : ∀ m : ℕ, ∀ x ∈ m.bitIndices.toFinset.image (2 ^ ·), ∃ a, x = 2 ^ a := by
    intro m x hx
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    exact ⟨a, rfl⟩
  have hsumQ : ∀ T : Finset ℕ, ∑ x ∈ T.image (q * ·), x = q * ∑ y ∈ T, y := by
    intro T
    rw [sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq0 h), mul_sum]
  have hsumD : ∀ S : Finset ℕ, (∀ x ∈ S, q ∣ x) →
      q * ∑ y ∈ S.image (· / q), y = ∑ x ∈ S, x := by
    intro S hS
    rw [sum_image (fun a ha b hb h => (Nat.div_left_inj (hS a ha) (hS b hb)).mp h), mul_sum]
    exact sum_congr rfl fun x hx => Nat.mul_div_cancel' (hS x hx)
  apply card_nbij' (fun S => (S.filter (q ∣ ·)).image (· / q))
    (fun S' => (n - q * ∑ y ∈ S', y).bitIndices.toFinset.image (2 ^ ·) ∪ S'.image (q * ·))
  · intro S hS
    rw [mem_coe, mem_f2qSet] at hS
    obtain ⟨hS2q, hSsum⟩ := hS
    have hle : q * ∑ y ∈ (S.filter (q ∣ ·)).image (· / q), y ≤ n := by
      rw [hsumD _ (fun x hx => (mem_filter.mp hx).2), ← hSsum]
      exact sum_le_sum_of_subset (filter_subset _ _)
    rw [mem_coe, mem_biUnion]
    refine ⟨_, mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq0).mpr
      (by rw [mul_comm]; exact hle))), mem_f2qSet.mpr ⟨?_, rfl⟩⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hxS, hxq⟩ := mem_filter.mp hx
    exact (isTwoQ_div hq h1 (hS2q x hxS) hxq).1
  · intro S' hS'
    rw [mem_coe, mem_biUnion] at hS'
    obtain ⟨k, hk, hS'k⟩ := hS'
    rw [mem_f2qSet] at hS'k
    obtain ⟨hS'2q, hS'sum⟩ := hS'k
    have hkn : q * k ≤ n := by
      have := (Nat.le_div_iff_mul_le hq0).mp (Nat.lt_succ_iff.mp (mem_range.mp hk))
      rw [mul_comm]; exact this
    rw [mem_coe, mem_f2qSet]
    have hdisj : Disjoint ((n - q * ∑ y ∈ S', y).bitIndices.toFinset.image (2 ^ ·))
        (S'.image (q * ·)) := by
      refine Finset.disjoint_left.mpr fun x hx hx' => ?_
      obtain ⟨a, -, rfl⟩ := mem_image.mp hx
      obtain ⟨y, -, hy⟩ := mem_image.mp hx'
      exact not_dvd_two_pow hq h1 a ⟨y, hy.symm⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨a, -, rfl⟩ := mem_image.mp hx
        exact ⟨a, 0, by simp⟩
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        obtain ⟨a, b, rfl⟩ := hS'2q y hy
        exact ⟨a, b + 1, by ring⟩
    · rw [sum_union hdisj, hsumP, hsumQ, hS'sum]
      omega
  · intro S hS
    rw [mem_coe, mem_f2qSet] at hS
    obtain ⟨hS2q, hSsum⟩ := hS
    have hdvd : ∀ x ∈ S.filter (q ∣ ·), q ∣ x := fun x hx => (mem_filter.mp hx).2
    have himg : ((S.filter (q ∣ ·)).image (· / q)).image (q * ·) = S.filter (q ∣ ·) := by
      rw [image_image]
      ext x
      simp only [mem_image, Function.comp_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rwa [Nat.mul_div_cancel' (hdvd y hy)]
      · intro hx
        exact ⟨x, hx, Nat.mul_div_cancel' (hdvd x hx)⟩
    have hsplit := sum_filter_add_sum_filter_not S (q ∣ ·) (fun x => x)
    have hP : (n - q * ∑ y ∈ (S.filter (q ∣ ·)).image (· / q), y).bitIndices.toFinset.image
        (2 ^ ·) = S.filter (fun x => ¬ q ∣ x) := by
      apply pow_two_finset_eq_of_sum_eq (hP2 _)
      · intro x hx
        obtain ⟨hxS, hxq⟩ := mem_filter.mp hx
        exact isTwoQ_pow_two_of_not_dvd (hS2q x hxS) hxq
      · rw [hsumP, hsumD _ hdvd]
        omega
    simp only
    rw [himg, hP, union_comm]
    exact filter_union_filter_not_eq _ _
  · intro S' hS'
    rw [mem_coe, mem_biUnion] at hS'
    obtain ⟨k, -, -⟩ := hS'
    simp only
    rw [filter_union, filter_false_of_mem, filter_true_of_mem, empty_union, image_image]
    · ext y
      simp [Nat.mul_div_cancel_left _ hq0]
    · intro x hx
      obtain ⟨y, -, rfl⟩ := mem_image.mp hx
      exact dvd_mul_right q y
    · intro x hx
      obtain ⟨a, -, rfl⟩ := mem_image.mp hx
      exact not_dvd_two_pow hq h1 a

/-- `i` is a power `q^k` of `q`. -/
def IsQPow (q i : ℕ) : Prop := ∃ k : ℕ, i = q ^ k

/-- Bounded form of `IsQPow`, used only to decide it. -/
lemma isQPow_iff_bdd (q i : ℕ) : IsQPow q i ↔ ∃ k < i + 2, i = q ^ k := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨1, by simp [zero_pow hk.ne'], by simp [zero_pow hk.ne']⟩
      · exact ⟨0, by simp, by simp⟩
    · exact ⟨k, by have := Nat.lt_pow_self (n := k) hq; omega, rfl⟩
  · rintro ⟨k, -, h⟩
    exact ⟨k, h⟩

/-- `IsQPow q` is decidable via the bounded form `isQPow_iff_bdd`. -/
instance (q : ℕ) : DecidablePred (IsQPow q) := fun i =>
  decidable_of_iff _ (isQPow_iff_bdd q i).symm

/-- `b_q(n)`: the number of partitions of `n` into powers of `q`. -/
def qary (q n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, IsQPow q i)).card

/-- The multisets of parts of the partitions counted by `qary q n`. -/
def qarySet (q n : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, IsQPow q i)).map
    ⟨Nat.Partition.parts, fun _ _ h => Nat.Partition.ext h⟩

/-- `qary` counts `qarySet`. -/
lemma qary_eq_card_qarySet (q n : ℕ) : qary q n = (qarySet q n).card :=
  (card_map _).symm

/-- For `q > 0`, `qarySet q n` is the set of multisets of powers of `q` summing to `n`. -/
lemma mem_qarySet {q n : ℕ} (hq : 0 < q) {M : Multiset ℕ} :
    M ∈ qarySet q n ↔ (∀ i ∈ M, IsQPow q i) ∧ M.sum = n := by
  unfold qarySet
  rw [mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(mem_filter.mp hp).2, p.parts_sum⟩
  · rintro ⟨hM, hsum⟩
    refine ⟨⟨M, fun {i} hi => ?_, hsum⟩, mem_filter.mpr ⟨mem_univ _, hM⟩, rfl⟩
    obtain ⟨k, rfl⟩ := hM i hi
    exact Nat.pow_pos (n := k) hq

/-- The members of `qarySet q n` sum to `n`. -/
lemma sum_eq_of_mem_qarySet {q n : ℕ} (hq : 0 < q) {M : Multiset ℕ} (h : M ∈ qarySet q n) :
    M.sum = n :=
  ((mem_qarySet hq).mp h).2

/-- A power of `q > 1` other than `1` is `q` times a power of `q`. -/
lemma isQPow_div {q x : ℕ} (h1 : 1 < q) (hx : IsQPow q x) (hne : ¬ x = 1) :
    q ∣ x ∧ IsQPow q (x / q) := by
  obtain ⟨k, rfl⟩ := hx
  rcases k with _ | k
  · exact absurd (pow_zero q) hne
  · refine ⟨dvd_pow_self q (Nat.succ_ne_zero k), k, ?_⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by omega)]

/-- Bottom-level recursion: `b_q(n) = ∑_{k ≤ n/q} b_q(k)` for `q > 1`. -/
lemma qary_rec {q : ℕ} (h1 : 1 < q) (n : ℕ) :
    (qarySet q n).card = ∑ k ∈ range (n / q + 1), (qarySet q k).card := by
  classical
  have hq0 : 0 < q := by omega
  rw [← card_biUnion]
  swap
  · intro k _ k' _ hkk'
    refine Finset.disjoint_left.mpr fun M hM hM' => hkk' ?_
    rw [← sum_eq_of_mem_qarySet hq0 hM, ← sum_eq_of_mem_qarySet hq0 hM']
  have hsumQ : ∀ M : Multiset ℕ, (M.map (q * ·)).sum = q * M.sum := by
    intro M
    rw [Multiset.sum_map_mul_left, Multiset.map_id']
  have hsumD : ∀ M : Multiset ℕ, (∀ x ∈ M, q ∣ x) → q * (M.map (· / q)).sum = M.sum := by
    intro M hM
    rw [← Multiset.sum_map_mul_left]
    congr 1
    conv_rhs => rw [← Multiset.map_id M]
    exact Multiset.map_congr rfl fun x hx => Nat.mul_div_cancel' (hM x hx)
  have hsplit : ∀ M : Multiset ℕ, M.count 1 + (M.filter (fun x => ¬ x = 1)).sum = M.sum := by
    intro M
    conv_rhs => rw [← Multiset.filter_add_not (fun x => x = 1) M]
    rw [Multiset.sum_add, Multiset.filter_eq' M 1, Multiset.sum_replicate, smul_eq_mul, mul_one]
  apply card_nbij' (fun M => (M.filter (fun x => ¬ x = 1)).map (· / q))
    (fun M' => Multiset.replicate (n - q * M'.sum) 1 + M'.map (q * ·))
  · intro M hM
    rw [mem_coe, mem_qarySet hq0] at hM
    obtain ⟨hMq, hMsum⟩ := hM
    have hdvd : ∀ x ∈ M.filter (fun x => ¬ x = 1), q ∣ x := fun x hx =>
      (isQPow_div h1 (hMq x (Multiset.mem_of_mem_filter hx)) (Multiset.mem_filter.mp hx).2).1
    have hle : q * ((M.filter (fun x => ¬ x = 1)).map (· / q)).sum ≤ n := by
      rw [hsumD _ hdvd, ← hMsum, ← hsplit M]
      exact Nat.le_add_left _ _
    rw [mem_coe, mem_biUnion]
    refine ⟨_, mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq0).mpr
      (by rw [mul_comm]; exact hle))), (mem_qarySet hq0).mpr ⟨?_, rfl⟩⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    exact (isQPow_div h1 (hMq x (Multiset.mem_of_mem_filter hx)) (Multiset.mem_filter.mp hx).2).2
  · intro M' hM'
    rw [mem_coe, mem_biUnion] at hM'
    obtain ⟨k, hk, hM'k⟩ := hM'
    rw [mem_qarySet hq0] at hM'k
    obtain ⟨hM'q, hM'sum⟩ := hM'k
    have hkn : q * k ≤ n := by
      have := (Nat.le_div_iff_mul_le hq0).mp (Nat.lt_succ_iff.mp (mem_range.mp hk))
      rw [mul_comm]; exact this
    rw [mem_coe, mem_qarySet hq0]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]
        exact ⟨0, (pow_zero q).symm⟩
      · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        obtain ⟨b, rfl⟩ := hM'q y hy
        exact ⟨b + 1, by ring⟩
    · rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one, hsumQ, hM'sum]
      omega
  · intro M hM
    rw [mem_coe, mem_qarySet hq0] at hM
    obtain ⟨hMq, hMsum⟩ := hM
    have hdvd : ∀ x ∈ M.filter (fun x => ¬ x = 1), q ∣ x := fun x hx =>
      (isQPow_div h1 (hMq x (Multiset.mem_of_mem_filter hx)) (Multiset.mem_filter.mp hx).2).1
    have himg : ((M.filter (fun x => ¬ x = 1)).map (· / q)).map (q * ·) =
        M.filter (fun x => ¬ x = 1) := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id (M.filter (fun x => ¬ x = 1))]
      exact Multiset.map_congr rfl fun x hx => Nat.mul_div_cancel' (hdvd x hx)
    have hcount : n - q * ((M.filter (fun x => ¬ x = 1)).map (· / q)).sum = M.count 1 := by
      rw [hsumD _ hdvd, ← hMsum, ← hsplit M]
      omega
    simp only
    rw [himg, hcount, ← Multiset.filter_eq' M 1]
    exact Multiset.filter_add_not (fun x => x = 1) M
  · intro M' hM'
    rw [mem_coe, mem_biUnion] at hM'
    obtain ⟨k, -, hM'k⟩ := hM'
    rw [mem_qarySet hq0] at hM'k
    obtain ⟨hM'q, -⟩ := hM'k
    simp only
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr, Multiset.filter_eq_self.mpr,
      zero_add, Multiset.map_map]
    · conv_rhs => rw [← Multiset.map_id M']
      exact Multiset.map_congr rfl fun y _ => Nat.mul_div_cancel_left y hq0
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨b, rfl⟩ := hM'q y hy
      have : 1 < q * q ^ b := by
        calc 1 < q := h1
          _ ≤ q * q ^ b := Nat.le_mul_of_pos_right q (Nat.pow_pos (n := b) hq0)
      omega
    · intro x hx
      rw [Multiset.eq_of_mem_replicate hx]
      exact not_not.mpr rfl

/-- Two functions with the same value at `0` satisfying the recursion
`F(n) = ∑_{k ≤ n/q} F(k)` agree, for `q > 1`. -/
lemma eq_of_rec {q : ℕ} (h1 : 1 < q) {F G : ℕ → ℕ} (h0 : F 0 = G 0)
    (hF : ∀ n, F n = ∑ k ∈ range (n / q + 1), F k)
    (hG : ∀ n, G n = ∑ k ∈ range (n / q + 1), G k) : F = G := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    · rw [hF n, hG n]
      refine sum_congr rfl fun k hk => ih k ?_
      have hk' := mem_range.mp hk
      have hdiv := Nat.div_lt_self hn h1
      omega

/-- `f_{2,q}(0) = 1` (the empty sum) for `q > 0`. -/
lemma f2q_zero {q : ℕ} (hq : 0 < q) : f2q q 0 = 1 := by
  unfold f2q
  rw [card_eq_one]
  refine ⟨∅, Finset.ext fun S => ?_⟩
  rw [mem_f2qSet, mem_singleton]
  constructor
  · rintro ⟨hS, hsum⟩
    rw [sum_eq_zero_iff] at hsum
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨a, b, hab⟩ := hS x hx
    have hpos : 0 < 2 ^ a * q ^ b := Nat.mul_pos (Nat.two_pow_pos a) (Nat.pow_pos hq)
    rw [← hab, hsum x hx] at hpos
    exact lt_irrefl 0 hpos
  · rintro rfl
    simp

/-- `b_q(0) = 1` (the empty partition) for `q > 0`. -/
lemma qary_zero {q : ℕ} (hq : 0 < q) : qary q 0 = 1 := by
  rw [qary_eq_card_qarySet, card_eq_one]
  refine ⟨0, Finset.ext fun M => ?_⟩
  rw [mem_qarySet hq, mem_singleton]
  constructor
  · rintro ⟨hM, hsum⟩
    rw [Multiset.sum_eq_zero_iff] at hsum
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    obtain ⟨k, hk⟩ := hM x hx
    have hpos : 0 < q ^ k := Nat.pow_pos hq
    rw [← hk, hsum x hx] at hpos
    exact lt_irrefl 0 hpos
  · rintro rfl
    simp

/-- **Proposition 1** (arXiv:2503.11676, Section 1).  For odd `q > 1` and every `n`,
`f_{2,q}(n) = b_q(n)`: the number of representations of `n` as a sum of distinct
numbers `2^a q^b` equals the number of partitions of `n` into powers of `q`. -/
theorem f2q_eq_qary {q : ℕ} (hq : Odd q) (h1 : 1 < q) (n : ℕ) : f2q q n = qary q n := by
  have hq0 : 0 < q := by omega
  have hfun : f2q q = fun m => (qarySet q m).card :=
    eq_of_rec h1 (by rw [f2q_zero hq0, ← qary_eq_card_qarySet, qary_zero hq0])
      (f2q_rec hq h1) (qary_rec h1)
  rw [hfun, qary_eq_card_qarySet]

/-- **Theorem 2** (arXiv:2503.11676, Section 1).  For odd `q > 1` and every `n`
(the paper states `n ≥ 1`; the identity also holds at `n = 0`),
`f_{2,q}(n+1) = f_{2,q}(n) + [q ∣ n+1] · f_{2,q}((n+1)/q)`. -/
theorem f2q_succ {q : ℕ} (hq : Odd q) (h1 : 1 < q) (n : ℕ) :
    f2q q (n + 1) = f2q q n + if q ∣ n + 1 then f2q q ((n + 1) / q) else 0 := by
  have hrec := f2q_rec hq h1 (n + 1)
  rw [f2q_rec hq h1 n]
  split_ifs with h
  · rw [hrec, Nat.succ_div_of_dvd h, sum_range_succ]
  · rw [hrec, Nat.succ_div_of_not_dvd h, add_zero]

/-- **Corollary 4** (arXiv:2503.11676, Section 1).  For odd `q > 1`, `f_{2,q}` is
nondecreasing: `f_{2,q}(n) ≤ f_{2,q}(n+1)` for every `n`. -/
theorem f2q_monotone {q : ℕ} (hq : Odd q) (h1 : 1 < q) : Monotone (f2q q) :=
  monotone_nat_of_le_succ fun n => by
    rw [f2q_succ hq h1 n]
    exact Nat.le_add_right _ _

/-- **Corollary 6** (arXiv:2503.11676, Section 1).  For odd `q > 1`, if `n = qm + r`
with `r < q`, then `f_{2,q}(n) = 1 + f_{2,q}(1) + ⋯ + f_{2,q}(m)` (the paper assumes
`m ≥ 1`; the identity also holds for `m = 0`). -/
theorem f2q_mul_add {q : ℕ} (hq : Odd q) (h1 : 1 < q) (m r : ℕ) (hr : r < q) :
    f2q q (q * m + r) = 1 + ∑ k ∈ Icc 1 m, f2q q k := by
  have hq0 : 0 < q := by omega
  have hdiv : (q * m + r) / q = m := by
    rw [Nat.mul_add_div hq0, Nat.div_eq_of_lt hr, add_zero]
  rw [f2q_rec hq h1, hdiv, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos m),
    f2q_zero hq0, zero_add]
  have hIco : Ico 1 m.succ = Icc 1 m := by
    ext k
    rw [mem_Ico, mem_Icc]
    omega
  rw [hIco]

/-- **Corollary 7** (arXiv:2503.11676, Section 1).  For odd `1 < q₁ < q₂` and every `n`,
`f_{2,q₂}(n) ≤ f_{2,q₁}(n)`. -/
theorem f2q_anti {q₁ q₂ : ℕ} (hq₁ : Odd q₁) (hq₂ : Odd q₂) (h1 : 1 < q₁) (h12 : q₁ < q₂)
    (n : ℕ) : f2q q₂ n ≤ f2q q₁ n := by
  have h2 : 1 < q₂ := h1.trans h12
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [f2q_zero (by omega), f2q_zero (by omega)]
    · rw [f2q_rec hq₁ h1 n, f2q_rec hq₂ h2 n]
      calc ∑ k ∈ range (n / q₂ + 1), f2q q₂ k
          ≤ ∑ k ∈ range (n / q₂ + 1), f2q q₁ k := by
            refine sum_le_sum fun k hk => ih k ?_
            have hk' := mem_range.mp hk
            have hdiv := Nat.div_lt_self hn h2
            omega
        _ ≤ ∑ k ∈ range (n / q₁ + 1), f2q q₁ k := by
            refine sum_le_sum_of_subset (range_subset_range.mpr ?_)
            have := Nat.div_le_div_left h12.le (by omega : 0 < q₁) (a := n)
            omega

/-! ## Examples

`f_{2,3}` against OEIS A062051 (`1,1,1,2,2,2,3,3,3,5,…` from `n = 0`). -/

example : IsTwoQ 3 12 := ⟨2, 1, rfl⟩
example : ¬ IsTwoQ 3 5 := by decide
example : IsQPow 3 27 := ⟨3, rfl⟩
example : ¬ IsQPow 3 6 := by decide
example : f2q 3 4 = 2 := by decide
example : f2q 3 7 = 3 := by decide
set_option maxRecDepth 100000 in
example : f2q 3 9 = 5 := by decide
example : f2q 5 6 = 2 := by decide
/-- `b_3(9) = 5`: `9`, `3+3+3`, `3+3+1+1+1`, `3+1·6`, `1·9`
(read off through Proposition 1, since `Nat.Partition`'s enumeration does not
reduce in the kernel). -/
example : qary 3 9 = 5 := by
  rw [← f2q_eq_qary (by decide) (by decide)]
  set_option maxRecDepth 100000 in decide

/-- Non-vacuity of the hypotheses: `q = 3` satisfies `Odd q ∧ 1 < q`. -/
example : Odd 3 ∧ 1 < 3 := ⟨by decide, by decide⟩

end BirchErdosQaryPartition
