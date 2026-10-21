/-
# A128440 — consecutive rows of `⌊k φ^m⌋` are disjoint, with Wythoff ranks

## Source

arXiv:2610.05776, Alex Ashburn, "On three conjectures of Kimberling concerning
the array ⌊kφ^n⌋".  Section 1 (Conjectures 1 and 2, recorded by Kimberling in
OEIS A128440, November 2022) and Section 3 (Corollary 4, the case `d = 1` of
Theorem 3; also Russo–Schwiebert, Fibonacci Quart. 2011, Theorem 2.2).
Recorded 2026-10-21.

Verbatim informal claims:

  Conjecture 1 (Kimberling). For every n ≥ 1, the rows R_{2n-1} and R_{2n}
  are disjoint.

  Conjecture 2 (Kimberling, stronger form). For every n ≥ 1, if the numbers in
  rows 2n-1 and 2n are arranged together in increasing order and each number
  is replaced by its position in this ordering, then the two resulting rows
  are rows 1 and 2.

  Corollary 4. For every m ≥ 1:
  (1) R_m ∩ R_{m+1} = ∅.
  (2) For all k, j ≥ 1, ⌊kφ^m⌋ < ⌊jφ^{m+1}⌋ if and only if ⌊kφ⌋ < ⌊jφ^2⌋.
  Consequently, when R_m ∪ R_{m+1} is listed in increasing order, the element
  ⌊kφ^m⌋ has position ⌊kφ⌋ and the element ⌊jφ^{m+1}⌋ has position ⌊jφ^2⌋.

Here `R_n = {⌊kφ^n⌋ : k ≥ 1}` and `φ = (1 + √5)/2`.

## Status

Proved in the paper (Corollary 4); the OEIS still lists the statements as
conjectures.  This module proves Corollary 4 in full for every consecutive
pair `(m, m+1)`, `m ≥ 1`, and Conjecture 1 as stated.  The proof of (1) is the
Russo–Schwiebert identity `F_{m+1} φ + F_m = φ^{m+1}` used directly: a common
value `N` would force the integer `k F_{m+1} + j F_m` to equal `N`, hence
`k φ^m = N`, contradicting irrationality.  Positions are counted with
`Set.ncard`.  Not formalized here: Theorem 3 (needs Skolem–Bang),
Proposition 6 and Theorem 8 (Conjecture 3, A358359).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A128440PhiRows

open Real goldenRatio

/-- Row `n` of Kimberling's array A128440: `R_n = {⌊k φ^n⌋ : k ≥ 1}`. -/
def kimbRow (n : ℕ) : Set ℤ := {N | ∃ k : ℕ, 0 < k ∧ ⌊(k : ℝ) * φ ^ n⌋ = N}

/-- Numerical enclosure `1.6 < φ < 1.65`, used for the ground-truth checks. -/
theorem goldenRatio_bounds : (1.6 : ℝ) < φ ∧ φ < 1.65 := by
  have h1 : (2.2 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < (2.3 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> rw [goldenRatio] <;> linarith

/-! ### Ground truth on small instances -/

/-- `T(1,1) = ⌊φ⌋ = 1` (A000201 starts `1, 3, 4, 6, …`). -/
example : (1 : ℤ) ∈ kimbRow 1 := by
  refine ⟨1, one_pos, ?_⟩
  obtain ⟨h1, h2⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith

/-- `T(1,2) = ⌊2φ⌋ = 3`. -/
example : (3 : ℤ) ∈ kimbRow 1 := by
  refine ⟨2, two_pos, ?_⟩
  obtain ⟨h1, h2⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff]; norm_num; constructor <;> linarith

/-- `T(2,1) = ⌊φ^2⌋ = 2` (A001950 starts `2, 5, 7, …`). -/
example : (2 : ℤ) ∈ kimbRow 2 := by
  refine ⟨1, one_pos, ?_⟩
  obtain ⟨h1, h2⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff, goldenRatio_sq]; norm_num; constructor <;> linarith

/-- The paper's example `13 = ⌊5φ^2⌋ = ⌊2φ^4⌋ ∈ R_2 ∩ R_4`: non-consecutive rows can meet,
so disjointness of consecutive rows is a genuine restriction. -/
example : (13 : ℤ) ∈ kimbRow 2 ∩ kimbRow 4 := by
  obtain ⟨h1, h2⟩ := goldenRatio_bounds
  have h4 : φ ^ 4 = 3 * φ + 2 := by
    have hsq := goldenRatio_sq
    calc φ ^ 4 = (φ ^ 2) ^ 2 := by ring
      _ = 3 * φ + 2 := by rw [hsq]; nlinarith [hsq]
  refine ⟨⟨5, by norm_num, ?_⟩, ⟨2, two_pos, ?_⟩⟩
  · rw [Int.floor_eq_iff, goldenRatio_sq]; norm_num; constructor <;> linarith
  · rw [Int.floor_eq_iff, h4]; norm_num; constructor <;> linarith

/-- For `k ≥ 1` and `m ≥ 1`, the number `k φ^m` is irrational. -/
theorem irrational_natCast_mul_goldenRatio_pow {k m : ℕ} (hk : 0 < k) (hm : 1 ≤ m) :
    Irrational ((k : ℝ) * φ ^ m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpow : φ ^ (n + 1) = φ * (Nat.fib (n + 1) : ℝ) + Nat.fib n :=
    (goldenRatio_mul_fib_succ_add_fib n).symm
  have hfib : Nat.fib (n + 1) ≠ 0 := (Nat.fib_pos.2 (Nat.succ_pos n)).ne'
  have h1 : Irrational (φ * (Nat.fib (n + 1) : ℝ)) :=
    goldenRatio_irrational.mul_natCast hfib
  have h2 : Irrational (φ * (Nat.fib (n + 1) : ℝ) + Nat.fib n) := h1.add_natCast _
  rw [hpow]
  exact h2.natCast_mul hk.ne'

/-- **Corollary 4(1) (Ashburn).** For `m ≥ 1`, consecutive rows `R_m` and `R_{m+1}` of
A128440 are disjoint. -/
theorem kimbRow_disjoint_succ {m : ℕ} (hm : 1 ≤ m) : Disjoint (kimbRow m) (kimbRow (m + 1)) := by
  rw [Set.disjoint_left]
  rintro N ⟨k, hk, hkN⟩ ⟨j, hj, hjN⟩
  set x : ℝ := (k : ℝ) * φ ^ m with hx
  set y : ℝ := (j : ℝ) * φ ^ (m + 1) with hy
  set a : ℝ := (Nat.fib (m + 1) : ℝ) with ha
  set b : ℝ := (Nat.fib m : ℝ) with hb
  set P : ℝ := φ ^ (m + 1) with hP
  have hab : φ * a + b = P := goldenRatio_mul_fib_succ_add_fib m
  have hPpos : 0 < P := pow_pos goldenRatio_pos _
  have hapos : 0 < a := by
    rw [ha]; exact_mod_cast Nat.fib_pos.2 (Nat.succ_pos m)
  have hbnn : 0 ≤ b := Nat.cast_nonneg _
  have hx1 : (N : ℝ) ≤ x := hkN ▸ Int.floor_le x
  have hx2 : x < N + 1 := hkN ▸ Int.lt_floor_add_one x
  have hy1 : (N : ℝ) ≤ y := hjN ▸ Int.floor_le y
  have hy2 : y < N + 1 := hjN ▸ Int.lt_floor_add_one y
  -- the integer `I = k F_{m+1} + j F_m` satisfies `I P = a φ x + b y`
  set I : ℤ := (k : ℤ) * Nat.fib (m + 1) + (j : ℤ) * Nat.fib m with hI
  have hIP : (I : ℝ) * P = φ * a * x + b * y := by
    rw [hI, hx, hy, hP, ha, hb]; push_cast; ring
  have hlow : (N : ℝ) * P ≤ (I : ℝ) * P := by
    rw [hIP, ← hab]; nlinarith [mul_pos goldenRatio_pos hapos]
  have hup : (I : ℝ) * P < ((N : ℝ) + 1) * P := by
    rw [hIP, ← hab]; nlinarith [mul_pos goldenRatio_pos hapos]
  have hNI : (N : ℝ) ≤ I := le_of_mul_le_mul_right hlow hPpos
  have hIN : (I : ℝ) < N + 1 := lt_of_mul_lt_mul_right hup hPpos.le
  have hIeq : I = N := by
    have h1 : N ≤ I := by exact_mod_cast hNI
    have h2 : I < N + 1 := by exact_mod_cast hIN
    omega
  have hxN : x = N := by
    have hsum : φ * a * (x - N) + b * (y - N) = 0 := by
      have := hIP
      rw [hIeq, ← hab] at this
      linarith
    have hpa : 0 < φ * a := mul_pos goldenRatio_pos hapos
    nlinarith [mul_nonneg hbnn (sub_nonneg.2 hy1), mul_nonneg hpa.le (sub_nonneg.2 hx1)]
  exact (irrational_natCast_mul_goldenRatio_pow hk hm).ne_int N hxN

/-- For `m ≥ 1` and `k, j ≥ 1`: `⌊k φ^m⌋ < ⌊j φ^(m+1)⌋ ↔ k < j φ`. -/
theorem floor_lt_floor_iff_lt {m : ℕ} (hm : 1 ≤ m) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    ⌊(k : ℝ) * φ ^ m⌋ < ⌊(j : ℝ) * φ ^ (m + 1)⌋ ↔ (k : ℝ) < j * φ := by
  have hpm : 0 < φ ^ m := pow_pos goldenRatio_pos m
  have hsplit : (j : ℝ) * φ ^ (m + 1) = (j * φ) * φ ^ m := by ring
  constructor
  · intro hlt
    by_contra hge'
    have hge : (j : ℝ) * φ ≤ k := not_lt.1 hge'
    have hle : (j : ℝ) * φ ^ (m + 1) ≤ k * φ ^ m := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_right hge hpm.le
    exact absurd (Int.floor_mono hle) (not_le.2 hlt)
  · intro hlt
    have hle : (k : ℝ) * φ ^ m ≤ j * φ ^ (m + 1) := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_right hlt.le hpm.le
    refine lt_of_le_of_ne (Int.floor_mono hle) fun heq => ?_
    have hmem1 : ⌊(k : ℝ) * φ ^ m⌋ ∈ kimbRow m := ⟨k, hk, rfl⟩
    have hmem2 : ⌊(k : ℝ) * φ ^ m⌋ ∈ kimbRow (m + 1) := ⟨j, hj, heq.symm⟩
    exact Set.disjoint_left.1 (kimbRow_disjoint_succ hm) hmem1 hmem2

/-- **Corollary 4(2), order part (Ashburn).** For `m ≥ 1` and `k, j ≥ 1`,
`⌊k φ^m⌋ < ⌊j φ^(m+1)⌋` if and only if `⌊k φ⌋ < ⌊j φ^2⌋`. -/
theorem floor_lt_floor_iff_wythoff {m : ℕ} (hm : 1 ≤ m) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    ⌊(k : ℝ) * φ ^ m⌋ < ⌊(j : ℝ) * φ ^ (m + 1)⌋ ↔ ⌊(k : ℝ) * φ⌋ < ⌊(j : ℝ) * φ ^ 2⌋ := by
  rw [floor_lt_floor_iff_lt hm hk hj]
  have h1 := floor_lt_floor_iff_lt (m := 1) le_rfl hk hj
  rw [pow_one] at h1
  exact h1.symm

/-- The position (`1`-based rank) of `N` in a set `S` of integers listed in increasing
order: the number of elements of `S` that are at most `N`. -/
noncomputable def mergePos (S : Set ℤ) (N : ℤ) : ℕ := {M ∈ S | M ≤ N}.ncard

/-- Ground truth for `mergePos`: in the increasing listing `1, 2, 5` the entry `5` is third. -/
example : mergePos {1, 2, 5} 5 = 3 := by
  have h : {M ∈ ({1, 2, 5} : Set ℤ) | M ≤ 5} = {1, 2, 5} := by
    ext M; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]; omega
  rw [mergePos, h, Set.ncard_insert_of_notMem (by norm_num), Set.ncard_pair (by norm_num)]

/-- Counting lemma: if `g` is strictly monotone and, for `j ≥ 1`, `g j ≤ x ↔ j ≤ J`, then the
values `g j` (`j ≥ 1`) that are at most `x` form the image of `[1, J]`, a finite set of
size `J`. -/
theorem setOf_le_eq_image {g : ℕ → ℤ} {J : ℕ} {x : ℤ} (h : ∀ j, 0 < j → (g j ≤ x ↔ j ≤ J)) :
    {M ∈ {N | ∃ j : ℕ, 0 < j ∧ g j = N} | M ≤ x} = g '' (Finset.Icc 1 J : Set ℕ) := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hle⟩
    exact ⟨j, ⟨hj, (h j hj).1 hle⟩, rfl⟩
  · rintro ⟨j, ⟨hj, hjJ⟩, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, (h j hj).2 hjJ⟩

/-- Cardinality form of `setOf_le_eq_image`. -/
theorem ncard_setOf_le {g : ℕ → ℤ} (hg : StrictMono g) {J : ℕ} {x : ℤ}
    (h : ∀ j, 0 < j → (g j ≤ x ↔ j ≤ J)) :
    {M ∈ {N | ∃ j : ℕ, 0 < j ∧ g j = N} | M ≤ x}.ncard = J := by
  rw [setOf_le_eq_image h, Set.ncard_image_of_injective _ hg.injective, Set.ncard_coe_finset,
    Nat.card_Icc]
  omega

/-- The row map `k ↦ ⌊k φ^n⌋` is strictly increasing. -/
theorem strictMono_floor_mul_goldenRatio_pow (n : ℕ) :
    StrictMono fun k : ℕ => ⌊(k : ℝ) * φ ^ n⌋ := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hone : (1 : ℝ) ≤ φ ^ n := one_le_pow₀ one_lt_goldenRatio.le
  have hle : (k : ℝ) * φ ^ n + 1 ≤ ((k + 1 : ℕ) : ℝ) * φ ^ n := by
    push_cast; nlinarith
  calc ⌊(k : ℝ) * φ ^ n⌋ < ⌊(k : ℝ) * φ ^ n⌋ + 1 := lt_add_one _
    _ = ⌊(k : ℝ) * φ ^ n + 1⌋ := (Int.floor_add_one _).symm
    _ ≤ ⌊((k + 1 : ℕ) : ℝ) * φ ^ n⌋ := Int.floor_mono hle

/-- **Corollary 4(2), rank of the lower row (Ashburn).** For `m ≥ 1` and `k ≥ 1`, when
`R_m ∪ R_{m+1}` is listed in increasing order, `⌊k φ^m⌋` sits at position `⌊k φ⌋`
(the `k`-th lower Wythoff number, row `1`). -/
theorem mergePos_lower {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : 0 < k) :
    (mergePos (kimbRow m ∪ kimbRow (m + 1)) ⌊(k : ℝ) * φ ^ m⌋ : ℤ) = ⌊(k : ℝ) * φ⌋ := by
  set x : ℤ := ⌊(k : ℝ) * φ ^ m⌋ with hx
  have hA : ∀ i : ℕ, 0 < i → (⌊(i : ℝ) * φ ^ m⌋ ≤ x ↔ i ≤ k) := fun i _ =>
    (strictMono_floor_mul_goldenRatio_pow m).le_iff_le
  have hB : ∀ j : ℕ, 0 < j → (⌊(j : ℝ) * φ ^ (m + 1)⌋ ≤ x ↔ j ≤ ⌊(k : ℝ) / φ⌋₊) := by
    intro j hj
    rw [← not_lt, floor_lt_floor_iff_lt hm hk hj, not_lt, Nat.le_floor_iff (by positivity),
      le_div_iff₀ goldenRatio_pos]
  have hunion : {M ∈ kimbRow m ∪ kimbRow (m + 1) | M ≤ x} =
      {M ∈ kimbRow m | M ≤ x} ∪ {M ∈ kimbRow (m + 1) | M ≤ x} := Set.sep_union
  have hdisj : Disjoint {M ∈ kimbRow m | M ≤ x} {M ∈ kimbRow (m + 1) | M ≤ x} :=
    (kimbRow_disjoint_succ hm).mono (Set.sep_subset _ _) (Set.sep_subset _ _)
  have hfinA : {M ∈ kimbRow m | M ≤ x}.Finite := by
    rw [kimbRow, setOf_le_eq_image hA]; exact Set.toFinite _
  have hfinB : {M ∈ kimbRow (m + 1) | M ≤ x}.Finite := by
    rw [kimbRow, setOf_le_eq_image hB]; exact Set.toFinite _
  have hcount : mergePos (kimbRow m ∪ kimbRow (m + 1)) x = k + ⌊(k : ℝ) / φ⌋₊ := by
    rw [mergePos, hunion, Set.ncard_union_eq hdisj hfinA hfinB, kimbRow, kimbRow,
      ncard_setOf_le (strictMono_floor_mul_goldenRatio_pow m) hA,
      ncard_setOf_le (strictMono_floor_mul_goldenRatio_pow (m + 1)) hB]
  have hphi : (k : ℝ) * φ = k + k / φ := by
    rw [div_eq_mul_inv, inv_goldenRatio, ← one_sub_goldenConj]
    ring
  rw [hcount, hphi, Int.floor_natCast_add, Nat.cast_add,
    Int.natCast_floor_eq_floor (by positivity)]

/-- **Corollary 4(2), rank of the upper row (Ashburn).** For `m ≥ 1` and `j ≥ 1`, when
`R_m ∪ R_{m+1}` is listed in increasing order, `⌊j φ^(m+1)⌋` sits at position `⌊j φ^2⌋`
(the `j`-th upper Wythoff number, row `2`). -/
theorem mergePos_upper {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : 0 < j) :
    (mergePos (kimbRow m ∪ kimbRow (m + 1)) ⌊(j : ℝ) * φ ^ (m + 1)⌋ : ℤ) = ⌊(j : ℝ) * φ ^ 2⌋ := by
  set x : ℤ := ⌊(j : ℝ) * φ ^ (m + 1)⌋ with hx
  have hirr : Irrational ((j : ℝ) * φ) := by
    simpa using irrational_natCast_mul_goldenRatio_pow (m := 1) hj le_rfl
  have hA : ∀ k : ℕ, 0 < k → (⌊(k : ℝ) * φ ^ m⌋ ≤ x ↔ k ≤ ⌊(j : ℝ) * φ⌋₊) := by
    intro k hk
    have hne : ⌊(k : ℝ) * φ ^ m⌋ ≠ x := fun heq =>
      Set.disjoint_left.1 (kimbRow_disjoint_succ hm) ⟨k, hk, rfl⟩ ⟨j, hj, heq.symm⟩
    have hkne : (k : ℝ) ≠ j * φ := fun heq => hirr.ne_nat k heq.symm
    rw [le_iff_lt_or_eq, or_iff_left hne, floor_lt_floor_iff_lt hm hk hj,
      Nat.le_floor_iff (by positivity), lt_iff_le_and_ne, and_iff_left hkne]
  have hB : ∀ i : ℕ, 0 < i → (⌊(i : ℝ) * φ ^ (m + 1)⌋ ≤ x ↔ i ≤ j) := fun i _ =>
    (strictMono_floor_mul_goldenRatio_pow (m + 1)).le_iff_le
  have hunion : {M ∈ kimbRow m ∪ kimbRow (m + 1) | M ≤ x} =
      {M ∈ kimbRow m | M ≤ x} ∪ {M ∈ kimbRow (m + 1) | M ≤ x} := Set.sep_union
  have hdisj : Disjoint {M ∈ kimbRow m | M ≤ x} {M ∈ kimbRow (m + 1) | M ≤ x} :=
    (kimbRow_disjoint_succ hm).mono (Set.sep_subset _ _) (Set.sep_subset _ _)
  have hfinA : {M ∈ kimbRow m | M ≤ x}.Finite := by
    rw [kimbRow, setOf_le_eq_image hA]; exact Set.toFinite _
  have hfinB : {M ∈ kimbRow (m + 1) | M ≤ x}.Finite := by
    rw [kimbRow, setOf_le_eq_image hB]; exact Set.toFinite _
  have hcount : mergePos (kimbRow m ∪ kimbRow (m + 1)) x = ⌊(j : ℝ) * φ⌋₊ + j := by
    rw [mergePos, hunion, Set.ncard_union_eq hdisj hfinA hfinB, kimbRow, kimbRow,
      ncard_setOf_le (strictMono_floor_mul_goldenRatio_pow m) hA,
      ncard_setOf_le (strictMono_floor_mul_goldenRatio_pow (m + 1)) hB]
  have hphi : (j : ℝ) * φ ^ 2 = j + j * φ := by
    rw [goldenRatio_sq]; ring
  rw [hcount, hphi, Int.floor_natCast_add, Nat.cast_add,
    Int.natCast_floor_eq_floor (by positivity), add_comm]

/-- **Kimberling's stronger conjecture (A128440), Corollary 4(2) (Ashburn).** For `m ≥ 1`,
replacing each entry of `R_m` by its position in the increasing listing of `R_m ∪ R_{m+1}`
yields row `1` (the lower Wythoff sequence). -/
theorem mergePos_image_kimbRow {m : ℕ} (hm : 1 ≤ m) :
    (fun N => (mergePos (kimbRow m ∪ kimbRow (m + 1)) N : ℤ)) '' kimbRow m = kimbRow 1 := by
  ext M
  constructor
  · rintro ⟨N, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by rw [pow_one]; exact (mergePos_lower hm hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, by rw [pow_one]; exact mergePos_lower hm hk⟩

/-- **Kimberling's stronger conjecture (A128440), Corollary 4(2) (Ashburn).** For `m ≥ 1`,
replacing each entry of `R_{m+1}` by its position in the increasing listing of
`R_m ∪ R_{m+1}` yields row `2` (the upper Wythoff sequence). -/
theorem mergePos_image_kimbRow_succ {m : ℕ} (hm : 1 ≤ m) :
    (fun N => (mergePos (kimbRow m ∪ kimbRow (m + 1)) N : ℤ)) '' kimbRow (m + 1) = kimbRow 2 := by
  ext M
  constructor
  · rintro ⟨N, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (mergePos_upper hm hj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, mergePos_upper hm hj⟩

/-- **Kimberling's conjecture (A128440), as stated: Conjecture 1.** For every `n ≥ 1`, the rows
`R_{2n-1}` and `R_{2n}` are disjoint. -/
theorem kimberling_conj_disjoint {n : ℕ} (hn : 1 ≤ n) :
    Disjoint (kimbRow (2 * n - 1)) (kimbRow (2 * n)) := by
  have h := kimbRow_disjoint_succ (m := 2 * n - 1) (by omega)
  rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h

end Candidates.A128440PhiRows
