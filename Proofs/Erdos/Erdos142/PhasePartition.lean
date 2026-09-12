/-
  Erdős Problem #142 — finite phase partitions.

  Residue classes modulo a positive step are split into consecutive index
  blocks.  A final remainder shorter than `K` is merged into the preceding
  block, so every cell has between `K` and `2*K-1` points.  The resulting
  cells are pairwise disjoint, cover `range N`, and have an explicit affine
  parameterization of common difference `d`.

  The analytic endpoint is only an oscillation lemma: any function whose
  step-`d` variation is at most `δ` varies by at most `2*K*δ` on a cell.
  A complex multiplicative-character specialization is included.  Selecting
  a useful `d` with small phase still requires a separate simultaneous
  Diophantine approximation theorem; no correlation or density increment is
  asserted here.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-- The length of the `j`th block when a final short remainder is merged into
its preceding block. -/
def mergedBlockLength (L K j : ℕ) : ℕ :=
  if j + 1 < L / K then K else L - j * K

/-- The `j`th block of indices in `range L`, with the final short remainder
merged into its preceding block. -/
def mergedBlock (L K j : ℕ) : Finset ℕ :=
  (Finset.range (mergedBlockLength L K j)).image fun i => j * K + i

example : mergedBlockLength 11 3 2 = 5 := by decide
example : mergedBlock 11 3 2 = {6, 7, 8, 9, 10} := by decide

/-- Membership in a merged block is membership in its half-open index interval. -/
theorem mem_mergedBlock_iff {L K j i : ℕ} :
    i ∈ mergedBlock L K j ↔
      j * K ≤ i ∧ i < j * K + mergedBlockLength L K j := by
  rw [mergedBlock, mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [mem_range] at ha
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨i - j * K, mem_range.mpr ?_, ?_⟩
    · omega
    · omega

/-- Every active merged block has length between `K` and `2*K-1`. -/
theorem mergedBlockLength_bounds {L K j : ℕ} (hK : 0 < K) (hKL : K ≤ L)
    (hj : j < L / K) :
    K ≤ mergedBlockLength L K j ∧ mergedBlockLength L K j < 2 * K := by
  let q := L / K
  have hq : 0 < q := Nat.div_pos hKL hK
  have hqK : q * K ≤ L := Nat.div_mul_le_self L K
  have hL : L < (q + 1) * K := (Nat.div_lt_iff_lt_mul hK).mp (by omega)
  unfold mergedBlockLength
  split_ifs with hlast
  · omega
  · have hjlast : j + 1 = q := by omega
    have hjmul : j * K + K = q * K := by
      rw [← hjlast, add_mul, one_mul]
    have hlow : K ≤ L - j * K := Nat.le_sub_of_add_le (by omega)
    have hjmul_le : j * K ≤ L := by omega
    have hupp : L - j * K < 2 * K := by
      rw [Nat.sub_lt_iff_lt_add hjmul_le]
      calc
        L < (q + 1) * K := hL
        _ = 2 * K + j * K := by rw [← hjlast]; ring
    exact ⟨hlow, hupp⟩

/-- Every active merged block lies in `range L`. -/
theorem mergedBlock_subset_range {L K j : ℕ} (hK : 0 < K) (hKL : K ≤ L)
    (_hj : j < L / K) : mergedBlock L K j ⊆ Finset.range L := by
  intro i hi
  rw [mem_mergedBlock_iff] at hi
  rw [mem_range]
  let q := L / K
  have hq : 0 < q := Nat.div_pos hKL hK
  have hqK : q * K ≤ L := Nat.div_mul_le_self L K
  unfold mergedBlockLength at hi
  split_ifs at hi with hlast
  · have hjq : j + 1 ≤ q := by omega
    have hend : j * K + K ≤ L := by
      calc
        j * K + K = (j + 1) * K := by ring
        _ ≤ q * K := Nat.mul_le_mul_right K hjq
        _ ≤ L := hqK
    omega
  · omega

/-- The cardinality of a merged block is its declared length. -/
theorem card_mergedBlock (L K j : ℕ) :
    (mergedBlock L K j).card = mergedBlockLength L K j := by
  rw [mergedBlock]
  calc
    ((Finset.range (mergedBlockLength L K j)).image fun i => j * K + i).card =
        (Finset.range (mergedBlockLength L K j)).card :=
      card_image_of_injective _ (by
        intro a b hab
        change j * K + a = j * K + b at hab
        omega)
    _ = mergedBlockLength L K j := card_range _

/-- Every index below `L` belongs to an active merged block. -/
theorem exists_mem_mergedBlock {L K i : ℕ} (hK : 0 < K) (hKL : K ≤ L)
    (hi : i < L) :
    ∃ j < L / K, i ∈ mergedBlock L K j := by
  let q := L / K
  have hq : 0 < q := Nat.div_pos hKL hK
  by_cases hbefore : i < (q - 1) * K
  · let j := i / K
    have hj : j < q - 1 := (Nat.div_lt_iff_lt_mul hK).mpr hbefore
    refine ⟨j, by omega, ?_⟩
    rw [mem_mergedBlock_iff]
    have hlo : j * K ≤ i := Nat.div_mul_le_self i K
    have hhi : i < (j + 1) * K := (Nat.div_lt_iff_lt_mul hK).mp (by omega)
    have hnonlast : j + 1 < q := by omega
    have hlen : mergedBlockLength L K j = K := by
      rw [mergedBlockLength, if_pos (by simpa only [q] using hnonlast)]
    rw [hlen]
    exact ⟨hlo, by simpa only [add_mul, one_mul] using hhi⟩
  · let j := q - 1
    refine ⟨j, by omega, ?_⟩
    rw [mem_mergedBlock_iff]
    have hjlast : j + 1 = q := by dsimp only [j]; omega
    have hlo : j * K ≤ i := by
      dsimp only [j]
      omega
    have hnot : ¬j + 1 < q := by omega
    have hlen : mergedBlockLength L K j = L - j * K := by
      rw [mergedBlockLength, if_neg (by simpa only [q] using hnot)]
    rw [hlen]
    exact ⟨hlo, by omega⟩

/-- Distinct active merged blocks are disjoint. -/
theorem disjoint_mergedBlock {L K j k : ℕ}
    (hj : j < L / K) (hk : k < L / K) (hjk : j ≠ k) :
    Disjoint (mergedBlock L K j) (mergedBlock L K k) := by
  rw [Finset.disjoint_left]
  intro i hij hik
  rw [mem_mergedBlock_iff] at hij hik
  let q := L / K
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hjnonlast : j + 1 < q := by omega
    have hlen : mergedBlockLength L K j = K := by
      rw [mergedBlockLength, if_pos (by simpa only [q] using hjnonlast)]
    rw [hlen] at hij
    have hend : j * K + K ≤ k * K := by
      calc
        j * K + K = (j + 1) * K := by ring
        _ ≤ k * K := Nat.mul_le_mul_right K (by omega)
    omega
  · have hknonlast : k + 1 < q := by omega
    have hlen : mergedBlockLength L K k = K := by
      rw [mergedBlockLength, if_pos (by simpa only [q] using hknonlast)]
    rw [hlen] at hik
    have hend : k * K + K ≤ j * K := by
      calc
        k * K + K = (k + 1) * K := by ring
        _ ≤ j * K := Nat.mul_le_mul_right K (by omega)
    omega

/-- Number of terms of the residue class `r mod d` lying in `range N`. -/
def residueLength (N d r : ℕ) : ℕ :=
  (N - 1 - r) / d + 1

example : residueLength 11 2 0 = 6 := by decide
example : residueLength 11 2 1 = 5 := by decide

/-- The residue-class length exactly controls when `r+d*i` lies below `N`. -/
theorem lt_residueLength_iff {N d r i : ℕ} (hd : 0 < d) (hr : r < N) :
    i < residueLength N d r ↔ r + d * i < N := by
  rw [residueLength]
  constructor
  · intro hi
    have hile : i ≤ (N - 1 - r) / d := by omega
    have hmul : i * d ≤ N - 1 - r := (Nat.le_div_iff_mul_le hd).mp hile
    have htotal : r + d * i ≤ N - 1 := by
      rw [mul_comm d i]
      omega
    omega
  · intro hi
    have htotal : i * d + r ≤ N - 1 := by
      rw [mul_comm i d, add_comm]
      omega
    have hmul : i * d ≤ N - 1 - r := Nat.le_sub_of_add_le htotal
    have hile : i ≤ (N - 1 - r) / d := (Nat.le_div_iff_mul_le hd).mpr hmul
    omega

/-- Under `d*K ≤ N`, every residue class modulo `d` in `range N` has at
least `K` terms. -/
theorem K_le_residueLength {N d K r : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) (hr : r < d) : K ≤ residueLength N d r := by
  have hrN : r < N := by nlinarith
  have hpred : K - 1 < residueLength N d r := by
    rw [lt_residueLength_iff hd hrN]
    calc
      r + d * (K - 1) < d + d * (K - 1) := Nat.add_lt_add_right hr _
      _ = d * K := by
        have hsucc : K - 1 + 1 = K := by omega
        calc
          d + d * (K - 1) = d * ((K - 1) + 1) := by ring
          _ = d * K := by rw [hsucc]
      _ ≤ N := hdK
  omega

/-- A controlled cell: one merged index block inside one residue class. -/
def phaseCell (N d K r j : ℕ) : Finset ℕ :=
  (Finset.range (mergedBlockLength (residueLength N d r) K j)).image fun i =>
    r + d * (j * K + i)

example : phaseCell 11 2 2 1 1 = {5, 7, 9} := by decide

/-- Membership has an explicit no-wrap affine parameterization. -/
theorem mem_phaseCell_iff {N d K r j x : ℕ} :
    x ∈ phaseCell N d K r j ↔
      ∃ i < mergedBlockLength (residueLength N d r) K j,
        x = r + d * (j * K + i) := by
  simp only [phaseCell, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

/-- Every active phase cell is contained in `range N`. -/
theorem phaseCell_subset_range {N d K r j : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) (hr : r < d)
    (hj : j < residueLength N d r / K) :
    phaseCell N d K r j ⊆ Finset.range N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_phaseCell_iff.mp hx
  rw [mem_range, ← lt_residueLength_iff hd (by nlinarith)]
  have hmem : j * K + i ∈ mergedBlock (residueLength N d r) K j := by
    rw [mem_mergedBlock_iff]
    exact ⟨Nat.le_add_right _ _, by omega⟩
  exact mem_range.mp
    (mergedBlock_subset_range hK (K_le_residueLength hd hK hdK hr) hj hmem)

/-- A phase cell has exactly its declared affine-progression length. -/
theorem card_phaseCell {N d K r j : ℕ} (hd : 0 < d) :
    (phaseCell N d K r j).card = mergedBlockLength (residueLength N d r) K j := by
  rw [phaseCell]
  calc
    ((Finset.range (mergedBlockLength (residueLength N d r) K j)).image fun i =>
        r + d * (j * K + i)).card =
        (Finset.range (mergedBlockLength (residueLength N d r) K j)).card :=
      card_image_of_injective _ (by
        intro a b hab
        have hmul : d * (j * K + a) = d * (j * K + b) := Nat.add_left_cancel hab
        have hab' : j * K + a = j * K + b := Nat.mul_left_cancel hd hmul
        omega)
    _ = mergedBlockLength (residueLength N d r) K j := card_range _

/-- Active phase cells have cardinality in `[K,2*K)`. -/
theorem phaseCell_card_bounds {N d K r j : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) (hr : r < d)
    (hj : j < residueLength N d r / K) :
    K ≤ (phaseCell N d K r j).card ∧ (phaseCell N d K r j).card < 2 * K := by
  rw [card_phaseCell hd]
  exact mergedBlockLength_bounds hK (K_le_residueLength hd hK hdK hr) hj

/-- Distinct active parameter pairs define disjoint phase cells. -/
theorem disjoint_phaseCell {N d K r j s k : ℕ} (hd : 0 < d)
    (hr : r < d) (hs : s < d)
    (hj : j < residueLength N d r / K)
    (hk : k < residueLength N d s / K)
    (hp : r ≠ s ∨ j ≠ k) :
    Disjoint (phaseCell N d K r j) (phaseCell N d K s k) := by
  rw [Finset.disjoint_left]
  intro x hxr hxs
  obtain ⟨a, ha, hxa⟩ := mem_phaseCell_iff.mp hxr
  obtain ⟨b, hb, hxb⟩ := mem_phaseCell_iff.mp hxs
  have hrs : r = s := by
    have hmodr : (r + d * (j * K + a)) % d = r := by simp [Nat.mod_eq_of_lt hr]
    have hmods : (s + d * (k * K + b)) % d = s := by simp [Nat.mod_eq_of_lt hs]
    calc
      r = (r + d * (j * K + a)) % d := hmodr.symm
      _ = (s + d * (k * K + b)) % d := congrArg (fun n => n % d) (hxa.symm.trans hxb)
      _ = s := hmods
  subst s
  have hab : j * K + a = k * K + b := by
    have hmul : d * (j * K + a) = d * (k * K + b) :=
      Nat.add_left_cancel (hxa.symm.trans hxb)
    exact Nat.mul_left_cancel hd hmul
  have hindexj : j * K + a ∈ mergedBlock (residueLength N d r) K j := by
    rw [mem_mergedBlock_iff]
    exact ⟨Nat.le_add_right _ _, by omega⟩
  have hindexk : k * K + b ∈ mergedBlock (residueLength N d r) K k := by
    rw [mem_mergedBlock_iff]
    exact ⟨Nat.le_add_right _ _, by omega⟩
  have hjk : j ≠ k := hp.resolve_left (by simp)
  have hdis := disjoint_mergedBlock hj hk hjk
  rw [Finset.disjoint_left] at hdis
  exact hdis hindexj (hab ▸ hindexk)

/-- The finite family of all active controlled phase cells. -/
def phasePartition (N d K : ℕ) : Finset (Finset ℕ) :=
  (Finset.range d).biUnion fun r =>
    (Finset.range (residueLength N d r / K)).image fun j => phaseCell N d K r j

example :
    phasePartition 11 2 2 =
      {{0, 2}, {4, 6}, {8, 10}, {1, 3}, {5, 7, 9}} := by decide

/-- A cell belongs to the partition exactly when it has active residue and
block parameters. -/
theorem mem_phasePartition_iff {N d K : ℕ} {C : Finset ℕ} :
    C ∈ phasePartition N d K ↔
      ∃ r < d, ∃ j < residueLength N d r / K, C = phaseCell N d K r j := by
  simp only [phasePartition, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨r, hrd, j, hj, rfl⟩
    exact ⟨r, hrd, j, hj, rfl⟩
  · rintro ⟨r, hrd, j, hj, rfl⟩
    exact ⟨r, hrd, j, hj, rfl⟩

/-- Every point of `range N` belongs to one controlled phase cell. -/
theorem exists_phaseCell_of_mem_range {N d K x : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) (hx : x ∈ Finset.range N) :
    ∃ r < d, ∃ j < residueLength N d r / K, x ∈ phaseCell N d K r j := by
  let r := x % d
  let i := x / d
  have hr : r < d := Nat.mod_lt x hd
  have hdecomp : r + d * i = x := by
    dsimp only [r, i]
    exact Nat.mod_add_div x d
  have hrN : r < N := by
    have hxN := mem_range.mp hx
    omega
  have hi : i < residueLength N d r := by
    rw [lt_residueLength_iff hd hrN]
    simpa only [hdecomp] using mem_range.mp hx
  obtain ⟨j, hj, hij⟩ := exists_mem_mergedBlock hK
    (K_le_residueLength hd hK hdK hr) hi
  refine ⟨r, hr, j, hj, ?_⟩
  rw [mem_mergedBlock_iff] at hij
  rw [mem_phaseCell_iff]
  refine ⟨i - j * K, by omega, ?_⟩
  have hindex : j * K + (i - j * K) = i := Nat.add_sub_of_le hij.1
  rw [hindex, hdecomp]

/-- The union of the controlled cells is exactly `range N`. -/
theorem biUnion_phasePartition {N d K : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) :
    (phasePartition N d K).biUnion id = Finset.range N := by
  ext x
  simp only [mem_biUnion, id_eq]
  constructor
  · rintro ⟨C, hC, hxC⟩
    obtain ⟨r, hr, j, hj, rfl⟩ := mem_phasePartition_iff.mp hC
    exact phaseCell_subset_range hd hK hdK hr hj hxC
  · intro hx
    obtain ⟨r, hr, j, hj, hxcell⟩ := exists_phaseCell_of_mem_range hd hK hdK hx
    exact ⟨phaseCell N d K r j, mem_phasePartition_iff.mpr ⟨r, hr, j, hj, rfl⟩,
      hxcell⟩

/-- Distinct members of the controlled partition are disjoint. -/
theorem phasePartition_pairwiseDisjoint {N d K : ℕ} (hd : 0 < d)
    {C D : Finset ℕ}
    (hC : C ∈ phasePartition N d K) (hD : D ∈ phasePartition N d K)
    (hCD : C ≠ D) : Disjoint C D := by
  obtain ⟨r, hr, j, hj, rfl⟩ := mem_phasePartition_iff.mp hC
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_phasePartition_iff.mp hD
  apply disjoint_phaseCell hd hr hs hj hk
  by_contra hp
  push Not at hp
  exact hCD (by rw [hp.1, hp.2])

/-- Every member of the partition is an affine progression of step `d`, of
length at least `K` and strictly less than `2*K`. -/
theorem phasePartition_cell_structure {N d K : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) {C : Finset ℕ} (hC : C ∈ phasePartition N d K) :
    ∃ r < d, ∃ j < residueLength N d r / K,
      C = (Finset.range (mergedBlockLength (residueLength N d r) K j)).image
        (fun i => r + d * (j * K + i)) ∧
      K ≤ C.card ∧ C.card < 2 * K := by
  obtain ⟨r, hr, j, hj, rfl⟩ := mem_phasePartition_iff.mp hC
  refine ⟨r, hr, j, hj, rfl, ?_⟩
  exact phaseCell_card_bounds hd hK hdK hr hj

/-- Telescoping a uniform step bound along an affine progression. -/
theorem norm_affine_sub_le {E : Type*} [SeminormedAddCommGroup E]
    (χ : ℕ → E) {d : ℕ} {δ : ℝ}
    (hstep : ∀ n, ‖χ (n + d) - χ n‖ ≤ δ) (a t : ℕ) :
    ‖χ (a + d * t) - χ a‖ ≤ (t : ℝ) * δ := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs := hstep (a + d * t)
      have hpoint : a + d * (t + 1) = (a + d * t) + d := by ring
      rw [hpoint]
      calc
        ‖χ ((a + d * t) + d) - χ a‖ =
            ‖(χ ((a + d * t) + d) - χ (a + d * t)) +
              (χ (a + d * t) - χ a)‖ := by
                congr 1
                abel
        _ ≤ ‖χ ((a + d * t) + d) - χ (a + d * t)‖ +
              ‖χ (a + d * t) - χ a‖ := norm_add_le _ _
        _ ≤ δ + (t : ℝ) * δ := add_le_add hs ih
        _ = ((t + 1 : ℕ) : ℝ) * δ := by
          push_cast
          ring

/-- A function with step-`d` variation at most `δ` oscillates by less than
`2*K*δ` between any two points of one active controlled phase cell. -/
theorem norm_sub_le_of_mem_phaseCell {E : Type*} [SeminormedAddCommGroup E]
    (χ : ℕ → E) {N d K r j x y : ℕ} {δ : ℝ}
    (hd : 0 < d) (hK : 0 < K) (hδ : 0 ≤ δ) (hdK : d * K ≤ N)
    (hr : r < d) (hj : j < residueLength N d r / K)
    (hstep : ∀ n, ‖χ (n + d) - χ n‖ ≤ δ)
    (hx : x ∈ phaseCell N d K r j) (hy : y ∈ phaseCell N d K r j) :
    ‖χ x - χ y‖ ≤ (2 * K : ℕ) * δ := by
  obtain ⟨a, ha, rfl⟩ := mem_phaseCell_iff.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_phaseCell_iff.mp hy
  have hlen := (mergedBlockLength_bounds hK
    (K_le_residueLength hd hK hdK hr) hj).2
  rcases le_total b a with hab | hab
  · have htel := norm_affine_sub_le χ hstep
      (r + d * (j * K + b)) (a - b)
    have hindex : b + (a - b) = a := Nat.add_sub_of_le hab
    have heq : (r + d * (j * K + b)) + d * (a - b) =
        r + d * (j * K + a) := by
      calc
        (r + d * (j * K + b)) + d * (a - b) =
            r + d * (j * K + (b + (a - b))) := by ring
        _ = r + d * (j * K + a) := by rw [hindex]
    rw [heq] at htel
    calc
      ‖χ (r + d * (j * K + a)) - χ (r + d * (j * K + b))‖ ≤
          ((a - b : ℕ) : ℝ) * δ := htel
      _ ≤ ((2 * K : ℕ) : ℝ) * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ
        exact_mod_cast (show a - b ≤ 2 * K by omega)
  · have htel := norm_affine_sub_le χ hstep
      (r + d * (j * K + a)) (b - a)
    have hindex : a + (b - a) = b := Nat.add_sub_of_le hab
    have heq : (r + d * (j * K + a)) + d * (b - a) =
        r + d * (j * K + b) := by
      calc
        (r + d * (j * K + a)) + d * (b - a) =
            r + d * (j * K + (a + (b - a))) := by ring
        _ = r + d * (j * K + b) := by rw [hindex]
    rw [heq] at htel
    calc
      ‖χ (r + d * (j * K + a)) - χ (r + d * (j * K + b))‖ =
          ‖χ (r + d * (j * K + b)) - χ (r + d * (j * K + a))‖ := norm_sub_rev _ _
      _ ≤ ((b - a : ℕ) : ℝ) * δ := htel
      _ ≤ ((2 * K : ℕ) : ℝ) * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ
        exact_mod_cast (show b - a ≤ 2 * K by omega)

/-- The oscillation bound applies to every cell selected from the partition. -/
theorem norm_sub_le_of_mem_phasePartition {E : Type*} [SeminormedAddCommGroup E]
    (χ : ℕ → E) {N d K : ℕ} {δ : ℝ}
    (hd : 0 < d) (hK : 0 < K) (hδ : 0 ≤ δ) (hdK : d * K ≤ N)
    (hstep : ∀ n, ‖χ (n + d) - χ n‖ ≤ δ)
    {C : Finset ℕ} (hC : C ∈ phasePartition N d K) {x y : ℕ}
    (hx : x ∈ C) (hy : y ∈ C) :
    ‖χ x - χ y‖ ≤ (2 * K : ℕ) * δ := by
  obtain ⟨r, hr, j, hj, rfl⟩ := mem_phasePartition_iff.mp hC
  exact norm_sub_le_of_mem_phaseCell χ hd hK hδ hdK hr hj hstep hx hy

/-- A unit-norm complex additive character with `χ(d)` within `δ` of one
has oscillation at most `2*K*δ` on each controlled cell. -/
theorem norm_sub_le_of_mem_phasePartition_additiveCharacter
    (χ : ℕ → ℂ) {N d K : ℕ} {δ : ℝ}
    (hd : 0 < d) (hK : 0 < K) (hδ : 0 ≤ δ) (hdK : d * K ≤ N)
    (hadd : ∀ m n, χ (m + n) = χ m * χ n)
    (hnorm : ∀ n, ‖χ n‖ = 1) (hphase : ‖χ d - 1‖ ≤ δ)
    {C : Finset ℕ} (hC : C ∈ phasePartition N d K) {x y : ℕ}
    (hx : x ∈ C) (hy : y ∈ C) :
    ‖χ x - χ y‖ ≤ (2 * K : ℕ) * δ := by
  apply norm_sub_le_of_mem_phasePartition χ hd hK hδ hdK _ hC hx hy
  intro n
  calc
    ‖χ (n + d) - χ n‖ = ‖χ n * (χ d - 1)‖ := by rw [hadd]; congr 1; ring
    _ = ‖χ n‖ * ‖χ d - 1‖ := norm_mul _ _
    _ ≤ 1 * δ := by
      rw [hnorm]
      simpa only [one_mul] using hphase
    _ = δ := one_mul δ

/-- The controlled-partition specification packages exact cover,
pairwise disjointness, and the explicit affine structure and size bounds of
every cell. -/
theorem phasePartition_spec {N d K : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) :
    (phasePartition N d K).biUnion id = Finset.range N ∧
      (∀ C ∈ phasePartition N d K, ∀ D ∈ phasePartition N d K,
        C ≠ D → Disjoint C D) ∧
      ∀ C ∈ phasePartition N d K,
        ∃ r < d, ∃ j < residueLength N d r / K,
          C = (Finset.range (mergedBlockLength (residueLength N d r) K j)).image
            (fun i => r + d * (j * K + i)) ∧
          K ≤ C.card ∧ C.card < 2 * K := by
  refine ⟨biUnion_phasePartition hd hK hdK, ?_, ?_⟩
  · intro C hC D hD hCD
    exact phasePartition_pairwiseDisjoint hd hC hD hCD
  · intro C hC
    exact phasePartition_cell_structure hd hK hdK hC

/-- Joint satisfiability of all partition hypotheses, with a non-singleton
cell and a genuinely merged final remainder. -/
example :
    let N := 11
    let d := 2
    let K := 2
    0 < d ∧ 0 < K ∧ d * K ≤ N ∧
      phaseCell N d K 1 1 = {5, 7, 9} ∧
      (phasePartition N d K).biUnion id = Finset.range N := by
  dsimp only
  refine ⟨by omega, by omega, by omega, by decide, ?_⟩
  exact biUnion_phasePartition (by omega) (by omega) (by omega)

#check @phasePartition
#check @phasePartition_spec
#check @norm_affine_sub_le
#check @norm_sub_le_of_mem_phasePartition
#check @norm_sub_le_of_mem_phasePartition_additiveCharacter

#print axioms phasePartition_spec
#print axioms norm_sub_le_of_mem_phasePartition
#print axioms norm_sub_le_of_mem_phasePartition_additiveCharacter

end Erdos142
