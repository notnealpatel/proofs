/-
# Erdős Problem 348, existence half: powers of two and Fibonacci deletions

## Source

Jesse Geneson, "Deletion thresholds and exponential examples for complete
sequences", arXiv:2609.25107, Section 3 ("The two existence constructions"),
proofs labelled "Existence for m=0" and "Existence for m=1".  The underlying
results are classical: Brown (1961) for completeness of the Fibonacci
sequence after one deletion, Graham (1964) for incompleteness after two.
Recorded 2026-10-21.

Conventions of the paper (Section 1): for a sequence `A = (a_i)`, `FS(A)` is
the set of sums of finite selections of terms with distinct indices,
including the empty sum; `A` is *complete* if `FS(A)` contains every
sufficiently large integer; a deletion removes an occurrence (index).

Verbatim informal claims (Section 3):

> The sequence $1,2,4,8,\ldots$ represents every nonnegative integer by
> binary expansion. After deleting $2^j$, no remaining subset sum is
> congruent to $2^j$ modulo $2^{j+1}$ [...] Thus a one-occurrence deletion
> leaves infinitely many missing integers.

> [Fibonacci, $F_1 = F_2 = 1$] The interval induction therefore shows that
> every nonnegative integer is represented after any one-occurrence
> deletion.
> Now delete $F_i,F_j$ with $i<j$. For $t\ge0$ and $1\le d\le F_i$, put
> $x_t(d)=F_{j+2t+1}-d$. We prove by induction on $t$ that these integers
> are missing. [...] The Fibonacci sequence therefore works for every pair
> $(1,n)$ with $n\ge2$.

Together these give the "if" direction of the paper's Theorem 1.1
(Erdős Problem 348): for `0 ≤ m < n` with `m ≤ 1` there is a nondecreasing
sequence complete after every deletion of `m` occurrences and incomplete
after every deletion of `n` occurrences.

## Status

Proved in the paper (and classical: Brown 1961, Graham 1964).  Fully
formalized here, no `sorry`.

## Indexing

Lean indices start at `0`: `fibSeq i = Nat.fib (i + 1)`, so
`fibSeq 0 = fibSeq 1 = 1` are the paper's `F_1 = F_2 = 1` as two distinct
occurrences, and the paper's `F_k` is `fibSeq (k - 1)`.  The paper's missing
integers `F_{j+2t+1} - d` for paper indices `i < j` become
`Nat.fib (j + 2 t + 2) - d` for Lean indices `i < j`, with `1 ≤ d ≤ fibSeq i`.
-/
import Mathlib

set_option autoImplicit false

namespace Erdos348FibonacciDeletion

open Finset

/-- `FS a D`: the finite-selection sums of the sequence `a` after deleting the
occurrences with index in `D`, i.e. all `∑ i ∈ T, a i` over finite index sets `T`
disjoint from `D` (the empty sum `0` included).  This is the paper's `FS(A)`. -/
def FS (a : ℕ → ℕ) (D : Finset ℕ) : Set ℕ :=
  {x | ∃ T : Finset ℕ, Disjoint T D ∧ ∑ i ∈ T, a i = x}

/-- Brown's interval criterion (paper, Section 3): if each retained term is at
most one plus the sum of the retained terms before it, then each retained prefix
represents every integer from `0` to its total. -/
theorem brown_interval (a : ℕ → ℕ) (D : Finset ℕ)
    (h : ∀ k, k ∉ D → a k ≤ ∑ i ∈ range k \ D, a i + 1) :
    ∀ k x, x ≤ ∑ i ∈ range k \ D, a i →
      ∃ T ⊆ range k, Disjoint T D ∧ ∑ i ∈ T, a i = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    refine ⟨∅, empty_subset _, disjoint_empty_left _, ?_⟩
    simp only [range_zero, empty_sdiff, sum_empty, nonpos_iff_eq_zero] at hx
    simp [hx]
  | succ k ih =>
    intro x hx
    by_cases hkD : k ∈ D
    · have hset : range (k + 1) \ D = range k \ D := by
        ext m
        simp only [mem_sdiff, mem_range]
        constructor
        · rintro ⟨hm, hmD⟩
          refine ⟨?_, hmD⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact hlt
          · exact absurd (heq ▸ hkD) hmD
        · rintro ⟨hm, hmD⟩
          exact ⟨Nat.lt_succ_of_lt hm, hmD⟩
      rw [hset] at hx
      obtain ⟨T, hT, hTD, hTs⟩ := ih x hx
      exact ⟨T, hT.trans (range_subset_range.mpr (Nat.le_succ k)), hTD, hTs⟩
    · have hset : range (k + 1) \ D = insert k (range k \ D) := by
        rw [range_add_one, insert_sdiff_of_notMem _ hkD]
      have hknot : k ∉ range k \ D := by simp
      rw [hset, sum_insert hknot] at hx
      by_cases hxS : x ≤ ∑ i ∈ range k \ D, a i
      · obtain ⟨T, hT, hTD, hTs⟩ := ih x hxS
        exact ⟨T, hT.trans (range_subset_range.mpr (Nat.le_succ k)), hTD, hTs⟩
      · have hak := h k hkD
        obtain ⟨T, hT, hTD, hTs⟩ := ih (x - a k) (by omega)
        have hkT : k ∉ T := fun hk => by simpa using hT hk
        refine ⟨insert k T, ?_, ?_, ?_⟩
        · intro m hm
          rcases mem_insert.mp hm with rfl | hm
          · simp
          · exact range_subset_range.mpr (Nat.le_succ k) (hT hm)
        · exact disjoint_insert_left.mpr ⟨hkD, hTD⟩
        · rw [sum_insert hkT, hTs]
          omega

/-- The Fibonacci sequence with two initial ones, `1, 1, 2, 3, 5, …`, indexed
from `0`: `fibSeq i = F_{i+1}` in the paper's convention `F_1 = F_2 = 1`. -/
def fibSeq (i : ℕ) : ℕ := Nat.fib (i + 1)

/-- The partial-sum identity `∑_{r=1}^k F_r = F_{k+2} - 1`, stated without
subtraction. -/
theorem sum_range_fibSeq (k : ℕ) : ∑ i ∈ range k, fibSeq i + 1 = Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, add_right_comm, ih, fibSeq, Nat.fib_add_two (n := k + 1)]
    ring

/-- Two disjoint index sets inside `range n` have total sum at most the sum over
`range n`. -/
theorem sum_add_sum_le_sum_range (a : ℕ → ℕ) (n : ℕ) (T E : Finset ℕ)
    (hT : T ⊆ range n) (hE : E ⊆ range n) (hTE : Disjoint T E) :
    ∑ i ∈ T, a i + ∑ i ∈ E, a i ≤ ∑ i ∈ range n, a i := by
  rw [← sum_union hTE]
  exact sum_le_sum_of_subset (union_subset hT hE)

/-- A selection of Fibonacci terms with total below `F_{n+1}` uses only indices
below `n`. -/
theorem subset_range_of_sum_fibSeq_lt (T : Finset ℕ) (n : ℕ)
    (h : ∑ i ∈ T, fibSeq i < Nat.fib (n + 1)) : T ⊆ range n := by
  intro m hm
  rw [mem_range]
  by_contra hmn
  have h1 : fibSeq m ≤ ∑ i ∈ T, fibSeq i := single_le_sum (fun _ _ => Nat.zero_le _) hm
  have h2 : Nat.fib (n + 1) ≤ fibSeq m := Nat.fib_mono (by omega)
  omega

/-- Brown: after deleting any single occurrence of the Fibonacci sequence, every
nonnegative integer is a finite-selection sum. -/
theorem fibSeq_complete_erase (j x : ℕ) : x ∈ FS fibSeq {j} := by
  have hstep : ∀ k, k ∉ ({j} : Finset ℕ) →
      fibSeq k ≤ ∑ i ∈ range k \ {j}, fibSeq i + 1 := by
    intro k hk
    rw [mem_singleton] at hk
    rw [sdiff_singleton_eq_erase]
    have hsum := sum_range_fibSeq k
    by_cases hjk : j < k
    · rw [← sum_erase_add _ _ (mem_range.mpr hjk)] at hsum
      have hmono : fibSeq j ≤ Nat.fib k := Nat.fib_mono (by omega)
      have hrec : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      simp only [fibSeq] at hsum hmono ⊢
      omega
    · rw [erase_eq_of_notMem (by simpa using hjk)]
      have hmono : Nat.fib (k + 1) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
      simp only [fibSeq] at hsum ⊢
      omega
  have hbig : x ≤ ∑ i ∈ range (x + j + 3) \ {j}, fibSeq i := by
    rw [sdiff_singleton_eq_erase]
    have hsum := sum_range_fibSeq (x + j + 3)
    rw [← sum_erase_add _ _ (mem_range.mpr (by omega : j < x + j + 3))] at hsum
    have hmono : fibSeq j ≤ Nat.fib (x + j + 3) := Nat.fib_mono (by omega)
    have hrec : Nat.fib (x + j + 3 + 2) = Nat.fib (x + j + 3) + Nat.fib (x + j + 3 + 1) :=
      Nat.fib_add_two
    have hlow := Nat.le_fib_add_one (x + j + 3 + 1)
    simp only [fibSeq] at hsum hmono ⊢
    omega
  obtain ⟨T, -, hTD, hTs⟩ := brown_interval fibSeq {j} hstep _ x hbig
  exact ⟨T, hTD, hTs⟩

/-- Graham: after deleting the occurrences with indices `i < j`, the integers
`F_{j+2t+2} - d` (Lean indexing; the paper's `F_{j+2t+1} - d`) are missing for
every `t` and every `1 ≤ d ≤ fibSeq i`. -/
theorem fibSeq_missing_two (i j : ℕ) (hij : i < j) (t d : ℕ) (hd1 : 1 ≤ d)
    (hdi : d ≤ fibSeq i) : Nat.fib (j + 2 * t + 2) - d ∉ FS fibSeq {i, j} := by
  induction t with
  | zero =>
    rintro ⟨T, hTD, hTs⟩
    have hjT : j ∉ T := fun h => disjoint_left.mp hTD h (by simp)
    have hT1 : T ⊆ range (j + 1) :=
      subset_range_of_sum_fibSeq_lt T (j + 1) (by
        have hpos : 0 < Nat.fib (j + 2) := Nat.fib_pos.mpr (by omega)
        rw [hTs]
        show Nat.fib (j + 2) - d < Nat.fib (j + 2)
        omega)
    have hT : T ⊆ range j := by
      intro m hm
      have := mem_range.mp (hT1 hm)
      have hmj : m ≠ j := fun h => hjT (h ▸ hm)
      exact mem_range.mpr (by omega)
    have hiE : ({i} : Finset ℕ) ⊆ range j := by simpa using hij
    have hTi : Disjoint T {i} :=
      disjoint_of_subset_right (by simp) hTD
    have hle := sum_add_sum_le_sum_range fibSeq j T {i} hT hiE hTi
    have hsum := sum_range_fibSeq j
    have hmono : Nat.fib (j + 1) ≤ Nat.fib (j + 2) := Nat.fib_mono (by omega)
    rw [sum_singleton] at hle
    simp only [fibSeq, mul_zero, add_zero] at hle hsum hmono hTs hdi
    omega
  | succ t ih =>
    rintro ⟨T, hTD, hTs⟩
    set s := j + 2 * t + 2 with hs
    have hxs : Nat.fib (j + 2 * (t + 1) + 2) = Nat.fib (s + 2) := by
      rw [hs]; ring_nf
    rw [hxs] at hTs
    have hT1 : T ⊆ range (s + 1) :=
      subset_range_of_sum_fibSeq_lt T (s + 1) (by
        have hpos : 0 < Nat.fib (s + 2) := Nat.fib_pos.mpr (by omega)
        rw [hTs]
        show Nat.fib (s + 2) - d < Nat.fib (s + 2)
        omega)
    have hrec : Nat.fib (s + 2) = Nat.fib s + Nat.fib (s + 1) := Nat.fib_add_two
    by_cases hsT : s ∈ T
    · apply ih
      refine ⟨T.erase s, disjoint_of_subset_left (erase_subset _ _) hTD, ?_⟩
      have hsplit := sum_erase_add T fibSeq hsT
      simp only [fibSeq] at hsplit hTs ⊢
      omega
    · have hT : T ⊆ range s := by
        intro m hm
        have := mem_range.mp (hT1 hm)
        have hms : m ≠ s := fun h => hsT (h ▸ hm)
        exact mem_range.mpr (by omega)
      have hE : ({i, j} : Finset ℕ) ⊆ range s := by
        intro m hm
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with rfl | rfl <;> exact mem_range.mpr (by omega)
      have hle := sum_add_sum_le_sum_range fibSeq s T {i, j} hT hE hTD
      rw [sum_pair hij.ne] at hle
      have hsum := sum_range_fibSeq s
      have hmono : Nat.fib (s + 1) ≤ Nat.fib (s + 2) := Nat.fib_mono (by omega)
      have hj1 : 0 < Nat.fib (j + 1) := Nat.fib_pos.mpr (by omega)
      simp only [fibSeq] at hle hsum hmono hTs hdi
      omega

/-- After deleting any two occurrences `i < j` of the Fibonacci sequence,
infinitely many natural numbers are not finite-selection sums. -/
theorem fibSeq_missing_infinite (i j : ℕ) (hij : i < j) :
    (FS fibSeq {i, j})ᶜ.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨Nat.fib (j + 2 * N + 2) - 1,
    fibSeq_missing_two i j hij N 1 le_rfl (Nat.fib_pos.mpr (by omega)), ?_⟩
  have hlow := Nat.le_fib_add_one (j + 2 * N + 2)
  omega

/-- The powers of two `1, 2, 4, 8, …`, indexed from `0`. -/
def powTwo (i : ℕ) : ℕ := 2 ^ i

/-- Binary expansion: every natural number is a sum of distinct powers of two. -/
theorem powTwo_complete (x : ℕ) : x ∈ FS powTwo ∅ :=
  ⟨x.bitIndices.toFinset, disjoint_empty_right _, Finset.sum_toFinset_bitIndices_two_pow x⟩

/-- After deleting `2^j`, no finite-selection sum is congruent to `2^j` modulo
`2^(j+1)`. -/
theorem powTwo_mod_ne_of_mem (j x : ℕ) (hx : x ∈ FS powTwo {j}) :
    x % 2 ^ (j + 1) ≠ 2 ^ j := by
  obtain ⟨T, hTD, hTs⟩ := hx
  have hjT : j ∉ T := fun h => disjoint_left.mp hTD h (mem_singleton_self j)
  have hsplit := sum_filter_add_sum_filter_not T (fun m => m < j) powTwo
  have hlow : ∑ m ∈ T.filter (fun m => m < j), powTwo m < 2 ^ j :=
    Nat.geomSum_lt le_rfl (fun k hk => (mem_filter.mp hk).2)
  have hhigh : 2 ^ (j + 1) ∣ ∑ m ∈ T.filter (fun m => ¬ m < j), powTwo m := by
    apply dvd_sum
    intro m hm
    have hm' := mem_filter.mp hm
    have hmj : m ≠ j := fun h => hjT (h ▸ hm'.1)
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨c, hc⟩ := hhigh
  have hlt2 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [← hTs, ← hsplit, hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlow.trans hlt2)]
  exact hlow.ne

/-- After deleting `2^j`, infinitely many natural numbers are not
finite-selection sums. -/
theorem powTwo_missing_infinite (j : ℕ) : (FS powTwo {j})ᶜ.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨2 ^ j + 2 ^ (j + 1) * N, fun hmem => powTwo_mod_ne_of_mem j _ hmem ?_, ?_⟩
  · have hlt2 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
  · have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    nlinarith

/-- The sequence `a` with the occurrences indexed by `D` deleted is *complete*
(in the paper's eventual sense): every sufficiently large integer lies in
`FS a D`. -/
def IsComplete (a : ℕ → ℕ) (D : Finset ℕ) : Prop :=
  ∃ N, ∀ x, N ≤ x → x ∈ FS a D

/-- Deleting more occurrences can only shrink the set of finite-selection
sums. -/
theorem FS_anti (a : ℕ → ℕ) {D D' : Finset ℕ} (h : D ⊆ D') : FS a D' ⊆ FS a D := by
  rintro x ⟨T, hTD, hTs⟩
  exact ⟨T, disjoint_of_subset_right h hTD, hTs⟩

/-- If infinitely many natural numbers are missing, the sequence is not
complete. -/
theorem not_isComplete_of_infinite (a : ℕ → ℕ) (D : Finset ℕ) (h : (FS a D)ᶜ.Infinite) :
    ¬ IsComplete a D := by
  rintro ⟨N, hN⟩
  obtain ⟨x, hx, hNx⟩ := h.exists_gt N
  exact hx (hN x hNx.le)

/-- The Fibonacci sequence stays complete after every deletion of at most one
occurrence. -/
theorem fibSeq_isComplete_of_card_le_one (D : Finset ℕ) (hD : D.card ≤ 1) :
    IsComplete fibSeq D := by
  refine ⟨0, fun x _ => ?_⟩
  rcases card_le_one_iff_subset_singleton.mp hD with ⟨j, hj⟩
  exact FS_anti fibSeq hj (fibSeq_complete_erase j x)

/-- The Fibonacci sequence becomes incomplete after every deletion of at least
two occurrences. -/
theorem fibSeq_not_isComplete_of_one_lt_card (D : Finset ℕ) (hD : 1 < D.card) :
    ¬ IsComplete fibSeq D := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hD
  rcases lt_or_gt_of_ne hab with h | h
  · refine not_isComplete_of_infinite _ _ ((fibSeq_missing_infinite a b h).mono ?_)
    exact Set.compl_subset_compl.mpr (FS_anti fibSeq (insert_subset ha (singleton_subset_iff.mpr hb)))
  · refine not_isComplete_of_infinite _ _ ((fibSeq_missing_infinite b a h).mono ?_)
    exact Set.compl_subset_compl.mpr (FS_anti fibSeq (insert_subset hb (singleton_subset_iff.mpr ha)))

/-- The powers of two become incomplete after every nonempty deletion. -/
theorem powTwo_not_isComplete_of_nonempty (D : Finset ℕ) (hD : D.Nonempty) :
    ¬ IsComplete powTwo D := by
  obtain ⟨j, hj⟩ := hD
  refine not_isComplete_of_infinite _ _ ((powTwo_missing_infinite j).mono ?_)
  exact Set.compl_subset_compl.mpr (FS_anti powTwo (singleton_subset_iff.mpr hj))

/-- Erdős Problem 348, existence half (the "if" direction of Theorem 1.1 of
arXiv:2609.25107, Section 3): for `m ≤ 1` and `m < n` there is a nondecreasing
sequence of natural numbers that is complete after every deletion of `m`
occurrences and incomplete after every deletion of `n` occurrences.  The
witnesses are the powers of two (`m = 0`) and the Fibonacci sequence with two
initial ones (`m = 1`). -/
theorem erdos348_existence (m n : ℕ) (hm : m ≤ 1) (hmn : m < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ D : Finset ℕ, D.card = m → IsComplete a D) ∧
      (∀ D : Finset ℕ, D.card = n → ¬ IsComplete a D) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
  · refine ⟨powTwo, fun _ _ hab => Nat.pow_le_pow_right (by norm_num) hab, ?_, ?_⟩
    · intro D hD
      rw [card_eq_zero] at hD
      subst hD
      exact ⟨0, fun x _ => powTwo_complete x⟩
    · intro D hD
      exact powTwo_not_isComplete_of_nonempty D (card_pos.mp (by omega))
  · refine ⟨fibSeq, fun _ _ hab => Nat.fib_mono (by omega), ?_, ?_⟩
    · intro D hD
      exact fibSeq_isComplete_of_card_le_one D hD.le
    · intro D hD
      exact fibSeq_not_isComplete_of_one_lt_card D (by omega)

/-! ## Ground-truth checks -/

example : (List.range 6).map fibSeq = [1, 1, 2, 3, 5, 8] := by decide
example : (List.range 5).map powTwo = [1, 2, 4, 8, 16] := by decide

/-- `4 = F_1 + F_4` survives deleting the occurrence `2` (value `2`). -/
example : 4 ∈ FS fibSeq {2} := ⟨{0, 3}, by decide, by decide⟩

/-- `5 = 1 + 4` survives deleting `2 = powTwo 1`, while `2 ≡ 2 (mod 4)` is lost. -/
example : 5 ∈ FS powTwo {1} := ⟨{0, 2}, by decide, by decide⟩
example : 2 ∉ FS powTwo {1} := fun h => powTwo_mod_ne_of_mem 1 2 h (by decide)

/-- Deleting both initial ones loses `1 = F_3 - 1` (paper: `t = 0`, `d = 1`). -/
example : 1 ∉ FS fibSeq {0, 1} := by
  have hfib : Nat.fib (1 + 2 * 0 + 2) - 1 = 1 := by decide
  have hmiss := fibSeq_missing_two 0 1 Nat.zero_lt_one 0 1 le_rfl le_rfl
  rwa [hfib] at hmiss

/-- Joint satisfiability of the packaged hypotheses at `m = 1`, `n = 2`. -/
example : IsComplete fibSeq {5} ∧ ¬ IsComplete fibSeq {0, 7} :=
  ⟨fibSeq_isComplete_of_card_le_one _ (by decide),
    fibSeq_not_isComplete_of_one_lt_card _ (by decide)⟩

end Erdos348FibonacciDeletion
