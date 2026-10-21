/-
# A242258 — Kimberling: p(n) is A000041-greedy summable for n ≥ 3

## OEIS source (retrieved 2026-10-21 with `oeis show A242258`; AUTHOR line
## from https://oeis.org/A242258)

```
NAME:     Number of summands in s-greedy sum of s(n), where s(n) = A000041(n),
          the partitions numbers.
OFFSET:   2,2
TERMS:    1,2,2,2,3,3,2,3,3,3,4,3,4,3,4,4,3,4,3,3,5,3,4,5,5,4,5,5,4,4,6,5,5,...
COMMENT:  See A242252 for the definitions of greedy sum and summability.
COMMENT (the conjecture, unsigned, in the entry by its author):
  Conjecture:  A000041(n) is A000041-greedy summable for n >= 3.
AUTHOR:   Clark Kimberling, May 10 2014
PROGRAM:  (Mathematica, Peter J. C. Moses, May 06 2014)
  z = 200;  s = Table[PartitionsP[n], {n, 1, z}];
  t = Table[{s[[n]], #, Total[#] == s[[n]]} &[DeleteCases[-Differences[
        FoldList[If[#1 - #2 >= 0, #1 - #2, #1] &, s[[n]],
          Reverse[Select[s, # < s[[n]] &]]]], 0]], {n, z}]; ...
```

## Reading of the conjecture

The algorithm is the one in the Mathematica program: starting from
`r = p(n)`, scan the terms `p(k) < p(n)` (`k ≥ 1`) in decreasing order and
subtract `p(k)` whenever `p(k) ≤ r`, each term used at most once.  "Greedy
summable" means the final residue is `0`.  Since `p(1) < p(2) < ⋯`, the
scanned terms are exactly `p(n-1), p(n-2), …, p(1)`
(`scanList_eq_select` proves this against the literal `Select`/`Reverse`).

## Status

Triage: open (the entry gives no proof; no source applying Brown's
complete-sequence criterion to this entry was found, search shallow).
Computation (python3, this campaign): residue `0` for every `n ∈ [3, 6000]`;
the only failure in `[2, 6000]` is the excluded `n = 2`; summand counts for
`n = 2..40` match the DATA line.

This module **proves** the conjecture for all `n ≥ 3`.  Proof: (1) a
Brown-type lemma — if `s(k+1) ≤ 1 + s(1) + ⋯ + s(k)` for all `k < m`, the
decreasing distinct greedy fold over `s(m), …, s(1)` sends every
`x ≤ s(1) + ⋯ + s(m)` to `0`; (2) removing the minimum part injects the
partitions of `n ≥ 1` into `Σ_{j<n} Partition j`, so `p(n) ≤ Σ_{j<n} p(j)`,
and for `n ≥ 3` the injection misses the fibre `j = 1`, giving the strict
inequality `p(n) < Σ_{j<n} p(j)`, i.e. `p(n) ≤ p(1) + ⋯ + p(n-1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A242258DistinctGreedyAlgorithm

/-! ## Definition layer -/

/-- The partition number `p(k) = A000041(k)`: the number of partitions of `k`,
i.e. Mathlib's `Fintype.card (Nat.Partition k)`. -/
def P (k : ℕ) : ℕ := Fintype.card (Nat.Partition k)

/-- The distinct-term greedy residue of `x` along the list `l`, exactly the
Mathematica `Fold[If[#1 - #2 >= 0, #1 - #2, #1] &, x, l]`: scan `l` from the
left and subtract a term whenever it does not exceed the current remainder. -/
def greedyResidue (x : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun r t => if t ≤ r then r - t else r) x

/-- The scan list `[p(n-1), p(n-2), …, p(1)]` used by the greedy algorithm
for `x = p(n)`. -/
def scanList (n : ℕ) : List ℕ := (List.range (n - 1)).reverse.map (fun i => P (i + 1))

/-! ## Ground truth -/

/-- `p(0) = 1`. -/
theorem P_zero : P 0 = 1 := by decide

/-- `p(1) = 1`. -/
theorem P_one : P 1 = 1 := by decide

example : greedyResidue 7 [5, 3, 2, 1] = 0 := by decide
example : greedyResidue 2 [1] = 1 := by decide
example : greedyResidue 15 [11, 7, 5, 3, 2, 1] = 0 := by decide
example : scanList 4 = [P 3, P 2, P 1] := rfl

/-! ## Brown-type greedy lemma -/

/-- **Brown-type greedy lemma.**  If `s(k+1) ≤ 1 + s(1) + ⋯ + s(k)` for every
`k < m`, then for every `x ≤ s(1) + ⋯ + s(m)` the distinct greedy fold over
`s(m), s(m-1), …, s(1)` ends with residue `0`. -/
theorem greedyResidue_eq_zero_of_brown (s : ℕ → ℕ) (m : ℕ)
    (hbrown : ∀ k < m, s (k + 1) ≤ 1 + ∑ i ∈ Finset.range k, s (i + 1))
    (x : ℕ) (hx : x ≤ ∑ i ∈ Finset.range m, s (i + 1)) :
    greedyResidue x ((List.range m).reverse.map (fun i => s (i + 1))) = 0 := by
  induction m generalizing x with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero] at hx
    simp [greedyResidue, hx]
  | succ m ih =>
    have hb := hbrown m (Nat.lt_succ_self m)
    have ih' := ih (fun k hk => hbrown k (Nat.lt_succ_of_lt hk))
    rw [Finset.sum_range_succ] at hx
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    unfold greedyResidue at ih' ⊢
    rw [List.foldl_cons]
    split_ifs with h
    · exact ih' _ (by omega)
    · exact ih' _ (by omega)

/-! ## Partition-number bounds -/

/-- **Partition bound.**  For `n ≥ 1`, `p(n) ≤ p(0) + ⋯ + p(n-1)`, and for
`n ≥ 3` the inequality is strict.  The map removing one copy of the minimum
part `m` sends a partition of `n` to `(n - m, partition of n - m)`; it is
injective (the part is recovered from the index), and for `n ≥ 3` it misses
the fibre over `1` (a partition `{n-1} ∪ μ` with `μ ⊢ 1` has minimum `1`). -/
theorem P_sum_bounds (n : ℕ) (hn : 1 ≤ n) :
    P n ≤ ∑ j ∈ Finset.range n, P j ∧ (3 ≤ n → P n < ∑ j ∈ Finset.range n, P j) := by
  classical
  have hne : ∀ q : Nat.Partition n, q.parts.toFinset.Nonempty := fun q => by
    rw [Multiset.toFinset_nonempty]
    intro h0
    have hs := q.parts_sum
    rw [h0, Multiset.sum_zero] at hs
    omega
  let mn : Nat.Partition n → ℕ := fun q => q.parts.toFinset.min' (hne q)
  have hmem : ∀ q, mn q ∈ q.parts := fun q => Multiset.mem_toFinset.mp (Finset.min'_mem _ _)
  have hle : ∀ q, ∀ i ∈ q.parts, mn q ≤ i := fun q i hi =>
    Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hi)
  have hpos : ∀ q, 0 < mn q := fun q => q.parts_pos (hmem q)
  have hlen : ∀ q, mn q ≤ n := fun q => Nat.Partition.le_of_mem_parts (hmem q)
  have hsum : ∀ q, mn q + (q.parts.erase (mn q)).sum = n := fun q => by
    rw [Multiset.sum_erase (hmem q), q.parts_sum]
  let f : Nat.Partition n → Σ j : Fin n, Nat.Partition j := fun q =>
    ⟨⟨n - mn q, by have := hpos q; omega⟩,
     { parts := q.parts.erase (mn q)
       parts_pos := fun hi => q.parts_pos (Multiset.mem_of_mem_erase hi)
       parts_sum := by have := hsum q; dsimp only; omega }⟩
  let g : (Σ j : Fin n, Nat.Partition j) → Multiset ℕ := fun z => (n - z.1.val) ::ₘ z.2.parts
  have hgf : ∀ q, g (f q) = q.parts := fun q => by
    simp only [g, f]
    rw [show n - (n - mn q) = mn q by have := hlen q; omega]
    exact Multiset.cons_erase (hmem q)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Nat.Partition.ext
    rw [← hgf a, ← hgf b, hab]
  have hcardS : Fintype.card (Σ j : Fin n, Nat.Partition j) = ∑ j ∈ Finset.range n, P j := by
    rw [Fintype.card_sigma]
    exact Fin.sum_univ_eq_sum_range P n
  refine ⟨?_, fun h3 => ?_⟩
  · have hc := Fintype.card_le_of_injective f hinj
    rw [hcardS] at hc
    exact hc
  · have hns : ¬ Function.Surjective f := by
      intro hsurj
      obtain ⟨μ, -⟩ : ∃ μ : Nat.Partition 1, True := ⟨Nat.Partition.indiscrete 1, trivial⟩
      obtain ⟨q, hq⟩ := hsurj ⟨⟨1, by omega⟩, μ⟩
      have h1 : n - mn q = 1 := congrArg (fun z => z.1.val) hq
      have hparts : q.parts = (n - 1) ::ₘ μ.parts := by
        rw [← hgf q, hq]
      have hμne : μ.parts ≠ 0 := by
        intro h0
        have hs := μ.parts_sum
        rw [h0, Multiset.sum_zero] at hs
        omega
      obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hμne
      have hi1 : i ≤ 1 := Nat.Partition.le_of_mem_parts hi
      have hiq : i ∈ q.parts := by
        rw [hparts]
        exact Multiset.mem_cons_of_mem hi
      have hmi := hle q i hiq
      omega
    have hc := Fintype.card_lt_of_injective_not_surjective f hinj hns
    rw [hcardS] at hc
    exact hc

/-- **Strict growth.**  `p(k) < p(k+1)` for `k ≥ 1`: adding a part `1` injects
partitions of `k` into partitions of `k+1`, missing the one-part partition
`{k+1}`. -/
theorem P_lt_P_succ (k : ℕ) (hk : 1 ≤ k) : P k < P (k + 1) := by
  let f : Nat.Partition k → Nat.Partition (k + 1) := fun q =>
    { parts := 1 ::ₘ q.parts
      parts_pos := fun hi => by
        rcases Multiset.mem_cons.mp hi with h | h
        · omega
        · exact q.parts_pos h
      parts_sum := by rw [Multiset.sum_cons, q.parts_sum, add_comm] }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Nat.Partition.ext
    have hp := congrArg Nat.Partition.parts hab
    exact (Multiset.cons_inj_right 1).mp hp
  have hns : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨q, hq⟩ := hsurj
      { parts := {k + 1}
        parts_pos := fun hi => by rw [Multiset.mem_singleton.mp hi]; omega
        parts_sum := Multiset.sum_singleton (k + 1) }
    have hp := congrArg Nat.Partition.parts hq
    have h1 : (1 : ℕ) ∈ (f q).parts := Multiset.mem_cons_self 1 q.parts
    rw [hp, Multiset.mem_singleton] at h1
    omega
  exact Fintype.card_lt_of_injective_not_surjective f hinj hns

/-- On indices `≥ 1`, `p(i) < p(j) ↔ i < j`. -/
theorem P_lt_P_iff (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) : P i < P j ↔ i < j := by
  have hmono : StrictMono (fun k => P (k + 1)) :=
    strictMono_nat_of_lt_succ (fun k => P_lt_P_succ (k + 1) (by omega))
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  rw [hmono.lt_iff_lt]
  omega

/-- `p(2) = 2`, pinned by `p(1) < p(2) ≤ p(0) + p(1)`. -/
theorem P_two : P 2 = 2 := by
  have hlt : P 1 < P 2 := P_lt_P_succ 1 le_rfl
  have hle := (P_sum_bounds 2 (by norm_num)).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, P_zero, P_one] at hle hlt
  omega

/-- `p(3) = 3`, pinned by `p(2) < p(3) < p(0) + p(1) + p(2)`. -/
theorem P_three : P 3 = 3 := by
  have hlt : P 2 < P 3 := P_lt_P_succ 2 (by norm_num)
  have hle := (P_sum_bounds 3 (by norm_num)).2 le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, P_zero, P_one, P_two] at hle hlt
  omega

/-- **Fidelity to the Mathematica program.**  For `1 ≤ n ≤ z`, the list
`Reverse[Select[s, # < s[[n]] &]]` with `s = (p(1), …, p(z))` is exactly
`scanList n = [p(n-1), …, p(1)]`. -/
theorem scanList_eq_select (n z : ℕ) (hn : 1 ≤ n) (hz : n ≤ z) :
    (((List.range' 1 z).map P).filter (fun v => v < P n)).reverse = scanList n := by
  have hsplit : List.range' 1 z = List.range' 1 (n - 1) ++ List.range' n (z - (n - 1)) := by
    have happ := List.range'_append (s := 1) (m := n - 1) (n := z - (n - 1)) (step := 1)
    rw [show 1 + 1 * (n - 1) = n by omega, show n - 1 + (z - (n - 1)) = z by omega] at happ
    exact happ.symm
  rw [hsplit, List.map_append, List.filter_append]
  have hlow : ((List.range' 1 (n - 1)).map P).filter (fun v => v < P n) =
      (List.range' 1 (n - 1)).map P := by
    rw [List.filter_eq_self]
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range'_1] at hj
    simpa using (P_lt_P_iff j n (by omega) hn).mpr (by omega)
  have hhigh : ((List.range' n (z - (n - 1))).map P).filter (fun v => v < P n) = [] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range'_1] at hj
    have hnot : ¬ P j < P n := fun h => by
      have := (P_lt_P_iff j n (by omega) hn).mp h
      omega
    simpa using hnot
  rw [hlow, hhigh, List.append_nil, scanList, List.range'_eq_map_range, List.map_map,
    List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, add_comm]

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A242258, Clark Kimberling, May 2014).**

Verbatim: "Conjecture: A000041(n) is A000041-greedy summable for n >= 3."

For every `n ≥ 3`, starting from `r = p(n)` and scanning `p(n-1), …, p(1)` in
decreasing order, subtracting each `p(k)` with `p(k) ≤ r`, ends with residue
`0`.  The guard `3 ≤ n` is load-bearing: at `n = 2` the residue is `1`
(`greedyResidue_two`). -/
theorem A242258_conjecture (n : ℕ) (hn : 3 ≤ n) :
    greedyResidue (P n) (scanList n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hshift : ∀ k, ∑ j ∈ Finset.range (k + 1), P j = 1 + ∑ i ∈ Finset.range k, P (i + 1) := by
    intro k
    rw [Finset.sum_range_succ', P_zero, add_comm]
  unfold scanList
  rw [Nat.add_sub_cancel]
  apply greedyResidue_eq_zero_of_brown P m
  · intro k hk
    rw [← hshift]
    exact (P_sum_bounds (k + 1) (by omega)).1
  · have hlt := (P_sum_bounds (m + 1) (by omega)).2 hn
    rw [hshift] at hlt
    omega

/-- **Kimberling's conjecture, in the literal Mathematica form.**  For `n ≥ 3`
and any table length `z ≥ n`,
`Fold[If[#1 - #2 >= 0, #1 - #2, #1] &, s[[n]], Reverse[Select[s, # < s[[n]] &]]]`
with `s = (p(1), …, p(z))` equals `0`. -/
theorem A242258_conjecture_select (n z : ℕ) (hn : 3 ≤ n) (hz : n ≤ z) :
    greedyResidue (P n) (((List.range' 1 z).map P).filter (fun v => v < P n)).reverse = 0 := by
  rw [scanList_eq_select n z (by omega) hz]
  exact A242258_conjecture n hn

/-! ## Sanity layer -/

/-- The excluded case `n = 2`: `p(2) = 2` and the scan `[p(1)] = [1]` leaves
residue `1`, so the guard `3 ≤ n` cannot be dropped. -/
theorem greedyResidue_two : greedyResidue (P 2) (scanList 2) = 1 := by
  simp [scanList, greedyResidue, P_two, P_one]

-- Non-vacuity at the boundary `n = 3`: `3 - 2 - 1 = 0` on concrete values.
example : greedyResidue (P 3) (scanList 3) = 0 := by
  rw [show scanList 3 = [P 2, P 1] from rfl, P_three, P_two, P_one]
  decide

end Candidates.A242258DistinctGreedyAlgorithm
