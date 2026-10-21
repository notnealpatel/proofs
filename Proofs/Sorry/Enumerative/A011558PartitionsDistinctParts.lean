/-
# A011558 — Mathar: distinct-part partitions into terms of A084215

## OEIS source (retrieved with `oeis show A011558`, 2026-10-21)

```
NAME:     Expansion of (x + x^3)/(1 + x + ... + x^4) mod 2.
TERMS:    0,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0,...
COMMENT:  Characteristic function of numbers coprime to 5.
          - _Reinhard Zumkeller_, Nov 30 2009
FORMULA:  O.g.f.: x*(1+x+x^2+x^3)/(1-x^5). - _Wolfdieter Lang_, Feb 05 2009
FORMULA:  a(n) = sgn(n mod 5). - _Wesley Ivan Hurt_, Jun 30 2013
COMMENT (the conjecture):
  Conjecture: a(n+1) is the number of ways of partitioning n into distinct
  parts of A084215. - _R. J. Mathar_, Mar 01 2023
```

A084215 (`oeis show A084215`): "Expansion of g.f.: (1+x^2)/(1-2*x)",
terms `1, 2, 5, 10, 20, 40, 80, 160, …`; formula
"a(n) = 2*a(n-1) for n >= 3, a(0) = 1, a(1) = 2, a(2) = 5"
(Philippe Deléham, Mar 13 2013).

## Status

Triage: open (no proof in the entry or in the literature as far as the
triage could tell).  Computation: the claim holds for every `n ≤ 20000`
(subset-sum DP over the 14 terms of A084215 below 20000, 2026-10-21).
This module proves the conjecture in full (`mathar_conjecture`).

## Proof

Index a distinct-part partition by the finite set `S` of indices `k` with
`A084215(k)` a part (A084215 is strictly increasing, so this is a bijection,
`toPartition_bijective`).  Writing `x = ∑_{k ∈ S} 2^k`, the parts sum to
`x % 4 + 5 * (x / 4)` (`indexSum_eq`): the indices `0, 1` contribute the two
low bits of `x` unchanged and every index `k ≥ 2` contributes
`5 * 2^(k-2)`.  Since `S ↦ x` is a bijection `Finset ℕ ≃ ℕ`
(`Finset.equivBitIndices`), the count equals the number of `x` with
`x % 4 + 5 * (x / 4) = n`, which is `0` when `n % 5 = 4` and `1` otherwise.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A011558PartitionsDistinctParts

/-! ## Definition layer -/

/-- A011558, in the form `a(n) = sgn(n mod 5)` (Hurt; equivalently the
expansion of the O.g.f. `x*(1+x+x^2+x^3)/(1-x^5)`, Lang): the period-5
sequence `0, 1, 1, 1, 1, …`. -/
def a011558 (n : ℕ) : ℕ := if n % 5 = 0 then 0 else 1

/-- Ground truth: the first 30 listed terms of A011558. -/
example : (List.range 30).map a011558 =
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1,
      0, 1, 1, 1, 1] := by
  decide

/-- A084215, by Deléham's recurrence: `a(0) = 1`, `a(1) = 2`, and
`a(k + 2) = 5 * 2^k` (so `a(n) = 2 * a(n-1)` for `n ≥ 3`, `a(2) = 5`). -/
def a084215 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 5 * 2 ^ k

/-- Ground truth: the first 12 listed terms of A084215. -/
example : (List.range 12).map a084215 =
    [1, 2, 5, 10, 20, 40, 80, 160, 320, 640, 1280, 2560] := by
  decide

/-- A partition `p` of `n` is a partition into distinct parts of A084215 when
its parts are pairwise distinct and each part is a term of A084215. -/
def DistinctA084215 {n : ℕ} (p : n.Partition) : Prop :=
  p.parts.Nodup ∧ ∀ i ∈ p.parts, i ∈ Set.range a084215

/-- Non-vacuity: `8 = 1 + 2 + 5` is a partition of `8` into distinct parts of
A084215. -/
example : ∃ p : Nat.Partition 8, DistinctA084215 p :=
  ⟨⟨{1, 2, 5}, by decide, by decide⟩, by decide,
    by
      intro i hi
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩⟩

/-! ## Index sets -/

/-- The sum of the A084215 terms indexed by the finite set `S`. -/
def indexSum (S : Finset ℕ) : ℕ := ∑ k ∈ S, a084215 k

/-- Independent finite check of the index-set count: for `n < 30` exactly
`a(n + 1)` subsets of `{0, …, 4}` index a sum equal to `n` (indices `≥ 5`
give parts `≥ 40`, so no other index set is relevant). -/
example : ∀ n ∈ Finset.range 30,
    ((Finset.range 5).powerset.filter (fun S => indexSum S = n)).card =
      a011558 (n + 1) := by
  decide

/-- Load-bearing identity: with `x = ∑_{k ∈ S} 2^k`, the A084215 terms indexed
by `S` sum to `x % 4 + 5 * (x / 4)`. -/
theorem indexSum_eq (S : Finset ℕ) :
    indexSum S = (∑ k ∈ S, 2 ^ k) % 4 + 5 * ((∑ k ∈ S, 2 ^ k) / 4) := by
  have hsplitA := Finset.sum_filter_add_sum_filter_not S (fun k => k < 2) a084215
  have hsplitB := Finset.sum_filter_add_sum_filter_not S (fun k => k < 2) (fun k => 2 ^ k)
  set A := ∑ k ∈ S.filter (fun k => k < 2), 2 ^ k with hA
  set m := ∑ k ∈ S.filter (fun k => ¬ k < 2), 2 ^ (k - 2) with hm
  have hlowEq : ∑ k ∈ S.filter (fun k => k < 2), a084215 k = A := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : k < 2 := (Finset.mem_filter.mp hk).2
    interval_cases k <;> rfl
  have hlowLe : A ≤ 3 := by
    calc A ≤ ∑ k ∈ Finset.range 2, 2 ^ k :=
          Finset.sum_le_sum_of_subset (fun k hk => by
            simp only [Finset.mem_filter] at hk
            simpa using hk.2)
      _ = 3 := by decide
  have hhighA : ∑ k ∈ S.filter (fun k => ¬ k < 2), a084215 k = 5 * m := by
    rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    simp [a084215, add_comm]
  have hhighB : ∑ k ∈ S.filter (fun k => ¬ k < 2), 2 ^ k = 4 * m := by
    rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add]
    simp
  unfold indexSum
  rw [← hsplitA, ← hsplitB, hlowEq, hhighA, hhighB]
  omega

/-- Arithmetic core: the map `x ↦ x % 4 + 5 * (x / 4)` hits `n` exactly once
when `n % 5 ≠ 4` (at `x = n % 5 + 4 * (n / 5)`) and never when `n % 5 = 4`. -/
theorem fiber_card (n : ℕ) :
    Nat.card {x : ℕ // x % 4 + 5 * (x / 4) = n} = if n % 5 = 4 then 0 else 1 := by
  split_ifs with h
  · haveI : IsEmpty {x : ℕ // x % 4 + 5 * (x / 4) = n} :=
      ⟨fun ⟨x, hx⟩ => by omega⟩
    exact Nat.card_of_isEmpty
  · have e : {x : ℕ // x % 4 + 5 * (x / 4) = n} ≃ {x : ℕ // x = n % 5 + 4 * (n / 5)} :=
      Equiv.subtypeEquivRight fun x => by omega
    rw [Nat.card_congr e, Nat.card_unique]

/-- The number of finite index sets `S ⊆ ℕ` whose A084215 terms sum to `n` is
`0` if `n % 5 = 4` and `1` otherwise. -/
theorem indexSet_card (n : ℕ) :
    Nat.card {S : Finset ℕ // indexSum S = n} = if n % 5 = 4 then 0 else 1 := by
  have e : {S : Finset ℕ // indexSum S = n} ≃ {x : ℕ // x % 4 + 5 * (x / 4) = n} :=
    Equiv.subtypeEquiv Finset.equivBitIndices.symm fun S => by
      rw [Finset.equivBitIndices_symm_apply, indexSum_eq]
  rw [Nat.card_congr e, fiber_card]

/-! ## Index sets versus partitions -/

/-- Every term of A084215 is positive. -/
theorem a084215_pos (k : ℕ) : 0 < a084215 k := by
  rcases k with _ | _ | k <;> simp [a084215]

/-- A084215 is strictly increasing. -/
theorem a084215_strictMono : StrictMono a084215 := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rcases k with _ | _ | k
  · decide
  · decide
  · simp only [a084215, pow_succ]
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    omega

/-- The partition of `n` whose parts are the A084215 terms indexed by `S`. -/
def toPartition (n : ℕ) (S : {S : Finset ℕ // indexSum S = n}) :
    {p : n.Partition // DistinctA084215 p} :=
  ⟨⟨S.1.val.map a084215, fun hi => by
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hi
      exact a084215_pos k,
    by rw [← Finset.sum_eq_multiset_sum]; exact S.2⟩,
   S.1.nodup.map a084215_strictMono.injective,
   fun i hi => by
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hi
      exact ⟨k, rfl⟩⟩

/-- Index sets summing to `n` correspond bijectively to partitions of `n` into
distinct parts of A084215. -/
theorem toPartition_bijective (n : ℕ) : Function.Bijective (toPartition n) := by
  constructor
  · rintro ⟨S, hS⟩ ⟨T, hT⟩ h
    have hparts : S.val.map a084215 = T.val.map a084215 :=
      congrArg (fun q : {p : n.Partition // DistinctA084215 p} => q.1.parts) h
    have hval : S.val = T.val := Multiset.map_injective a084215_strictMono.injective hparts
    exact Subtype.ext (Finset.val_inj.mp hval)
  · rintro ⟨p, hnodup, hrange⟩
    let g : ℕ → ℕ := Function.invFun a084215
    have hgb : ∀ i ∈ p.parts, a084215 (g i) = i := fun i hi =>
      Function.invFun_eq (hrange i hi)
    have hmap : (p.parts.map g).map a084215 = p.parts := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id p.parts]
      exact Multiset.map_congr rfl fun i hi => hgb i hi
    have hnd : (p.parts.map g).Nodup :=
      hnodup.map_on fun i hi j hj hij => by rw [← hgb i hi, ← hgb j hj, hij]
    let S : Finset ℕ := ⟨p.parts.map g, hnd⟩
    have hS : indexSum S = n := by
      rw [indexSum, Finset.sum_eq_multiset_sum]
      change ((p.parts.map g).map a084215).sum = n
      rw [hmap, p.parts_sum]
    refine ⟨⟨S, hS⟩, Subtype.ext (Nat.Partition.ext ?_)⟩
    exact hmap

/-! ## The conjecture -/

/-- The number of partitions of `n` into distinct parts from A084215
`{1, 2, 5, 10, 20, 40, …}` is `0` if `n ≡ 4 (mod 5)` and `1` otherwise. -/
theorem card_distinctA084215_partitions (n : ℕ) :
    Nat.card {p : n.Partition // DistinctA084215 p} = if n % 5 = 4 then 0 else 1 := by
  rw [← Nat.card_eq_of_bijective (toPartition n) (toPartition_bijective n), indexSet_card]

/-- **Mathar's conjecture (A011558, R. J. Mathar, Mar 01 2023).**

Verbatim: "Conjecture: a(n+1) is the number of ways of partitioning n into
distinct parts of A084215."

For every `n ≥ 0`, the number of partitions of `n` into distinct parts, each a
term of A084215 `{1, 2, 5, 10, 20, 40, …}`, equals `A011558(n + 1)`. -/
theorem mathar_conjecture (n : ℕ) :
    Nat.card {p : n.Partition // DistinctA084215 p} = a011558 (n + 1) := by
  rw [card_distinctA084215_partitions, a011558]
  split_ifs with h4 h0 h0 <;> omega

end Candidates.A011558PartitionsDistinctParts
