/-
# A360070 — Gus Wiseman: no squarefree term greater than 1

## OEIS source (retrieved 2026-10-21 with `oeis show A360070` and the live
## entry https://oeis.org/A360070/internal)

```
NAME:     Numbers for which there exists an integer partition such that the
          parts have the same mean as the multiplicities.
TERMS:    1,4,8,9,12,16,18,20,25,27,32,36,45,48,49,50,54,63,64,72,75,80,81,
          90,96,98,99,100,108,112,117,121,125,128,144,147,150,160,162,169,175,
          176,180,192,196,200,208,216,224,225,240,242,243,245,250,252,256,272
COMMENT:  Conjecture: No term > 1 is squarefree.
EXAMPLE:  A partition of 20 with the same mean as its multiplicities is
          (5,4,3,2,1,1,1,1,1,1), so 20 is in the sequence.
MATHEMATICA:
          Select[Range[30],Select[IntegerPartitions[#],
            Mean[#]==Mean[Length/@Split[#]]&]!={}&]
AUTHOR:   _Gus Wiseman_, Jan 27 2023
```

The conjecture comment carries no separate signature; it belongs to the
original submission by Gus Wiseman (Jan 27 2023).

## Status

Triage (2026-10-21): open as far as the entry and the literature go; no
proof or refutation on the live OEIS page.

## Mathematics

For a partition of `n` with `L` parts and `k` distinct parts, the mean of
the parts is `n / L` and the mean of the multiplicities is `L / k` (the
multiplicities sum to `L`).  Equality is `n * k = L ^ 2`.  If `n` is
squarefree, `n ∣ L ^ 2` forces `n ∣ L`; as `L ≤ n` this gives `L = n`, so
every part is `1`, hence `k = 1` and `n = n ^ 2`, i.e. `n = 1`.
This file proves it (`not_isTerm_of_squarefree`), together with the full
characterization `isTerm_iff`: `n` is a term iff some `0 < k ≤ L` satisfy
`n * k = L ^ 2` and `2 (L - k) + k (k + 1) ≤ 2 n`.

Computation (2026-10-21, Python brute force over all partitions): the set of
terms for `n ≤ 60` matches the entry exactly, and no squarefree `n` in
`[2, 60]` is a term.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A360070GusWisemanSquarefree

/-! ## Definition layer -/

/-- The mean of the parts of a partition `p` of `n`, counted with
multiplicity: `(sum of parts) / (number of parts)`, in `ℚ`. -/
def partsMean {n : ℕ} (p : n.Partition) : ℚ :=
  (p.parts.sum : ℚ) / (Multiset.card p.parts : ℚ)

/-- The multiset of multiplicities of a partition: one entry
`count a p.parts` for each distinct part `a` (Mathematica's
`Length /@ Split[#]`). -/
def multiplicities {n : ℕ} (p : n.Partition) : Multiset ℕ :=
  p.parts.toFinset.val.map fun a => p.parts.count a

/-- The mean of the multiplicities of a partition, in `ℚ`. -/
def multMean {n : ℕ} (p : n.Partition) : ℚ :=
  ((multiplicities p).sum : ℚ) / (Multiset.card (multiplicities p) : ℚ)

/-- `n` is a term of A360070: `n` is positive (the entry has offset `1`, and
both means of the empty partition of `0` are the junk value `0 / 0`) and some
integer partition of `n` has the mean of its parts equal to the mean of its
multiplicities. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ ∃ p : n.Partition, partsMean p = multMean p

/-! ## Ground truth -/

/-- The partition `(2,2)` of `4`. -/
def p4 : (4 : ℕ).Partition where
  parts := {2, 2}
  parts_pos := by
    intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      or_self] at hi
    omega
  parts_sum := by decide

/-! ## Core lemmas -/

/-- The multiplicities of a partition sum to its number of parts. -/
theorem sum_multiplicities {n : ℕ} (p : n.Partition) :
    (multiplicities p).sum = Multiset.card p.parts := by
  simpa [multiplicities, Finset.sum_eq_multiset_sum] using
    Multiset.toFinset_sum_count_eq p.parts

/-- There is one multiplicity per distinct part. -/
theorem card_multiplicities {n : ℕ} (p : n.Partition) :
    Multiset.card (multiplicities p) = p.parts.toFinset.card := by
  simp only [multiplicities, Multiset.card_map]
  rfl

/-- A partition of `n` has at most `n` parts. -/
theorem card_parts_le {n : ℕ} (p : n.Partition) : Multiset.card p.parts ≤ n := by
  have h := Multiset.card_nsmul_le_sum (a := 1) (fun x hx => p.parts_pos hx)
  simpa [p.parts_sum] using h

/-- A partition of a positive `n` has at least one part. -/
theorem card_parts_pos {n : ℕ} (hn : 0 < n) (p : n.Partition) :
    0 < Multiset.card p.parts := by
  rw [Multiset.card_pos]
  rintro h
  have hs := p.parts_sum
  rw [h, Multiset.sum_zero] at hs
  omega

/-- A partition of a positive `n` has at least one distinct part. -/
theorem card_toFinset_pos {n : ℕ} (hn : 0 < n) (p : n.Partition) :
    0 < p.parts.toFinset.card := by
  have h := card_parts_pos hn p
  rw [Multiset.card_pos] at h
  exact Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr h)

/-- For a partition of a positive `n` with `L` parts and `k` distinct parts,
the parts and the multiplicities have the same mean iff `n * k = L ^ 2`. -/
theorem partsMean_eq_multMean_iff {n : ℕ} (hn : 0 < n) (p : n.Partition) :
    partsMean p = multMean p ↔
      n * p.parts.toFinset.card = Multiset.card p.parts ^ 2 := by
  have hL : (0 : ℚ) < Multiset.card p.parts := by exact_mod_cast card_parts_pos hn p
  have hk : (0 : ℚ) < p.parts.toFinset.card := by exact_mod_cast card_toFinset_pos hn p
  rw [partsMean, multMean, sum_multiplicities, card_multiplicities, p.parts_sum,
    div_eq_div_iff hL.ne' hk.ne']
  rw [sq]
  norm_cast

/-- A multiset of positive naturals whose sum equals its cardinality consists
of ones. -/
theorem eq_one_of_sum_eq_card (s : Multiset ℕ) (hpos : ∀ a ∈ s, 0 < a)
    (h : s.sum = Multiset.card s) : ∀ a ∈ s, a = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have ht : Multiset.card t ≤ t.sum := by
      simpa using Multiset.card_nsmul_le_sum (a := 1)
        (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
    have hb : 0 < b := hpos b (Multiset.mem_cons_self b t)
    rw [Multiset.sum_cons, Multiset.card_cons] at h
    intro a ha
    rcases Multiset.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih (fun x hx => hpos x (Multiset.mem_cons_of_mem hx)) (by omega) a ha

/-! ## Helpers for the characterization -/

/-- `k` distinct positive naturals have sum at least `k (k + 1) / 2`. -/
theorem card_mul_succ_le_two_mul_sum (s : Finset ℕ) (hpos : ∀ a ∈ s, 0 < a) :
    s.card * (s.card + 1) ≤ 2 * ∑ a ∈ s, a := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hsub : s ⊆ Finset.Ico 1 a := fun x hx =>
      Finset.mem_Ico.mpr ⟨hpos x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hcard : s.card ≤ a - 1 := by simpa using Finset.card_le_card hsub
    have hapos : 0 < a := hpos a (Finset.mem_insert_self a s)
    have hca : s.card + 1 ≤ a := by omega
    have ih' := ih (fun x hx => hpos x (Finset.mem_insert_of_mem hx))
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    nlinarith

/-- A partition of `n` with `L` parts and `k` distinct parts satisfies
`2 (L - k) + k (k + 1) ≤ 2 n`: the distinct parts contribute at least
`1 + 2 + ⋯ + k` and each repeated part at least `1`. -/
theorem two_mul_sub_add_le {n : ℕ} (p : n.Partition) :
    2 * (Multiset.card p.parts - p.parts.toFinset.card) +
      p.parts.toFinset.card * (p.parts.toFinset.card + 1) ≤ 2 * n := by
  set D := p.parts.dedup with hD
  set R := p.parts - D with hR
  have hDle : D ≤ p.parts := Multiset.dedup_le p.parts
  have hsplit : p.parts = D + R := (add_tsub_cancel_of_le hDle).symm
  have hsum : D.sum + R.sum = n := by rw [← Multiset.sum_add, ← hsplit, p.parts_sum]
  have hDsum : D.sum = ∑ a ∈ p.parts.toFinset, a := by
    rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.map_id']
  have hRcard : Multiset.card R = Multiset.card p.parts - p.parts.toFinset.card := by
    rw [hR, Multiset.card_sub hDle, Multiset.card_toFinset]
  have hRsum : Multiset.card R ≤ R.sum := by
    simpa using Multiset.card_nsmul_le_sum (a := 1) (s := R)
      (fun x hx => p.parts_pos (Multiset.mem_of_le tsub_le_self hx))
  have hdist := card_mul_succ_le_two_mul_sum p.parts.toFinset
    (fun a ha => p.parts_pos (Multiset.mem_toFinset.mp ha))
  omega

/-- If `0 < k ≤ L`, `n * k = L ^ 2` and `2 (L - k) + k (k + 1) ≤ 2 n`, then
`n` is a term.  For `k = 1` take `L` copies of `L`; for `k ≥ 2` take the parts
`1, 2, …, k - 1`, `L - k` further ones, and one large part `m ≥ k`. -/
theorem isTerm_of_bounds {n L k : ℕ} (hk : 0 < k) (hkL : k ≤ L)
    (hsq : n * k = L ^ 2) (hbd : 2 * (L - k) + k * (k + 1) ≤ 2 * n) : IsTerm n := by
  have hLpos : 0 < L := lt_of_lt_of_le hk hkL
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, zero_mul] at hsq
      exact absurd hsq.symm (pow_ne_zero 2 hLpos.ne')
    · exact h0
  refine ⟨hnpos, ?_⟩
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `k = 1`: the partition `(L, L, …, L)` of `n = L ^ 2`.
    have hk1' : k = 1 := by omega
    subst hk1'
    let p : n.Partition :=
      { parts := Multiset.replicate L L
        parts_pos := fun {i} hi => by
          rw [Multiset.eq_of_mem_replicate hi]
          exact hLpos
        parts_sum := by
          rw [Multiset.sum_replicate, smul_eq_mul, ← sq, ← hsq, mul_one] }
    refine ⟨p, (partsMean_eq_multMean_iff hnpos p).mpr ?_⟩
    have hcard : Multiset.card p.parts = L := Multiset.card_replicate L L
    have htf : p.parts.toFinset.card = 1 := by
      simp only [p, Multiset.toFinset_replicate, hLpos.ne', if_false,
        Finset.card_singleton]
    rw [hcard, htf, hsq]
  · -- `k ≥ 2`: the parts `1, …, k - 1`, a part `m ≥ k`, and `L - k` ones.
    set T := ∑ x ∈ Finset.Ico 1 k, x with hTdef
    have hT : 2 * T + 2 * k = k * (k + 1) := by
      have hr := Finset.sum_range_id_mul_two k
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk] at hr
      simp only [zero_add, ← hTdef] at hr
      have hkk : k * (k - 1) + 2 * k = k * (k + 1) := by
        cases k with
        | zero => omega
        | succ j => simp only [Nat.add_sub_cancel]; ring
      omega
    set m := n - (L - k) - T with hm
    have hmk : k ≤ m := by
      generalize k * (k + 1) = P at hT hbd
      omega
    have hmD : m ∉ Finset.Ico 1 k := fun h => by
      rw [Finset.mem_Ico] at h
      omega
    let D : Finset ℕ := insert m (Finset.Ico 1 k)
    have hDcard : D.card = k := by
      simp only [D, Finset.card_insert_of_notMem hmD, Nat.card_Ico]
      omega
    have hDsum : ∑ x ∈ D, x = m + T := by
      simp only [D, Finset.sum_insert hmD, hTdef]
    have h1D : 1 ∈ D := Finset.mem_insert_of_mem (Finset.mem_Ico.mpr ⟨le_rfl, hk2⟩)
    let p : n.Partition :=
      { parts := D.val + Multiset.replicate (L - k) 1
        parts_pos := fun {i} hi => by
          rcases Multiset.mem_add.mp hi with hi | hi
          · rcases Finset.mem_insert.mp (Finset.mem_val.mp hi) with hi | hi
            · omega
            · exact (Finset.mem_Ico.mp hi).1
          · rw [Multiset.eq_of_mem_replicate hi]
            exact Nat.one_pos
        parts_sum := by
          have hval : D.val.sum = ∑ x ∈ D, x := by
            rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
          rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one, hval, hDsum]
          generalize k * (k + 1) = P at hT hbd
          omega }
    refine ⟨p, (partsMean_eq_multMean_iff hnpos p).mpr ?_⟩
    have hcard : Multiset.card p.parts = L := by
      simp only [p, Multiset.card_add, Finset.card_val, hDcard, Multiset.card_replicate]
      omega
    have htf : p.parts.toFinset = D := by
      simp only [p, Multiset.toFinset_add, Finset.val_toFinset, Multiset.toFinset_replicate]
      split_ifs
      · exact Finset.union_empty D
      · exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr h1D)
    rw [hcard, htf, hDcard, hsq]

/-- **Characterization of A360070.** `n` is a term iff there are `L, k` with
`0 < k ≤ L`, `n * k = L ^ 2` and `2 (L - k) + k (k + 1) ≤ 2 n` (`L` is the
number of parts and `k` the number of distinct parts of a witness). -/
theorem isTerm_iff (n : ℕ) :
    IsTerm n ↔ ∃ L k : ℕ, 0 < k ∧ k ≤ L ∧ n * k = L ^ 2 ∧
      2 * (L - k) + k * (k + 1) ≤ 2 * n := by
  constructor
  · rintro ⟨hn, p, hp⟩
    exact ⟨Multiset.card p.parts, p.parts.toFinset.card, card_toFinset_pos hn p,
      Multiset.toFinset_card_le p.parts, (partsMean_eq_multMean_iff hn p).mp hp,
      two_mul_sub_add_le p⟩
  · rintro ⟨L, k, hk, hkL, hsq, hbd⟩
    exact isTerm_of_bounds hk hkL hsq hbd

/-- Bounded (decidable) form of `isTerm_iff`: the witnesses satisfy
`L ≤ n`. -/
theorem isTerm_iff_bounded (n : ℕ) :
    IsTerm n ↔ ∃ L ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (L + 1), 0 < k ∧
      n * k = L ^ 2 ∧ 2 * (L - k) + k * (k + 1) ≤ 2 * n := by
  rw [isTerm_iff]
  constructor
  · rintro ⟨L, k, hk, hkL, hsq, hbd⟩
    have hLn : L ≤ n := by
      have hLpos : 0 < L := lt_of_lt_of_le hk hkL
      have h1 : L * L ≤ n * L := by
        rw [← sq, ← hsq]
        exact Nat.mul_le_mul_left n hkL
      exact Nat.le_of_mul_le_mul_right h1 hLpos
    exact ⟨L, Finset.mem_range.mpr (Nat.lt_succ_of_le hLn), k,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hkL), hk, hsq, hbd⟩
  · rintro ⟨L, -, k, hk, hk0, hsq, hbd⟩
    exact ⟨L, k, hk0, Nat.le_of_lt_succ (Finset.mem_range.mp hk), hsq, hbd⟩

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A360070, Gus Wiseman, Jan 27 2023), proved.**

Verbatim: "Conjecture: No term > 1 is squarefree."

For every squarefree `n > 1`, no integer partition of `n` has the mean of its
parts (counted with multiplicity) equal to the mean of its multiplicities.
The guard `1 < n` is from the source: `n = 1` is squarefree and is a term
(the partition `(1)`). -/
theorem not_isTerm_of_squarefree {n : ℕ} (hn : 1 < n) (hsq : Squarefree n) :
    ¬ IsTerm n := by
  rintro ⟨hn0, p, hp⟩
  set L := Multiset.card p.parts with hLdef
  set k := p.parts.toFinset.card with hkdef
  have hkL : n * k = L ^ 2 := (partsMean_eq_multMean_iff hn0 p).mp hp
  -- `n ∣ L ^ 2`, hence `n ∣ L` by squarefreeness.
  have hdvd : n ∣ L := (hsq.dvd_pow_iff_dvd two_ne_zero).mp ⟨k, hkL.symm⟩
  have hLpos : 0 < L := card_parts_pos hn0 p
  have hLle : L ≤ n := card_parts_le p
  have hLeq : L = n := le_antisymm hLle (Nat.le_of_dvd hLpos hdvd)
  -- `L = n` forces every part to be `1`, so there is one distinct part.
  have hones : ∀ a ∈ p.parts, a = 1 :=
    eq_one_of_sum_eq_card p.parts (fun a ha => p.parts_pos ha)
      (by rw [p.parts_sum, ← hLdef, hLeq])
  have hk1 : k ≤ 1 := by
    rw [hkdef, Finset.card_le_one]
    intro a ha b hb
    rw [Multiset.mem_toFinset] at ha hb
    rw [hones a ha, hones b hb]
  -- Then `n * k = n ^ 2` with `k ≤ 1` contradicts `1 < n`.
  rw [hLeq] at hkL
  nlinarith

/-- The partition `(1)` of `1` witnesses that `1` is a term, so the guard
`1 < n` in `not_isTerm_of_squarefree` is needed. -/
example : IsTerm 1 :=
  ⟨by norm_num, Nat.Partition.indiscrete 1,
    (partsMean_eq_multMean_iff (by norm_num) _).mpr (by decide)⟩

/-- `6 = 2 * 3` is squarefree, so the hypotheses of
`not_isTerm_of_squarefree` are jointly satisfiable. -/
example : 1 < 2 ∧ Squarefree 2 := ⟨by norm_num, Nat.prime_two.prime.squarefree⟩

example : IsTerm 4 :=
  ⟨by norm_num, p4, (partsMean_eq_multMean_iff (by norm_num) p4).mpr (by decide)⟩

/-- The entry's example partition `(5,4,3,2,1,1,1,1,1,1)` of `20`. -/
def p20 : (20 : ℕ).Partition where
  parts := {5, 4, 3, 2, 1, 1, 1, 1, 1, 1}
  parts_pos := by
    intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
    omega
  parts_sum := by decide

/-- Ground truth for `multiplicities`: the multiplicities of the entry's
example partition of `20` are `1, 1, 1, 1, 6`. -/
example : multiplicities p20 = {1, 1, 1, 1, 6} := by decide

/-- Ground truth (entry EXAMPLE): the partition `(5,4,3,2,1,1,1,1,1,1)` has
parts mean `20 / 10 = 2` and multiplicities mean `10 / 5 = 2`. -/
example : partsMean p20 = 2 ∧ multMean p20 = 2 := by
  have hm : multiplicities p20 = {1, 1, 1, 1, 6} := by decide
  constructor
  · rw [partsMean, p20.parts_sum, show Multiset.card p20.parts = 10 by decide]
    norm_num
  · rw [multMean, hm]
    norm_num

/-- Ground truth: the terms of A360070 below `31` are exactly the first ten
listed terms `1, 4, 8, 9, 12, 16, 18, 20, 25, 27`. -/
example : ∀ n < 31, IsTerm n ↔ n ∈ ({1, 4, 8, 9, 12, 16, 18, 20, 25, 27} : Finset ℕ) := by
  intro n hn
  rw [isTerm_iff_bounded]
  interval_cases n <;> decide

end Candidates.A360070GusWisemanSquarefree
