/-
# Davenport constant of `(ℤ/p)^r` via Chevalley–Warning: `D = r(p-1)+1`

## Source

David J. Grynkiewicz, "A Generalization of the Chevalley-Warning and Ax-Katz
Theorems with a View Towards Combinatorial Number Theory", arXiv:2208.12895.
Section 1.2 (Introduction), Theorem `thm-dav-pgroup`, proved in Section 3
("Applications in Combinatorial Number Theory").  Retrieved 2026-10-21.

## Verbatim informal claim

"Let `G` be a finite abelian `p`-group. Then `D(G) = D*(G)`."
Here `D(G)` is "the minimal integer `ℓ` such that every sequence of `ℓ` terms
from `G` must contain a nontrivial subsequence whose terms sum to zero", and
`D*(G) = 1 + ∑_{i=1}^r (n_i - 1)` for `G = C_{n_1} ⊕ ⋯ ⊕ C_{n_r}`.
The lower bound: "the sequence `∏_{i ∈ [1,s]} e_i^{[q_i - 1]}` is zero-sum
free, showing `D(G) ≥ D*(G)`."

## Status

Known (Olson 1969; van Emde Boas–Kruyswijk 1967); reproved in the paper.
This module formalizes the elementary abelian case `G = (ℤ/p)^r`, where
`D*(G) = r(p-1)+1`, using Mathlib's Chevalley–Warning theorem (following the
template of Mathlib's Erdős–Ginzburg–Ziv proof) for the upper bound and the
basis sequence `∏_j e_j^{[p-1]}` for the lower bound.  The Davenport bound
vocabulary (`HasDavenportBound`, `ZeroSumFree`) is the repository's, from
`GroupCount.GaoGeroldingerRefutation`.
-/
import Mathlib
import GroupCount.GaoGeroldingerRefutation

set_option autoImplicit false

namespace DavenportElementaryAbelian

open Finset MvPolynomial GaoGeroldinger

variable {p r : ℕ} [Fact p.Prime]

/-! ## Upper bound via Chevalley–Warning -/

/-- The `j`-th Chevalley–Warning polynomial: `∑_{i ∈ s} a_i(j) • X_i^(p-1)`. -/
noncomputable def cwPoly {ι : Type*} (s : Finset ι) (a : ι → Fin r → ZMod p) (j : Fin r) :
    MvPolynomial s (ZMod p) :=
  ∑ i : s, a i j • X i ^ (p - 1)

/-- Ground truth for `cwPoly`: evaluating at `x` gives `∑_{i ∈ s} a_i(j) x_i^(p-1)`. -/
theorem eval_cwPoly {ι : Type*} (s : Finset ι) (a : ι → Fin r → ZMod p) (j : Fin r)
    (x : s → ZMod p) : eval x (cwPoly s a j) = ∑ i : s, a i j * x i ^ (p - 1) := by
  simp [cwPoly, map_sum]

/-- Each Chevalley–Warning polynomial has total degree at most `p - 1`. -/
theorem totalDegree_cwPoly_le {ι : Type*} (s : Finset ι) (a : ι → Fin r → ZMod p)
    (j : Fin r) : (cwPoly s a j).totalDegree ≤ p - 1 := by
  apply totalDegree_finsetSum_le
  rintro i _
  exact (totalDegree_smul_le ..).trans (totalDegree_X_pow ..).le

/-- **Chevalley–Warning form of `D((ℤ/p)^r) ≤ r(p-1)+1`.**  Every family of more
than `r(p-1)` vectors of `(ℤ/p)^r`, indexed by a finset `s`, has a nonempty
subfamily with zero sum. -/
theorem exists_nonempty_zero_sum {ι : Type*} (s : Finset ι) (a : ι → Fin r → ZMod p)
    (hs : r * (p - 1) < #s) : ∃ t ⊆ s, t.Nonempty ∧ ∑ i ∈ t, a i = 0 := by
  classical
  have hp : p.Prime := Fact.out
  let zero_sol : {x : s → ZMod p // ∀ j, eval x (cwPoly s a j) = 0} :=
    ⟨0, fun j => by simp [cwPoly, map_sum, hp.one_lt, tsub_eq_zero_iff_le]⟩
  have hdeg : (∑ j, (cwPoly s a j).totalDegree) < Fintype.card s := by
    calc (∑ j, (cwPoly s a j).totalDegree) ≤ ∑ _j : Fin r, (p - 1) :=
          Finset.sum_le_sum fun j _ => totalDegree_cwPoly_le s a j
      _ = r * (p - 1) := by simp
      _ < Fintype.card s := by simpa using hs
  -- Chevalley–Warning: `p` divides the number of common zeros.
  have hpN : p ∣ Nat.card {x : s → ZMod p // ∀ j, eval x (cwPoly s a j) = 0} := by
    simpa only [Fintype.card_eq_nat_card] using
      char_dvd_card_solutions_of_fintype_sum_lt p hdeg
  have hN₀ : 0 < Nat.card {x : s → ZMod p // ∀ j, eval x (cwPoly s a j) = 0} :=
    haveI : Nonempty {x : s → ZMod p // ∀ j, eval x (cwPoly s a j) = 0} := ⟨zero_sol⟩
    Nat.card_pos
  have hnt : Nontrivial {x : s → ZMod p // ∀ j, eval x (cwPoly s a j) = 0} :=
    Finite.one_lt_card_iff_nontrivial.1 (hp.one_lt.trans_le (Nat.le_of_dvd hN₀ hpN))
  -- A nonzero common zero `x`; its support is the required subfamily.
  obtain ⟨x, hx⟩ := exists_ne zero_sol
  refine ⟨({i | x.1 i ≠ 0} : Finset s).map ⟨(↑), Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · simp +contextual [subset_iff]
  · rw [Finset.map_nonempty]
    rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  · funext j
    have hj := x.2 j
    simpa [cwPoly, ZMod.pow_card_sub_one, Finset.sum_filter, Finset.sum_apply] using hj

/-- **Upper bound `D((ℤ/p)^r) ≤ r(p-1)+1`** (Olson; van Emde Boas–Kruyswijk;
arXiv:2208.12895, Theorem `thm-dav-pgroup`, elementary abelian case): every
sequence of at least `r(p-1)+1` terms of `(ℤ/p)^r` has a nonempty zero-sum
subsequence. -/
theorem hasDavenportBound (p r : ℕ) [Fact p.Prime] :
    HasDavenportBound (Fin r → ZMod p) (r * (p - 1) + 1) := by
  classical
  intro S hS
  obtain ⟨t, hts, htne, hsum⟩ :=
    exists_nonempty_zero_sum (s := S.toEnumFinset) Prod.fst (by simpa using hS)
  refine ⟨t.1.map Prod.fst, Multiset.map_fst_le_of_subset_toEnumFinset hts, ?_, ?_⟩
  · rw [Ne, Multiset.map_eq_zero, Finset.val_eq_zero]
    exact htne.ne_empty
  · rw [← Finset.sum_eq_multiset_sum]
    exact hsum

/-! ## Lower bound: the basis sequence -/

/-- The basis vector `e_j = (0, …, 0, 1, 0, …, 0)` of `(ℤ/p)^r`. -/
noncomputable def e (p r : ℕ) (j : Fin r) : Fin r → ZMod p := Pi.single j 1

/-- The extremal sequence `∏_j e_j^{[p-1]}`: each basis vector repeated `p - 1`
times. -/
noncomputable def basisSeq (p r : ℕ) : Multiset (Fin r → ZMod p) :=
  ∑ j : Fin r, Multiset.replicate (p - 1) (e p r j)

/-- Ground truth: in `(ℤ/3)^2`, `e_0 = (1, 0)` and `e_1 = (0, 1)`. -/
example : e 3 2 0 = ![1, 0] ∧ e 3 2 1 = ![0, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Ground truth: over `(ℤ/3)^2` the extremal sequence is `e_0^{[2]} e_1^{[2]}`. -/
example : basisSeq 3 2 = Multiset.replicate 2 (e 3 2 0) + Multiset.replicate 2 (e 3 2 1) := by
  simp [basisSeq, Fin.sum_univ_two]

/-- Ground truth, independent of the general proof: the length-4 sequence
`(1,0)^{[2]} (0,1)^{[2]}` over `(ℤ/3)^2` is zero-sum free (exhaustive check). -/
example : ZeroSumFree ({![1, 0], ![1, 0], ![0, 1], ![0, 1]} : Multiset (Fin 2 → ZMod 3)) := by
  rw [zeroSumFree_iff_powerset]
  decide

/-- Ground truth: in `(ℤ/3)^2` the length-5 sequence `(1,0)^{[2]} (0,1)^{[2]} (1,1)`
is not zero-sum free (e.g. the whole sequence sums to `0`). -/
example : ¬ ZeroSumFree
    ({![1, 0], ![1, 0], ![0, 1], ![0, 1], ![1, 1]} : Multiset (Fin 2 → ZMod 3)) := by
  rw [zeroSumFree_iff_powerset]
  decide

/-- The extremal sequence has length `r(p-1)`. -/
theorem card_basisSeq (p r : ℕ) : Multiset.card (basisSeq p r) = r * (p - 1) := by
  simp [basisSeq, Multiset.card_sum]

/-- Distinct indices give distinct basis vectors. -/
theorem e_inj {k j : Fin r} (h : e p r k = e p r j) : k = j := by
  have hj := congrFun h j
  by_contra hkj
  simp [e, Ne.symm hkj] at hj

/-- Coordinate `j` of `e_k` is the indicator of `e_k = e_j`. -/
theorem e_apply (k j : Fin r) :
    e p r k j = if e p r k = e p r j then 1 else 0 := by
  by_cases hkj : k = j
  · subst hkj
    simp [e]
  · have hne : e p r k ≠ e p r j := fun h => hkj (e_inj h)
    rw [if_neg hne]
    simp [e, Ne.symm hkj]

/-- Over a sequence of basis vectors, coordinate `j` of the sum counts the copies
of `e_j`. -/
theorem sum_apply_eq_count (j : Fin r) (t : Multiset (Fin r → ZMod p))
    (ht : ∀ x ∈ t, ∃ k, x = e p r k) : t.sum j = (t.count (e p r j) : ZMod p) := by
  classical
  induction t using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
    obtain ⟨k, rfl⟩ := ht x (Multiset.mem_cons_self _ _)
    have ih' := ih fun y hy => ht y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.sum_cons, Pi.add_apply, ih', Multiset.count_cons, e_apply k j]
    by_cases hkj : e p r k = e p r j
    · simp [hkj, add_comm]
    · simp [hkj, Ne.symm hkj]

omit [Fact p.Prime] in
/-- Every term of the extremal sequence is a basis vector. -/
theorem exists_eq_e_of_mem_basisSeq {x : Fin r → ZMod p} (hx : x ∈ basisSeq p r) :
    ∃ k, x = e p r k := by
  obtain ⟨k, -, hk⟩ := Multiset.mem_sum.1 hx
  exact ⟨k, Multiset.eq_of_mem_replicate hk⟩

/-- The extremal sequence contains exactly `p - 1` copies of `e_j`. -/
theorem count_basisSeq (j : Fin r) : (basisSeq p r).count (e p r j) = p - 1 := by
  classical
  rw [basisSeq, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [if_neg fun h => hkj (e_inj h)]
  · simp

/-- **Lower bound construction** (arXiv:2208.12895, proof of Theorem
`thm-dav-pgroup`): the sequence `∏_j e_j^{[p-1]}` over `(ℤ/p)^r` is zero-sum
free. -/
theorem zeroSumFree_basisSeq : ZeroSumFree (basisSeq p r) := by
  classical
  intro t hts htne hsum
  have hp : p.Prime := Fact.out
  have hmem : ∀ x ∈ t, ∃ k, x = e p r k := fun x hx =>
    exists_eq_e_of_mem_basisSeq (Multiset.subset_of_le hts hx)
  have hcount : ∀ j, t.count (e p r j) = 0 := by
    intro j
    have hj : (t.count (e p r j) : ZMod p) = 0 := by
      rw [← sum_apply_eq_count j t hmem, hsum, Pi.zero_apply]
    have hle : t.count (e p r j) ≤ p - 1 :=
      (Multiset.count_le_of_le _ hts).trans (count_basisSeq j).le
    have hdvd : p ∣ t.count (e p r j) := (ZMod.natCast_eq_zero_iff _ _).1 hj
    have hlt : t.count (e p r j) < p := by
      have := hp.one_lt
      omega
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  apply htne
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  obtain ⟨k, rfl⟩ := hmem x hx
  exact (Multiset.count_ne_zero.2 hx) (hcount k)

/-- **Lower bound `r(p-1) < D((ℤ/p)^r)`**: the length `r(p-1)` does not force a
nonempty zero-sum subsequence. -/
theorem not_hasDavenportBound (p r : ℕ) [Fact p.Prime] :
    ¬ HasDavenportBound (Fin r → ZMod p) (r * (p - 1)) := by
  have h := not_hasDavenportBound_of_zeroSumFree (zeroSumFree_basisSeq (p := p) (r := r))
  rwa [card_basisSeq] at h

/-- **`D((ℤ/p)^r) = r(p-1)+1`** (Olson 1969; van Emde Boas–Kruyswijk 1967;
reproved in arXiv:2208.12895, Theorem `thm-dav-pgroup`, here for elementary
abelian `p`-groups): `r(p-1)+1` is a Davenport bound for `(ℤ/p)^r` and
`r(p-1)` is not.  Since `HasDavenportBound` is upward closed in the length
(`HasDavenportBound.mono`), `r(p-1)+1` is the least Davenport bound. -/
theorem davenport_eq (p r : ℕ) [Fact p.Prime] :
    HasDavenportBound (Fin r → ZMod p) (r * (p - 1) + 1) ∧
      ¬ HasDavenportBound (Fin r → ZMod p) (r * (p - 1)) :=
  ⟨hasDavenportBound p r, not_hasDavenportBound p r⟩

/-- Non-vacuity: the hypotheses are jointly satisfiable at `p = 3`, `r = 2`, where
`D((ℤ/3)^2) = 5`. -/
example : HasDavenportBound (Fin 2 → ZMod 3) 5 ∧ ¬ HasDavenportBound (Fin 2 → ZMod 3) 4 :=
  davenport_eq 3 2

end DavenportElementaryAbelian
