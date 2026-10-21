/-
# Cyclic Hamilton decompositions of the carousel tournaments `T_33` and `T_35`

## Source

Hongci Liao, Yongju Peng, Guang Li, Yingbin Ma, *Cyclic Hamilton Cycle
Decompositions of Carousel Tournaments of Order pq*, arXiv:2610.07102.
Retrieved and read 2026-10-21.

* Introduction: for odd `n`, the carousel tournament is
  `T_n = Cay(ℤ_n, S_n)` with `S_n = {1, 2, …, (n-1)/2}`; there is an arc
  `(x, y)` iff `y - x ∈ S_n`.  A Hamilton cycle decomposition `𝒞` is
  *cyclic* if `C + 1 ∈ 𝒞` for every `C ∈ 𝒞` (Section 2).
* Problem 1.2 (verbatim): "For which odd integers `n` does the carousel
  tournament `T_n` admit a cyclic Hamilton cycle decomposition?"
* Theorem 1.3 (proved in the paper): for primes `7 ≤ p < q`, `T_{p,q}` has a
  cyclic Hamilton cycle decomposition.
* Concluding remarks (verbatim): "The remaining products `pq` with
  `p ∈ {3,5}`, and more generally all odd composite orders, remain open."

## Claim formalized here

`T_33` (`p = 3`, `q = 11`) and `T_35` (`p = 5`, `q = 7`) each admit a cyclic
Hamilton cycle decomposition.  These are cases the paper leaves **open**; the
witnesses are explicit base paths in the sense of the paper's Lemma 2.1
(`\label{bpd}`: directed base paths and their cyclic developments `𝒞(P)`), found by
computer search during triage and re-verified independently in Python on
2026-10-21 (`T_15` is excluded for this method by counting,
`p + q > (pq-1)/2`, and an exhaustive search found no two-long-path system
for `T_21`).

* `T_33`: base paths with difference sequences
  `[3,1,2,4,6,8,7,9,12,15,10]` (length 11), `[11,5,14]` (length 3),
  `[13]`, `[16]` (length 1).
* `T_35`: `[5,3,10,16,17,15,11]` (length 7), `[7,4,13,14,12]` (length 5),
  `[1]`, `[2]`, `[6]`, `[8]`, `[9]` (length 1).

## Status

Open in the source (concluding remarks).  Both cases are proved in this file
without `sorry`; the finite checks run by `decide +kernel` (no
`native_decide`).

## Encoding

A directed Hamilton cycle on the vertex set `ℤ_n` is encoded by its successor
permutation `σ`: a single cycle (`σ.IsCycle`) moving every vertex
(`σ.support = univ`), each of whose arcs `(x, σ x)` is an arc of `T_n`.  A
decomposition is a finite set of such permutations such that every arc of
`T_n` is `(x, σ x)` for exactly one member `σ`.  The translate `C + t` of a
cycle with successor `σ` has successor `x ↦ σ (x - t) + t`.
-/
import Mathlib

set_option autoImplicit false

namespace CarouselTournament

open Equiv Function

/-! ## Statement-level definitions -/

/-- The arc relation of the carousel tournament
`T_n = Cay(ℤ_n, {1, …, (n-1)/2})`: there is an arc `x → y` iff the
difference `y - x`, read as a residue in `{0, …, n-1}`, lies in
`{1, …, (n-1)/2}`. -/
def carouselArc (n : ℕ) (x y : ZMod n) : Prop :=
  (y - x).val ∈ Finset.Icc 1 ((n - 1) / 2)

instance (n : ℕ) : DecidableRel (carouselArc n) := fun _ _ => by
  unfold carouselArc; infer_instance

/-- A permutation `σ` of a finite vertex set is (the successor map of) a
directed Hamilton cycle of the digraph `Adj`: it is a single cycle through
every vertex and each step `x → σ x` is an arc. -/
def IsHamiltonCycle {V : Type*} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) (σ : Perm V) : Prop :=
  σ.IsCycle ∧ σ.support = Finset.univ ∧ ∀ x, Adj x (σ x)

/-- A finite family `D` of directed Hamilton cycles (encoded by successor
permutations) is a Hamilton decomposition of the digraph `Adj`: every member is
a Hamilton cycle and every arc `x → y` is used by exactly one member. -/
def IsHamiltonDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) (D : Finset (Perm V)) : Prop :=
  (∀ σ ∈ D, IsHamiltonCycle Adj σ) ∧ ∀ x y, Adj x y → ∃! σ, σ ∈ D ∧ σ x = y

/-- The translate `C + t` of the cycle with successor permutation `σ`:
conjugation by `x ↦ x + t`, so that `translate t σ x = σ (x - t) + t`. -/
def translate {n : ℕ} (t : ZMod n) (σ : Perm (ZMod n)) : Perm (ZMod n) :=
  Equiv.addRight t * σ * (Equiv.addRight t)⁻¹

/-- A cyclic Hamilton cycle decomposition of the carousel tournament `T_n`:
a Hamilton decomposition `D` of `T_n` closed under translation by `1`
(`C ∈ D → C + 1 ∈ D`), as in Section 2 of arXiv:2610.07102. -/
def IsCyclicHamiltonDecomposition (n : ℕ) [NeZero n]
    (D : Finset (Perm (ZMod n))) : Prop :=
  IsHamiltonDecomposition (carouselArc n) D ∧ ∀ σ ∈ D, translate 1 σ ∈ D

/-! ## Ground truth for the arc relation -/

example : carouselArc 33 0 16 := by decide
example : ¬ carouselArc 33 0 17 := by decide
example : carouselArc 33 30 1 := by decide
example : ¬ carouselArc 33 1 30 := by decide
example : carouselArc 35 34 16 := by decide
example : ¬ carouselArc 35 0 0 := by decide

/-- The successor map of a translate: `(C + t)` steps from `x` to
`σ (x - t) + t`. -/
@[simp]
theorem translate_apply {n : ℕ} (t : ZMod n) (σ : Perm (ZMod n)) (x : ZMod n) :
    translate t σ x = σ (x - t) + t := by
  simp [translate, Perm.mul_apply, sub_eq_add_neg]

/-! ## General lemmas -/

/-- A permutation whose powers carry one non-fixed vertex `x` to every vertex,
and all of whose steps are arcs, is a directed Hamilton cycle. -/
theorem isHamiltonCycle_of_forall_pow_eq {V : Type*} [Fintype V] [DecidableEq V]
    {Adj : V → V → Prop} (σ : Perm V) (x : V) (hne : σ x ≠ x)
    (hcov : ∀ y, ∃ k : ℕ, (σ ^ k) x = y) (harc : ∀ y, Adj y (σ y)) :
    IsHamiltonCycle Adj σ := by
  refine ⟨⟨x, hne, fun y _ => ?_⟩, ?_, harc⟩
  · obtain ⟨k, hk⟩ := hcov y
    exact ⟨k, by rw [zpow_natCast]; exact hk⟩
  · ext y
    simp only [Finset.mem_univ, iff_true, Perm.mem_support]
    intro hy
    obtain ⟨k, hk⟩ := hcov y
    apply hne
    have hstep : (σ ^ k) (σ x) = (σ ^ k) x := by
      calc (σ ^ k) (σ x) = (σ ^ (k + 1)) x := by rw [pow_succ, Perm.mul_apply]
        _ = σ ((σ ^ k) x) := by rw [pow_succ', Perm.mul_apply]
        _ = (σ ^ k) x := by rw [hk, hy]
    exact (σ ^ k).injective hstep

/-- Translating a Hamilton cycle of `T_n` gives a Hamilton cycle of `T_n`
(translations are automorphisms of the Cayley tournament). -/
theorem isHamiltonCycle_translate {n : ℕ} [NeZero n] (t : ZMod n)
    {σ : Perm (ZMod n)} (hσ : IsHamiltonCycle (carouselArc n) σ) :
    IsHamiltonCycle (carouselArc n) (translate t σ) := by
  obtain ⟨hcyc, hsupp, harc⟩ := hσ
  refine ⟨hcyc.conj, ?_, fun x => ?_⟩
  · rw [translate, Perm.support_conj, hsupp, Finset.map_univ_equiv]
  · have hdiff : translate t σ x - x = σ (x - t) - (x - t) := by
      rw [translate_apply]; ring
    have h := harc (x - t)
    unfold carouselArc at h ⊢
    rw [hdiff]
    exact h

/-- Assembly: a list `L` of Hamilton cycles of `T_n` such that, at every vertex
`x`, the successors `σ x` (`σ ∈ L`) are pairwise distinct and exhaust the
out-neighbours of `x`, and which is closed under translation by `1`, is a
cyclic Hamilton cycle decomposition of `T_n`. -/
theorem isCyclicHamiltonDecomposition_of_list {n : ℕ} [NeZero n]
    (L : List (Perm (ZMod n)))
    (hham : ∀ σ ∈ L, IsHamiltonCycle (carouselArc n) σ)
    (hnodup : ∀ x, (L.map fun σ => σ x).Nodup)
    (hcov : ∀ x y, carouselArc n x y → y ∈ L.map fun σ => σ x)
    (htr : ∀ σ ∈ L, translate 1 σ ∈ L) :
    IsCyclicHamiltonDecomposition n L.toFinset := by
  refine ⟨⟨fun σ hσ => hham σ (List.mem_toFinset.mp hσ), fun x y hxy => ?_⟩,
    fun σ hσ => List.mem_toFinset.mpr (htr σ (List.mem_toFinset.mp hσ))⟩
  obtain ⟨σ, hσL, hσx⟩ := List.mem_map.mp (hcov x y hxy)
  refine ⟨σ, ⟨List.mem_toFinset.mpr hσL, hσx⟩, fun τ ⟨hτ, hτx⟩ => ?_⟩
  exact List.inj_on_of_nodup_map (hnodup x) (List.mem_toFinset.mp hτ) hσL
    (hτx.trans hσx.symm)

/-! ## Directed base paths and their cyclic development (Lemma 2.1) -/

/-- For a difference sequence `δ = [δ₁, …, δ_d]` of a base path
`P = (v₀, …, v_d)` with `v₀ = 0` and `v_i = δ₁ + ⋯ + δ_i`, the residues
`[v₀]_d, …, [v_{d-1}]_d`, in order. -/
def basePositions (δ : List ℕ) : List ℕ :=
  (List.range δ.length).map fun i => (δ.take i).sum % δ.length

/-- The successor map of the Hamilton cycle `C(P) = P ∪ (P + h) ∪ ⋯` of
Lemma 2.1, `h = v_d`: a vertex `x` of `C(P)` is `v_i + j h` with `i < d`,
so `i` is located by `x ≡ v_i (mod d)` and the step from `x` is `δ_{i+1}`. -/
def devSucc (n : ℕ) (δ : List ℕ) (x : ZMod n) : ZMod n :=
  x + ((δ.getD ((basePositions δ).idxOf (x.val % δ.length)) 0 : ℕ) : ZMod n)

/-- Finite certificate that the development of `δ` is a Hamilton cycle of
`T_n`: the orbit of `0` under `devSucc n δ` reaches every vertex within `n`
steps and returns to `0` after `n` steps, `0` is not fixed, and every step is
an arc of `T_n`, and the cycle is invariant under translation by `d = |δ|`
(the stabilizer `dℤ_n` in the proof of Lemma 2.1). -/
def DevelopsToHamiltonCycle (n : ℕ) (δ : List ℕ) : Prop :=
  (∀ y : ZMod n, ∃ k < n, (devSucc n δ)^[k] 0 = y) ∧ (devSucc n δ)^[n] 0 = 0 ∧
    devSucc n δ 0 ≠ 0 ∧ (∀ x, carouselArc n x (devSucc n δ x)) ∧
    ∀ x, devSucc n δ (x - δ.length) + δ.length = devSucc n δ x

instance (n : ℕ) [NeZero n] (δ : List ℕ) : Decidable (DevelopsToHamiltonCycle n δ) := by
  unfold DevelopsToHamiltonCycle; infer_instance

/-- Under the certificate, `devSucc n δ` is surjective (every vertex is the
successor of the previous vertex on the orbit of `0`). -/
theorem devSucc_surjective {n : ℕ} [NeZero n] {δ : List ℕ}
    (h : DevelopsToHamiltonCycle n δ) : Surjective (devSucc n δ) := by
  intro y
  obtain ⟨k, -, hk⟩ := h.1 y
  cases k with
  | zero =>
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    refine ⟨(devSucc n δ)^[m] 0, ?_⟩
    rw [← iterate_succ_apply' (devSucc n δ) m 0, Nat.succ_eq_add_one, ← hm, h.2.1, ← hk,
      iterate_zero_apply]
  | succ k =>
    exact ⟨(devSucc n δ)^[k] 0, by rw [← hk, iterate_succ_apply']⟩

/-- The successor permutation of the Hamilton cycle `C(P)`. -/
noncomputable def devPerm (n : ℕ) [NeZero n] (δ : List ℕ)
    (h : DevelopsToHamiltonCycle n δ) : Perm (ZMod n) :=
  Equiv.ofBijective (devSucc n δ)
    ⟨Finite.injective_iff_surjective.mpr (devSucc_surjective h), devSucc_surjective h⟩

/-- `C(P)` is a Hamilton cycle of `T_n`. -/
theorem isHamiltonCycle_devPerm {n : ℕ} [NeZero n] {δ : List ℕ}
    (h : DevelopsToHamiltonCycle n δ) : IsHamiltonCycle (carouselArc n) (devPerm n δ h) := by
  refine isHamiltonCycle_of_forall_pow_eq (devPerm n δ h) 0 h.2.2.1 (fun y => ?_) h.2.2.2.1
  obtain ⟨k, -, hk⟩ := h.1 y
  exact ⟨k, by rw [← Perm.iterate_eq_pow]; exact hk⟩

/-- The translation orbit `𝒞(P) = {C(P) + t : 0 ≤ t < d}` of Lemma 2.1,
`d = |δ|`. -/
noncomputable def development (n : ℕ) [NeZero n] (δ : List ℕ)
    (h : DevelopsToHamiltonCycle n δ) : List (Perm (ZMod n)) :=
  (List.range δ.length).map fun t : ℕ => translate (t : ZMod n) (devPerm n δ h)

/-- Every member of `𝒞(P)` is a Hamilton cycle of `T_n`. -/
theorem isHamiltonCycle_of_mem_development {n : ℕ} [NeZero n] {δ : List ℕ}
    (h : DevelopsToHamiltonCycle n δ) {σ : Perm (ZMod n)} (hσ : σ ∈ development n δ h) :
    IsHamiltonCycle (carouselArc n) σ := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hσ
  exact isHamiltonCycle_translate _ (isHamiltonCycle_devPerm h)

/-- Translating twice: `(C + t) + 1 = C + (t + 1)`. -/
theorem translate_one_translate {n : ℕ} (t : ZMod n) (σ : Perm (ZMod n)) :
    translate 1 (translate t σ) = translate (t + 1) σ := by
  ext x
  simp only [translate_apply]
  rw [sub_sub, add_assoc, add_comm 1 t]

/-- `𝒞(P)` is closed under translation by `1`. -/
theorem translate_one_mem_development {n : ℕ} [NeZero n] {δ : List ℕ}
    (h : DevelopsToHamiltonCycle n δ) {σ : Perm (ZMod n)} (hσ : σ ∈ development n δ h) :
    translate 1 σ ∈ development n δ h := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hσ
  rw [List.mem_range] at ht
  rw [translate_one_translate]
  rcases Nat.lt_or_ge (t + 1) δ.length with hlt | hge
  · exact List.mem_map.mpr ⟨t + 1, List.mem_range.mpr hlt, by push_cast; rfl⟩
  · have hd : t + 1 = δ.length := le_antisymm (Nat.succ_le_of_lt ht) hge
    have hfix : translate ((δ.length : ℕ) : ZMod n) (devPerm n δ h) = devPerm n δ h := by
      ext x
      rw [translate_apply]
      exact h.2.2.2.2 x
    refine List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.zero_lt_of_lt ht), ?_⟩
    rw [Nat.cast_zero, ← Nat.cast_one, ← Nat.cast_add, hd, hfix]
    ext x
    simp

/-! ### Ground truth: the development follows the base path -/

/-- The long base path for `T_33`: `P = (0, 3, 4, 6, 10, 16, 24, 31, 7, 19, 1, 11)`. -/
def δ33A : List ℕ := [3, 1, 2, 4, 6, 8, 7, 9, 12, 15, 10]

example : basePositions δ33A = [0, 3, 4, 6, 10, 5, 2, 9, 7, 8, 1] := by decide
example : List.iterate (devSucc 33 δ33A) 0 12 = [0, 3, 4, 6, 10, 16, 24, 31, 7, 19, 1, 11] := by
  decide
example : devSucc 33 [16] 5 = 21 := by decide

/-- Ground truth: the translation `x ↦ x + 3` of `ℤ_33` steps along arcs of
`T_33` but is not a Hamilton cycle (it splits into three 11-cycles). -/
example : ¬ IsHamiltonCycle (carouselArc 33) (Equiv.addRight (3 : ZMod 33)) := by
  rintro ⟨hcyc, -, -⟩
  obtain ⟨i, hi⟩ := hcyc.sameCycle (x := 0) (y := 1) (by decide) (by decide)
  have hpow : ∀ (j : ℤ) (x : ZMod 33), (Equiv.addRight (3 : ZMod 33) ^ j) x = x + j * 3 := by
    intro j
    induction j using Int.induction_on with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [zpow_add_one, Perm.mul_apply, ih, Equiv.coe_addRight]
      push_cast; ring
    | pred k ih =>
      intro x
      rw [zpow_sub_one, Perm.mul_apply, ih, Perm.inv_def, Equiv.addRight_symm,
        Equiv.coe_addRight]
      push_cast; ring
  rw [hpow, zero_add] at hi
  have h33 : ((i : ZMod 33) * 3) * 11 = 11 := by rw [hi, one_mul]
  rw [mul_assoc, show (3 : ZMod 33) * 11 = 0 by decide, mul_zero] at h33
  exact absurd h33 (by decide)

/-- Certificate for the unit difference `1` of `T_5`. -/
private theorem dev5One : DevelopsToHamiltonCycle 5 [1] := by decide

/-- Certificate for the unit difference `2` of `T_5`. -/
private theorem dev5Two : DevelopsToHamiltonCycle 5 [2] := by decide

/-- Ground truth (satisfiability at a prime order, the paper's immediate case):
`T_5` has the cyclic Hamilton decomposition `{x ↦ x + 1, x ↦ x + 2}`. -/
example : ∃ D, IsCyclicHamiltonDecomposition 5 D := by
  refine ⟨_, isCyclicHamiltonDecomposition_of_list (development 5 [1] dev5One ++
    development 5 [2] dev5Two)
    ?_ ?_ ?_ ?_⟩
  · intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ <;> exact isHamiltonCycle_of_mem_development _ hσ
  · decide +kernel
  · decide +kernel
  · intro σ hσ
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact List.mem_append_left _ (translate_one_mem_development _ hσ)
    · exact List.mem_append_right _ (translate_one_mem_development _ hσ)

/-- The length-3 base path for `T_33`. -/
def δ33B : List ℕ := [11, 5, 14]

/-- Certificate for the length-11 base path of `T_33`. -/
theorem dev33A : DevelopsToHamiltonCycle 33 δ33A := by decide +kernel
/-- Certificate for the length-3 base path of `T_33`. -/
theorem dev33B : DevelopsToHamiltonCycle 33 δ33B := by decide +kernel
/-- Certificate for the unit difference `13` of `T_33`. -/
theorem dev33C : DevelopsToHamiltonCycle 33 [13] := by decide +kernel
/-- Certificate for the unit difference `16` of `T_33`. -/
theorem dev33D : DevelopsToHamiltonCycle 33 [16] := by decide +kernel

/-- The explicit cyclic Hamilton decomposition of `T_33`, as a list. -/
noncomputable def list33 : List (Perm (ZMod 33)) :=
  development 33 δ33A dev33A ++ development 33 δ33B dev33B ++
    development 33 [13] dev33C ++ development 33 [16] dev33D

/-- At every vertex of `T_33` the 16 cycles leave along distinct arcs. -/
theorem list33_nodup : ∀ x : ZMod 33, (list33.map fun σ => σ x).Nodup := by
  decide +kernel

/-- Every arc of `T_33` is used by some cycle of the list. -/
theorem list33_cov : ∀ x y : ZMod 33, carouselArc 33 x y → y ∈ list33.map fun σ => σ x := by
  decide +kernel

/-- The `T_33` list is closed under translation by `1`. -/
theorem list33_translate : ∀ σ ∈ list33, translate 1 σ ∈ list33 := by
  intro σ hσ
  simp only [list33, List.mem_append] at hσ ⊢
  rcases hσ with ((hσ | hσ) | hσ) | hσ
  · exact Or.inl (Or.inl (Or.inl (translate_one_mem_development _ hσ)))
  · exact Or.inl (Or.inl (Or.inr (translate_one_mem_development _ hσ)))
  · exact Or.inl (Or.inr (translate_one_mem_development _ hσ))
  · exact Or.inr (translate_one_mem_development _ hσ)

/-- Every member of the `T_33` list is a Hamilton cycle of `T_33`. -/
theorem list33_ham : ∀ σ ∈ list33, IsHamiltonCycle (carouselArc 33) σ := by
  intro σ hσ
  simp only [list33, List.mem_append] at hσ
  rcases hσ with ((hσ | hσ) | hσ) | hσ <;> exact isHamiltonCycle_of_mem_development _ hσ

/-- The explicit cyclic Hamilton decomposition of `T_33`: the developments of
the base paths `[3,1,2,4,6,8,7,9,12,15,10]`, `[11,5,14]`, `[13]`, `[16]`
(11 + 3 + 1 + 1 = 16 Hamilton cycles). -/
noncomputable def D33 : Finset (Perm (ZMod 33)) := list33.toFinset

/-- **`T_33` has a cyclic Hamilton cycle decomposition** (the case
`p = 3`, `q = 11` left open in the concluding remarks of arXiv:2610.07102):
`D33` is a Hamilton decomposition of the carousel tournament `T_33` closed
under translation by `1`. -/
theorem isCyclicHamiltonDecomposition_D33 : IsCyclicHamiltonDecomposition 33 D33 :=
  isCyclicHamiltonDecomposition_of_list list33 list33_ham list33_nodup list33_cov
    list33_translate

/-- `D33` consists of exactly `16 = (33 - 1)/2` Hamilton cycles. -/
theorem card_D33 : D33.card = 16 := by
  rw [D33, List.toFinset_card_of_nodup]
  · rfl
  · exact List.Nodup.of_map (fun σ => σ 0) (list33_nodup 0)

/-- **`T_33` admits a cyclic Hamilton cycle decomposition.** -/
theorem carousel33_cyclic : ∃ D, IsCyclicHamiltonDecomposition 33 D :=
  ⟨D33, isCyclicHamiltonDecomposition_D33⟩

/-! ## `T_35` -/

/-- The length-7 base path for `T_35`. -/
def δ35A : List ℕ := [5, 3, 10, 16, 17, 15, 11]

/-- The length-5 base path for `T_35`. -/
def δ35B : List ℕ := [7, 4, 13, 14, 12]

/-- Certificate for the length-7 base path of `T_35`. -/
theorem dev35A : DevelopsToHamiltonCycle 35 δ35A := by decide +kernel
/-- Certificate for the length-5 base path of `T_35`. -/
theorem dev35B : DevelopsToHamiltonCycle 35 δ35B := by decide +kernel
/-- Certificate for the unit difference `1` of `T_35`. -/
theorem dev35C : DevelopsToHamiltonCycle 35 [1] := by decide +kernel
/-- Certificate for the unit difference `2` of `T_35`. -/
theorem dev35D : DevelopsToHamiltonCycle 35 [2] := by decide +kernel
/-- Certificate for the unit difference `6` of `T_35`. -/
theorem dev35E : DevelopsToHamiltonCycle 35 [6] := by decide +kernel
/-- Certificate for the unit difference `8` of `T_35`. -/
theorem dev35F : DevelopsToHamiltonCycle 35 [8] := by decide +kernel
/-- Certificate for the unit difference `9` of `T_35`. -/
theorem dev35G : DevelopsToHamiltonCycle 35 [9] := by decide +kernel

/-- The explicit cyclic Hamilton decomposition of `T_35`, as a list. -/
noncomputable def list35 : List (Perm (ZMod 35)) :=
  development 35 δ35A dev35A ++ development 35 δ35B dev35B ++
    development 35 [1] dev35C ++ development 35 [2] dev35D ++
    development 35 [6] dev35E ++ development 35 [8] dev35F ++
    development 35 [9] dev35G

/-- At every vertex of `T_35` the 17 cycles leave along distinct arcs. -/
theorem list35_nodup : ∀ x : ZMod 35, (list35.map fun σ => σ x).Nodup := by
  decide +kernel

/-- Every arc of `T_35` is used by some cycle of the list. -/
theorem list35_cov : ∀ x y : ZMod 35, carouselArc 35 x y → y ∈ list35.map fun σ => σ x := by
  decide +kernel

/-- The `T_35` list is closed under translation by `1`. -/
theorem list35_translate : ∀ σ ∈ list35, translate 1 σ ∈ list35 := by
  intro σ hσ
  simp only [list35, List.mem_append] at hσ ⊢
  rcases hσ with (((((hσ | hσ) | hσ) | hσ) | hσ) | hσ) | hσ
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (translate_one_mem_development _ hσ))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (translate_one_mem_development _ hσ))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (translate_one_mem_development _ hσ)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (translate_one_mem_development _ hσ))))
  · exact Or.inl (Or.inl (Or.inr (translate_one_mem_development _ hσ)))
  · exact Or.inl (Or.inr (translate_one_mem_development _ hσ))
  · exact Or.inr (translate_one_mem_development _ hσ)

/-- Every member of the `T_35` list is a Hamilton cycle of `T_35`. -/
theorem list35_ham : ∀ σ ∈ list35, IsHamiltonCycle (carouselArc 35) σ := by
  intro σ hσ
  simp only [list35, List.mem_append] at hσ
  rcases hσ with (((((hσ | hσ) | hσ) | hσ) | hσ) | hσ) | hσ <;>
    exact isHamiltonCycle_of_mem_development _ hσ

/-- The explicit cyclic Hamilton decomposition of `T_35`: the developments of
the base paths `[5,3,10,16,17,15,11]`, `[7,4,13,14,12]` and the unit
differences `1, 2, 6, 8, 9` (7 + 5 + 5 = 17 Hamilton cycles). -/
noncomputable def D35 : Finset (Perm (ZMod 35)) := list35.toFinset

/-- **`T_35` has a cyclic Hamilton cycle decomposition** (the case
`p = 5`, `q = 7` left open in the concluding remarks of arXiv:2610.07102):
`D35` is a Hamilton decomposition of the carousel tournament `T_35` closed
under translation by `1`. -/
theorem isCyclicHamiltonDecomposition_D35 : IsCyclicHamiltonDecomposition 35 D35 :=
  isCyclicHamiltonDecomposition_of_list list35 list35_ham list35_nodup list35_cov
    list35_translate

/-- `D35` consists of exactly `17 = (35 - 1)/2` Hamilton cycles. -/
theorem card_D35 : D35.card = 17 := by
  rw [D35, List.toFinset_card_of_nodup]
  · rfl
  · exact List.Nodup.of_map (fun σ => σ 0) (list35_nodup 0)

/-- **`T_35` admits a cyclic Hamilton cycle decomposition.** -/
theorem carousel35_cyclic : ∃ D, IsCyclicHamiltonDecomposition 35 D :=
  ⟨D35, isCyclicHamiltonDecomposition_D35⟩

end CarouselTournament
