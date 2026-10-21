/-
# Sambale — the complement of a union of `n` cosets (Kourovka 21.115)

## Source

Benjamin Sambale, *On the complement of a union of cosets*, arXiv:2609.09052.
Recorded 2026-10-21.

* Section 1, inequality (1.1): the conjecture of Sambale and Tărnăuceanu
  (J. Algebraic Combin. 55 (2022) 979–987), Kourovka notebook Problem 21.115.
* Section 1, Theorem 1 (proved in Section 3):
  "Let $G$ be a group with (left or right) cosets $C_1,\ldots,C_n$ of subgroups
  such that $A:=G\setminus(C_1\cup\ldots\cup C_n)\ne\varnothing$. Then there exist
  $t_1,\ldots,t_m\in G$ with $G=t_1A\cup\ldots\cup t_mA$ and $m\le2^n$."
  "For finite $G$ the union bound $|G|\le m|A|\le2^n|A|$ yields (1.1)", that is
  $|A|\ge|G|/2^n$.
* Section 2, Lemma 2 (Helly lemma): "Let $X$ be a set equipped with equivalence
  relations $\sim_1,\ldots,\sim_n$ and let $U_1,\ldots,U_m\subseteq X$ be sets of
  the form $U_j=Q_{j,1}\cup\ldots\cup Q_{j,n}$, where $Q_{j,i}$ is a
  $\sim_i$-class. If $U_1\cap\ldots\cap U_m=\varnothing$ while no proper
  subfamily has empty intersection, then $m\le2^n$."
* Section 1, Theorem 3 (proved in Section 5): "Let $G=C_1\cup\ldots\cup C_n$ be
  an irredundant cover of a group $G$ by left cosets $C_i=g_iH_i$. Then
  $|G:H_i|\le2^{n-1}$ for $i=1,\ldots,n$."

Status: proved in the paper. Every statement below is kernel-checked here.

## Formalization notes

* Left cosets `g • (H : Set G)` only; the paper reduces right cosets to left
  cosets via $Hg=g(g^{-1}Hg)$.
* The cosets are indexed by `Fin n` and may repeat, as in the paper.
* Theorem 1 is proved for arbitrary (possibly infinite) groups. The paper uses
  an inclusion-minimal family plus a termination lemma (Lemma 5) for infinite
  groups. Here a greedy chain $t_1,t_2,\ldots$ with $t_ka\notin t_jA$ for $j<k$
  gives a triangular evaluation matrix for the polynomials
  $p_k=\prod_i(X_i-\lambda_i(t_kaH_i))$ at the points
  $\alpha_j=(\lambda_i(t_jg_iH_i))_i$, so every such chain has length at most
  $2^n$; a maximal chain covers $G$. This route avoids Lemma 5.
* Multilinear polynomials are modelled as functions `(Fin n → ℚ) → ℚ` in the
  `ℚ`-span of the $2^n$ monomial functions `x ↦ ∏ i ∈ S, x i`.
* Theorem 3 is stated for `Fin (n + 1)` cosets with bound `2 ^ n`, avoiding
  `Nat` subtraction; finiteness of the index is part of the conclusion because
  `Subgroup.index` is `0` for infinite index.
-/
import Mathlib

set_option autoImplicit false

open Module Pointwise

namespace GroupCount.SambaleCosetComplement

/-! ## Linear algebra over `ℚ`: evaluation criteria and the monomial span -/

/-- A family of functions `v j : X → ℚ` with points `a j` such that `v j (a j) ≠ 0`
and `v j (a k) = 0` for `j ≠ k` is linearly independent over `ℚ`. -/
theorem linearIndependent_of_eval {ι X : Type*} (v : ι → X → ℚ) (a : ι → X)
    (hdiag : ∀ j, v j (a j) ≠ 0) (hoff : ∀ j k, j ≠ k → v j (a k) = 0) :
    LinearIndependent ℚ v := by
  rw [linearIndependent_iff']
  intro s c hsum k hk
  have heval : (∑ j ∈ s, c j • v j) (a k) = c k * v k (a k) := by
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      simp [hoff j k hjk]
    · intro hks
      exact absurd hk hks
  rw [hsum] at heval
  have h0 : c k * v k (a k) = 0 := by simpa using heval.symm
  exact (mul_eq_zero.mp h0).resolve_right (hdiag k)

/-- Triangular evaluation criterion: functions `v k : X → ℚ` (`k : Fin m`) with
points `a k` such that `v k (a k) ≠ 0` and `v k (a j) = 0` whenever `j < k` are
linearly independent over `ℚ`. -/
theorem linearIndependent_of_eval_triangular {m : ℕ} {X : Type*} (v : Fin m → X → ℚ)
    (a : Fin m → X) (hdiag : ∀ k, v k (a k) ≠ 0) (hlow : ∀ j k, j < k → v k (a j) = 0) :
    LinearIndependent ℚ v := by
  rw [linearIndependent_iff']
  intro s c hsum k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    intro hk
    have heval : (∑ j ∈ s, c j • v j) (a k) = c k * v k (a k) := by
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro j hj hjk
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · simp [ih j hlt hj]
        · simp [hlow k j hgt]
      · intro hks
        exact absurd hk hks
    rw [hsum] at heval
    have h0 : c k * v k (a k) = 0 := by simpa using heval.symm
    exact (mul_eq_zero.mp h0).resolve_right (hdiag k)

/-- The `2 ^ n` monomial functions `x ↦ ∏ i ∈ S, x i` on `ℚ^n`, indexed by
`S ⊆ Fin n`; their `ℚ`-span models the multilinear polynomials `𝓜_n`. -/
def monomialFun {n : ℕ} (S : Finset (Fin n)) : (Fin n → ℚ) → ℚ :=
  fun x => ∏ i ∈ S, x i

example : monomialFun (n := 3) {0, 2} ![2, 5, 7] = 14 := by
  simp [monomialFun]
  norm_num

example : monomialFun (n := 2) ∅ ![2, 5] = 1 := by
  simp [monomialFun]

/-- The product `x ↦ ∏ i, (x i - b i)` of linear factors in distinct variables is a
multilinear polynomial function: it lies in the `ℚ`-span of the monomials. -/
theorem prod_sub_mem_span_monomialFun {n : ℕ} (b : Fin n → ℚ) :
    (fun x : Fin n → ℚ => ∏ i, (x i - b i)) ∈
      Submodule.span ℚ (Set.range (monomialFun (n := n))) := by
  have hexp : (fun x : Fin n → ℚ => ∏ i, (x i - b i)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ Finset.univ \ S, -b i) • monomialFun S := by
    funext x
    simp only [sub_eq_add_neg, Finset.prod_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      monomialFun]
    exact Finset.sum_congr rfl fun S _ => mul_comm _ _
  rw [hexp]
  refine Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨S, rfl⟩

/-- A linearly independent family of functions in the span of the monomials
`monomialFun` has at most `2 ^ n` members. -/
theorem card_le_two_pow_of_linearIndependent {n : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → (Fin n → ℚ) → ℚ) (hli : LinearIndependent ℚ p)
    (hspan : ∀ j, p j ∈ Submodule.span ℚ (Set.range (monomialFun (n := n)))) :
    Fintype.card ι ≤ 2 ^ n := by
  classical
  have hrange : Set.range p ≤ Submodule.span ℚ (Set.range (monomialFun (n := n))) := by
    rintro _ ⟨j, rfl⟩
    exact hspan j
  have hcard := linearIndependent_le_span' p hli (Set.range (monomialFun (n := n))) hrange
  have hmono : Fintype.card (Set.range (monomialFun (n := n))) ≤ 2 ^ n := by
    calc Fintype.card (Set.range (monomialFun (n := n)))
        ≤ Fintype.card (Finset (Fin n)) := Fintype.card_range_le _
      _ = 2 ^ n := by simp
  rw [Cardinal.mk_fintype] at hcard
  exact (Nat.cast_le.mp hcard).trans hmono

/-- Coordinate form of the Helly lemma (diagonal case): if points
`β j, α j ∈ ℚ^n` satisfy `β j i ≠ α j i` for all `i`, and for `j ≠ k` some
coordinate has `β j i = α k i`, then there are at most `2 ^ n` indices. -/
theorem card_le_two_pow_of_coords {n : ℕ} {ι : Type*} [Fintype ι] (β α : ι → Fin n → ℚ)
    (hdiag : ∀ j i, β j i ≠ α j i) (hoff : ∀ j k, j ≠ k → ∃ i, β j i = α k i) :
    Fintype.card ι ≤ 2 ^ n := by
  let p : ι → (Fin n → ℚ) → ℚ := fun j x => ∏ i, (x i - β j i)
  have hli : LinearIndependent ℚ p := by
    refine linearIndependent_of_eval p α (fun j => ?_) (fun j k hjk => ?_)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hdiag j i).symm
    · obtain ⟨i, hi⟩ := hoff j k hjk
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.mpr hi.symm)
  exact card_le_two_pow_of_linearIndependent p hli fun j => prod_sub_mem_span_monomialFun (β j)

/-- Coordinate form of the Helly lemma (triangular case): if points
`β k, α k ∈ ℚ^n` (`k : Fin m`) satisfy `β k i ≠ α k i` for all `i`, and for
`j < k` some coordinate has `β k i = α j i`, then `m ≤ 2 ^ n`. -/
theorem le_two_pow_of_coords_triangular {n m : ℕ} (β α : Fin m → Fin n → ℚ)
    (hdiag : ∀ k i, β k i ≠ α k i) (hlow : ∀ j k, j < k → ∃ i, β k i = α j i) :
    m ≤ 2 ^ n := by
  let p : Fin m → (Fin n → ℚ) → ℚ := fun k x => ∏ i, (x i - β k i)
  have hli : LinearIndependent ℚ p := by
    refine linearIndependent_of_eval_triangular p α (fun k => ?_) (fun j k hjk => ?_)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hdiag k i).symm
    · obtain ⟨i, hi⟩ := hlow j k hjk
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.mpr hi.symm)
  have hcard := card_le_two_pow_of_linearIndependent p hli
    fun k => prod_sub_mem_span_monomialFun (β k)
  rwa [Fintype.card_fin] at hcard

/-- Every finite set admits a map to `ℚ` that is injective on it. -/
theorem exists_injOn_rat {α : Type*} (s : Finset α) : ∃ f : α → ℚ, Set.InjOn f s := by
  classical
  refine ⟨fun q => if h : q ∈ s then ((s.equivFin ⟨q, h⟩ : ℕ) : ℚ) else 0, ?_⟩
  intro q₁ h₁ q₂ h₂ heq
  have h₁' : q₁ ∈ s := h₁
  have h₂' : q₂ ∈ s := h₂
  simp only [h₁', h₂', dite_true, Nat.cast_inj] at heq
  have hsub := s.equivFin.injective (Fin.ext heq)
  exact congrArg Subtype.val hsub

/-! ## Helly lemma for unions of equivalence classes (Lemma 2) -/

/-- **Sambale, arXiv:2609.09052, Lemma 2 (Helly lemma).** Let `X` carry equivalence
relations `r 0, …, r (n-1)` and let `U j = ⋃ i, [c j i]_{r i}` (`j : ι`, `ι` finite)
be a union of one `r i`-class for each `i`. If `⋂ j, U j = ∅` while every
subfamily omitting one member has nonempty intersection, then `|ι| ≤ 2 ^ n`. -/
theorem card_le_two_pow_of_setoid {X ι : Type*} [Fintype ι] {n : ℕ} (r : Fin n → Setoid X)
    (c : ι → Fin n → X) (hempty : ⋂ j, ⋃ i, {y | r i y (c j i)} = ∅)
    (hmin : ∀ j, (⋂ (k) (_ : k ≠ j), ⋃ i, {y | r i y (c k i)}).Nonempty) :
    Fintype.card ι ≤ 2 ^ n := by
  classical
  choose x hx using hmin
  have hxk : ∀ j k, k ≠ j → ∃ i, r i (x j) (c k i) := by
    intro j k hkj
    have hmem := Set.mem_iInter₂.mp (hx j) k hkj
    simpa using hmem
  have hxj : ∀ j i, ¬ r i (x j) (c j i) := by
    intro j i hji
    have hmem : x j ∈ ⋂ j', ⋃ i', {y | r i' y (c j' i')} := by
      refine Set.mem_iInter.mpr fun k => ?_
      by_cases hkj : k = j
      · subst hkj
        exact Set.mem_iUnion.mpr ⟨i, hji⟩
      · obtain ⟨i', hi'⟩ := hxk j k hkj
        exact Set.mem_iUnion.mpr ⟨i', hi'⟩
    rw [hempty] at hmem
    exact hmem
  let S : ∀ i, Finset (Quotient (r i)) := fun i =>
    (Finset.univ.image fun j => Quotient.mk (r i) (c j i)) ∪
      (Finset.univ.image fun j => Quotient.mk (r i) (x j))
  choose lam hlam using fun i => exists_injOn_rat (S i)
  have hcS : ∀ i j, Quotient.mk (r i) (c j i) ∈ S i := fun i j =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hxS : ∀ i j, Quotient.mk (r i) (x j) ∈ S i := fun i j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let β : ι → Fin n → ℚ := fun j i => lam i (Quotient.mk (r i) (x j))
  let α : ι → Fin n → ℚ := fun j i => lam i (Quotient.mk (r i) (c j i))
  refine card_le_two_pow_of_coords β α (fun j i hβα => ?_) (fun j k hjk => ?_)
  · exact hxj j i (Quotient.eq.mp (hlam i (hxS i j) (hcS i j) hβα))
  · obtain ⟨i, hi⟩ := hxk j k (Ne.symm hjk)
    exact ⟨i, congrArg (lam i) (Quotient.sound hi)⟩

/-- Triangular (chain) form of the Helly lemma: if points `y k` and representatives
`c k i` (`k : Fin m`) satisfy `y k ∉ [c k i]_{r i}` for every `i`, and for `j < k`
the point `y k` lies in `[c j i]_{r i}` for some `i`, then `m ≤ 2 ^ n`. -/
theorem le_two_pow_of_setoid_chain {X : Type*} {n m : ℕ} (r : Fin n → Setoid X)
    (y : Fin m → X) (c : Fin m → Fin n → X) (hdiag : ∀ k i, ¬ r i (y k) (c k i))
    (hlow : ∀ j k, j < k → ∃ i, r i (y k) (c j i)) :
    m ≤ 2 ^ n := by
  classical
  let S : ∀ i, Finset (Quotient (r i)) := fun i =>
    (Finset.univ.image fun j => Quotient.mk (r i) (c j i)) ∪
      (Finset.univ.image fun j => Quotient.mk (r i) (y j))
  choose lam hlam using fun i => exists_injOn_rat (S i)
  have hcS : ∀ i j, Quotient.mk (r i) (c j i) ∈ S i := fun i j =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hyS : ∀ i j, Quotient.mk (r i) (y j) ∈ S i := fun i j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let β : Fin m → Fin n → ℚ := fun k i => lam i (Quotient.mk (r i) (y k))
  let α : Fin m → Fin n → ℚ := fun j i => lam i (Quotient.mk (r i) (c j i))
  refine le_two_pow_of_coords_triangular β α (fun k i hβα => ?_) (fun j k hjk => ?_)
  · exact hdiag k i (Quotient.eq.mp (hlam i (hyS i k) (hcS i k) hβα))
  · obtain ⟨i, hi⟩ := hlow j k hjk
    exact ⟨i, congrArg (lam i) (Quotient.sound hi)⟩

/-! ## The complement of a union of cosets -/

variable {G : Type*} [Group G] {n : ℕ}

/-- `A = G \ (g 0 • H 0 ∪ … ∪ g (n-1) • H (n-1))`, the complement of a union of
`n` left cosets of subgroups (Sambale, arXiv:2609.09052, Section 1). -/
def cosetUnionCompl (g : Fin n → G) (H : Fin n → Subgroup G) : Set G :=
  (⋃ i, g i • (H i : Set G))ᶜ

/-- Membership in the complement: `x ∈ A` iff `x` lies in none of the cosets. -/
theorem mem_cosetUnionCompl_iff (g : Fin n → G) (H : Fin n → Subgroup G) (x : G) :
    x ∈ cosetUnionCompl g H ↔ ∀ i, x ∉ g i • (H i : Set G) := by
  simp [cosetUnionCompl]

/-- With no cosets, the complement is all of `G`. -/
example : cosetUnionCompl (G := Multiplicative (ZMod 2)) (n := 0) ![] ![] = Set.univ := by
  simp [cosetUnionCompl]

/-- A single coset `1 • ⊥ = {1}` leaves the complement `{1}ᶜ`. -/
example : cosetUnionCompl (G := Multiplicative (ZMod 2)) ![1] ![⊥] = {1}ᶜ := by
  ext x
  simp [cosetUnionCompl]

/-- A coset of `⊤` leaves nothing. -/
example (g : Multiplicative (ZMod 2)) : cosetUnionCompl ![g] ![⊤] = ∅ := by
  ext x
  simp [cosetUnionCompl]

/-- Translate form of membership: `y ∈ t • A` iff for every `i` the left coset
`y H_i` differs from `t g_i H_i`. -/
theorem mem_smul_cosetUnionCompl_iff (g : Fin n → G) (H : Fin n → Subgroup G) (t y : G) :
    y ∈ t • cosetUnionCompl g H ↔ ∀ i, ¬ QuotientGroup.leftRel (H i) y (t * g i) := by
  rw [mem_leftCoset_iff, mem_cosetUnionCompl_iff]
  refine forall_congr' fun i => ?_
  rw [mem_leftCoset_iff, QuotientGroup.leftRel_apply, ← inv_mem_iff (x := y⁻¹ * (t * g i)),
    mul_inv_rev, inv_inv, mul_inv_rev, mul_assoc, SetLike.mem_coe]

/-- Chain bound: if `a ∈ A` and `t : ℕ → G` satisfies `t k * a ∉ t j • A` for all
`j < k < m`, then `m ≤ 2 ^ n`. -/
theorem le_two_pow_of_chain (g : Fin n → G) (H : Fin n → Subgroup G) {a : G}
    (ha : a ∈ cosetUnionCompl g H) (t : ℕ → G) (m : ℕ)
    (hchain : ∀ j k, j < k → k < m → t k * a ∉ t j • cosetUnionCompl g H) :
    m ≤ 2 ^ n := by
  have hself : ∀ k : ℕ, t k * a ∈ t k • cosetUnionCompl g H :=
    fun k => Set.smul_mem_smul_set ha
  refine le_two_pow_of_setoid_chain (fun i => QuotientGroup.leftRel (H i))
    (fun k : Fin m => t k * a) (fun j i => t j * g i) (fun k i => ?_) (fun j k hjk => ?_)
  · exact (mem_smul_cosetUnionCompl_iff g H (t k) (t k * a)).mp (hself k) i
  · have hnot := hchain j k hjk k.2
    rw [mem_smul_cosetUnionCompl_iff] at hnot
    push Not at hnot
    exact hnot

/-- **Sambale, arXiv:2609.09052, Theorem 1.** Let `g i • H i` (`i : Fin n`) be left
cosets of subgroups of a group `G` such that `A = G \ ⋃ i, g i • H i` is nonempty.
Then `G` is the union of at most `2 ^ n` left translates `t • A`. -/
theorem exists_finset_iUnion_smul_eq_univ (g : Fin n → G) (H : Fin n → Subgroup G)
    (hA : (cosetUnionCompl g H).Nonempty) :
    ∃ T : Finset G, T.card ≤ 2 ^ n ∧ ⋃ t ∈ T, t • cosetUnionCompl g H = Set.univ := by
  classical
  obtain ⟨a, ha⟩ := hA
  set A := cosetUnionCompl g H with hAdef
  by_contra hno
  push Not at hno
  -- every chain extends by one more element, so chains of every length exist
  have hext : ∀ m : ℕ, ∃ t : ℕ → G, ∀ j k, j < k → k < m → t k * a ∉ t j • A := by
    intro m
    induction m with
    | zero => exact ⟨fun _ => 1, fun j k _ hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      have hm : m ≤ 2 ^ n := le_two_pow_of_chain g H ha t m ht
      let T : Finset G := (Finset.range m).image t
      have hTcard : T.card ≤ 2 ^ n := (Finset.card_image_le.trans (by simp)).trans hm
      obtain ⟨z, hz⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp (hno T hTcard)
      refine ⟨fun k => if k < m then t k else z * a⁻¹, fun j k hjk hk => ?_⟩
      have hjm : j < m := by omega
      simp only [hjm, if_true]
      by_cases hkm : k < m
      · simp only [hkm, if_true]
        exact ht j k hjk hkm
      · simp only [hkm, if_false, inv_mul_cancel_right]
        intro hzj
        exact hz (Set.mem_biUnion (Finset.mem_image_of_mem t (Finset.mem_range.mpr hjm)) hzj)
  obtain ⟨t, ht⟩ := hext (2 ^ n + 1)
  have hle := le_two_pow_of_chain g H ha t (2 ^ n + 1) ht
  omega

/-- **Kourovka Problem 21.115 (Sambale–Tărnăuceanu conjecture), proved in
Sambale, arXiv:2609.09052, inequality (1.1).** If `G` is a finite group and the
complement `A` of a union of `n` left cosets of subgroups is nonempty, then
`|G| ≤ 2 ^ n * |A|`, i.e. `|A| ≥ |G| / 2 ^ n`. -/
theorem card_le_two_pow_mul_ncard [Finite G] (g : Fin n → G) (H : Fin n → Subgroup G)
    (hA : (cosetUnionCompl g H).Nonempty) :
    Nat.card G ≤ 2 ^ n * (cosetUnionCompl g H).ncard := by
  obtain ⟨T, hTcard, hTcover⟩ := exists_finset_iUnion_smul_eq_univ g H hA
  calc Nat.card G = (Set.univ : Set G).ncard := (Set.ncard_univ G).symm
    _ = (⋃ t ∈ T, t • cosetUnionCompl g H).ncard := by rw [hTcover]
    _ ≤ ∑ t ∈ T, (t • cosetUnionCompl g H).ncard := Finset.set_ncard_biUnion_le T _
    _ = T.card * (cosetUnionCompl g H).ncard := by simp [Set.ncard_smul_set]
    _ ≤ 2 ^ n * (cosetUnionCompl g H).ncard := Nat.mul_le_mul_right _ hTcard

/-- Non-vacuity and sharpness at `n = 1`: in `C₂`, the coset `1 • ⊥ = {1}` leaves a
nonempty complement of size exactly `|G| / 2`. -/
example : (cosetUnionCompl (G := Multiplicative (ZMod 2)) ![1] ![⊥]).Nonempty ∧
    Nat.card (Multiplicative (ZMod 2)) = 2 ^ 1 * (cosetUnionCompl
      (G := Multiplicative (ZMod 2)) ![1] ![⊥]).ncard := by
  have hA : cosetUnionCompl (G := Multiplicative (ZMod 2)) ![1] ![⊥] =
      {Multiplicative.ofAdd 1} := by
    ext x
    simp only [cosetUnionCompl, Matrix.cons_val_fin_one, Subgroup.coe_bot, one_smul,
      Set.iUnion_singleton_eq_range, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff]
    revert x
    decide
  rw [hA]
  refine ⟨Set.singleton_nonempty _, ?_⟩
  simp

/-- **Sambale, arXiv:2609.09052, Theorem 3.** Let `G = ⋃ i, g i • H i` be an
irredundant cover of a group `G` by `n + 1` left cosets (no coset can be omitted).
Then every `H i` has finite index and `|G : H i| ≤ 2 ^ n`. -/
theorem index_le_two_pow_of_irredundant (g : Fin (n + 1) → G)
    (H : Fin (n + 1) → Subgroup G) (hcover : ⋃ i, g i • (H i : Set G) = Set.univ)
    (hirr : ∀ i, ⋃ (j) (_ : j ≠ i), g j • (H j : Set G) ≠ Set.univ) (i : Fin (n + 1)) :
    (H i).FiniteIndex ∧ (H i).index ≤ 2 ^ n := by
  classical
  let g' : Fin n → G := fun k => g (i.succAbove k)
  let H' : Fin n → Subgroup G := fun k => H (i.succAbove k)
  have hunion : ⋃ k, g' k • (H' k : Set G) = ⋃ (j) (_ : j ≠ i), g j • (H j : Set G) := by
    ext x
    simp only [Set.mem_iUnion, g', H']
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨i.succAbove k, Fin.succAbove_ne i k, hk⟩
    · rintro ⟨j, hj, hx⟩
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact ⟨k, hx⟩
  have hne : (cosetUnionCompl g' H').Nonempty := by
    rw [cosetUnionCompl, hunion, Set.nonempty_compl]
    exact hirr i
  have hsub : cosetUnionCompl g' H' ⊆ g i • (H i : Set G) := by
    intro x hx
    rw [cosetUnionCompl, hunion, Set.mem_compl_iff] at hx
    have hxcov : x ∈ ⋃ j, g j • (H j : Set G) := hcover ▸ Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxcov
    by_cases hji : j = i
    · rwa [← hji]
    · exact absurd (Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩) hx
  obtain ⟨T, hTcard, hTcover⟩ := exists_finset_iUnion_smul_eq_univ g' H' hne
  -- every left coset of `H i` is `mk (t * g i)` for some `t ∈ T`
  have hsurj : ∀ q : G ⧸ H i, ∃ t ∈ T, (QuotientGroup.mk (t * g i) : G ⧸ H i) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ ⋃ t ∈ T, t • cosetUnionCompl g' H' := hTcover ▸ Set.mem_univ x
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
      have hxt' : x ∈ (t * g i) • (H i : Set G) := by
        rw [mul_smul]
        exact Set.smul_set_mono hsub hxt
      refine ⟨t, ht, QuotientGroup.eq.mpr ?_⟩
      exact (mem_leftCoset_iff (t * g i)).mp hxt'
  have hrange : Set.range (fun t : T => (QuotientGroup.mk ((t : G) * g i) : G ⧸ H i)) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨t, ht, htq⟩ := hsurj q
    exact ⟨⟨t, ht⟩, htq⟩
  have hfin : Finite (G ⧸ H i) := by
    rw [← Set.finite_univ_iff, ← hrange]
    exact Set.finite_range _
  have hidx_le : Nat.card (G ⧸ H i) ≤ T.card := by
    have hle := Nat.card_le_card_of_surjective
      (fun t : T => (QuotientGroup.mk ((t : G) * g i) : G ⧸ H i))
      (fun q => by
        obtain ⟨t, ht, htq⟩ := hsurj q
        exact ⟨⟨t, ht⟩, htq⟩)
    simpa using hle
  have hfi : (H i).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨hfi, (Subgroup.index.eq_1 (H i) ▸ hidx_le).trans hTcard⟩

/-- Non-vacuity of Theorem 3: in `C₂`, the cosets `1 • ⊥ = {1}` and
`ofAdd 1 • ⊥ = {ofAdd 1}` form an irredundant cover, so the hypotheses of
`index_le_two_pow_of_irredundant` are jointly satisfiable (with `|C₂ : ⊥| = 2 = 2 ^ 1`). -/
example :
    (⋃ i, (![1, Multiplicative.ofAdd 1] : Fin 2 → Multiplicative (ZMod 2)) i •
        (((![⊥, ⊥] : Fin 2 → Subgroup (Multiplicative (ZMod 2))) i :
          Set (Multiplicative (ZMod 2)))) = Set.univ) ∧
    (∀ i : Fin 2, ⋃ (j) (_ : j ≠ i),
        (![1, Multiplicative.ofAdd 1] : Fin 2 → Multiplicative (ZMod 2)) j •
          (((![⊥, ⊥] : Fin 2 → Subgroup (Multiplicative (ZMod 2))) j :
            Set (Multiplicative (ZMod 2)))) ≠ Set.univ) := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Matrix.cons_val_zero, Subgroup.coe_bot,
      one_smul, Set.mem_singleton_iff, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Set.smul_set_singleton, smul_eq_mul, mul_one, Set.mem_univ, iff_true]
    revert x
    decide
  · intro i
    rw [Ne, Set.eq_univ_iff_forall]
    fin_cases i
    · push Not
      refine ⟨1, ?_⟩
      simp only [Fin.zero_eta, ne_eq, Set.mem_iUnion, exists_prop, Fin.exists_fin_two,
        not_true_eq_false, Matrix.cons_val_zero, Subgroup.coe_bot, one_smul,
        Set.mem_singleton_iff, and_true, one_ne_zero, not_false_eq_true, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Set.smul_set_singleton, smul_eq_mul, mul_one, true_and,
        false_or]
      decide
    · push Not
      refine ⟨Multiplicative.ofAdd 1, ?_⟩
      simp [Fin.exists_fin_two]

end GroupCount.SambaleCosetComplement
