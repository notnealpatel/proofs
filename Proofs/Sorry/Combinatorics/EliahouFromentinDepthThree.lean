/-
# Eliahou–Fromentin: Fibonacci-like lower bound for depth `≤ 3`, and Zhao's count

## Source

arXiv:1811.10295, Shalom Eliahou and Jean Fromentin, *Gapsets and numerical
semigroups* (J. Combin. Theory Ser. A 169 (2020)).

* Section 4 ("The case $q \le 2$"): Lemma `filtrations of depth 2`, Proposition
  (`q <= 2`) and Corollary `fibo`.
* Section 5 ("A lower bound on $n_g'$"): Notation (`α₁`, `α₂`), Proposition `alpha`,
  Proposition (disjoint images) and Corollary `cor n'`; this is the left inequality
  of Theorem `theorem main`.

Verbatim printed claims:

> Corollary (cor n'). For all $g \ge 2$, we have $n_g' \,\ge \, n_{g-1}'+n_{g-2}'$.

where $n'_g = |\Gamma(g, q \le 3)|$ is the number of numerical semigroups (gapsets)
of genus $g$ and depth $q = \lceil c/m \rceil \le 3$ ($m$ the multiplicity, $c$ the
conductor).

> Corollary (fibo). For all $g \ge 0$, we have $|\mathcal{F}(g, q \le 2)|=\F_{g+1}$,
> where $\F_n$ denote the $n$th Fibonacci number.

(Zhao's theorem, reproved bijectively in the paper.)

Date: 2026-10-21. Status: proved in the paper (known result).

## Conventions

`depthLe q g` is the set of numerical semigroups of genus `g` (`genus` from
`Enumerative.MultiparameterCountingNumericalSemigroups`, the number of gaps) with a
multiplicity `m` (`HasMultiplicity`, least nonzero element) such that every
`x ≥ q m` lies in `S`, i.e. conductor `c ≤ q m`, i.e. depth `⌈c/m⌉ ≤ q`. `ℕ` itself
(multiplicity `1`, conductor `0`, depth `0`, genus `0`) is included, as in the paper
(`n'_0 = 1`).

## Proof

Semigroup form of the paper's maps: for `S` of multiplicity `m` and gapset
`G = G₀ ⊔ G₁ ⊔ G₂`, `α₁(S)` has gapset `[1, m] ⊔ (1 + G₁) ⊔ (2 + G₂)` and `α₂(S)`
additionally the gap `2m + 1`. Closure under addition uses depth `≤ 3` exactly as in
Proposition `alpha`; `S` is recovered by pulling back along `psi`; `2m + 1`
separates the two images. For depth `≤ 2` the pull-back inverts `α_b` on genus
`≥ 1`, giving the Fibonacci recurrence.
-/
import Mathlib
import Enumerative.MultiparameterCountingNumericalSemigroups

set_option autoImplicit false

namespace Candidates.EliahouFromentinDepthThree

open Candidates.NumericalSemigroupLeafInternal Candidates.MultiparameterCountingNumericalSemigroups

/-- `𝒩(q, g)`: numerical semigroups of genus `g` and depth `⌈c/m⌉ ≤ q`, where `m` is the
multiplicity and `c` the conductor. The depth condition `c ≤ q m` is spelled
`∀ x ≥ q m, x ∈ S`; it also forces `S` to be cofinite, so every member is a numerical
semigroup. `ℕ = ⊤` (multiplicity `1`, conductor `0`, genus `0`) belongs to every `𝒩(q, 0)`. -/
def depthLe (q g : ℕ) : Set (AddSubmonoid ℕ) :=
  {S | genus S = g ∧ ∃ m, HasMultiplicity S m ∧ ∀ x, q * m ≤ x → x ∈ S}

/-- Membership predicate of `α_b(S)`: for `S` of multiplicity `m` and depth `≤ 3` its gapset
`G = G₀ ⊔ G₁ ⊔ G₂` becomes `H = [1, m] ⊔ (1 + G₁) ⊔ (2 + G₂)`, plus the gap `2m + 1` when
`b = false`. -/
def alphaPred (S : AddSubmonoid ℕ) (m : ℕ) (b : Bool) (x : ℕ) : Prop :=
  x = 0 ∨ (m + 1 ≤ x ∧ x ≤ 2 * m ∧ x - 1 ∈ S) ∨ (b = true ∧ x = 2 * m + 1) ∨
    (2 * m + 2 ≤ x ∧ x - 2 ∈ S)

/-- `α_b(S)`: the paper's `α₁(F) = (F₀ ⊔ {m}, F₁, F₂)` for `b = true` and
`α₂(F) = (F₀ ⊔ {m}, F₁ ⊔ {m}, F₂)` for `b = false`, on semigroups of multiplicity `m`
(arXiv:1811.10295, §5). Defined as the closure of `alphaPred`, which is already closed
under addition when `S` has depth `≤ 3` (`mem_alpha_iff`). -/
def alpha (S : AddSubmonoid ℕ) (m : ℕ) (b : Bool) : AddSubmonoid ℕ :=
  AddSubmonoid.closure {x | alphaPred S m b x}

/-- Nonzero elements of `α_b(S)` are at least `m + 1`. -/
theorem le_of_alphaPred {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool} {x : ℕ}
    (hx : alphaPred S m b x) : x = 0 ∨ m + 1 ≤ x := by
  rcases hx with h | h | h | h <;> omega

/-- **Proposition `alpha`, gapset part.** For `S` of depth `≤ 3` (all `x ≥ 3m` in `S`),
`alphaPred S m b` is closed under addition. -/
theorem alphaPred_add {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool}
    (hd : ∀ x, 3 * m ≤ x → x ∈ S) {x y : ℕ}
    (hx : alphaPred S m b x) (hy : alphaPred S m b y) : alphaPred S m b (x + y) := by
  rcases le_of_alphaPred hx with rfl | hx0
  · simpa using hy
  rcases le_of_alphaPred hy with rfl | hy0
  · simpa using hx
  by_cases hbig : 2 * m + 1 ≤ x ∨ 2 * m + 1 ≤ y
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, hd _ (by omega)⟩))
  have hx1 : x - 1 ∈ S := by
    rcases hx with h | h | h | h
    · omega
    · exact h.2.2
    · omega
    · omega
  have hy1 : y - 1 ∈ S := by
    rcases hy with h | h | h | h
    · omega
    · exact h.2.2
    · omega
    · omega
  refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))
  have hxy := S.add_mem hx1 hy1
  rwa [show x - 1 + (y - 1) = x + y - 2 by omega] at hxy

/-- Under depth `≤ 3`, membership in `α_b(S)` is exactly `alphaPred`. -/
theorem mem_alpha_iff {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool}
    (hd : ∀ x, 3 * m ≤ x → x ∈ S) {x : ℕ} : x ∈ alpha S m b ↔ alphaPred S m b x := by
  let P : AddSubmonoid ℕ :=
    { carrier := {x | alphaPred S m b x}
      zero_mem' := Or.inl rfl
      add_mem' := fun ha hb => alphaPred_add hd ha hb }
  have hle : alpha S m b ≤ P := (AddSubmonoid.closure_le).2 fun _ h => h
  exact ⟨fun h => hle h, fun h => AddSubmonoid.subset_closure h⟩

/-- The reindexing `ψ_m(y) = y` on `[0, m)`, `y + 1` on `[m, 2m)`, `y + 2` on `[2m, ∞)`;
it carries `G₀, G₁, G₂` to the corresponding pieces of `α_b`. -/
def psi (m y : ℕ) : ℕ := if y < m then y else if y < 2 * m then y + 1 else y + 2

/-- `ψ_m` is strictly monotone. -/
theorem psi_strictMono (m : ℕ) : StrictMono (psi m) := by
  intro a b hab
  unfold psi
  split_ifs <;> omega

/-- The range of `ψ_m` is everything except `m` and `2m + 1`. -/
theorem exists_psi_eq {m x : ℕ} (h1 : x ≠ m) (h2 : x ≠ 2 * m + 1) : ∃ y, psi m y = x := by
  by_cases hx : x < m
  · exact ⟨x, by simp [psi, hx]⟩
  by_cases hx2 : x ≤ 2 * m
  · exact ⟨x - 1, by unfold psi; split_ifs <;> omega⟩
  · exact ⟨x - 2, by unfold psi; split_ifs <;> omega⟩

/-- `ψ_m` misses `m`. -/
theorem psi_ne_m (m y : ℕ) : psi m y ≠ m := by unfold psi; split_ifs <;> omega

/-- `ψ_m` misses `2m + 1`. -/
theorem psi_ne_two_mul_add_one (m y : ℕ) : psi m y ≠ 2 * m + 1 := by
  unfold psi; split_ifs <;> omega

/-- `S` is recovered from `α_b(S)` by pulling back along `ψ_m`. -/
theorem mem_iff_psi_mem {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool} (hm : HasMultiplicity S m)
    (hd : ∀ x, 3 * m ≤ x → x ∈ S) (y : ℕ) : y ∈ S ↔ psi m y ∈ alpha S m b := by
  rw [mem_alpha_iff hd]
  have hm0 := hm.1
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · exact iff_of_true S.zero_mem (Or.inl (by simp [psi, hm0]))
  by_cases hy1 : y < m
  · have hpsi : psi m y = y := by simp [psi, hy1]
    refine iff_of_false (notMem_of_pos_of_lt hm hy0 hy1) ?_
    rw [hpsi]
    rintro (h | h | h | h) <;> omega
  by_cases hy2 : y < 2 * m
  · have hpsi : psi m y = y + 1 := by simp [psi, hy1, hy2]
    rw [hpsi]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨by omega, by omega, by simpa using h⟩)
    · rintro (h | h | h | h)
      · omega
      · simpa using h.2.2
      · omega
      · omega
  · have hpsi : psi m y = y + 2 := by simp [psi, hy1, hy2]
    rw [hpsi]
    constructor
    · intro h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by simpa using h⟩))
    · rintro (h | h | h | h)
      · omega
      · omega
      · omega
      · simpa using h.2

/-- `α_b(S)` has multiplicity `m + 1`. -/
theorem hasMultiplicity_alpha {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool}
    (hm : HasMultiplicity S m) (hd : ∀ x, 3 * m ≤ x → x ∈ S) :
    HasMultiplicity (alpha S m b) (m + 1) := by
  refine ⟨Nat.succ_pos m, ?_, fun x hx hx0 => ?_⟩
  · rw [mem_alpha_iff hd]
    exact Or.inr (Or.inl ⟨le_rfl, by have := hm.1; omega, by simpa using hm.2.1⟩)
  · rw [mem_alpha_iff hd] at hx
    have := le_of_alphaPred hx
    omega

/-- Depth `≤ q` with `q ≤ 3` implies depth `≤ 3`. -/
theorem depth_three_of_le {S : AddSubmonoid ℕ} {m q : ℕ} (hq3 : q ≤ 3)
    (hd : ∀ x, q * m ≤ x → x ∈ S) : ∀ x, 3 * m ≤ x → x ∈ S :=
  fun x hx => hd x (le_trans (Nat.mul_le_mul_right m hq3) hx)

/-- For `2 ≤ q ≤ 3`, `α_b` preserves depth `≤ q`. -/
theorem depth_alpha {S : AddSubmonoid ℕ} {m q : ℕ} {b : Bool} (hq2 : 2 ≤ q) (hq3 : q ≤ 3)
    (hd : ∀ x, q * m ≤ x → x ∈ S) : ∀ x, q * (m + 1) ≤ x → x ∈ alpha S m b := by
  intro x hx
  rw [mem_alpha_iff (depth_three_of_le hq3 hd)]
  have hqm : q * m + 2 ≤ x := by
    have : q * (m + 1) = q * m + q := by ring
    omega
  have h2m : 2 * m + 2 ≤ x := by
    have : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq2
    omega
  exact Or.inr (Or.inr (Or.inr ⟨h2m, hd _ (by omega)⟩))

/-- A submonoid containing every `x ≥ N` has finite complement. -/
theorem compl_finite_of_depth {S : AddSubmonoid ℕ} {N : ℕ} (hd : ∀ x, N ≤ x → x ∈ S) :
    ((S : Set ℕ)ᶜ).Finite :=
  (Set.finite_Iio N).subset fun x hx => by
    by_contra h
    exact hx (hd x (not_lt.1 h))

/-- The gapset of `α_b(S)` is `ψ_m(G) ⊔ {m}` (`b = true`) or `ψ_m(G) ⊔ {m, 2m+1}`. -/
theorem compl_alpha {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool} (hm : HasMultiplicity S m)
    (hd : ∀ x, 3 * m ≤ x → x ∈ S) :
    ((alpha S m b : Set ℕ))ᶜ =
      psi m '' (S : Set ℕ)ᶜ ∪ (if b then {m} else {m, 2 * m + 1}) := by
  have hm0 := hm.1
  ext x
  by_cases hxm : x = m
  · subst hxm
    refine iff_of_true ?_ (Or.inr (by cases b <;> simp))
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_alpha_iff hd]
    rintro (h | h | h | h) <;> omega
  by_cases hx2 : x = 2 * m + 1
  · subst hx2
    have himg : 2 * m + 1 ∉ psi m '' (S : Set ℕ)ᶜ := by
      rintro ⟨y, -, hy⟩
      exact psi_ne_two_mul_add_one m y hy
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_alpha_iff hd, Set.mem_union, himg,
      false_or]
    cases b
    · refine iff_of_true ?_ (by simp)
      rintro (h | h | h | h) <;> simp_all
    · refine iff_of_false (fun h => h (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) ?_
      simp only [if_true, Set.mem_singleton_iff]
      omega
  obtain ⟨y, rfl⟩ := exists_psi_eq hxm hx2
  have hE : psi m y ∉ (if b then ({m} : Set ℕ) else {m, 2 * m + 1}) := by
    cases b <;> simp [hxm, hx2]
  simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_union, hE, or_false,
    (psi_strictMono m).injective.mem_set_image, ← mem_iff_psi_mem (b := b) hm hd]

/-- **Proposition `alpha`, genus part.** `α₁` raises the genus by `1`, `α₂` by `2`. -/
theorem genus_alpha {S : AddSubmonoid ℕ} {m : ℕ} {b : Bool} (hm : HasMultiplicity S m)
    (hd : ∀ x, 3 * m ≤ x → x ∈ S) :
    genus (alpha S m b) = genus S + (if b then 1 else 2) := by
  have hfin := compl_finite_of_depth hd
  have hdisj : Disjoint (psi m '' (S : Set ℕ)ᶜ) (if b then ({m} : Set ℕ) else {m, 2 * m + 1}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, -, rfl⟩
    have h1 := psi_ne_m m y
    have h2 := psi_ne_two_mul_add_one m y
    cases b <;> simp [h1, h2]
  have hEfin : (if b then ({m} : Set ℕ) else {m, 2 * m + 1}).Finite := by
    cases b <;> simp
  unfold genus
  rw [compl_alpha hm hd, Set.ncard_union_eq hdisj (hfin.image _) hEfin,
    Set.ncard_image_of_injective _ (psi_strictMono m).injective]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [Set.ncard_pair (by omega)]
  · simp

/-- Submonoids of `ℕ` containing every `x ≥ N` form a finite set. -/
theorem setOf_forall_le_mem_finite (N : ℕ) :
    {S : AddSubmonoid ℕ | ∀ x, N ≤ x → x ∈ S}.Finite := by
  classical
  let f : AddSubmonoid ℕ → Finset ℕ := fun S => (Finset.range N).filter (· ∈ S)
  apply Set.Finite.of_finite_image (f := f)
  · apply (Finset.range N).powerset.finite_toSet.subset
    rintro _ ⟨S, -, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  · intro S hS T hT hST
    ext x
    by_cases hx : x < N
    · have h := congrArg (fun s : Finset ℕ => x ∈ s) hST
      simpa [f, hx] using h
    · exact iff_of_true (hS x (not_lt.1 hx)) (hT x (not_lt.1 hx))

/-- The gaps `1, …, m - 1` give `m ≤ g + 1`. -/
theorem le_genus_add_one {S : AddSubmonoid ℕ} {m : ℕ} (hm : HasMultiplicity S m)
    (hfin : ((S : Set ℕ)ᶜ).Finite) : m ≤ genus S + 1 := by
  have hsub : Set.Ioo 0 m ⊆ (S : Set ℕ)ᶜ := fun x hx =>
    notMem_of_pos_of_lt hm hx.1 hx.2
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [← Finset.coe_Ioo, Set.ncard_coe_finset, Nat.card_Ioo] at hcard
  unfold genus
  omega

/-- `𝒩(q, g)` is finite, so `Set.ncard` counts it faithfully. -/
theorem depthLe_finite (q g : ℕ) : (depthLe q g).Finite := by
  apply (setOf_forall_le_mem_finite (q * (g + 1))).subset
  rintro S ⟨hg, m, hm, hd⟩ x hx
  have hle := le_genus_add_one hm (compl_finite_of_depth hd)
  rw [hg] at hle
  exact hd x (le_trans (Nat.mul_le_mul_left q hle) hx)

/-- The multiplicity is unique. -/
theorem hasMultiplicity_unique {S : AddSubmonoid ℕ} {m m' : ℕ} (hm : HasMultiplicity S m)
    (hm' : HasMultiplicity S m') : m = m' :=
  le_antisymm (hm.2.2 m' hm'.2.1 hm'.1) (hm'.2.2 m hm.2.1 hm.1)

/-- The multiplicity `min (S \ {0})` (`sInf`, junk `0` when `S = {0}`). -/
noncomputable def mult (S : AddSubmonoid ℕ) : ℕ := sInf {x | x ∈ S ∧ 0 < x}

/-- `mult` agrees with `HasMultiplicity`. -/
theorem mult_eq {S : AddSubmonoid ℕ} {m : ℕ} (hm : HasMultiplicity S m) : mult S = m :=
  le_antisymm (Nat.sInf_le ⟨hm.2.1, hm.1⟩)
    (le_csInf ⟨m, hm.2.1, hm.1⟩ fun x hx => hm.2.2 x hx.1 hx.2)

/-- `α_b` as a self-map, using the multiplicity of its argument. -/
noncomputable def alphaMap (b : Bool) (S : AddSubmonoid ℕ) : AddSubmonoid ℕ :=
  alpha S (mult S) b

/-- For `2 ≤ q ≤ 3`, `α₁ : 𝒩(q, k) → 𝒩(q, k+1)` and `α₂ : 𝒩(q, k) → 𝒩(q, k+2)`. -/
theorem alphaMap_mem {b : Bool} {q k : ℕ} (hq2 : 2 ≤ q) (hq3 : q ≤ 3) {S : AddSubmonoid ℕ}
    (hS : S ∈ depthLe q k) : alphaMap b S ∈ depthLe q (k + if b then 1 else 2) := by
  obtain ⟨hg, m, hm, hd⟩ := hS
  have hd3 := depth_three_of_le hq3 hd
  unfold alphaMap
  rw [mult_eq hm]
  exact ⟨by rw [genus_alpha hm hd3, hg], m + 1, hasMultiplicity_alpha hm hd3,
    depth_alpha hq2 hq3 hd⟩

/-- `α_b(S) = α_{b'}(S')` forces `b = b'` and `S = S'` (injectivity and disjointness:
`2m + 1 ∈ α₁(S)` but `2m + 1 ∉ α₂(S')`). -/
theorem alphaMap_eq_iff {b b' : Bool} {S S' : AddSubmonoid ℕ} {m m' : ℕ}
    (hm : HasMultiplicity S m) (hd : ∀ x, 3 * m ≤ x → x ∈ S)
    (hm' : HasMultiplicity S' m') (hd' : ∀ x, 3 * m' ≤ x → x ∈ S')
    (h : alphaMap b S = alphaMap b' S') : b = b' ∧ S = S' := by
  unfold alphaMap at h
  rw [mult_eq hm, mult_eq hm'] at h
  have hmm : m = m' := by
    have h1 := hasMultiplicity_alpha (b := b) hm hd
    rw [h] at h1
    have h2 := hasMultiplicity_unique (hasMultiplicity_alpha (b := b') hm' hd') h1
    omega
  subst hmm
  have hb : b = b' := by
    have key : ∀ c : Bool, (2 * m + 1 ∈ alpha S m c ↔ c = true) ∧
        (2 * m + 1 ∈ alpha S' m c ↔ c = true) := by
      intro c
      constructor
      · rw [mem_alpha_iff hd]
        constructor
        · rintro (h | h | h | h)
          · omega
          · omega
          · exact h.1
          · omega
        · intro hc; exact Or.inr (Or.inr (Or.inl ⟨hc, rfl⟩))
      · rw [mem_alpha_iff hd']
        constructor
        · rintro (h | h | h | h)
          · omega
          · omega
          · exact h.1
          · omega
        · intro hc; exact Or.inr (Or.inr (Or.inl ⟨hc, rfl⟩))
    have e := (key b).1
    rw [h, (key b').2] at e
    cases b <;> cases b' <;> simp_all
  subst hb
  refine ⟨rfl, ?_⟩
  ext y
  rw [mem_iff_psi_mem (b := b) hm hd, mem_iff_psi_mem (b := b) hm' hd', h]

/-- `α₁` and `α₂` are injective on `𝒩(q, j)`. -/
theorem alphaMap_injOn {q : ℕ} (hq3 : q ≤ 3) (b : Bool) (j : ℕ) :
    Set.InjOn (alphaMap b) (depthLe q j) := by
  rintro S ⟨-, m, hm, hd⟩ S' ⟨-, m', hm', hd'⟩ h
  exact (alphaMap_eq_iff hm (depth_three_of_le hq3 hd) hm' (depth_three_of_le hq3 hd') h).2

/-- **Proposition (disjoint images), arXiv:1811.10295 §5.** `im α₁ ∩ im α₂ = ∅`. -/
theorem disjoint_image_alphaMap {q : ℕ} (hq3 : q ≤ 3) (j k : ℕ) :
    Disjoint (alphaMap true '' depthLe q j) (alphaMap false '' depthLe q k) := by
  rw [Set.disjoint_left]
  rintro _ ⟨S, ⟨-, m, hm, hd⟩, rfl⟩ ⟨S', ⟨-, m', hm', hd'⟩, h⟩
  exact absurd (alphaMap_eq_iff hm' (depth_three_of_le hq3 hd') hm
    (depth_three_of_le hq3 hd) h).1 (by decide)

/-- Both images land in genus `k + 2`: `α₁(𝒩(q, k+1)) ∪ α₂(𝒩(q, k)) ⊆ 𝒩(q, k+2)`. -/
theorem image_alphaMap_union_subset {q : ℕ} (hq2 : 2 ≤ q) (hq3 : q ≤ 3) (k : ℕ) :
    alphaMap true '' depthLe q (k + 1) ∪ alphaMap false '' depthLe q k ⊆ depthLe q (k + 2) := by
  rintro _ (⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩)
  · exact alphaMap_mem (b := true) hq2 hq3 hS
  · exact alphaMap_mem (b := false) hq2 hq3 hS

/-- The disjoint union of the two images has `#𝒩(q, k+1) + #𝒩(q, k)` elements. -/
theorem ncard_image_alphaMap_union {q : ℕ} (hq2 : 2 ≤ q) (hq3 : q ≤ 3) (k : ℕ) :
    (alphaMap true '' depthLe q (k + 1) ∪ alphaMap false '' depthLe q k).ncard =
      (depthLe q (k + 1)).ncard + (depthLe q k).ncard := by
  have hsub := image_alphaMap_union_subset hq2 hq3 k
  have hfin := depthLe_finite q (k + 2)
  rw [Set.ncard_union_eq (disjoint_image_alphaMap hq3 _ _)
    (hfin.subset (Set.subset_union_left.trans hsub))
    (hfin.subset (Set.subset_union_right.trans hsub)),
    (alphaMap_injOn hq3 true _).ncard_image, (alphaMap_injOn hq3 false _).ncard_image]

/-- For `q ∈ {2, 3}`: `#𝒩(q, k+1) + #𝒩(q, k) ≤ #𝒩(q, k+2)`. -/
theorem ncard_add_ncard_le {q : ℕ} (hq2 : 2 ≤ q) (hq3 : q ≤ 3) (k : ℕ) :
    (depthLe q (k + 1)).ncard + (depthLe q k).ncard ≤ (depthLe q (k + 2)).ncard := by
  rw [← ncard_image_alphaMap_union hq2 hq3 k]
  exact Set.ncard_le_ncard (image_alphaMap_union_subset hq2 hq3 k) (depthLe_finite q (k + 2))

/-- **Corollary `cor n'` of arXiv:1811.10295 (Eliahou–Fromentin, *Gapsets and numerical
semigroups*, §5).** Let `n'_g` be the number of numerical semigroups of genus `g` and depth
`q = ⌈c/m⌉ ≤ 3` (conductor `c ≤ 3m`), the semigroup `ℕ` (genus `0`, depth `0`) included.
Verbatim: "For all $g \ge 2$, we have $n_g' \,\ge \, n_{g-1}'+n_{g-2}'$."
Here `n'_g = (depthLe 3 g).ncard`; the hypothesis `2 ≤ g` keeps both `ℕ`-subtractions genuine. -/
theorem eliahou_fromentin_lower {g : ℕ} (hg : 2 ≤ g) :
    (depthLe 3 (g - 1)).ncard + (depthLe 3 (g - 2)).ncard ≤ (depthLe 3 g).ncard := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
  simpa using ncard_add_ncard_le (by norm_num : 2 ≤ 3) le_rfl k

/-! ## Zhao's count for depth `≤ 2` (arXiv:1811.10295, §4)

For depth `≤ 2` the maps `α₁, α₂` are jointly surjective onto genus `≥ 2` (Lemma
`filtrations of depth 2`): the inverse is the pull-back along `psi`. -/

/-- For `T` of multiplicity `m + 1` and depth `≤ 2`, the pull-back `ψ_m⁻¹(T)` as a
submonoid. -/
def pullSub (m : ℕ) (T : AddSubmonoid ℕ) (hm0 : 0 < m) (hT : HasMultiplicity T (m + 1))
    (hd : ∀ x, 2 * (m + 1) ≤ x → x ∈ T) : AddSubmonoid ℕ where
  carrier := {y | psi m y ∈ T}
  zero_mem' := by
    show psi m 0 ∈ T
    simp [psi, hm0]
  add_mem' := by
    intro a c ha hc
    show psi m (a + c) ∈ T
    have ha' : psi m a ∈ T := ha
    have hc' : psi m c ∈ T := hc
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simpa using hc'
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simpa using ha'
    have hpos : ∀ y, 0 < y → psi m y ∈ T → m ≤ y := by
      intro y hy0 hy
      by_contra hlt
      have hpy : psi m y = y := by simp [psi, show y < m by omega]
      rw [hpy] at hy
      have := hT.2.2 y hy hy0
      omega
    have h1 := hpos a ha0 ha'
    have h2 := hpos c hc0 hc'
    apply hd
    unfold psi
    split_ifs <;> omega

/-- **Surjectivity for depth `≤ 2`.** Every `T ∈ 𝒩(2, k+1)` is `α_b(S)` for some
`S ∈ 𝒩(2, j)` with `k + 1 = j + (1 or 2)`. -/
theorem exists_alpha_eq {k : ℕ} {T : AddSubmonoid ℕ} (hT : T ∈ depthLe 2 (k + 1)) :
    ∃ (b : Bool) (S : AddSubmonoid ℕ) (j : ℕ), S ∈ depthLe 2 j ∧ alphaMap b S = T ∧
      k + 1 = j + if b then 1 else 2 := by
  classical
  obtain ⟨hg, M, hM, hd⟩ := hT
  have hM2 : 2 ≤ M := by
    by_contra hlt
    have hM1 : M = 1 := by have := hM.1; omega
    subst hM1
    have htop : (T : Set ℕ)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false,
        not_not]
      rcases Nat.lt_or_ge x 2 with hx | hx
      · interval_cases x
        · exact T.zero_mem
        · exact hM.2.1
      · exact hd x (by omega)
    unfold genus at hg
    rw [htop, Set.ncard_empty] at hg
    omega
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hm0 : 0 < m := by omega
  let S := pullSub m T hm0 hM hd
  have hmemS : ∀ y, y ∈ S ↔ psi m y ∈ T := fun y => Iff.rfl
  have hSm : HasMultiplicity S m := by
    refine ⟨hm0, ?_, fun y hy hy0 => ?_⟩
    · rw [hmemS]
      simpa [psi, show m < 2 * m by omega] using hM.2.1
    · rw [hmemS] at hy
      by_contra hlt
      have hpy : psi m y = y := by simp [psi, show y < m by omega]
      rw [hpy] at hy
      have := hM.2.2 y hy hy0
      omega
  have hSd : ∀ x, 2 * m ≤ x → x ∈ S := by
    intro x hx
    rw [hmemS]
    apply hd
    unfold psi
    split_ifs <;> omega
  have hSd3 : ∀ x, 3 * m ≤ x → x ∈ S := depth_three_of_le (by norm_num) hSd
  let b : Bool := decide (2 * m + 1 ∈ T)
  have heq : alpha S m b = T := by
    ext x
    by_cases hxm : x = m
    · subst hxm
      rw [mem_alpha_iff hSd3]
      refine iff_of_false (by rintro (h | h | h | h) <;> omega) ?_
      exact notMem_of_pos_of_lt hM hm0 (by omega)
    by_cases hx2 : x = 2 * m + 1
    · subst hx2
      rw [mem_alpha_iff hSd3]
      constructor
      · rintro (h | h | h | h)
        · omega
        · omega
        · simpa [b] using h.1
        · omega
      · intro h
        exact Or.inr (Or.inr (Or.inl ⟨by simpa [b] using h, rfl⟩))
    obtain ⟨y, rfl⟩ := exists_psi_eq hxm hx2
    rw [← mem_iff_psi_mem hSm hSd3, hmemS]
  refine ⟨b, S, genus S, ⟨rfl, m, hSm, hSd⟩, ?_, ?_⟩
  · unfold alphaMap
    rw [mult_eq hSm, heq]
  · rw [← hg, ← heq, genus_alpha hSm hSd3]

/-- Genus `0`: the only numerical semigroup is `ℕ`. -/
theorem depthLe_zero (q : ℕ) : depthLe q 0 = {⊤} := by
  ext S
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hg, m, hm, hd⟩
    have hfin := compl_finite_of_depth hd
    unfold genus at hg
    rw [Set.ncard_eq_zero hfin, Set.compl_empty_iff] at hg
    exact SetLike.coe_injective (hg.trans AddSubmonoid.coe_top.symm)
  · rintro rfl
    refine ⟨?_, 1, ⟨Nat.one_pos, AddSubmonoid.mem_top 1, fun x _ hx => hx⟩,
      fun x _ => AddSubmonoid.mem_top x⟩
    unfold genus
    simp

/-- `#𝒩(q, 0) = 1`. -/
theorem ncard_depthLe_zero (q : ℕ) : (depthLe q 0).ncard = 1 := by
  rw [depthLe_zero, Set.ncard_singleton]

/-- `𝒩(2, k+2) = α₁(𝒩(2, k+1)) ⊔ α₂(𝒩(2, k))`. -/
theorem depthLe_two_eq_union (k : ℕ) :
    depthLe 2 (k + 2) = alphaMap true '' depthLe 2 (k + 1) ∪ alphaMap false '' depthLe 2 k := by
  apply le_antisymm
  · intro T hT
    obtain ⟨b, S, j, hS, rfl, hj⟩ := exists_alpha_eq hT
    cases b
    · have hjk : j = k := by
        simp only [Bool.false_eq_true, if_false] at hj
        omega
      right
      exact ⟨S, by simpa [hjk] using hS, rfl⟩
    · have hjk : j = k + 1 := by
        simp only [if_true] at hj
        omega
      left
      exact ⟨S, by simpa [hjk] using hS, rfl⟩
  · rintro _ (⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩)
    · exact alphaMap_mem (b := true) le_rfl (by norm_num) hS
    · exact alphaMap_mem (b := false) le_rfl (by norm_num) hS

/-- `𝒩(2, 1) = α₁(𝒩(2, 0)) = {⟨2, 3⟩}`. -/
theorem depthLe_two_one : depthLe 2 1 = alphaMap true '' depthLe 2 0 := by
  apply le_antisymm
  · intro T hT
    obtain ⟨b, S, j, hS, rfl, hj⟩ := exists_alpha_eq (k := 0) hT
    cases b
    · simp at hj
    · have hj0 : j = 0 := by
        simp only [if_true] at hj
        omega
      exact ⟨S, by simpa [hj0] using hS, rfl⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact alphaMap_mem (b := true) le_rfl (by norm_num) hS

/-- `#𝒩(2, 1) = 1`. -/
theorem ncard_depthLe_two_one : (depthLe 2 1).ncard = 1 := by
  rw [depthLe_two_one, (alphaMap_injOn (by norm_num) true 0).ncard_image, ncard_depthLe_zero]

/-- **Proposition (q ≤ 2) of arXiv:1811.10295, §4.** For `g ≥ 2`,
`|𝒩(g, q ≤ 2)| = |𝒩(g-1, q ≤ 2)| + |𝒩(g-2, q ≤ 2)|` (here at `g = k + 2`). -/
theorem ncard_depthLe_two_add_two (k : ℕ) :
    (depthLe 2 (k + 2)).ncard = (depthLe 2 (k + 1)).ncard + (depthLe 2 k).ncard := by
  rw [depthLe_two_eq_union, ncard_image_alphaMap_union le_rfl (by norm_num)]

/-- **Corollary `fibo` of arXiv:1811.10295 (Zhao's theorem).** Verbatim: "For all
$g \ge 0$, we have $|\mathcal{F}(g, q \le 2)|=\F_{g+1}$, where $\F_n$ denote the $n$th
Fibonacci number." The number of numerical semigroups of genus `g` and depth `≤ 2` is
`Nat.fib (g + 1)` (`fib 1 = fib 2 = 1`). -/
theorem zhao_depth_two (g : ℕ) : (depthLe 2 g).ncard = Nat.fib (g + 1) := by
  suffices h : ∀ k, (depthLe 2 k).ncard = Nat.fib (k + 1) ∧
      (depthLe 2 (k + 1)).ncard = Nat.fib (k + 2) from (h g).1
  intro k
  induction k with
  | zero => exact ⟨ncard_depthLe_zero 2, ncard_depthLe_two_one⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [ncard_depthLe_two_add_two, ih.1, ih.2, Nat.fib_add_two (n := k + 1), add_comm]

/-! ## Ground truth -/

/-- `⟨2, 7⟩ = ℕ \ {1, 3, 5}`: multiplicity `2`, conductor `6 = 3 · 2`, so depth exactly `3`. -/
def twoSeven : AddSubmonoid ℕ where
  carrier := {x | x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega

/-- `⟨2, 9⟩ = ℕ \ {1, 3, 5, 7}`: multiplicity `2`, conductor `8 > 3 · 2`, depth `4`. -/
def twoNine : AddSubmonoid ℕ where
  carrier := {x | x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5 ∧ x ≠ 7}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega

/-- `ℕ` is the unique member of `𝒩(3, 0)`, so `n'_0 = 1`. -/
example : depthLe 3 0 = {⊤} := depthLe_zero 3

/-- `⟨2, 5⟩ = ℕ \ {1, 3}` (conductor `4 = 2 · 2`) has depth `≤ 2` and genus `2`. -/
example : twoFive ∈ depthLe 2 2 :=
  ⟨genus_twoFive, 2, ⟨by norm_num, by simp [mem_twoFive], fun x hx hx0 => by
    rw [mem_twoFive] at hx; omega⟩, fun x hx => by rw [mem_twoFive]; omega⟩

/-- `⟨2, 7⟩` has genus `3` and depth `3`: it lies in `𝒩(3, 3)` but not in `𝒩(2, 3)`. -/
example : twoSeven ∈ depthLe 3 3 ∧ twoSeven ∉ depthLe 2 3 := by
  have hc : ((twoSeven : AddSubmonoid ℕ) : Set ℕ)ᶜ = {1, 3, 5} := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    change ¬(x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5) ↔ _
    omega
  have hg : genus twoSeven = 3 := by
    unfold genus
    rw [hc, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by norm_num)]
  have hm : HasMultiplicity twoSeven 2 :=
    ⟨by norm_num, by change (2 ≠ 1 ∧ 2 ≠ 3 ∧ 2 ≠ 5); omega, fun x hx hx0 => by
      change (x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5) at hx; omega⟩
  refine ⟨⟨hg, 2, hm, fun x hx => by change (x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5); omega⟩, ?_⟩
  rintro ⟨-, m, hm', hd⟩
  rw [hasMultiplicity_unique hm' hm] at hd
  exact (hd 5 (by norm_num)).2.2 rfl

/-- `⟨2, 9⟩` has depth `4`: it lies in no `𝒩(3, g)`. -/
example (g : ℕ) : twoNine ∉ depthLe 3 g := by
  have hm : HasMultiplicity twoNine 2 :=
    ⟨by norm_num, by change (2 ≠ 1 ∧ 2 ≠ 3 ∧ 2 ≠ 5 ∧ 2 ≠ 7); omega, fun x hx hx0 => by
      change (x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5 ∧ x ≠ 7) at hx; omega⟩
  rintro ⟨-, m, hm', hd⟩
  rw [hasMultiplicity_unique hm' hm] at hd
  exact (hd 7 (by norm_num)).2.2.2 rfl

/-- Zhao's count at small genus: `1, 1, 2, 3, 5, 8` semigroups of depth `≤ 2`. -/
example : ((List.range 6).map fun g => (depthLe 2 g).ncard) = [1, 1, 2, 3, 5, 8] := by
  simp [List.range_succ, zhao_depth_two, Nat.fib_add_two]

/-- The lower bound at `g = 2`: `n'_2 ≥ n'_1 + n'_0 ≥ 2`. -/
example : 2 ≤ (depthLe 3 2).ncard := by
  have h := eliahou_fromentin_lower (g := 2) le_rfl
  have hmem : alphaMap true ⊤ ∈ depthLe 3 (0 + 1) :=
    alphaMap_mem (by norm_num) le_rfl (by rw [depthLe_zero]; rfl)
  have h1 : 0 < (depthLe 3 1).ncard := (Set.ncard_pos (depthLe_finite 3 1)).2 ⟨_, hmem⟩
  norm_num [ncard_depthLe_zero] at h
  omega

end Candidates.EliahouFromentinDepthThree
