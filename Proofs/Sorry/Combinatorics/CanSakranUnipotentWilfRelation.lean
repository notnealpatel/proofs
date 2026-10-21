/-
# Can–Sakran Conjecture 1.9: relating the unipotent and generalized Wilf invariants

## Source

M. B. Can and N. Sakran, *On Generalized Wilf Conjectures*, arXiv:2306.05530
(published: Port. Math. 81 (2024) 21–55).  Introduction,
Conjecture `C:relatingconjectures`, display `A:newconjecture`
(Conjecture 1.9 in the published numbering).  Recorded 2026-10-21.

Verbatim (arXiv v1 source):

```
Independently of the relationship between the two conjectures, we think that
the following inequality will hold true for every unipotent numerical monoid
in P(n,N).
Conjecture. Let M := P(n,N). Let S be a unipotent numerical monoid in M.
Then we have
    c_M(S) / c(phi(S))  <=  n_M(S) / n(phi(S)).
```

with (same source, Introduction)

* `P(n,N)_k := {x : k <= max_{i,j} x_ij} ∪ {1_n}` (the `k`-th fundamental
  submonoid), and `r_M(S)` the smallest positive `k` with `P(n,N)_k ∩ M ⊆ S`;
* `c_M(S) := r_M(S)^(n-1)`,
  `n_M(S) := |{1_n} ∪ S \ P(n,N)_{r_M(S)}|`;
* `phi : P(n,N) ≅ N^(n-1)`, `(a_ij) ↦ (a_12, …, a_1n)`;
* for a complement-finite submonoid `T` of `N^(n-1)` with hole set `H(T)`,
  `c(T) := |{a : a ⩽ b for some b ∈ H(T)}|` and
  `n(T) := |{a ∈ T : a ⩽ b for some b ∈ H(T)}|`.

## Status

Stated as an open conjecture in the paper (checked there on one example only).
The proof below is elementary: every hole lies in the box `B = [0, r-1]^d`,
so `H ⊆ D ⊆ B` with `D` the down-closure of the holes, `c_M = |B|`,
`n_M = |B| - |H|`, `c = |D|`, `n = |D| - |H|`, and
`|B| (|D| - |H|) ≤ (|B| - |H|) |D|` is `|H| |D| ≤ |H| |B|`.

## Formalization choices

We work directly in `N^d = Fin d → ℕ` (with `d = n - 1`), i.e. with
`T = phi(S)`; `phi` is a monoid isomorphism and the fundamental submonoid
`P(n,N)_k` corresponds to `{x | x = 0 ∨ ∃ i, k ≤ x i}` for `k ≥ 1` (the
diagonal entries `1` make `P(n,N)_1` everything).  Every cardinality is a
`Set.ncard`; the complement-finiteness hypothesis keeps every counted set
finite.

## Ground truth

The paper's own example (Figure `F:thin2`, a thin monoid in `P(3,N)`) is
formalized below: `r_M = 6`, `c_M = 36`, `n_M = 12`, `n = 8` as in the paper,
and `c = 32`.  The paper prints `c(S) = 34` (and `2 c(S) = 68`); that is a
typo, since the figure has 24 holes, and `n = 8` forces `c = 8 + 24 = 32`.
-/
import Mathlib

set_option autoImplicit false

namespace CanSakranUnipotentWilfRelation

open Set

variable {d : ℕ}

/-! ## Definitions -/

/-- The `k`-th fundamental submonoid `P(n,ℕ)_k` of `P(n,ℕ)`, transported to
`ℕ^d` (`d = n - 1`) along `phi`: the identity together with the vectors having
some coordinate at least `k`. -/
def fundamentalSet (d k : ℕ) : Set (Fin d → ℕ) :=
  {x | x = 0 ∨ ∃ i, k ≤ x i}

/-- The hole set `H(S) = ℕ^d \ S`. -/
def holeSet (S : AddSubmonoid (Fin d → ℕ)) : Set (Fin d → ℕ) :=
  {x | x ∉ S}

/-- The generating number `r_M(S)`: the smallest positive `k` with
`P(n,ℕ)_k ⊆ S`. -/
noncomputable def generatingNumber (S : AddSubmonoid (Fin d → ℕ)) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ fundamentalSet d k ⊆ S}

/-- The conductor of `S` relative to `M = P(n,ℕ)`: `c_M(S) = r_M(S)^d`. -/
noncomputable def conductorM (S : AddSubmonoid (Fin d → ℕ)) : ℕ :=
  generatingNumber S ^ d

/-- The sporadicity of `S` relative to `M`:
`n_M(S) = |{1} ∪ (S \ P(n,ℕ)_{r_M(S)})|`. -/
noncomputable def sporadicityM (S : AddSubmonoid (Fin d → ℕ)) : ℕ :=
  ({0} ∪ ((S : Set (Fin d → ℕ)) \ fundamentalSet d (generatingNumber S))).ncard

/-- The down-closure `{a | a ⩽ b for some hole b}` of the hole set. -/
def holeDownClosure (S : AddSubmonoid (Fin d → ℕ)) : Set (Fin d → ℕ) :=
  {a | ∃ b ∈ holeSet S, a ≤ b}

/-- The Cisto et al. conductor `c(T) = |{a : a ⩽ b for some b ∈ H(T)}|`. -/
noncomputable def wilfC (S : AddSubmonoid (Fin d → ℕ)) : ℕ :=
  (holeDownClosure S).ncard

/-- The Cisto et al. count `n(T) = |{a ∈ T : a ⩽ b for some b ∈ H(T)}|`. -/
noncomputable def wilfN (S : AddSubmonoid (Fin d → ℕ)) : ℕ :=
  {a | a ∈ S ∧ a ∈ holeDownClosure S}.ncard

/-- The box `[0, r-1]^d`. -/
def boxSet (d r : ℕ) : Set (Fin d → ℕ) :=
  {a | ∀ i, a i < r}

/-! ## The counting core -/

/-- For finite sets `H ⊆ D ⊆ B`:
`|B| · |D \ H| ≤ |B \ H| · |D|`. -/
theorem ncard_mul_ncard_sdiff_le {α : Type*} {H D B : Set α} (hB : B.Finite)
    (hHD : H ⊆ D) (hDB : D ⊆ B) :
    B.ncard * (D \ H).ncard ≤ (B \ H).ncard * D.ncard := by
  have hD : D.Finite := hB.subset hDB
  have hH : H.Finite := hD.subset hHD
  have h1 : (D \ H).ncard = D.ncard - H.ncard := Set.ncard_sdiff hHD hH
  have h2 : (B \ H).ncard = B.ncard - H.ncard := Set.ncard_sdiff (hHD.trans hDB) hH
  have hHDc : H.ncard ≤ D.ncard := Set.ncard_le_ncard hHD hD
  have hDBc : D.ncard ≤ B.ncard := Set.ncard_le_ncard hDB hB
  rw [h1, h2]
  zify [hHDc, hHDc.trans hDBc]
  -- the inequality is `|H| |D| ≤ |H| |B|`
  nlinarith [Nat.zero_le H.ncard]

/-! ## Structure of complement-finite submonoids -/

/-- The box `[0, r-1]^d` is the finset `piFinset (fun _ => range r)`. -/
theorem boxSet_eq_piFinset (d r : ℕ) :
    boxSet d r = ↑(Fintype.piFinset fun _ : Fin d => Finset.range r) := by
  ext a
  simp [boxSet]

/-- The box `[0, r-1]^d` is finite. -/
theorem boxSet_finite (d r : ℕ) : (boxSet d r).Finite := by
  rw [boxSet_eq_piFinset]
  exact Finset.finite_toSet _

/-- The box `[0, r-1]^d` has `r^d` elements. -/
theorem ncard_boxSet (d r : ℕ) : (boxSet d r).ncard = r ^ d := by
  rw [boxSet_eq_piFinset, Set.ncard_coe_finset]
  simp

/-- A complement-finite submonoid contains some fundamental submonoid. -/
theorem exists_fundamentalSet_subset (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    ∃ k, 0 < k ∧ fundamentalSet d k ⊆ S := by
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨(∑ i, M i) + 1, Nat.succ_pos _, ?_⟩
  rintro x (hx0 | ⟨i, hi⟩)
  · rw [hx0]
    exact S.zero_mem
  · by_contra hxS
    have hxM : x ≤ M := hM hxS
    have hMi : M i ≤ ∑ j, M j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (M j)) (Finset.mem_univ i)
    have hxi : x i ≤ M i := hxM i
    omega

/-- The generating number is positive and its fundamental submonoid lies in
`S`. -/
theorem generatingNumber_spec (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    0 < generatingNumber S ∧ fundamentalSet d (generatingNumber S) ⊆ S :=
  Nat.sInf_mem (exists_fundamentalSet_subset S hfin)

/-- Every hole lies in the box `[0, r_M(S) - 1]^d`. -/
theorem holeSet_subset_boxSet (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    holeSet S ⊆ boxSet d (generatingNumber S) := by
  intro h hh i
  by_contra hle
  exact hh ((generatingNumber_spec S hfin).2 (Or.inr ⟨i, not_lt.mp hle⟩))

/-- The down-closure of the holes lies in the box `[0, r_M(S) - 1]^d`. -/
theorem holeDownClosure_subset_boxSet (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    holeDownClosure S ⊆ boxSet d (generatingNumber S) := by
  rintro a ⟨b, hb, hab⟩ i
  exact lt_of_le_of_lt (hab i) (holeSet_subset_boxSet S hfin hb i)

/-- Every hole lies in the down-closure of the holes. -/
theorem holeSet_subset_holeDownClosure (S : AddSubmonoid (Fin d → ℕ)) :
    holeSet S ⊆ holeDownClosure S :=
  fun h hh => ⟨h, hh, le_rfl⟩

/-- The sporadic elements are the box points of `S`:
`{0} ∪ (S \ P_r) = [0, r-1]^d \ H`. -/
theorem sporadic_eq_boxSet_diff (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    ({0} ∪ ((S : Set (Fin d → ℕ)) \ fundamentalSet d (generatingNumber S))) =
      boxSet d (generatingNumber S) \ holeSet S := by
  have hpos : 0 < generatingNumber S := (generatingNumber_spec S hfin).1
  ext a
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff, SetLike.mem_coe,
    fundamentalSet, Set.mem_ofPred_eq, boxSet, holeSet, not_not, not_or, not_exists, not_le]
  constructor
  · rintro (rfl | ⟨haS, -, hlt⟩)
    · exact ⟨fun _ => hpos, S.zero_mem⟩
    · exact ⟨hlt, haS⟩
  · rintro ⟨hlt, haS⟩
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · exact Or.inr ⟨haS, ha0, hlt⟩

/-- The sporadicity is `|[0, r-1]^d \ H|`. -/
theorem sporadicityM_eq (S : AddSubmonoid (Fin d → ℕ)) (hfin : (holeSet S).Finite) :
    sporadicityM S = (boxSet d (generatingNumber S) \ holeSet S).ncard := by
  rw [sporadicityM, sporadic_eq_boxSet_diff S hfin]

/-- The Cisto et al. count is `n(T) = |D \ H|`. -/
theorem wilfN_eq (S : AddSubmonoid (Fin d → ℕ)) :
    wilfN S = (holeDownClosure S \ holeSet S).ncard := by
  have hset : {a | a ∈ S ∧ a ∈ holeDownClosure S} = holeDownClosure S \ holeSet S := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, holeSet, not_not]
    exact and_comm
  rw [wilfN, hset]

/-- For a proper complement-finite submonoid, `0 ∈ D \ H`, so `n(T) > 0`. -/
theorem wilfN_pos (S : AddSubmonoid (Fin d → ℕ)) (hfin : (holeSet S).Finite)
    (hne : (holeSet S).Nonempty) : 0 < wilfN S := by
  rw [wilfN_eq]
  obtain ⟨h, hh⟩ := hne
  have hfinD : (holeDownClosure S \ holeSet S).Finite :=
    ((boxSet_finite d _).subset (holeDownClosure_subset_boxSet S hfin)).sdiff
  have hmem : (0 : Fin d → ℕ) ∈ holeDownClosure S \ holeSet S :=
    ⟨⟨h, hh, fun i => Nat.zero_le (h i)⟩, fun h0 => h0 S.zero_mem⟩
  exact (Set.ncard_pos hfinD).mpr ⟨0, hmem⟩

/-! ## Conjecture 1.9 -/

/-- **Can–Sakran Conjecture 1.9, cross-multiplied form.**  For every
complement-finite submonoid `S` of `ℕ^d` (a unipotent numerical monoid in
`P(d+1, ℕ)` read through `phi`): `c_M(S) · n(phi S) ≤ n_M(S) · c(phi S)`. -/
theorem conductorM_mul_wilfN_le (S : AddSubmonoid (Fin d → ℕ))
    (hfin : (holeSet S).Finite) :
    conductorM S * wilfN S ≤ sporadicityM S * wilfC S := by
  have hcM : conductorM S = (boxSet d (generatingNumber S)).ncard :=
    (ncard_boxSet d _).symm
  rw [hcM, sporadicityM_eq S hfin, wilfN_eq, wilfC]
  exact ncard_mul_ncard_sdiff_le (boxSet_finite d _) (holeSet_subset_holeDownClosure S)
    (holeDownClosure_subset_boxSet S hfin)

/-- **Can–Sakran Conjecture 1.9** (arXiv:2306.05530, Conjecture
`C:relatingconjectures`; stated open there).  Let `S` be a unipotent numerical
monoid in `M = P(d+1, ℕ)`, read through `phi` as a complement-finite submonoid
of `ℕ^d`, with nonempty hole set (so both denominators are positive).  Then
`c_M(S) / c(phi S) ≤ n_M(S) / n(phi S)`. -/
theorem conj_1_9 (S : AddSubmonoid (Fin d → ℕ)) (hfin : (holeSet S).Finite)
    (hne : (holeSet S).Nonempty) :
    (conductorM S : ℚ) / wilfC S ≤ (sporadicityM S : ℚ) / wilfN S := by
  have hnpos : 0 < wilfN S := wilfN_pos S hfin hne
  have hcpos : 0 < wilfC S := by
    have hsub : holeDownClosure S \ holeSet S ⊆ holeDownClosure S := Set.sdiff_subset
    have hfinD : (holeDownClosure S).Finite :=
      (boxSet_finite d _).subset (holeDownClosure_subset_boxSet S hfin)
    have hle : wilfN S ≤ wilfC S := by
      rw [wilfN_eq, wilfC]
      exact Set.ncard_le_ncard hsub hfinD
    omega
  have hcross : (conductorM S : ℚ) * wilfN S ≤ (sporadicityM S : ℚ) * wilfC S := by
    exact_mod_cast conductorM_mul_wilfN_le S hfin
  rw [div_le_div_iff₀ (by exact_mod_cast hcpos) (by exact_mod_cast hnpos)]
  exact hcross

/-! ## Ground truth: the paper's thin monoid in `P(3, ℕ)` (Figure `F:thin2`)

Holes (`x = a 0`, `y = a 1`): rows `y ∈ {1,2,3}` with `x ≤ 5`, and rows
`y ∈ {0,4,5}` with `x ∈ {1,3}`; 24 holes in all.  The paper reports
`r_M = 6`, `n_M = 12`, `n = 8` (checked below) and `c = 34`; the correct
value, checked below, is `c = 32`. -/

/-- A set of box points `{a | p a} ⊆ [0, r-1]^d` has `ncard` equal to the
cardinality of the corresponding filter of `piFinset`. -/
theorem ncard_setOf_eq_card_filter (r : ℕ) (p : (Fin d → ℕ) → Prop) [DecidablePred p]
    (hp : ∀ a, p a → a ∈ boxSet d r) :
    {a | p a}.ncard = ((Fintype.piFinset fun _ : Fin d => Finset.range r).filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  have hbox := boxSet_eq_piFinset d r
  constructor
  · intro hpa
    have hab : a ∈ boxSet d r := hp a hpa
    rw [hbox] at hab
    exact Finset.mem_filter.mpr ⟨hab, hpa⟩
  · intro ha
    exact (Finset.mem_filter.mp ha).2

/-- The hole predicate of the paper's Figure `F:thin2` monoid. -/
def exampleHole (a : Fin 2 → ℕ) : Prop :=
  a 0 ≤ 5 ∧ a 1 ≤ 5 ∧ ((1 ≤ a 1 ∧ a 1 ≤ 3) ∨ a 0 = 1 ∨ a 0 = 3)

/-- Decidability of `exampleHole`. -/
instance : DecidablePred exampleHole := fun a => by
  unfold exampleHole
  infer_instance

/-- The paper's Figure `F:thin2` monoid in `ℕ^2 ≅ P(3, ℕ)`: the complement of
`exampleHole`. -/
def exampleMonoid : AddSubmonoid (Fin 2 → ℕ) where
  carrier := {a | ¬ exampleHole a}
  zero_mem' := by
    simp [exampleHole]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, exampleHole, Pi.add_apply] at ha hb ⊢
    omega

/-- The hole set of the example monoid is `exampleHole`. -/
theorem exampleMonoid_holeSet : holeSet exampleMonoid = {a | exampleHole a} := by
  ext a
  simp [holeSet, exampleMonoid]

/-- The example's holes lie in the box `[0,5]^2`. -/
theorem exampleHole_mem_boxSet (a : Fin 2 → ℕ) (ha : exampleHole a) : a ∈ boxSet 2 6 := by
  intro i
  fin_cases i <;> simp only [exampleHole] at ha <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega

/-- The example monoid is complement-finite. -/
theorem exampleMonoid_holeSet_finite : (holeSet exampleMonoid).Finite := by
  rw [exampleMonoid_holeSet]
  exact (boxSet_finite 2 6).subset exampleHole_mem_boxSet

/-- The example monoid has 24 holes (genus `g_M = 24`). -/
example : (holeSet exampleMonoid).ncard = 24 := by
  rw [exampleMonoid_holeSet, ncard_setOf_eq_card_filter 6 exampleHole exampleHole_mem_boxSet]
  decide

/-- The example has generating number `r_M = 6`, as in the paper. -/
theorem exampleMonoid_generatingNumber : generatingNumber exampleMonoid = 6 := by
  have h6 : 6 ∈ {k : ℕ | 0 < k ∧ fundamentalSet 2 k ⊆ exampleMonoid} := by
    refine ⟨by norm_num, ?_⟩
    intro x hx
    by_contra hxS
    have hhole : x ∈ holeSet exampleMonoid := hxS
    rw [exampleMonoid_holeSet] at hhole
    have hbox : x ∈ boxSet 2 6 := exampleHole_mem_boxSet x hhole
    rcases hx with hx0 | ⟨i, hi⟩
    · rw [hx0] at hxS
      exact hxS exampleMonoid.zero_mem
    · exact absurd (hbox i) (not_lt.mpr hi)
  apply le_antisymm (Nat.sInf_le h6)
  apply le_csInf ⟨6, h6⟩
  rintro k ⟨hk, hsub⟩
  by_contra hlt
  -- the hole `(5, 3)` lies in `P_k` for every `k ≤ 5`
  have hmem : (![5, 3] : Fin 2 → ℕ) ∈ fundamentalSet 2 k :=
    Or.inr ⟨0, by simp only [Fin.isValue, Matrix.cons_val_zero]; omega⟩
  have hS : (![5, 3] : Fin 2 → ℕ) ∈ exampleMonoid := hsub hmem
  exact hS (by decide)

/-- The example has conductor `c_M = 6^2 = 36`, as in the paper. -/
example : conductorM exampleMonoid = 36 := by
  rw [conductorM, exampleMonoid_generatingNumber]
  norm_num

/-- The example has sporadicity `n_M = 12`, as in the paper. -/
example : sporadicityM exampleMonoid = 12 := by
  rw [sporadicityM_eq _ exampleMonoid_holeSet_finite, exampleMonoid_generatingNumber,
    exampleMonoid_holeSet]
  have hset : boxSet 2 6 \ {a | exampleHole a} =
      {a : Fin 2 → ℕ | (∀ i, a i < 6) ∧ ¬ exampleHole a} := rfl
  rw [hset, ncard_setOf_eq_card_filter 6 _ (fun a ha => ha.1)]
  decide

/-- The down-closure of the example's holes is `[0,5]×[0,3] ∪ [0,3]×[0,5]`. -/
theorem exampleMonoid_holeDownClosure :
    holeDownClosure exampleMonoid = {a | a 0 ≤ 5 ∧ a 1 ≤ 3 ∨ a 0 ≤ 3 ∧ a 1 ≤ 5} := by
  ext a
  simp only [holeDownClosure, exampleMonoid_holeSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb, hab⟩
    have h0 : a 0 ≤ b 0 := hab 0
    have h1 : a 1 ≤ b 1 := hab 1
    simp only [exampleHole] at hb
    omega
  · rintro (h | h)
    · refine ⟨![5, 3], by decide, ?_⟩
      intro i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega
    · refine ⟨![3, 5], by decide, ?_⟩
      intro i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega

/-- The example has `c(phi S) = 32` (the paper prints `34`, a typo). -/
example : wilfC exampleMonoid = 32 := by
  rw [wilfC, exampleMonoid_holeDownClosure,
    ncard_setOf_eq_card_filter 6 _ (fun a ha i => by fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega)]
  decide

/-- The example has `n(phi S) = 8`, as in the paper. -/
example : wilfN exampleMonoid = 8 := by
  rw [wilfN_eq, exampleMonoid_holeDownClosure, exampleMonoid_holeSet]
  have hset : {a : Fin 2 → ℕ | a 0 ≤ 5 ∧ a 1 ≤ 3 ∨ a 0 ≤ 3 ∧ a 1 ≤ 5} \ {a | exampleHole a} =
      {a | (a 0 ≤ 5 ∧ a 1 ≤ 3 ∨ a 0 ≤ 3 ∧ a 1 ≤ 5) ∧ ¬ exampleHole a} := rfl
  rw [hset, ncard_setOf_eq_card_filter 6 _ (fun a ha i => by fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega)]
  decide

/-- Non-vacuity: the hypotheses of `conj_1_9` hold jointly for the example. -/
example : (conductorM exampleMonoid : ℚ) / wilfC exampleMonoid ≤
    (sporadicityM exampleMonoid : ℚ) / wilfN exampleMonoid :=
  conj_1_9 exampleMonoid exampleMonoid_holeSet_finite
    ⟨![5, 3], by rw [exampleMonoid_holeSet]; decide⟩

end CanSakranUnipotentWilfRelation
