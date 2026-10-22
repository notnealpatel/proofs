/-
# Frankl–Wilson nonuniform `L`-intersection bound (Ray-Chaudhuri–Wilson type)

## Source

* P. Frankl, R. M. Wilson, "Intersection theorems with geometric
  consequences", Combinatorica 1 (1981) 357–368 (nonuniform `L`-intersection
  theorem).
* L. Babai, P. Frankl, *Linear Algebra Methods in Combinatorics*, Ch. 5
  (polynomial-space proof, which is the proof followed here).
* D. K. Ray-Chaudhuri, R. M. Wilson, "On `t`-designs", Osaka J. Math. 12
  (1975) 737–744 (the uniform case).

## Statement

> If `L ⊆ ℕ` has `|L| = s` and `𝒜 ⊆ 2^[n]` is `L`-intersecting
> (`|A ∩ B| ∈ L` for distinct `A, B ∈ 𝒜`), then `|𝒜| ≤ Σ_{i=0}^{s} C(n,i)`.

## Formal reading

`L`-intersecting is Mathlib's `Set.IsIntersectingOf (L : Set ℕ) 𝒜`
(`Mathlib/Combinatorics/SetFamily/Intersecting.lean`), which demands
`#(A ∩ B) ∈ L` for distinct `A, B ∈ 𝒜`.  The ground set `[n]` is `Fin n`.

## Proof (polynomial method, carried out on functions on the cube)

Work in `V := Finset (Fin n) → ℚ`.  For `S` let `supInd S X = [S ⊆ X]`.
Let `W d` be the span of `supInd S` over `#S ≤ d`; then
`dim W d ≤ Σ_{i ≤ d} C(n,i)` and `W d * W e ≤ W (d + e)` since
`supInd S * supInd T = supInd (S ∪ T)`.  For `A ∈ 𝒜` put
`f_A X = ∏_{ℓ ∈ L, ℓ < #A} (#(A ∩ X) - ℓ)`; each factor lies in `W 1`, so
`f_A ∈ W #L`.  Further `f_A A ≠ 0`, and `f_A B = 0` whenever `B ∈ 𝒜`,
`B ≠ A`, `#B ≤ #A`.  Evaluating a vanishing combination at a minimal-size set
with nonzero coefficient shows the `f_A` are linearly independent.
-/
import Mathlib

set_option autoImplicit false

namespace FranklWilson

open Finset

variable {n : ℕ}

/-- The up-set indicator of `S` on the cube: `supInd S X = 1` if `S ⊆ X`, else `0`.
In polynomial language this is the multilinear monomial `∏_{i ∈ S} x_i`
evaluated at the characteristic vector of `X`. -/
def supInd (S : Finset (Fin n)) : Finset (Fin n) → ℚ :=
  fun X => if S ⊆ X then 1 else 0

example : supInd ({0} : Finset (Fin 2)) {0, 1} = 1 := by decide
example : supInd ({0} : Finset (Fin 2)) {1} = 0 := by decide

/-- The generating up-set indicators of degree at most `d`: `supInd S` for `#S ≤ d`. -/
def gens (n d : ℕ) : Finset (Finset (Fin n) → ℚ) :=
  ((univ : Finset (Finset (Fin n))).filter fun S => #S ≤ d).image supInd

/-- The space `W d` of functions on the cube that are multilinear polynomials of
degree at most `d`: the span of `supInd S` over `#S ≤ d`. -/
def W (n d : ℕ) : Submodule ℚ (Finset (Fin n) → ℚ) :=
  Submodule.span ℚ (gens n d : Set (Finset (Fin n) → ℚ))

/-- The number of subsets of `Fin n` of size at most `d` is `Σ_{i ≤ d} C(n, i)`. -/
theorem card_filter_card_le (n d : ℕ) :
    #((univ : Finset (Finset (Fin n))).filter fun S => #S ≤ d) =
      ∑ i ∈ range (d + 1), n.choose i := by
  rw [card_eq_sum_card_fiberwise (f := fun S : Finset (Fin n) => #S) (t := range (d + 1))]
  · refine sum_congr rfl fun i hi => ?_
    have hid : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hfib : ((univ.filter fun S : Finset (Fin n) => #S ≤ d).filter fun S => #S = i) =
        powersetCard i (univ : Finset (Fin n)) := by
      ext S
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro h
        exact ⟨h ▸ hid, h⟩
    rw [hfib, card_powersetCard, card_univ, Fintype.card_fin]
  · intro S hS
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS
    simp only [coe_range, Set.mem_Iio]
    omega

/-- `dim W d ≤ Σ_{i ≤ d} C(n, i)`. -/
theorem finrank_W_le (n d : ℕ) :
    Module.finrank ℚ (W n d) ≤ ∑ i ∈ range (d + 1), n.choose i := by
  calc Module.finrank ℚ (W n d) ≤ #(gens n d) := finrank_span_finset_le_card _
    _ ≤ #((univ : Finset (Finset (Fin n))).filter fun S => #S ≤ d) := card_image_le
    _ = ∑ i ∈ range (d + 1), n.choose i := card_filter_card_le n d

/-- Product of up-set indicators: `supInd S * supInd T = supInd (S ∪ T)`. -/
theorem supInd_mul_supInd (S T : Finset (Fin n)) :
    supInd S * supInd T = supInd (S ∪ T) := by
  funext X
  simp only [Pi.mul_apply, supInd, union_subset_iff]
  split_ifs <;> simp_all

/-- Degree is subadditive: `f ∈ W d`, `g ∈ W e` imply `f * g ∈ W (d + e)`. -/
theorem mul_mem_W {d e : ℕ} {f g : Finset (Fin n) → ℚ} (hf : f ∈ W n d) (hg : g ∈ W n e) :
    f * g ∈ W n (d + e) := by
  have hle : W n d * W n e ≤ W n (d + e) := by
    rw [W, W, Submodule.span_mul_span]
    apply Submodule.span_mono
    rw [Set.mul_subset_iff]
    intro x hx y hy
    simp only [gens, coe_image, coe_filter, mem_univ, true_and, Set.mem_image,
      Set.mem_ofPred_eq] at hx hy ⊢
    obtain ⟨S, hS, rfl⟩ := hx
    obtain ⟨T, hT, rfl⟩ := hy
    exact ⟨S ∪ T, (card_union_le S T).trans (Nat.add_le_add hS hT),
      (supInd_mul_supInd S T).symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

/-- `supInd S ∈ W d` when `#S ≤ d`. -/
theorem supInd_mem_W {d : ℕ} {S : Finset (Fin n)} (hS : #S ≤ d) : supInd S ∈ W n d :=
  Submodule.subset_span (by
    simp only [gens, coe_image, coe_filter, mem_univ, true_and]
    exact ⟨S, hS, rfl⟩)

/-- The linear factor `X ↦ #(A ∩ X) - ℓ` lies in `W 1`. -/
theorem linFactor_mem_W (A : Finset (Fin n)) (ℓ : ℕ) :
    (fun X : Finset (Fin n) => (#(A ∩ X) : ℚ) - ℓ) ∈ W n 1 := by
  have hfun : (fun X : Finset (Fin n) => (#(A ∩ X) : ℚ) - ℓ) =
      (∑ i ∈ A, supInd {i}) - (ℓ : ℚ) • supInd ∅ := by
    funext X
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, supInd, singleton_subset_iff,
      empty_subset, if_true, smul_eq_mul, mul_one, sum_boole]
    congr 2
  rw [hfun]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => supInd_mem_W ?_)
    (Submodule.smul_mem _ _ (supInd_mem_W ?_))
  · simp
  · simp

/-- The Frankl–Wilson polynomial of `A`:
`f_A X = ∏_{ℓ ∈ L, ℓ < #A} (#(A ∩ X) - ℓ)`. -/
def fwPoly (L : Finset ℕ) (A : Finset (Fin n)) : Finset (Fin n) → ℚ :=
  ∏ ℓ ∈ L.filter (· < #A), fun X => (#(A ∩ X) : ℚ) - ℓ

example : fwPoly {0} ({0} : Finset (Fin 2)) {0} = 1 := by
  simp [fwPoly, Finset.filter_singleton]

/-- Each `f_A` has degree at most `#L`. -/
theorem fwPoly_mem_W (L : Finset ℕ) (A : Finset (Fin n)) : fwPoly L A ∈ W n #L := by
  have key : ∀ F : Finset ℕ,
      (∏ ℓ ∈ F, fun X : Finset (Fin n) => (#(A ∩ X) : ℚ) - ℓ) ∈ W n #F := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      rw [prod_empty]
      have h1 : (1 : Finset (Fin n) → ℚ) = supInd ∅ := by
        funext X
        simp [supInd]
      rw [h1]
      exact supInd_mem_W (by simp)
    | insert a F ha ih =>
      rw [prod_insert ha, card_insert_of_notMem ha, add_comm]
      exact mul_mem_W (linFactor_mem_W A a) ih
  have hmono : W n #(L.filter (· < #A)) ≤ W n #L :=
    Submodule.span_mono (by
      intro x hx
      simp only [gens, coe_image, coe_filter, mem_univ, true_and, Set.mem_image,
        Set.mem_ofPred_eq] at hx ⊢
      obtain ⟨S, hS, rfl⟩ := hx
      exact ⟨S, hS.trans (card_filter_le _ _), rfl⟩)
  exact hmono (key _)

/-- Evaluation formula `f_A X = ∏_{ℓ ∈ L, ℓ < #A} (#(A ∩ X) - ℓ)`. -/
theorem fwPoly_apply (L : Finset ℕ) (A X : Finset (Fin n)) :
    fwPoly L A X = ∏ ℓ ∈ L.filter (· < #A), ((#(A ∩ X) : ℚ) - ℓ) := by
  simp only [fwPoly, Finset.prod_apply]

/-- Diagonal nonvanishing: `f_A A ≠ 0`. -/
theorem fwPoly_self_ne_zero (L : Finset ℕ) (A : Finset (Fin n)) : fwPoly L A A ≠ 0 := by
  rw [fwPoly_apply, inter_self, prod_ne_zero_iff]
  intro ℓ hℓ
  rw [mem_filter] at hℓ
  rw [sub_ne_zero]
  exact_mod_cast (ne_of_lt hℓ.2).symm

/-- Triangularity: if `#(A ∩ B) ∈ L`, `B ≠ A` and `#B ≤ #A`, then `f_A B = 0`. -/
theorem fwPoly_eq_zero {L : Finset ℕ} {A B : Finset (Fin n)} (hAB : #(A ∩ B) ∈ L)
    (hne : B ≠ A) (hcard : #B ≤ #A) : fwPoly L A B = 0 := by
  rw [fwPoly_apply]
  have hlt : #(A ∩ B) < #A := by
    refine lt_of_le_of_ne (card_le_card inter_subset_left) fun heq => hne ?_
    have hsub : A ⊆ B := by
      have hAeq : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left heq.ge
      rw [← hAeq]
      exact inter_subset_right
    exact (eq_of_subset_of_card_le hsub hcard).symm
  exact prod_eq_zero (mem_filter.mpr ⟨hAB, hlt⟩) (sub_self _)

/-- The family `(f_A)_{A ∈ 𝒜}` is linearly independent for an `L`-intersecting `𝒜`. -/
theorem linearIndependent_fwPoly (L : Finset ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h : Set.IsIntersectingOf (L : Set ℕ) (𝒜 : Set (Finset (Fin n)))) :
    LinearIndependent ℚ (fun A : 𝒜 => fwPoly L (A : Finset (Fin n))) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  set T := s.filter fun j => g j ≠ 0
  have hTne : T.Nonempty := ⟨i, mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨A, hAT, hAmin⟩ := T.exists_min_image (fun j => #(j : Finset (Fin n))) hTne
  rw [mem_filter] at hAT
  have heval := congr_fun hsum (A : Finset (Fin n))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
  rw [sum_eq_single_of_mem A hAT.1] at heval
  · rcases mul_eq_zero.mp heval with h0 | h0
    · exact hAT.2 h0
    · exact fwPoly_self_ne_zero L (A : Finset (Fin n)) h0
  · intro j hj hjA
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hjT : j ∈ T := mem_filter.mpr ⟨hj, hgj⟩
      have hcard := hAmin j hjT
      have hneq : (A : Finset (Fin n)) ≠ j := fun heq => hjA (Subtype.ext heq).symm
      have hint : #((j : Finset (Fin n)) ∩ A) ∈ L :=
        h j.2 A.2 (fun heq => hneq heq.symm)
      rw [fwPoly_eq_zero hint hneq hcard, mul_zero]

/-- **Frankl–Wilson (1981), nonuniform `L`-intersection theorem.**
If `L ⊆ ℕ` is a finite set of size `s` and `𝒜` is a family of subsets of
`[n] = Fin n` such that `#(A ∩ B) ∈ L` for all distinct `A, B ∈ 𝒜`, then
`#𝒜 ≤ Σ_{i=0}^{s} C(n, i)`. -/
theorem card_le_sum_choose_of_isIntersectingOf (L : Finset ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h : Set.IsIntersectingOf (L : Set ℕ) (𝒜 : Set (Finset (Fin n)))) :
    #𝒜 ≤ ∑ i ∈ range (#L + 1), n.choose i := by
  let v : 𝒜 → W n #L := fun A =>
    ⟨fwPoly L (A : Finset (Fin n)), fwPoly_mem_W L (A : Finset (Fin n))⟩
  have hcomp : (W n #L).subtype ∘ v = fun A : 𝒜 => fwPoly L (A : Finset (Fin n)) := by
    funext A
    rfl
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp (W n #L).subtype
    rw [hcomp]
    exact linearIndependent_fwPoly L 𝒜 h
  calc #𝒜 = Fintype.card 𝒜 := (Fintype.card_coe 𝒜).symm
    _ ≤ Module.finrank ℚ (W n #L) := hv.fintype_card_le_finrank
    _ ≤ ∑ i ∈ range (#L + 1), n.choose i := finrank_W_le n #L

/-- Non-vacuity and sharpness: `{∅, {0}, {1}}` is `{0}`-intersecting in `Fin 2`
and attains the bound `C(2,0) + C(2,1) = 3`. -/
example : Set.IsIntersectingOf ((({0} : Finset ℕ)) : Set ℕ)
    (({∅, {0}, {1}} : Finset (Finset (Fin 2))) : Set (Finset (Fin 2))) ∧
    #({∅, {0}, {1}} : Finset (Finset (Fin 2))) =
      ∑ i ∈ range (#({0} : Finset ℕ) + 1), (2).choose i := by
  refine ⟨?_, by decide⟩
  intro A hA B hB hne
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;> simp_all

end FranklWilson
