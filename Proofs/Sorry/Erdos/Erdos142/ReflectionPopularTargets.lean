import Sorry.Erdos.Erdos142.ReflectionFiberOverlap

/-!
# AP-sensitive positional reflection constraints

For `A : Finset ℤ`, write `ν(s) = reflectionMultiplicity A s`. An admissible
centre is `a ∈ A` with `2*a-s ∈ A` and `a ≠ s`; diagonal representations are
excluded throughout. This module proves the following full public signatures
(in namespace `Erdos142`):

```
reflectionMultiplicity_triple_le (A : Finset ℤ) (c d e : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hap : c + e = 2 * d) (hne : c ≠ e) :
    reflectionMultiplicity A c + reflectionMultiplicity A d + reflectionMultiplicity A e
      ≤ 2 * (A.card - 1)

richReflectionTargets (A T : Finset ℤ) : Finset ℤ

threeAPFree_richReflectionTargets (A T : Finset ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) :
    ThreeAPFree (richReflectionTargets A T : Set ℤ)
```

The definition is exactly `T.filter (fun c => 2 * (A.card - 1) < 3 * ν(c))`.
All cardinal arithmetic is in `ℕ`; the predecessor is deliberately truncated.
There are no interval-scale or positive-mass assumptions.

Proof of the positional bound: reorder endpoints so `c < d < e`. The degree
of a centre is its number of admissible incidences with these three targets.
Every degree is at most two: three reflected endpoints would form a nonconstant
AP in `A`. If `A.card ≤ 1`, the universal multiplicity cap makes every count
zero. Otherwise take its distinct minimum `u` and maximum `v`. If `u < c`,
all three endpoints reflected at `u` lie below `u`, so its degree is zero;
if `e < v`, all three endpoints at `v` lie above `v`, again giving degree zero.
In either case the other `A.card - 1` degrees are at most two.

In the remaining case `c ≤ u ≤ v ≤ e`, both extremal degrees are at most one.
At `u`, target `e` is impossible: its endpoint is below the minimum or diagonal.
If both `c` and `d` were admissible, minimality for the `d` endpoint forces
`d < u`, while maximality for the `c` endpoint gives `2*u-c ≤ v ≤ e = 2*d-c`,
forcing `u ≤ d`. At `v`, target `c` is impossible by the symmetric argument.
Simultaneous targets `d,e` would force `v < d` and `d ≤ v`. Splitting off the
two extrema yields `1 + 1 + 2*(A.card - 2) = 2*(A.card - 1)`.

Three rich targets in a nonconstant AP would each satisfy
`2*(A.card - 1) < 3*ν(s)`. Adding contradicts three times the positional bound.
The strict threshold cannot be weakened: `A = {0,1,3,4}` is AP-free and the
AP of targets `(-1,2,5)` has multiplicities `(2,2,2)`, attaining the bound.
The examples below check this obstruction, a nonempty rich filter, and the
empty/singleton boundaries. Integer domains are nonempty. The hypotheses of
the positional theorem are jointly witnessed by the same equality model.

These are finite positional constraints, not global energy improvements or
asymptotic estimates; no novelty or resolution of the open problem is claimed.
-/

set_option autoImplicit false

open Finset

namespace Erdos142

private theorem degree_le (A : Finset ℤ) (c d e a : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hap : c + e = 2 * d) (hne : c ≠ e) :
    (if 2*a-c ∈ A ∧ a ≠ c then 1 else 0) +
      (if 2*a-d ∈ A ∧ a ≠ d then 1 else 0) +
      (if 2*a-e ∈ A ∧ a ≠ e then 1 else 0) ≤ (2 : ℕ) := by
  by_cases hc : 2*a-c ∈ A ∧ a ≠ c <;>
    by_cases hd : 2*a-d ∈ A ∧ a ≠ d <;>
    by_cases he : 2*a-e ∈ A ∧ a ≠ e
  · have heq := hfree hc.1 hd.1 he.1 (by omega)
    exfalso
    omega
  all_goals simp [hc, hd, he]

private theorem ordered_triple_le (A : Finset ℤ) (c d e : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hap : c + e = 2*d) (hce : c < e) :
    reflectionMultiplicity A c + reflectionMultiplicity A d + reflectionMultiplicity A e
      ≤ 2 * (A.card - 1) := by
  by_cases hm : A.card ≤ 1
  · have hc := reflectionMultiplicity_le A c
    have hd := reflectionMultiplicity_le A d
    have he := reflectionMultiplicity_le A e
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let u := A.min' hne
  let v := A.max' hne
  have hu : u ∈ A := A.min'_mem hne
  have hv : v ∈ A := A.max'_mem hne
  have hlo : ∀ a ∈ A, u ≤ a := fun a ha => A.min'_le a ha
  have hhi : ∀ a ∈ A, a ≤ v := fun a ha => A.le_max' a ha
  have huv : u ≠ v := by
    intro heq
    have hsub : A ⊆ {u} := by
      intro a ha
      have hl := hlo a ha
      have hh := hhi a ha
      simp only [Finset.mem_singleton]
      omega
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  let f : ℤ → ℕ := fun a => (if 2*a-c ∈ A ∧ a ≠ c then 1 else 0) +
      (if 2*a-d ∈ A ∧ a ≠ d then 1 else 0) +
      (if 2*a-e ∈ A ∧ a ≠ e then 1 else 0)
  have hf : ∀ a ∈ A, f a ≤ 2 := fun a _ => degree_le A c d e a hfree hap (by omega)
  have hsum : reflectionMultiplicity A c + reflectionMultiplicity A d +
      reflectionMultiplicity A e = ∑ a ∈ A, f a := by
    simp only [reflectionMultiplicity_eq_card_filter, f, Finset.sum_add_distrib]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum]
  have single : ∀ x ∈ A, f x = 0 → (∑ a ∈ A, f a) ≤ 2 * (A.card - 1) := by
    intro x hx hfx
    have hs := A.sum_erase_add f hx
    have hb : (∑ a ∈ A.erase x, f a) ≤ (A.erase x).card * 2 := by
      calc
        _ ≤ ∑ _a ∈ A.erase x, 2 := Finset.sum_le_sum fun a ha => hf a (Finset.mem_of_mem_erase ha)
        _ = _ := by simp
    have hcard := Finset.card_erase_of_mem hx
    omega
  by_cases hout : u < c
  · apply single u hu
    have hc : ¬ (2*u-c ∈ A ∧ u ≠ c) := by
      rintro ⟨hh, _⟩
      have hl := hlo _ hh
      omega
    have hd : ¬ (2*u-d ∈ A ∧ u ≠ d) := by
      rintro ⟨hh, _⟩
      have hl := hlo _ hh
      omega
    have he : ¬ (2*u-e ∈ A ∧ u ≠ e) := by
      rintro ⟨hh, _⟩
      have hl := hlo _ hh
      omega
    simp [f, hc, hd, he]
  by_cases houtv : e < v
  · apply single v hv
    have hc : ¬ (2*v-c ∈ A ∧ v ≠ c) := by
      rintro ⟨hh, _⟩
      have hh' := hhi _ hh
      omega
    have hd : ¬ (2*v-d ∈ A ∧ v ≠ d) := by
      rintro ⟨hh, _⟩
      have hh' := hhi _ hh
      omega
    have he : ¬ (2*v-e ∈ A ∧ v ≠ e) := by
      rintro ⟨hh, _⟩
      have hh' := hhi _ hh
      omega
    simp [f, hc, hd, he]
  have hfu : f u ≤ 1 := by
    have he : ¬ (2*u-e ∈ A ∧ u ≠ e) := by
      rintro ⟨hh, hhne⟩
      have hl := hlo _ hh
      have hh' := hhi u hu
      omega
    have hcd : ¬ ((2*u-c ∈ A ∧ u ≠ c) ∧ (2*u-d ∈ A ∧ u ≠ d)) := by
      rintro ⟨hc, hd⟩
      have hl := hlo _ hd.1
      have hh := hhi _ hc.1
      omega
    dsimp [f]
    by_cases hc : 2*u-c ∈ A ∧ u ≠ c <;>
      by_cases hd : 2*u-d ∈ A ∧ u ≠ d
    · exact False.elim (hcd ⟨hc, hd⟩)
    all_goals simp [hc, hd, he]
  have hfv : f v ≤ 1 := by
    have hc : ¬ (2*v-c ∈ A ∧ v ≠ c) := by
      rintro ⟨hh, hhne⟩
      have hh' := hhi _ hh
      have hl := hlo v hv
      omega
    have hde : ¬ ((2*v-d ∈ A ∧ v ≠ d) ∧ (2*v-e ∈ A ∧ v ≠ e)) := by
      rintro ⟨hd, he⟩
      have hh := hhi _ hd.1
      have hl := hlo _ he.1
      omega
    dsimp [f]
    by_cases hd : 2*v-d ∈ A ∧ v ≠ d <;>
      by_cases he : 2*v-e ∈ A ∧ v ≠ e
    · exact False.elim (hde ⟨hd, he⟩)
    all_goals simp [hc, hd, he]
  have hv' : v ∈ A.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
  have hs1 := A.sum_erase_add f hu
  have hs2 := (A.erase u).sum_erase_add f hv'
  have hb : (∑ a ∈ (A.erase u).erase v, f a) ≤ ((A.erase u).erase v).card * 2 := by
    calc
      _ ≤ ∑ _a ∈ (A.erase u).erase v, 2 := Finset.sum_le_sum fun a ha =>
        hf a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))
      _ = _ := by simp
  have hcard1 := Finset.card_erase_of_mem hu
  have hcard2 := Finset.card_erase_of_mem hv'
  omega

/-- Along any nonconstant target arithmetic progression, the sum of the three
reflection multiplicities is at most twice the predecessor of the set size.
No interval, nonempty-set, or positive-mass hypothesis is required. -/
theorem reflectionMultiplicity_triple_le (A : Finset ℤ) (c d e : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hap : c + e = 2 * d) (hne : c ≠ e) :
    reflectionMultiplicity A c + reflectionMultiplicity A d + reflectionMultiplicity A e
      ≤ 2 * (A.card - 1) := by
  rcases lt_or_gt_of_ne hne with hce | hec
  · exact ordered_triple_le A c d e hfree hap hce
  · have hb := ordered_triple_le A e d c hfree (by omega) hec
    omega

/-- Targets in `T` whose multiplicity is strictly greater than two thirds of
`A.card - 1`. The strict inequality is essential. -/
def richReflectionTargets (A T : Finset ℤ) : Finset ℤ :=
  T.filter (fun c => 2 * (A.card - 1) < 3 * reflectionMultiplicity A c)

/-- Rich reflection targets of a 3-AP-free set are themselves 3-AP-free,
for any finite set of candidate targets. -/
theorem threeAPFree_richReflectionTargets (A T : Finset ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) :
    ThreeAPFree (richReflectionTargets A T : Set ℤ) := by
  intro c hc d hd e he hap
  have hc' := (Finset.mem_filter.mp hc).2
  have hd' := (Finset.mem_filter.mp hd).2
  have he' := (Finset.mem_filter.mp he).2
  by_cases hce : c = e
  · omega
  · have hb := reflectionMultiplicity_triple_le A c d e hfree (by omega) hce
    omega

/-! ## Concrete models and boundaries -/

example : ThreeAPFree (({0, 1, 3, 4} : Finset ℤ) : Set ℤ) ∧
    (-1 : ℤ) + 5 = 2 * 2 ∧ (-1 : ℤ) ≠ 5 := by decide

example : reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) (-1) = 2 ∧
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 2 = 2 ∧
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 5 = 2 := by decide

example : reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) (-1) +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 2 +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 5 =
    2 * (({0, 1, 3, 4} : Finset ℤ).card - 1) := by decide

example : richReflectionTargets ({0, 1, 3, 4} : Finset ℤ) {-1, 2, 5} = ∅ := by decide

example : richReflectionTargets ({1, 2, 4, 8} : Finset ℤ) {0, 3} = {0} := by decide

example : ThreeAPFree (({1, 2, 4, 8} : Finset ℤ) : Set ℤ) := by decide

example : reflectionMultiplicity (∅ : Finset ℤ) (-1) +
    reflectionMultiplicity (∅ : Finset ℤ) 2 + reflectionMultiplicity (∅ : Finset ℤ) 5 ≤
    2 * ((∅ : Finset ℤ).card - 1) :=
  reflectionMultiplicity_triple_le _ _ _ _ (by simp) (by norm_num) (by norm_num)

example : richReflectionTargets ({7} : Finset ℤ) {-1, 2, 5, 7} = ∅ := by decide

example : ¬ ThreeAPFree ((({-1, 2, 5} : Finset ℤ).filter
    (fun c => 2 * (({0, 1, 3, 4} : Finset ℤ).card - 1) ≤
      3 * reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) c)) : Set ℤ) := by decide

end Erdos142
