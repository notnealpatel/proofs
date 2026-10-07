import Erdos.Erdos142.ReflectionPopularTargets

/-!
# Quantitative positional constraints for an odd reflection gap

For `A : Finset ℤ` and integer middle `d`, write
`S = ν(d-h) + ν(d) + ν(d+h)`, where `ν = reflectionMultiplicity A`.
Let `q` and `r` count the relative-even and relative-odd vertices:
`q = (A.filter (fun a => (a-d) % 2 = 0)).card` and
`r = (A.filter (fun a => (a-d) % 2 = 1)).card`.
The full public signatures, in namespace `Erdos142`, are:

```
two_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    2 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 3 * A.card +
      min (A.filter (fun a => (a-d) % 2 = 0)).card
        (A.filter (fun a => (a-d) % 2 = 1)).card

three_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    3 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 5 * A.card

four_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    4 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 7 * A.card
```

There are no interval, cardinality lower-bound, or mass hypotheses. Oddness
implies `h ≠ 0`; negative odd gaps are allowed. The proof works directly in
coordinates relative to `d`, so no translation adapter or division is needed.
In particular, relative-even vertices are not necessarily absolutely even.

Draw an arc `a → b = 2*a-s` for each target `s ∈ {d-h,d,d+h}` when both
vertices lie in `A` and `a ≠ s`. The last condition excludes precisely the
self-loops. Oddness separates target labels. Each label's endpoint set is the
injective image of its admissible centres; thus both total indegree and total
outdegree equal `S`. The proof uses sums of three indicators for these degrees.

Outdegree is at most two, since three endpoints would be a nonconstant AP.
An endpoint's relative parity equals its target's relative parity. Therefore
only the middle label can enter a relative-even vertex, giving indegree at
most one there; only the two outer labels can enter a relative-odd vertex,
giving indegree at most two. Let `H` be the vertices of total degree four.
They are relative-odd and have both outer-label predecessors. These two
predecessors differ by the odd number `h`, so precisely one is relative-even.
Assign that predecessor to the vertex of `H`.

This assignment is injective. If a source `a` served two distinct saturated
successors, their labels must be opposite outer labels. The other predecessors
of those successors then equal `a-h` and `a+h`. Together with `a` they form a
forbidden nonconstant AP. This argument requires neither acyclicity of `H` nor
any doubling-continuation property. Consequently `H.card ≤ q` and `H.card ≤ r`.
All other vertices have total degree at most three, and summing gives
`2*S ≤ 3*A.card + H.card ≤ 3*A.card + min q r`. Finally `q+r=A.card` implies
`2*min q r ≤ A.card`, yielding the seven-quarter bound. Endpoint parity also
bounds the middle multiplicity by `q` and each outer multiplicity by `r`,
without AP-freeness. Thus `S ≤ q+2*r`; adding this to
`2*S ≤ 3*A.card+q` yields `3*S ≤ 5*A.card`. The seven-quarter
corollary is retained as a historical checkpoint.

Concrete models below jointly witness AP-freeness and oddness, check a middle
of odd parity and a negative gap, and cover empty and singleton sets. The
seven-point cycle model and the missing-doubling model are checked as finite
regressions. The integer domains are nonempty. No asymptotic result, global
energy improvement, or novelty claim is made. The sharper universal bound
`S ≤ floor(3*A.card/2)` and the optional dyadic extension are not proved here.
-/

set_option autoImplicit false

open Finset

namespace Erdos142

/-- Endpoints of the nontrivial reflection representations of a fixed target. -/
private def oddGapEndpoints (A : Finset ℤ) (s : ℤ) : Finset ℤ :=
  (A.filter (fun a => 2 * a - s ∈ A ∧ a ≠ s)).image (fun a => 2 * a - s)

private theorem mem_oddGapEndpoints (A : Finset ℤ) (s b : ℤ) :
    b ∈ oddGapEndpoints A s ↔ ∃ a ∈ A, 2 * a - s = b ∧ a ≠ s ∧ b ∈ A := by
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
    obtain ⟨haA, habA, hne⟩ := Finset.mem_filter.mp ha
    exact ⟨a, haA, hab, hne, hab ▸ habA⟩
  · rintro ⟨a, ha, hab, hne, hbA⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab.symm ▸ hbA, hne⟩, hab⟩

private theorem oddGapEndpoints_subset (A : Finset ℤ) (s : ℤ) :
    oddGapEndpoints A s ⊆ A := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
  exact hab ▸ (Finset.mem_filter.mp ha).2.1

private theorem oddGapEndpoints_card (A : Finset ℤ) (s : ℤ) :
    (oddGapEndpoints A s).card = reflectionMultiplicity A s := by
  rw [reflectionMultiplicity_eq_card_filter]
  exact Finset.card_image_of_injective _ (fun a b hab => by omega)

example : oddGapEndpoints ({0, 1, 3, 4} : Finset ℤ) 2 = {0, 4} := by decide

private theorem endpoint_sum (A : Finset ℤ) (s : ℤ) :
    (∑ b ∈ A, if b ∈ oddGapEndpoints A s then 1 else 0) = reflectionMultiplicity A s := by
  have hfilt : A.filter (fun b => b ∈ oddGapEndpoints A s) = oddGapEndpoints A s := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · exact fun hb => hb.2
    · exact fun hb => ⟨oddGapEndpoints_subset A s hb, hb⟩
  calc
    _ = (A.filter (fun b => b ∈ oddGapEndpoints A s)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (oddGapEndpoints A s).card := congrArg Finset.card hfilt
    _ = _ := oddGapEndpoints_card A s

private theorem endpoint_parity (A : Finset ℤ) (s b d : ℤ)
    (hb : b ∈ oddGapEndpoints A s) : (b - d) % 2 = (s - d) % 2 := by
  obtain ⟨a, ha, hab, hne, _⟩ := (mem_oddGapEndpoints A s b).mp hb
  omega

private theorem saturated_even_predecessor (A : Finset ℤ) (d h b : ℤ)
    (hodd : h % 2 = 1)
    (hb : b ∈ oddGapEndpoints A (d-h) ∧ b ∈ oddGapEndpoints A (d+h)) :
    ∃ a ∈ A, (a-d) % 2 = 0 ∧ (b = 2*a-(d-h) ∨ b = 2*a-(d+h)) := by
  obtain ⟨x, hx, hxb, hxn, _⟩ := (mem_oddGapEndpoints A (d-h) b).mp hb.1
  obtain ⟨y, hy, hyb, hyn, _⟩ := (mem_oddGapEndpoints A (d+h) b).mp hb.2
  by_cases hp : (x-d) % 2 = 0
  · exact ⟨x, hx, hp, Or.inl hxb.symm⟩
  · exact ⟨y, hy, by omega, Or.inr hyb.symm⟩

private theorem saturated_successor_unique (A : Finset ℤ) (d h a b c : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) (ha : a ∈ A)
    (hb : b ∈ oddGapEndpoints A (d-h) ∧ b ∈ oddGapEndpoints A (d+h))
    (hc : c ∈ oddGapEndpoints A (d-h) ∧ c ∈ oddGapEndpoints A (d+h))
    (hab : b = 2*a-(d-h) ∨ b = 2*a-(d+h))
    (hac : c = 2*a-(d-h) ∨ c = 2*a-(d+h)) : b = c := by
  rcases hab with hab | hab <;> rcases hac with hac | hac
  · omega
  · obtain ⟨x, hx, hxb, hxn, _⟩ := (mem_oddGapEndpoints A (d+h) b).mp hb.2
    obtain ⟨y, hy, hyc, hyn, _⟩ := (mem_oddGapEndpoints A (d-h) c).mp hc.1
    have hAP := hfree hx ha hy (by omega)
    omega
  · obtain ⟨x, hx, hxc, hxn, _⟩ := (mem_oddGapEndpoints A (d+h) c).mp hc.2
    obtain ⟨y, hy, hyb, hyn, _⟩ := (mem_oddGapEndpoints A (d-h) b).mp hb.1
    have hAP := hfree hx ha hy (by omega)
    omega
  · omega

/-- For an odd target gap, twice the total multiplicity is at most three
set sizes plus the smaller relative-parity class. -/
theorem two_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    2 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 3 * A.card +
      min (A.filter (fun a => (a-d) % 2 = 0)).card
        (A.filter (fun a => (a-d) % 2 = 1)).card := by
  classical
  let out : ℤ → ℕ := fun a =>
    (if 2*a-(d-h) ∈ A ∧ a ≠ d-h then 1 else 0) +
    (if 2*a-d ∈ A ∧ a ≠ d then 1 else 0) +
    (if 2*a-(d+h) ∈ A ∧ a ≠ d+h then 1 else 0)
  let inn : ℤ → ℕ := fun b =>
    (if b ∈ oddGapEndpoints A (d-h) then 1 else 0) +
    (if b ∈ oddGapEndpoints A d then 1 else 0) +
    (if b ∈ oddGapEndpoints A (d+h) then 1 else 0)
  have hout : ∀ a, out a ≤ 2 := by
    intro a
    by_cases hm : 2*a-(d-h) ∈ A ∧ a ≠ d-h <;>
      by_cases hz : 2*a-d ∈ A ∧ a ≠ d <;>
      by_cases hp : 2*a-(d+h) ∈ A ∧ a ≠ d+h
    · have hAP := hfree hm.1 hz.1 hp.1 (by omega)
      exfalso
      omega
    all_goals simp [out, hm, hz, hp]
  have hno : ∀ b, b ∈ oddGapEndpoints A d →
      b ∉ oddGapEndpoints A (d-h) ∧ b ∉ oddGapEndpoints A (d+h) := by
    intro b hz
    have hzp := endpoint_parity A d b d hz
    constructor
    · intro hm
      have hmp := endpoint_parity A (d-h) b d hm
      omega
    · intro hp
      have hpp := endpoint_parity A (d+h) b d hp
      omega
  have hinn : ∀ b, inn b ≤ 2 := by
    intro b
    by_cases hz : b ∈ oddGapEndpoints A d
    · obtain ⟨hm, hp⟩ := hno b hz
      simp [inn, hz, hm, hp]
    · dsimp [inn]
      by_cases hm : b ∈ oddGapEndpoints A (d-h) <;>
        by_cases hp : b ∈ oddGapEndpoints A (d+h) <;> simp [hz, hm, hp]
  let H := A.filter (fun b => inn b + out b = 4)
  have hsat : ∀ b ∈ H,
      b ∈ oddGapEndpoints A (d-h) ∧ b ∈ oddGapEndpoints A (d+h) := by
    intro b hb
    have hdeg := (Finset.mem_filter.mp hb).2
    have ho := hout b
    have hi := hinn b
    have heq : inn b = 2 := by omega
    by_cases hz : b ∈ oddGapEndpoints A d
    · obtain ⟨hm, hp⟩ := hno b hz
      simp [inn, hz, hm, hp] at heq
    · by_cases hm : b ∈ oddGapEndpoints A (d-h) <;>
        by_cases hp : b ∈ oddGapEndpoints A (d+h)
      · exact ⟨hm, hp⟩
      all_goals simp [inn, hz, hm, hp] at heq
  have hr : H.card ≤ (A.filter (fun b => (b-d) % 2 = 1)).card := by
    apply Finset.card_le_card
    intro b hb
    have hm := (hsat b hb).1
    have hp := endpoint_parity A (d-h) b d hm
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, by omega⟩
  have hex : ∀ b : ℤ, ∃ a : ℤ, b ∈ H →
      a ∈ A ∧ (a-d) % 2 = 0 ∧ (b = 2*a-(d-h) ∨ b = 2*a-(d+h)) := by
    intro b
    by_cases hb : b ∈ H
    · obtain ⟨a, ha, hpar, harc⟩ := saturated_even_predecessor A d h b hodd (hsat b hb)
      exact ⟨a, fun _ => ⟨ha, hpar, harc⟩⟩
    · exact ⟨0, fun hb' => False.elim (hb hb')⟩
  choose f hf using hex
  have hq : H.card ≤ (A.filter (fun a => (a-d) % 2 = 0)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro b hb
      exact Finset.mem_filter.mpr ⟨(hf b hb).1, (hf b hb).2.1⟩
    · intro b hb c hc heq
      apply saturated_successor_unique A d h (f b) b c hfree hodd (hf b hb).1
        (hsat b hb) (hsat c hc) (hf b hb).2.2
      rw [heq]
      exact (hf c hc).2.2
  have hsout : (∑ a ∈ A, out a) = reflectionMultiplicity A (d-h) +
      reflectionMultiplicity A d + reflectionMultiplicity A (d+h) := by
    simp only [out, Finset.sum_add_distrib, reflectionMultiplicity_eq_card_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsinn : (∑ b ∈ A, inn b) = reflectionMultiplicity A (d-h) +
      reflectionMultiplicity A d + reflectionMultiplicity A (d+h) := by
    simp only [inn, Finset.sum_add_distrib, endpoint_sum]
  have hpoint : ∀ b ∈ A, inn b + out b ≤ 3 + (if b ∈ H then 1 else 0) := by
    intro b hb
    have hi := hinn b
    have ho := hout b
    by_cases hh : b ∈ H
    · simp only [hh, if_true]
      omega
    · have hdeg : inn b + out b ≠ 4 := by
        intro h4
        exact hh (Finset.mem_filter.mpr ⟨hb, h4⟩)
      simp only [hh, if_false]
      omega
  have hHsub : H ⊆ A := Finset.filter_subset _ _
  have hfilter : A.filter (fun b => b ∈ H) = H := by
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun hb => hb.2, fun hb => ⟨hHsub hb, hb⟩⟩
  have hsumH : (∑ b ∈ A, if b ∈ H then 1 else 0) = H.card := by
    rw [← hfilter]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hfilter]
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, hsinn, hsout] at hsum
  have hconst : (∑ _b ∈ A, (3 : ℕ)) = 3 * A.card := by simp [Nat.mul_comm]
  rw [hconst, hsumH] at hsum
  have hmin : H.card ≤ min (A.filter (fun a => (a-d) % 2 = 0)).card
      (A.filter (fun a => (a-d) % 2 = 1)).card := le_min hq hr
  omega

private theorem relative_parity_card (A : Finset ℤ) (d : ℤ) :
    (A.filter (fun a => (a-d) % 2 = 0)).card +
      (A.filter (fun a => (a-d) % 2 = 1)).card = A.card := by
  have heq : A.filter (fun a => (a-d) % 2 = 1) =
      A.filter (fun a => ¬ (a-d) % 2 = 0) := by
    apply Finset.filter_congr
    intro a ha
    omega
  rw [heq]
  exact Finset.card_filter_add_card_filter_not _

/-- For any odd gap and any middle target, four times the three-target
reflection multiplicity sum is at most seven times the set size. -/
theorem four_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    4 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 7 * A.card := by
  have hb := two_mul_reflectionMultiplicity_oddGap_le A d h hfree hodd
  have hpart := relative_parity_card A d
  have hq := min_le_left (A.filter (fun a => (a-d) % 2 = 0)).card
    (A.filter (fun a => (a-d) % 2 = 1)).card
  have hr := min_le_right (A.filter (fun a => (a-d) % 2 = 0)).card
    (A.filter (fun a => (a-d) % 2 = 1)).card
  omega

private theorem reflectionMultiplicity_le_relativeParity (A : Finset ℤ) (s d : ℤ) :
    reflectionMultiplicity A s ≤
      (A.filter (fun b => (b-d) % 2 = (s-d) % 2)).card := by
  rw [← oddGapEndpoints_card A s]
  apply Finset.card_le_card
  intro b hb
  exact Finset.mem_filter.mpr
    ⟨oddGapEndpoints_subset A s hb, endpoint_parity A s b d hb⟩

/-- For any odd gap and any middle target, three times the three-target
reflection multiplicity sum is at most five times the set size. -/
theorem three_mul_reflectionMultiplicity_oddGap_le (A : Finset ℤ) (d h : ℤ)
    (hfree : ThreeAPFree (A : Set ℤ)) (hodd : h % 2 = 1) :
    3 * (reflectionMultiplicity A (d-h) + reflectionMultiplicity A d +
      reflectionMultiplicity A (d+h)) ≤ 5 * A.card := by
  have hm := reflectionMultiplicity_le_relativeParity A (d-h) d
  have hz := reflectionMultiplicity_le_relativeParity A d d
  have hp := reflectionMultiplicity_le_relativeParity A (d+h) d
  have hmp : (d-h-d) % 2 = 1 := by omega
  have hpp : (d+h-d) % 2 = 1 := by omega
  simp only [hmp] at hm
  simp only [sub_self, Int.zero_emod] at hz
  simp only [hpp] at hp
  have hb := two_mul_reflectionMultiplicity_oddGap_le A d h hfree hodd
  have hpart := relative_parity_card A d
  have hq := min_le_left (A.filter (fun a => (a-d) % 2 = 0)).card
    (A.filter (fun a => (a-d) % 2 = 1)).card
  omega

/-! ## Satisfiability, relative parity, and structural regression models -/

example : ThreeAPFree (({0, 1, 3, 4} : Finset ℤ) : Set ℤ) ∧ (3 : ℤ) % 2 = 1 := by decide

example : ThreeAPFree (({1, 2, 4, 8} : Finset ℤ) : Set ℤ) ∧
    (({1, 2, 4, 8} : Finset ℤ).filter (fun a => (a-1) % 2 = 0)).card = 1 ∧
    (({1, 2, 4, 8} : Finset ℤ).filter (fun a => (a-1) % 2 = 1)).card = 3 := by decide

example : 2 * (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 0 +
    reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 1 +
    reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 2) ≤ 3 * 4 + min 1 3 :=
  two_mul_reflectionMultiplicity_oddGap_le _ 1 1 (by decide) (by decide)

example : 4 * (reflectionMultiplicity (∅ : Finset ℤ) (-3) +
    reflectionMultiplicity (∅ : Finset ℤ) 0 + reflectionMultiplicity (∅ : Finset ℤ) 3) ≤
    7 * (∅ : Finset ℤ).card :=
  four_mul_reflectionMultiplicity_oddGap_le _ 0 3 (by simp) (by decide)

example : 4 * (reflectionMultiplicity ({5} : Finset ℤ) 2 +
    reflectionMultiplicity ({5} : Finset ℤ) 5 + reflectionMultiplicity ({5} : Finset ℤ) 8) ≤
    7 * ({5} : Finset ℤ).card :=
  four_mul_reflectionMultiplicity_oddGap_le _ 5 3 (by decide) (by decide)

example : ThreeAPFree (({-17, -6, -5, -3, 1, 2, 4} : Finset ℤ) : Set ℤ) ∧
    reflectionMultiplicity ({-17, -6, -5, -3, 1, 2, 4} : Finset ℤ) (-7) +
    reflectionMultiplicity ({-17, -6, -5, -3, 1, 2, 4} : Finset ℤ) 0 +
    reflectionMultiplicity ({-17, -6, -5, -3, 1, 2, 4} : Finset ℤ) 7 = 10 := by decide

example : let A : Finset ℤ := {-17, -6, -5, -3, 1, 2, 4}
    ∀ b ∈ ({-5, -3, 1} : Finset ℤ),
      b ∈ oddGapEndpoints A (-7) ∧ b ∈ oddGapEndpoints A 7 ∧
      (({-7, 0, 7} : Finset ℤ).filter (fun s => 2*b-s ∈ A ∧ b ≠ s)).card = 2 := by decide

example : 2 * (-5 : ℤ) - (-7) = -3 ∧ 2 * (-3 : ℤ) - (-7) = 1 ∧
    2 * (1 : ℤ) - 7 = -5 := by decide

example : ThreeAPFree (({1, 2, 4, 5, 10, 11, 13} : Finset ℤ) : Set ℤ) ∧
    (8 : ℤ) ∉ ({1, 2, 4, 5, 10, 11, 13} : Finset ℤ) := by decide

example : let A : Finset ℤ := {1, 2, 4, 5, 10, 11, 13}
    (5 : ℤ) ∈ oddGapEndpoints A (-3) ∧ (5 : ℤ) ∈ oddGapEndpoints A 3 ∧
    (({-3, 0, 3} : Finset ℤ).filter (fun s => 2*5-s ∈ A ∧ (5 : ℤ) ≠ s)).card = 2 ∧
    (({-3, 0, 3} : Finset ℤ).filter (fun s => 2*4-s ∈ A ∧ (4 : ℤ) ≠ s)).card = 2 ∧
    (4 : ℤ) ∈ oddGapEndpoints A 0 ∧ (4 : ℤ) ∉ oddGapEndpoints A (-3) ∧
    (4 : ℤ) ∉ oddGapEndpoints A 3 := by decide

example : 4 * (reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 5 +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 2 +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) (-1)) ≤
    7 * ({0, 1, 3, 4} : Finset ℤ).card :=
  four_mul_reflectionMultiplicity_oddGap_le _ 2 (-3) (by decide) (by decide)

example : 3 * (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 0 +
    reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 1 +
    reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 2) ≤
    5 * ({1, 2, 4, 8} : Finset ℤ).card :=
  three_mul_reflectionMultiplicity_oddGap_le _ 1 1 (by decide) (by decide)

example : 3 * (reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 5 +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) 2 +
    reflectionMultiplicity ({0, 1, 3, 4} : Finset ℤ) (-1)) ≤
    5 * ({0, 1, 3, 4} : Finset ℤ).card :=
  three_mul_reflectionMultiplicity_oddGap_le _ 2 (-3) (by decide) (by decide)

end Erdos142
