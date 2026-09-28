/-
  Erdős Problem #142 — the averaged reflection-energy bound.

  This file formalizes a finite averaging theorem for the reflection-energy
  bookkeeping of Erdős Problem #142.  The setting is the exact finite one of
  `Erdos.Erdos142.ReflectionMassEnergy` and `Erdos.Erdos142.ReflectionShadow`:
  `A : Finset ℤ` is a finite set, `L : ℤ` is the interval scale, and
  `ν(c) = reflectionMultiplicity A c`, `M = reflectionMass A L` are the existing
  fixed-target multiplicity and total mass.

  Three ingredients are combined.

  1. *Fiber overlap (geometric).*  For distinct targets `c ≠ d` the admissible
     centre sets `X_c = {a : 2*a - c ∈ A, a ≠ c}` and `X_d` intersect in at most
     `⌊m/2⌋` points: the map `a ↦ 2*a - c` injects `X_c ∩ X_d` into the fixed
     difference sources `differenceSources A (c - d)`, whose cardinality is at
     most `⌊m/2⌋` by `two_mul_card_differenceSources_le`.  Since `X_c, X_d ⊆ A`,
     this gives the pairwise sum bound

       `ν(c) + ν(d) ≤ m + ⌊m/2⌋`  for `c ≠ d`.

  2. *Mass lower bound.*  From `card_le_reflectionMass`, for `m ≥ 9` the mass
     satisfies `2*(m-1) ≤ ⌊(m-1)²/4⌋ ≤ M`, while `ν(c) ≤ m - 1` for every `c`.
     Hence `2*ν(c) ≤ M` for every target `c`.

  3. *Pure averaging.*  For any finite index set `T` and `f : T → ℕ`, the
     pairwise bound `f(c) + f(d) ≤ B` (`c ≠ d`) together with `2*f(c) ≤ Σ f`
     forces `2 * Σ f² ≤ B * Σ f`: split off a maximizer; if it is at most `B/2`
     the bound is termwise, otherwise every other value is at most `B - K` and
     the residual inequality reduces to `(K - (B-K))·(K - Σ_{≠} f) ≤ 0`.

  The public endpoint is the denominator-free energy inequality

    `2 * ∑_{c ∈ [0,L)} ν(c)² ≤ (m + m / 2) * M`,  for `9 ≤ m` and 3-AP-free `A`.

  Scope and honesty.  The fiber-overlap step (1) is proved here, not assumed:
  the module contains no `sorry`, `admit`, or new axiom, and no hypothesis is
  smuggled in for the geometric claim.  The statements are exact finite
  combinatorics; nothing here is asymptotic and nothing asserts the open
  estimates `(O)` or `(C)` of the reflection-shadow route.
-/

import Erdos.Erdos142.ReflectionShadow
import Erdos.Erdos142.ReflectionMassEnergy
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-! ## Fiber overlap: distinct targets have small intersection

The admissible centre set of the target `c` is `{a ∈ A : 2*a - c ∈ A, a ≠ c}`,
the filter whose cardinality is `reflectionMultiplicity A c`.  For `c ≠ d`, the
centres common to both fibres determine a fixed-difference pair of `A`, and the
fixed-difference source count is at most `⌊m/2⌋`. -/

/-- **Fiber overlap bound.**  For distinct targets `c ≠ d` and a 3-AP-free
`A : Finset ℤ`, twice the number of common admissible centres of `c` and `d` is
at most `A.card`.  Equivalently, `|X_c ∩ X_d| ≤ ⌊A.card/2⌋`.

The proof sends a common centre `a` to the fixed-difference source `2*a - c`,
which lies in `differenceSources A (c - d)` because
`(2*a - c) + (c - d) = 2*a - d ∈ A`.  The map `a ↦ 2*a - c` is injective, so
the intersection embeds into the source set, and
`two_mul_card_differenceSources_le` caps the latter by `A.card`. -/
theorem two_mul_card_inter_centers_le (A : Finset ℤ) {c d : ℤ} (hcd : c ≠ d)
    (hfree : ThreeAPFree (A : Set ℤ)) :
    2 * ((A.filter (fun a : ℤ => 2 * a - c ∈ A ∧ a ≠ c)) ∩
         (A.filter (fun a : ℤ => 2 * a - d ∈ A ∧ a ≠ d))).card ≤ A.card := by
  set S := (A.filter (fun a : ℤ => 2 * a - c ∈ A ∧ a ≠ c)) ∩
      (A.filter (fun a : ℤ => 2 * a - d ∈ A ∧ a ≠ d)) with hS
  have hmap : ∀ a ∈ S, 2 * a - c ∈ differenceSources A (c - d) := by
    intro a ha
    rw [hS, Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at ha
    obtain ⟨⟨-, hca, -⟩, ⟨-, hda, -⟩⟩ := ha
    rw [mem_differenceSources]
    have hkey : 2 * a - c + (c - d) = 2 * a - d := by ring
    exact ⟨hca, by rw [hkey]; exact hda⟩
  have hinj : Function.Injective (fun a : ℤ => 2 * a - c) := by
    intro a b hab
    simp only at hab
    omega
  have hcard : (S.image (fun a : ℤ => 2 * a - c)).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hsub : S.image (fun a : ℤ => 2 * a - c) ⊆ differenceSources A (c - d) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hmap a ha
  have hle : S.card ≤ (differenceSources A (c - d)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hd : c - d ≠ 0 := by omega
  have h2 := two_mul_card_differenceSources_le hd hfree
  omega

/-- **Pairwise multiplicity sum bound.**  For distinct targets `c ≠ d` and a
3-AP-free `A : Finset ℤ`,

  `ν(c) + ν(d) ≤ A.card + A.card / 2`.

This is the geometric fiber-overlap bound packaged using the union: the two
centre sets are subsets of `A`, so their union has at most `A.card` elements,
and their intersection at most `A.card / 2`. -/
theorem reflectionMultiplicity_pair_le (A : Finset ℤ) {c d : ℤ} (hcd : c ≠ d)
    (hfree : ThreeAPFree (A : Set ℤ)) :
    reflectionMultiplicity A c + reflectionMultiplicity A d ≤ A.card + A.card / 2 := by
  set Xc := A.filter (fun a : ℤ => 2 * a - c ∈ A ∧ a ≠ c) with hXc
  set Xd := A.filter (fun a : ℤ => 2 * a - d ∈ A ∧ a ≠ d) with hXd
  have hc : reflectionMultiplicity A c = Xc.card := by
    rw [hXc]; exact reflectionMultiplicity_eq_card_filter A c
  have hd : reflectionMultiplicity A d = Xd.card := by
    rw [hXd]; exact reflectionMultiplicity_eq_card_filter A d
  rw [hc, hd]
  have hsub : Xc ∪ Xd ⊆ A := by
    intro a ha
    rw [Finset.mem_union] at ha
    rcases ha with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hunion : (Xc ∪ Xd).card ≤ A.card := Finset.card_le_card hsub
  have hinter : 2 * (Xc ∩ Xd).card ≤ A.card := by
    rw [hXc, hXd]
    exact two_mul_card_inter_centers_le A hcd hfree
  have hden : Xc.card + Xd.card = (Xc ∪ Xd).card + (Xc ∩ Xd).card :=
    (Finset.card_union_add_card_inter Xc Xd).symm
  have hhalf : (Xc ∩ Xd).card ≤ A.card / 2 := by omega
  omega

/-! ## The mass lower bound `2*(m-1) ≤ M` for `m ≥ 9` -/

/-- **Mass dominates twice the multiplicity cap.**  For `A ⊆ [0,L)` with at
least `9` elements, `2 * (A.card - 1) ≤ reflectionMass A L`.  This combines the
universal mass bound `⌊(m-1)²/4⌋ ≤ M` with `2*(m-1) ≤ ⌊(m-1)²/4⌋` for
`m - 1 ≥ 8`. -/
theorem two_mul_pred_card_le_reflectionMass (A : Finset ℤ) (L : ℤ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hm : 9 ≤ A.card) :
    2 * (A.card - 1) ≤ reflectionMass A L := by
  have h1 := card_le_reflectionMass A L hA
  have h2 : 2 * (A.card - 1) ≤ (A.card - 1) ^ 2 / 4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
    have hn : 8 ≤ A.card - 1 := by omega
    calc 2 * (A.card - 1) * 4 = 8 * (A.card - 1) := by ring
      _ ≤ (A.card - 1) * (A.card - 1) := Nat.mul_le_mul_right _ hn
      _ = (A.card - 1) ^ 2 := by ring
  omega

/-! ## Pure aggregation: pairwise sum bound and mass domination give the energy bound

The remaining content is independent of reflections. -/

/-- **Numeric core.**  For natural numbers `K`, `bb`, `mm` with `bb ≤ K ≤ mm`,

  `2*K² + 2*(bb*mm) ≤ (bb + K)*(mm + K)`.

The two sides differ by `(K - bb)*(mm - K)`, which is nonnegative by the
hypotheses. -/
theorem two_mul_sq_add_le_mul (K bb mm : ℕ) (hb : bb ≤ K) (hm : K ≤ mm) :
    2 * K ^ 2 + 2 * (bb * mm) ≤ (bb + K) * (mm + K) := by
  have hprod : (0 : ℤ) ≤ ((K : ℤ) - bb) * ((mm : ℤ) - K) :=
    mul_nonneg (by omega) (by omega)
  have key : (2 : ℤ) * (K : ℤ) ^ 2 + 2 * ((bb : ℤ) * (mm : ℤ))
      ≤ ((bb : ℤ) + K) * ((mm : ℤ) + K) := by
    nlinarith [hprod]
  exact_mod_cast key

/-- **Averaged second moment.**  Let `T` be a finite index set and `f : T → ℕ`
with `Σ f = ∑ d ∈ T, f d`.  Suppose

  * `f c + f d ≤ B` for all distinct `c, d ∈ T`, and
  * `2 * f c ≤ ∑ d ∈ T, f d` for all `c ∈ T`.

Then `2 * ∑ c ∈ T, f c² ≤ B * ∑ d ∈ T, f d`.

The proof splits off a maximizer `c*` with value `K = f c*`.  If `2*K ≤ B`, the
bound is termwise: `2*(f c)² ≤ B * f c` since `f c ≤ K`.  Otherwise every other
value is at most `B - K` (from the pairwise bound) and the mass domination gives
`K ≤ Σ_{d ≠ c*} f d`, so the residual inequality is exactly `two_mul_sq_add_le_mul`
with `bb = B - K` and `mm = Σ_{d ≠ c*} f d`. -/
theorem two_mul_sum_sq_le_of_pairwise_sum_le {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (f : ι → ℕ) (B : ℕ)
    (hpair : ∀ c ∈ T, ∀ d ∈ T, c ≠ d → f c + f d ≤ B)
    (hbig : ∀ c ∈ T, 2 * f c ≤ ∑ d ∈ T, f d) :
    2 * ∑ c ∈ T, (f c) ^ 2 ≤ B * ∑ d ∈ T, f d := by
  by_cases hcard : T.card ≤ 1
  · rcases T.eq_empty_or_nonempty with hT | hne
    · simp [hT]
    · obtain ⟨c, hc⟩ := hne
      have hsub : T ⊆ {c} := by
        intro x hx
        rw [Finset.mem_singleton]
        exact (Finset.card_le_one.mp hcard) x hx c hc
      have hTeq : T = {c} := Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hc)
      have hb := hbig c hc
      rw [hTeq] at hb
      simp only [Finset.sum_singleton] at hb
      have hz : f c = 0 := by omega
      rw [hTeq]
      simp only [Finset.sum_singleton]
      simp [hz]
  · simp only [not_le] at hcard
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨cstar, hcstar, hmax⟩ := T.exists_max_image f hne
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    have hsecond : ∃ d ∈ T, d ≠ cstar := by
      by_cases hxc : x = cstar
      · exact ⟨y, hy, fun hyc => hxy (hxc.trans hyc.symm)⟩
      · exact ⟨x, hx, hxc⟩
    obtain ⟨d, hdT, hdne⟩ := hsecond
    have hKle : f cstar ≤ B := by
      have hp := hpair cstar hcstar d hdT (fun h => hdne h.symm)
      omega
    by_cases hcase : 2 * f cstar ≤ B
    · have hstep : ∀ c ∈ T, 2 * (f c) ^ 2 ≤ B * f c := by
        intro c hc
        have hfc : f c ≤ f cstar := hmax c hc
        have h2 : 2 * f c ≤ B := by omega
        calc 2 * (f c) ^ 2 = (f c) * (2 * f c) := by ring
          _ ≤ (f c) * B := Nat.mul_le_mul_left _ h2
          _ = B * f c := by ring
      calc 2 * ∑ c ∈ T, (f c) ^ 2 = ∑ c ∈ T, 2 * (f c) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ ∑ c ∈ T, B * f c := Finset.sum_le_sum hstep
        _ = B * ∑ c ∈ T, f c := by rw [Finset.mul_sum]
    · simp only [not_le] at hcase
      set SM := ∑ c ∈ T.erase cstar, f c with hSM
      have hM : ∑ c ∈ T, f c = f cstar + SM := by
        have h := T.sum_erase_add f hcstar
        rw [← hSM] at h
        omega
      have hKSM : f cstar ≤ SM := by
        have hb := hbig cstar hcstar
        rw [hM] at hb
        omega
      have hbb : B - f cstar ≤ f cstar := by omega
      have hnum := two_mul_sq_add_le_mul (f cstar) (B - f cstar) SM hbb hKSM
      have hEbound : ∑ c ∈ T, (f c) ^ 2 ≤ (f cstar) ^ 2 + (B - f cstar) * SM := by
        have hsplitE : ∑ c ∈ T, (f c) ^ 2
            = (f cstar) ^ 2 + ∑ c ∈ T.erase cstar, (f c) ^ 2 := by
          have h := T.sum_erase_add (fun c => (f c) ^ 2) hcstar
          omega
        have herase : ∑ c ∈ T.erase cstar, (f c) ^ 2 ≤ (B - f cstar) * SM := by
          rw [hSM, Finset.mul_sum]
          refine Finset.sum_le_sum fun c hc => ?_
          have hcT : c ∈ T := (Finset.mem_erase.mp hc).2
          have hcne : c ≠ cstar := (Finset.mem_erase.mp hc).1
          have hp := hpair c hcT cstar hcstar hcne
          have hfc : f c ≤ B - f cstar := by omega
          calc (f c) ^ 2 = (f c) * (f c) := by ring
            _ ≤ (f c) * (B - f cstar) := Nat.mul_le_mul_left _ hfc
            _ = (B - f cstar) * (f c) := by ring
        rw [hsplitE]
        omega
      calc 2 * ∑ c ∈ T, (f c) ^ 2
          ≤ 2 * ((f cstar) ^ 2 + (B - f cstar) * SM) := Nat.mul_le_mul_left 2 hEbound
        _ = 2 * (f cstar) ^ 2 + 2 * ((B - f cstar) * SM) := by ring
        _ ≤ ((B - f cstar) + f cstar) * (SM + f cstar) := hnum
        _ = B * ∑ c ∈ T, f c := by
              rw [Nat.sub_add_cancel hKle, hM]
              congr 1
              omega

/-! ## The public averaged reflection-energy bound -/

/-- **Averaged reflection-energy bound.**  Let `A : Finset ℤ` be contained in
the half-open interval `[0,L)` and be scalar (ordinary) 3-AP-free, with
`m = A.card ≥ 9`.  Then

  `2 * ∑_{c ∈ [0,L)} ν(c)² ≤ (m + m / 2) * M`,

where `ν(c) = reflectionMultiplicity A c` and `M = reflectionMass A L`.  Since
`m / 2` is the `ℕ` floor, the factor is `m + ⌊m/2⌋`, i.e. the exact `B` of the
informal argument.

This is the denominator-free form of the averaged second-moment estimate
`E ≤ (B/2) * M`.  Its inputs are the fiber-overlap bound
`reflectionMultiplicity_pair_le` (geometric, proved above), the universal mass
bound `card_le_reflectionMass`, and the pointwise bound
`reflectionMultiplicity_le`. -/
theorem two_mul_sum_sq_multiplicity_le (A : Finset ℤ) (L : ℤ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hfree : ThreeAPFree (A : Set ℤ))
    (hm : 9 ≤ A.card) :
    2 * (∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2)
      ≤ (A.card + A.card / 2) * reflectionMass A L := by
  set B := A.card + A.card / 2 with hB
  have hmass := reflectionMass_eq_sum_multiplicity A L
  have hpair : ∀ c ∈ Finset.Ico 0 L, ∀ d ∈ Finset.Ico 0 L, c ≠ d →
      reflectionMultiplicity A c + reflectionMultiplicity A d ≤ B := by
    intro c _ d _ hcd
    rw [hB]
    exact reflectionMultiplicity_pair_le A hcd hfree
  have hbig : ∀ c ∈ Finset.Ico 0 L, 2 * reflectionMultiplicity A c
      ≤ ∑ d ∈ Finset.Ico 0 L, reflectionMultiplicity A d := by
    intro c _
    rw [← hmass]
    have hnu := reflectionMultiplicity_le A c
    have hMlow := two_mul_pred_card_le_reflectionMass A L hA hm
    omega
  have hmain := two_mul_sum_sq_le_of_pairwise_sum_le (Finset.Ico 0 L)
    (reflectionMultiplicity A) B hpair hbig
  rw [hmass]
  exact hmain

/-! ## Ground truth, satisfiability, and boundary audit -/

/-- Ground truth: `{1,2,4,8}` is 3-AP-free. -/
example : ThreeAPFree (({1, 2, 4, 8} : Finset ℤ) : Set ℤ) := by decide

/-- Ground truth for the multiplicity at that set: the three representations
`2*1 - 2 = 2*2 - 4 = 2*4 - 8 = 0` give `ν(0) = 3`. -/
example : reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 0 = 3 := by decide

/-- Satisfiability of the fiber-overlap bound at `c = 0`, `d = 3`: the common
centres of `{1,2,4,8}` are just `{2}`, and `2 * 1 ≤ 4`. -/
example : 2 * ((({1, 2, 4, 8} : Finset ℤ).filter (fun a : ℤ => 2 * a - 0 ∈
      ({1, 2, 4, 8} : Finset ℤ) ∧ a ≠ 0)) ∩
      (({1, 2, 4, 8} : Finset ℤ).filter (fun a : ℤ => 2 * a - 3 ∈
      ({1, 2, 4, 8} : Finset ℤ) ∧ a ≠ 3))).card ≤ ({1, 2, 4, 8} : Finset ℤ).card :=
  two_mul_card_inter_centers_le _ (c := 0) (d := 3) (by norm_num) (by decide)

/-- Satisfiability of the pairwise sum bound at the same targets:
`ν(0) + ν(3) = 3 + 1 = 4 ≤ 4 + 4/2 = 6`. -/
example : reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 0
    + reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) 3 ≤ 4 + 4 / 2 :=
  reflectionMultiplicity_pair_le _ (c := 0) (d := 3) (by norm_num) (by decide)

/-- Ground truth for the numeric core: `K = 5`, `bb = 3`, `mm = 7` satisfy
`2*25 + 2*21 = 92 ≤ 8*12 = 96`. -/
example : 2 * (5 : ℕ) ^ 2 + 2 * (3 * 7) ≤ (3 + 5) * (7 + 5) :=
  two_mul_sq_add_le_mul 5 3 7 (by norm_num) (by norm_num)

/-- Satisfiability of the pure averaging lemma at a concrete dataset: with
`T = {0,1,2}` and `f = ![3,1,1]`, the pairwise sums are at most `B = 6`, the
mass is `5 ≥ 2*max = 6` fails, so use `B = 7`; the bound `2*11 = 22 ≤ 7*5 = 35`
holds. -/
example : 2 * ((3 : ℕ) ^ 2 + 1 ^ 2 + 1 ^ 2) ≤ 7 * (3 + 1 + 1) := by norm_num

/-- A 3-AP-free set of size `9` inside `[0,28)` (all numbers with base-`3` digits
in `{0,1}` and at most three digits plus `27`), satisfying the range and cap
hypotheses of the main theorem. -/
example : (∀ a ∈ ({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ), 0 ≤ a ∧ a < 28) ∧
    ThreeAPFree ((({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ) : Set ℤ)) := by
  refine ⟨by decide, by decide⟩

/-- The main theorem at that nonvacuous input: the hypotheses `9 ≤ m` and
3-AP-freeness are jointly satisfiable, and the endpoint holds. -/
example : 2 * (∑ c ∈ Finset.Ico (0 : ℤ) 28,
      (reflectionMultiplicity ({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ) c) ^ 2)
    ≤ (({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ).card
        + ({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ).card / 2)
      * reflectionMass ({0, 1, 3, 4, 9, 10, 12, 13, 27} : Finset ℤ) 28 :=
  two_mul_sum_sq_multiplicity_le _ _ (by decide) (by decide) (by decide)

end Erdos142