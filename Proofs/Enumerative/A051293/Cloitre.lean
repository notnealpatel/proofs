import Enumerative.A051293.Counting

/-!
# A051293: Cloitre's conjecture in its published form

`Enumerative.A051293.Counting` proves `cloitre_conjecture` for every truncation
order `M`, phrased over the in-tree combinatorial count `a_comb` (subsets of
`Finset.range n`, shifted by one) and with coefficients named as `fubini i`.

This file closes the last two gaps between that theorem and the statement a
reader of OEIS A051293 would recognise.

1. **Ground truth.** `a_comb` carries no ground-truth anchor in `Counting.lean`:
   nothing there pins the definition to the actual OEIS terms, so a
   misformalization would compile clean. We pin both the in-tree definition and
   the OEIS-literal one (`a_oeis`, over `Finset.Icc 1 n` with `S.sum id`)
   against the first ten terms of the A051293 DATA section by kernel `decide`,
   and prove the two definitions equal for all `n`.

2. **Explicit coefficients.** Cloitre's Oct 2002 comment ends with an explicit
   truncation, and it is this form that the DeepMind/AlphaProof-Nexus agent
   proved (arXiv:2605.22763, `APNOutputs/OEIS/oeis_51293_conjecture_0.lean`,
   `target_theorem_0`):

   `a(n) = 2^(n+1)/n · (1 + 1/n + 3/n² + 13/n³ + 75/n⁴ + 541/n⁵ + o(1/n⁵))`.

   `cloitre_explicit_tendsto` below is that statement, over the OEIS-literal
   definition and in the same `Tendsto … (nhds 0)` ratio form, obtained as the
   `M = 5` instance of the general-`M` in-tree theorem. The general-`M` theorem
   is therefore strictly stronger than the published result, which fixes `M = 5`.

## Reading the two error terms

`cloitre_conjecture M` bounds the error by `o(2^n / n^(M+1))`. Dividing by the
prefactor `2^(n+1)/n`, that says

  `a(n)·n/2^(n+1) − ∑_{i≤M} fubini i / n^i = o(1/n^M)`,

which is the standard asymptotic-expansion statement, and at `M = 5` it is
exactly Cloitre's explicit `+ o(1/n⁵)`. Cloitre's *general* phrasing on OEIS
(`∑_{k=0..m} … + o(1/n^(m+1))`) is off by one power against his own explicit
instance: read with the error inside the prefactor it would force
`fubini (m+1) = 0`. The in-tree family follows the explicit reading.
-/

open Finset BigOperators Filter Asymptotics

namespace A051293

section OeisDef

/-- The OEIS-literal count: nonempty `S ⊆ {1,…,n}` whose elements have an
integer average, i.e. `#S ∣ ∑_{s ∈ S} s`. This is the definition used by the
DeepMind formalization (`def A051293` in `oeis_51293_conjecture_0.lean`);
`a_comb` is the same count over `{0,…,n−1}` with elements shifted by one. -/
def a_oeis (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S : Finset ℕ =>
    S.Nonempty ∧ S.card ∣ S.sum id)).card

end OeisDef

section GroundTruth

/-! ### Ground truth against the OEIS terms

A051293 begins `1, 2, 5, 8, 15, 26, 45, 76, 135, 238, 425`. Every check below is
kernel `decide` — no `native_decide`, so nothing here enlarges the trust base.
This is the guard the DeepMind pipeline calls a "test lemma": it is what makes a
proof about `a_comb` a proof about A051293. -/

example : a_comb 1 = 1 := by decide
example : a_comb 2 = 2 := by decide
example : a_comb 3 = 5 := by decide
example : a_comb 4 = 8 := by decide
example : a_comb 5 = 15 := by decide
example : a_comb 6 = 26 := by decide
example : a_comb 7 = 45 := by decide
example : a_comb 8 = 76 := by decide

example : a_oeis 1 = 1 := by decide
example : a_oeis 2 = 2 := by decide
example : a_oeis 3 = 5 := by decide
example : a_oeis 4 = 8 := by decide
example : a_oeis 5 = 15 := by decide
example : a_oeis 6 = 26 := by decide
example : a_oeis 7 = 45 := by decide
example : a_oeis 8 = 76 := by decide

/-! Past `n = 8` the powerset enumeration exceeds the default elaborator
recursion limit; `maxRecDepth` is raised locally. These stay kernel `decide`. -/

set_option maxRecDepth 100000 in
example : a_comb 9 = 135 := by decide

set_option maxRecDepth 100000 in
example : a_oeis 9 = 135 := by decide

set_option maxRecDepth 100000 in
example : a_comb 10 = 238 := by decide

set_option maxRecDepth 100000 in
example : a_oeis 10 = 238 := by decide

end GroundTruth

section Bridge

/-- The shift `m ↦ m + 1`, as an embedding `ℕ ↪ ℕ`. -/
private def shiftEmb : ℕ ↪ ℕ := ⟨fun m => m + 1, fun _ _ h => by simpa using h⟩

@[simp] private lemma shiftEmb_apply (m : ℕ) : shiftEmb m = m + 1 := rfl

/-- Shifting by one is a bijection from the subsets of `{0,…,n−1}` with integer
mean onto the subsets of `{1,…,n}` with integer mean. -/
theorem a_comb_eq_a_oeis (n : ℕ) : a_comb n = a_oeis n := by
  have hsum_map : ∀ S : Finset ℕ, (S.map shiftEmb).sum id = S.sum (· + 1) := by
    intro S; rw [Finset.sum_map]; rfl
  simp only [a_comb, a_oeis, intMeanSubsets]
  refine Finset.card_nbij (fun S => S.map shiftEmb) ?_ ?_ ?_
  · -- `S ↦ S+1` maps integer-mean subsets of `{0,…,n−1}` into those of `{1,…,n}`
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    obtain ⟨hsub, hne, hdvd⟩ := hS
    refine ⟨fun x hx => ?_, Finset.map_nonempty.mpr hne, ?_⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hx
      have hslt : s < n := Finset.mem_range.mp (hsub hs)
      simp only [shiftEmb_apply]
      exact Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 s, by omega⟩
    · rw [Finset.card_map, hsum_map]; exact hdvd
  · exact fun a _ b _ hab => Finset.map_injective shiftEmb hab
  · -- every integer-mean subset of `{1,…,n}` is such a shift
    intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hsub, hne, hdvd⟩ := hT
    have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => (Finset.mem_Icc.mp (hsub ht)).1
    have hinj : Set.InjOn (fun t : ℕ => t - 1) ↑T := by
      intro a ha b hb hab
      have ha1 := hT1 a (Finset.mem_coe.mp ha)
      have hb1 := hT1 b (Finset.mem_coe.mp hb)
      simp only at hab
      omega
    refine ⟨T.image (fun t => t - 1), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun x hx => ?_, Finset.image_nonempty.mpr hne, ?_⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
        have h1 := hT1 t ht
        have h2 := (Finset.mem_Icc.mp (hsub ht)).2
        exact Finset.mem_range.mpr (by omega)
      · rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj]
        have hsumid : ∑ t ∈ T, (t - 1 + 1) = T.sum id :=
          Finset.sum_congr rfl fun t ht => by have := hT1 t ht; simp only [id]; omega
        rw [hsumid]; exact hdvd
    · show Finset.map shiftEmb (T.image (fun t => t - 1)) = T
      rw [Finset.map_eq_image, Finset.image_image]
      have hcongr : T.image ((shiftEmb : ℕ → ℕ) ∘ fun t => t - 1) = T.image id :=
        Finset.image_congr fun t ht => by
          have := hT1 t (Finset.mem_coe.mp ht)
          simp only [Function.comp_apply, shiftEmb_apply, id]
          omega
      rw [hcongr, Finset.image_id]

end Bridge

section Explicit

/-- The `M = 5` truncation of the Fubini coefficient sum, in numerals:
`∑_{i<6} fubini i / n^i = 1 + 1/n + 3/n² + 13/n³ + 75/n⁴ + 541/n⁵`. -/
theorem sum_fubini_range_six (x : ℝ) :
    ∑ i ∈ Finset.range 6, (fubini i : ℝ) / x ^ i =
      1 + 1 / x + 3 / x ^ 2 + 13 / x ^ 3 + 75 / x ^ 4 + 541 / x ^ 5 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fubini_zero, fubini_one, fubini_two,
    fubini_three, fubini_four, fubini_five, pow_zero, pow_one]
  push_cast
  ring

/-- **Cloitre's explicit conjecture (OEIS A051293, Oct 2002).**
`a(n) − 2^(n+1)/n · (1 + 1/n + 3/n² + 13/n³ + 75/n⁴ + 541/n⁵) = o(2^(n+1)/n⁶)`,
stated over the OEIS-literal count `a_oeis`. -/
theorem cloitre_explicit :
    (fun n : ℕ => (a_oeis n : ℝ) - (2 : ℝ) ^ (n + 1) / (n : ℝ) *
        (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3
          + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5))
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ (n + 1) / (n : ℝ) ^ 6) := by
  have h := cloitre_conjecture 5
  have hfun : (fun n : ℕ => (a_comb n : ℝ) - (2 : ℝ) ^ (n + 1) / (n : ℝ) *
        ∑ i ∈ Finset.range (5 + 1), ((fubini i : ℕ) : ℝ) / (n : ℝ) ^ i)
      = fun n : ℕ => (a_oeis n : ℝ) - (2 : ℝ) ^ (n + 1) / (n : ℝ) *
        (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3
          + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5) := by
    funext n
    rw [a_comb_eq_a_oeis, sum_fubini_range_six]
  rw [hfun] at h
  -- The two error scales differ only by the constant factor `2`.
  refine h.trans_isBigO ?_
  have hscale : (fun n : ℕ => (2 : ℝ) ^ (n + 1) / (n : ℝ) ^ 6)
      = fun n : ℕ => 2 * ((2 : ℝ) ^ n / (n : ℝ) ^ 6) := by
    funext n; rw [pow_succ]; ring
  rw [hscale]
  exact Asymptotics.isBigO_self_const_mul (by norm_num) _ _

/-- Cloitre's explicit conjecture in the ratio form used by the DeepMind
formalization: this is `target_theorem_0` of
`alphaproof-nexus-results/APNOutputs/OEIS/oeis_51293_conjecture_0.lean`
(arXiv:2605.22763), with `a_real` replaced by the definitionally matching
`a_oeis`. It is the `M = 5` instance of `cloitre_conjecture`. -/
theorem cloitre_explicit_tendsto :
    Tendsto (fun n : ℕ => ((a_oeis n : ℝ) - (2 : ℝ) ^ (n + 1) / (n : ℝ) *
        (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3
          + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5))
      / ((2 : ℝ) ^ (n + 1) / (n : ℝ) ^ 6)) atTop (nhds 0) := by
  have hne : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (n + 1) / (n : ℝ) ^ 6 = 0 →
      (a_oeis n : ℝ) - (2 : ℝ) ^ (n + 1) / (n : ℝ) *
        (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3
          + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5) = 0 := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn hzero => absurd hzero ?_⟩
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  exact (Asymptotics.isLittleO_iff_tendsto' hne).mp cloitre_explicit

end Explicit

end A051293
