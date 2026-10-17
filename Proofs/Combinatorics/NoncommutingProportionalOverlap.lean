import Combinatorics.NoncommutingBoxWindows

set_option autoImplicit false

namespace NoncommutingProportionalOverlap

open NoncommutingBoxWindows

/-- The proportional integer selector for ordered positive interval lengths. -/
def selector (L M u : ℤ) : ℤ := L * u / (L + M - 1)

example : selector 1 1 0 = 0 := by decide
example : selector 1 4 3 = 0 := by decide
example : selector 4 1 3 = 3 := by decide
example : selector 2 2 2 = 1 := by decide
example : selector 2 4 4 = 1 := by decide

/-- The proportional selector lies between the two endpoints of the overlap. -/
theorem selector_bounds (L M u : ℤ) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hu : 0 ≤ u) (huT : u ≤ L + M - 2) :
    max 0 (u - M + 1) ≤ selector L M u ∧
      selector L M u ≤ min (L - 1) u := by
  have hT : 0 < L + M - 1 := by omega
  have hnonneg : 0 ≤ selector L M u := by
    apply (Int.le_ediv_iff_mul_le hT).mpr
    nlinarith
  have hlower : u - M + 1 ≤ selector L M u := by
    apply (Int.le_ediv_iff_mul_le hT).mpr
    nlinarith [mul_nonneg (show 0 ≤ M - 1 by omega)
      (show 0 ≤ L + M - 1 - u by omega)]
  have hupper : selector L M u < L := by
    apply (Int.ediv_lt_iff_lt_mul hT).mpr
    nlinarith
  have hself : selector L M u < u + 1 := by
    apply (Int.ediv_lt_iff_lt_mul hT).mpr
    nlinarith [mul_nonneg (show 0 ≤ M - 1 by omega) hu]
  exact ⟨max_le hnonneg hlower, le_min (by omega) (by omega)⟩

/-- A single mark in the original first-coordinate interval. -/
def mark (r L q M t : ℤ) : ℤ := r + selector L M (t - r - q)

example : mark 5 2 (-3) 4 4 = 5 := by decide
example : mark 5 2 (-3) 4 6 = 6 := by decide

/-- Every nonempty actual overlap contains its proportional mark, for arbitrary
positive ordered lengths and arbitrary translations. -/
theorem mark_mem_actualOverlap (r L q M t : ℤ) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hne : (actualOverlap r L q M t).Nonempty) :
    mark r L q M t ∈ actualOverlap r L q M t := by
  obtain ⟨hu, huT⟩ := actualOverlap_source_bounds r L q M t hL hM hne
  obtain ⟨hlo, hhi⟩ := selector_bounds L M (t - r - q) hL hM hu huT
  rw [mem_actualOverlap]
  dsimp [mark]
  have hlo0 := le_trans (le_max_left 0 (t - r - q - M + 1)) hlo
  have hlo1 := le_trans (le_max_right 0 (t - r - q - M + 1)) hlo
  have hhi0 := le_trans hhi (min_le_left (L - 1) (t - r - q))
  have hhi1 := le_trans hhi (min_le_right (L - 1) (t - r - q))
  omega

private theorem card_mul_le_of_span (S : Finset ℤ) (L M : ℤ)
    (hL : 1 ≤ L) (_hM : 1 ≤ M)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, L * (y - x) < L + M - 1) :
    L * (S.card : ℤ) ≤ 3 * max L M := by
  classical
  by_cases hne : S.Nonempty
  · let a := S.min' hne
    let b := S.max' hne
    have ha : a ∈ S := S.min'_mem hne
    have hb : b ∈ S := S.max'_mem hne
    have hab : a ≤ b := S.min'_le_max' hne
    have hsub : S ⊆ Finset.Icc a b := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hc
    have hcZ : (S.card : ℤ) ≤ b + 1 - a := by
      have hcast : (S.card : ℤ) ≤ ((b + 1 - a).toNat : ℤ) := by
        exact_mod_cast hc
      rwa [Int.toNat_of_nonneg (by omega)] at hcast
    have hmul := mul_le_mul_of_nonneg_left hcZ (show 0 ≤ L by omega)
    have hdiam := hspan a ha b hb
    have hmaxL : L ≤ max L M := le_max_left L M
    have hmaxM : M ≤ max L M := le_max_right L M
    nlinarith
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    have hmaxL : L ≤ max L M := le_max_left L M
    omega

private theorem selector_fiber_span (L M x y : ℤ) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (heq : selector L M x = selector L M y) :
    L * (y - x) < L + M - 1 := by
  have hT : 0 < L + M - 1 := by omega
  have hx := Int.ediv_mul_le (L * x) (ne_of_gt hT)
  have hy := Int.lt_ediv_add_one_mul_self (L * y) hT
  change selector L M x * (L + M - 1) ≤ L * x at hx
  change L * y < (selector L M y + 1) * (L + M - 1) at hy
  rw [← heq] at hy
  nlinarith

/-- The global scalar fiber bound retains its individual first-length weight;
no source-range restriction is needed. -/
theorem selector_fiber_card_int (S : Finset ℤ) (L M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    L * ((S.filter (fun u => selector L M u = j)).card : ℤ) ≤ 3 * max L M := by
  apply card_mul_le_of_span _ L M hL hM
  intro x hx y hy
  exact selector_fiber_span L M x y hL hM
    ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)

/-- The natural-number scalar fiber bound, with the retained length on the left. -/
theorem selector_fiber_card (S : Finset ℤ) (L M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    L.toNat * (S.filter (fun u => selector L M u = j)).card ≤
      3 * (max L M).toNat := by
  have h := selector_fiber_card_int S L M j hL hM
  have hLn : (L.toNat : ℤ) = L := Int.toNat_of_nonneg (by omega)
  have hmaxn : ((max L M).toNat : ℤ) = max L M :=
    Int.toNat_of_nonneg (by omega)
  exact_mod_cast (show (L.toNat : ℤ) *
    ((S.filter (fun u => selector L M u = j)).card : ℤ) ≤
      3 * ((max L M).toNat : ℤ) by rwa [hLn, hmaxn])

/-- Translation preserves the global weighted fiber estimate for actual marks. -/
theorem mark_fiber_card_int (S : Finset ℤ) (r L q M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    L * ((S.filter (fun t => mark r L q M t = j)).card : ℤ) ≤ 3 * max L M := by
  apply card_mul_le_of_span _ L M hL hM
  intro x hx y hy
  have heq : selector L M (x - r - q) = selector L M (y - r - q) := by
    have hxj := (Finset.mem_filter.mp hx).2
    have hyj := (Finset.mem_filter.mp hy).2
    dsimp [mark] at hxj hyj
    omega
  have hspan := selector_fiber_span L M (x - r - q) (y - r - q) hL hM heq
  convert hspan using 1
  ring

/-- Natural-number version of the translated mark fiber bound. -/
theorem mark_fiber_card (S : Finset ℤ) (r L q M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    L.toNat * (S.filter (fun t => mark r L q M t = j)).card ≤
      3 * (max L M).toNat := by
  have h := mark_fiber_card_int S r L q M j hL hM
  have hLn : (L.toNat : ℤ) = L := Int.toNat_of_nonneg (by omega)
  have hmaxn : ((max L M).toNat : ℤ) = max L M :=
    Int.toNat_of_nonneg (by omega)
  exact_mod_cast (show (L.toNat : ℤ) *
    ((S.filter (fun t => mark r L q M t = j)).card : ℤ) ≤
      3 * ((max L M).toNat : ℤ) by rwa [hLn, hmaxn])

private theorem real_card_le_of_weight (n : ℕ) (L M : ℤ) (hL : 1 ≤ L)
    (h : L * (n : ℤ) ≤ 3 * max L M) :
    (n : ℝ) ≤ 3 * max 1 ((M : ℝ) / L) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hR : (L : ℝ) * (n : ℝ) ≤ 3 * max (L : ℝ) (M : ℝ) := by
    exact_mod_cast h
  have hratio : (L : ℝ) * ((M : ℝ) / L) = M := by field_simp
  have hscaled0 := mul_le_mul_of_nonneg_left
    (le_max_left (1 : ℝ) ((M : ℝ) / L)) (le_of_lt hLp)
  have hscaled1 := mul_le_mul_of_nonneg_left
    (le_max_right (1 : ℝ) ((M : ℝ) / L)) (le_of_lt hLp)
  have hm : max (L : ℝ) (M : ℝ) ≤ (L : ℝ) * max 1 ((M : ℝ) / L) := by
    apply max_le <;> nlinarith
  nlinarith

/-- Scalar fibers retain their individual aspect-ratio bound, with no
valid-source restriction. -/
theorem selector_fiber_card_real (S : Finset ℤ) (L M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    ((S.filter (fun u => selector L M u = j)).card : ℝ) ≤
      3 * max 1 ((M : ℝ) / L) :=
  real_card_le_of_weight _ L M hL (selector_fiber_card_int S L M j hL hM)

/-- Actual translated scalar mark fibers retain the individual aspect ratio. -/
theorem mark_fiber_card_real (S : Finset ℤ) (r L q M j : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) :
    ((S.filter (fun t => mark r L q M t = j)).card : ℝ) ≤
      3 * max 1 ((M : ℝ) / L) :=
  real_card_le_of_weight _ L M hL (mark_fiber_card_int S r L q M j hL hM)

/-- Pair fibers are bounded by the product of the individual aspect ratios,
not by a common aspect parameter. -/
theorem pair_mark_fiber_card_real (S : Finset (ℤ × ℤ))
    (r L q M r' L' q' M' j j' : ℤ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hL' : 1 ≤ L') (hM' : 1 ≤ M') :
    ((S.filter (fun p =>
      (mark r L q M p.1, mark r' L' q' M' p.2) = (j, j'))).card : ℝ) ≤
      9 * max 1 ((M : ℝ) / L) * max 1 ((M' : ℝ) / L') := by
  classical
  let A := (S.image Prod.fst).filter (fun t => mark r L q M t = j)
  let B := (S.image Prod.snd).filter (fun t => mark r' L' q' M' t = j')
  have hsub : S.filter (fun p =>
      (mark r L q M p.1, mark r' L' q' M' p.2) = (j, j')) ⊆ A ×ˢ B := by
    intro p hp
    obtain ⟨hpS, hpj⟩ := Finset.mem_filter.mp hp
    have hfst := congrArg Prod.fst hpj
    have hsnd := congrArg Prod.snd hpj
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hpS, rfl⟩, hfst⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hpS, rfl⟩, hsnd⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product] at hc
  have hcR : ((S.filter (fun p =>
      (mark r L q M p.1, mark r' L' q' M' p.2) = (j, j'))).card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) := by exact_mod_cast hc
  have hA : (A.card : ℝ) ≤ 3 * max 1 ((M : ℝ) / L) :=
    mark_fiber_card_real _ r L q M j hL hM
  have hB : (B.card : ℝ) ≤ 3 * max 1 ((M' : ℝ) / L') :=
    mark_fiber_card_real _ r' L' q' M' j' hL' hM'
  calc
    _ ≤ (A.card : ℝ) * (B.card : ℝ) := hcR
    _ ≤ (3 * max 1 ((M : ℝ) / L)) * (3 * max 1 ((M' : ℝ) / L')) :=
      mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

example : mark 0 1 0 1 0 ∈ actualOverlap 0 1 0 1 0 :=
  mark_mem_actualOverlap 0 1 0 1 0 (by decide) (by decide) (by decide)
example : mark 0 1 0 4 3 ∈ actualOverlap 0 1 0 4 3 :=
  mark_mem_actualOverlap 0 1 0 4 3 (by decide) (by decide) (by decide)
example : mark 0 4 0 1 3 ∈ actualOverlap 0 4 0 1 3 :=
  mark_mem_actualOverlap 0 4 0 1 3 (by decide) (by decide) (by decide)
example : mark 0 2 0 2 2 ∈ actualOverlap 0 2 0 2 2 :=
  mark_mem_actualOverlap 0 2 0 2 2 (by decide) (by decide) (by decide)
example : mark 5 2 (-3) 4 4 ∈ actualOverlap 5 2 (-3) 4 4 :=
  mark_mem_actualOverlap 5 2 (-3) 4 4 (by decide) (by decide) (by decide)
example : 2 * ((Finset.Icc (-10) 10).filter (fun u => selector 2 4 u = -1)).card ≤
    3 * 4 := by
  simpa using selector_fiber_card (Finset.Icc (-10) 10) 2 4 (-1) (by decide) (by decide)
example : (({(0, 0), (1, 1)} : Finset (ℤ × ℤ)).filter (fun p =>
    (mark 0 2 0 4 p.1, mark 0 4 0 2 p.2) = (0, 0))).card ≤ 2 := by decide

end NoncommutingProportionalOverlap
