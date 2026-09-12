/-
  Erdős Problem #142 — bounded affine-window infrastructure.

  A window is encoded without integer subtraction.  Its integer base is
  `b - (L - 1) * d`, and an index `i < L` pulls back a natural number `x`
  exactly when `x + (L - 1) * d = b + d * i`.  This permits windows which
  cross the left boundary of `range N` while keeping every definition in
  `ℕ`.

  The results below establish the affine embedding, canonical ordered
  witnesses for the unoriented progression edges, transport of such edges,
  and the exact uniform point-incidence identity for a fixed difference.
  They are finite counting infrastructure, not an asymptotic claim about
  Erdős Problem #142.
-/

import Erdos.Erdos142.ThreeAPCount

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos142

/-- The indices in `[0,L)` whose affine-window values belong to `A`.
The shifted base `b` represents the integer base `b - (L - 1) * d`. -/
def affineWindow (A : Finset ℕ) (L d b : ℕ) : Finset ℕ :=
  (Finset.range L).filter fun i =>
    ∃ x ∈ A, x + (L - 1) * d = b + d * i

/-- The natural value represented by index `i` in a shifted affine window.
On members of `affineWindow`, the subtraction is protected by its defining
incidence equality. -/
def affineWindowValue (L d b i : ℕ) : ℕ :=
  b + d * i - (L - 1) * d

/-- The empty set has an empty pullback in every affine window. -/
example : affineWindow ∅ 3 2 4 = ∅ := by decide

/-- The represented value at the first nonnegative index of the window with
integer base `-2` and difference one is zero. -/
example : affineWindowValue 5 1 2 2 = 0 := by decide

/-- A boundary-crossing window with integer base `-2` and difference one
pulls `{0,1,2}` back to the last three indices of a length-five window. -/
example : affineWindow {0, 1, 2} 5 1 2 = {2, 3, 4} := by decide

/-- Membership in an affine window gives its range bound, membership of the
represented value in `A`, and the subtraction-free incidence equality. -/
theorem mem_affineWindow_iff {A : Finset ℕ} {L d b i : ℕ} :
    i ∈ affineWindow A L d b ↔
      i < L ∧ affineWindowValue L d b i ∈ A ∧
        affineWindowValue L d b i + (L - 1) * d = b + d * i := by
  constructor
  · intro hi
    rw [affineWindow, mem_filter, mem_range] at hi
    obtain ⟨hil, x, hxA, hx⟩ := hi
    have hxvalue : x = affineWindowValue L d b i := by
      apply Nat.eq_sub_of_add_eq
      simpa only [add_comm] using hx
    subst x
    exact ⟨hil, hxA, hx⟩
  · rintro ⟨hil, hvalueA, hvalue⟩
    rw [affineWindow, mem_filter, mem_range]
    exact ⟨hil, affineWindowValue L d b i, hvalueA, hvalue⟩

/-- Every affine-window pullback is contained in `range L`. -/
theorem affineWindow_subset_range (A : Finset ℕ) (L d b : ℕ) :
    affineWindow A L d b ⊆ Finset.range L := by
  intro i hi
  exact mem_range.mpr (mem_affineWindow_iff.mp hi).1

/-- Positive-difference affine-window values are injective on the pullback. -/
theorem affineWindowValue_injOn {A : Finset ℕ} {L d b : ℕ} (hd : 0 < d) :
    Set.InjOn (affineWindowValue L d b) (affineWindow A L d b) := by
  intro i hi j hj hij
  have hirel := (mem_affineWindow_iff.mp hi).2.2
  have hjrel := (mem_affineWindow_iff.mp hj).2.2
  nlinarith

/-- Advancing the window index by `s` advances its represented value by
exactly `s*d`, provided both indices survive the boundary clipping. -/
theorem affineWindowValue_add {A : Finset ℕ} {L d b i s : ℕ}
    (hi : i ∈ affineWindow A L d b)
    (his : i + s ∈ affineWindow A L d b) :
    affineWindowValue L d b (i + s) =
      affineWindowValue L d b i + s * d := by
  have hirel := (mem_affineWindow_iff.mp hi).2.2
  have hisrel := (mem_affineWindow_iff.mp his).2.2
  nlinarith

/-- Every canonical natural-number progression edge has a unique increasing
orientation: it is `{x, x+q, x+2*q}` for a positive difference `q`. -/
theorem exists_ordered_threeAP_of_mem_threeAPEdges {A e : Finset ℕ}
    (he : e ∈ threeAPEdges A) :
    ∃ x q : ℕ, 0 < q ∧ e = {x, x + q, x + 2 * q} := by
  classical
  have hedata := mem_threeAPEdges.mp he
  have hnotfree := hedata.2.2
  rw [ThreeAPFree] at hnotfree
  push Not at hnotfree
  obtain ⟨a, ha, c, hc, z, hz, hacz, hac⟩ := hnotfree
  have hcz : c ≠ z := by
    intro hcz
    subst z
    omega
  have haz : a ≠ z := by
    intro haz
    subst z
    omega
  have hset : e = {a, c, z} := by
    have hsub : ({a, c, z} : Finset ℕ) ⊆ e := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨ha, hc, hz⟩
    have hcard : ({a, c, z} : Finset ℕ).card = 3 := by
      simp [hac, hcz, haz]
    exact (eq_of_subset_of_card_le hsub (by rw [hcard, hedata.2.1])).symm
  have hazlt : a < z ∨ z < a := lt_or_gt_of_ne haz
  rcases hazlt with hazlt | hzalt
  · let q := c - a
    have hq : 0 < q := by
      dsimp only [q]
      omega
    have hcq : c = a + q := by
      dsimp only [q]
      omega
    have hzq : z = a + 2 * q := by
      dsimp only [q]
      omega
    exact ⟨a, q, hq, by rw [hset, hcq, hzq]⟩
  · let q := c - z
    have hq : 0 < q := by
      dsimp only [q]
      omega
    have hcq : c = z + q := by
      dsimp only [q]
      omega
    have haq : a = z + 2 * q := by
      dsimp only [q]
      omega
    refine ⟨z, q, hq, ?_⟩
    rw [hset, hcq, haq]
    ext w
    simp only [mem_insert, mem_singleton]
    tauto

/-- The positive ordered representation of a canonical three-element
progression edge is unique. -/
theorem ordered_threeAP_finset_injective {x q y r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (h : ({x, x + q, x + 2 * q} : Finset ℕ) =
      {y, y + r, y + 2 * r}) :
    x = y ∧ q = r := by
  have hxmem : x ∈ ({y, y + r, y + 2 * r} : Finset ℕ) := by
    rw [← h]
    simp
  have hymem : y ∈ ({x, x + q, x + 2 * q} : Finset ℕ) := by
    rw [h]
    simp
  simp only [mem_insert, mem_singleton] at hxmem hymem
  have hxy : x = y := by
    rcases hxmem with hxy | hxy | hxy <;>
      rcases hymem with hyx | hyx | hyx <;> omega
  subst y
  have hmaxq : x + 2 * q ∈ ({x, x + r, x + 2 * r} : Finset ℕ) := by
    rw [← h]
    simp
  have hmaxr : x + 2 * r ∈ ({x, x + q, x + 2 * q} : Finset ℕ) := by
    rw [h]
    simp
  simp only [mem_insert, mem_singleton] at hmaxq hmaxr
  constructor
  · rfl
  · rcases hmaxq with hmaxq | hmaxq | hmaxq <;>
      rcases hmaxr with hmaxr | hmaxr | hmaxr <;> omega

/-- An affine image of a locally ordered progression is the globally ordered
progression with common difference multiplied by the window difference. -/
theorem affineWindow_ordered_threeAP_transport {A : Finset ℕ}
    {L d b x s : ℕ} (hx : x ∈ affineWindow A L d b)
    (hxs : x + s ∈ affineWindow A L d b)
    (hxss : x + 2 * s ∈ affineWindow A L d b) :
    ({x, x + s, x + 2 * s} : Finset ℕ).image (affineWindowValue L d b) =
      {affineWindowValue L d b x,
        affineWindowValue L d b x + s * d,
        affineWindowValue L d b x + 2 * (s * d)} := by
  have hstep := affineWindowValue_add hx hxs
  have hdouble := affineWindowValue_add hx hxss
  simp only [image_insert, image_singleton]
  rw [hstep, hdouble]
  simp only [mul_assoc]

/-- Mapping a local canonical edge through a positive-difference affine
window produces a canonical edge of the ambient set. -/
theorem image_mem_threeAPEdges_of_mem_affineWindow {A e : Finset ℕ}
    {L d b : ℕ} (hd : 0 < d) (he : e ∈ threeAPEdges (affineWindow A L d b)) :
    e.image (affineWindowValue L d b) ∈ threeAPEdges A := by
  classical
  have hedata := mem_threeAPEdges.mp he
  apply mem_threeAPEdges.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hie, rfl⟩ := mem_image.mp hx
    exact (mem_affineWindow_iff.mp (hedata.1 hie)).2.1
  · rw [card_image_of_injOn]
    · exact hedata.2.1
    · exact (affineWindowValue_injOn hd).mono hedata.1
  · intro hfree
    apply hedata.2.2
    intro i hie j hje k hke hijk
    have hiw := hedata.1 hie
    have hjw := hedata.1 hje
    have hkw := hedata.1 hke
    apply affineWindowValue_injOn hd hiw hjw
    apply hfree
    · exact mem_coe.mpr (mem_image_of_mem _ hie)
    · exact mem_coe.mpr (mem_image_of_mem _ hje)
    · exact mem_coe.mpr (mem_image_of_mem _ hke)
    have hirel := (mem_affineWindow_iff.mp hiw).2.2
    have hjrel := (mem_affineWindow_iff.mp hjw).2.2
    have hkrel := (mem_affineWindow_iff.mp hkw).2.2
    nlinarith

/-- A positive-difference affine embedding cannot create more canonical
progression edges than occur in the ambient set. -/
theorem threeAPCount_affineWindow_le (A : Finset ℕ) (L d b : ℕ) (hd : 0 < d) :
    threeAPCount (affineWindow A L d b) ≤ threeAPCount A := by
  classical
  let f : ℕ → ℕ := affineWindowValue L d b
  let mapEdge : Finset ℕ → Finset ℕ := fun e => e.image f
  have hmaps : ∀ e ∈ threeAPEdges (affineWindow A L d b),
      mapEdge e ∈ threeAPEdges A := by
    intro e he
    exact image_mem_threeAPEdges_of_mem_affineWindow hd he
  have hinj : Set.InjOn mapEdge (threeAPEdges (affineWindow A L d b)) := by
    intro e₁ he₁ e₂ he₂ heq
    have he₁sub := (mem_threeAPEdges.mp he₁).1
    have he₂sub := (mem_threeAPEdges.mp he₂).1
    apply Finset.ext
    intro i
    constructor
    · intro hi
      have hfi : f i ∈ mapEdge e₂ := by
        rw [← heq]
        exact mem_image_of_mem f hi
      obtain ⟨j, hj, hfij⟩ := mem_image.mp hfi
      have hij := affineWindowValue_injOn hd (he₁sub hi) (he₂sub hj) hfij.symm
      simpa only [hij] using hj
    · intro hi
      have hfi : f i ∈ mapEdge e₁ := by
        rw [heq]
        exact mem_image_of_mem f hi
      obtain ⟨j, hj, hfij⟩ := mem_image.mp hfi
      have hij := affineWindowValue_injOn hd (he₂sub hi) (he₁sub hj) hfij.symm
      simpa only [hij] using hj
  calc
    threeAPCount (affineWindow A L d b) =
        (threeAPEdges (affineWindow A L d b)).card := rfl
    _ = ((threeAPEdges (affineWindow A L d b)).image mapEdge).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ (threeAPEdges A).card := by
      apply card_le_card
      intro e he
      obtain ⟨e', he', rfl⟩ := mem_image.mp he
      exact hmaps e' he'
    _ = threeAPCount A := rfl

/-- Every affine pullback satisfies the local Roth deletion bound, and its
local edge count is bounded by the global canonical edge count. -/
theorem card_affineWindow_le_rothNumberNat_add_threeAPCount
    (A : Finset ℕ) (L d b : ℕ) (hd : 0 < d) :
    (affineWindow A L d b).card ≤ rothNumberNat L + threeAPCount A := by
  have hlocal := card_le_rothNumberNat_add_threeAPCount
    (affineWindow_subset_range A L d b)
  exact hlocal.trans (Nat.add_le_add_left (threeAPCount_affineWindow_le A L d b hd) _)

/-- For a fixed admissible index, the shifted bases whose windows contain
that index are in bijection with `A`. -/
theorem card_filter_base_affineWindow (A : Finset ℕ) {N L d i : ℕ}
    (hAN : A ⊆ Finset.range N) (hi : i < L) :
    ((Finset.range (N + (L - 1) * d)).filter fun b =>
      i ∈ affineWindow A L d b).card = A.card := by
  classical
  let base : ℕ → ℕ := fun x => x + (L - 1 - i) * d
  symm
  apply Finset.card_bij (fun x _ => base x)
  · intro x hx
    rw [mem_filter, mem_range]
    have hxN : x < N := mem_range.mp (hAN hx)
    have hsuble : L - 1 - i ≤ L - 1 := Nat.sub_le _ _
    have hmul : (L - 1 - i) * d ≤ (L - 1) * d := Nat.mul_le_mul_right d hsuble
    refine ⟨?_, ?_⟩
    · change x + (L - 1 - i) * d < N + (L - 1) * d
      omega
    rw [affineWindow, mem_filter, mem_range]
    refine ⟨hi, x, hx, ?_⟩
    have hsplit : (L - 1 - i) + i = L - 1 := by omega
    calc
      x + (L - 1) * d = x + ((L - 1 - i) + i) * d := by rw [hsplit]
      _ = base x + d * i := by
        simp only [base, add_mul]
        ac_rfl
  · intro x₁ hx₁ x₂ hx₂ hbase
    dsimp only [base] at hbase
    omega
  · intro b hb
    rw [mem_filter] at hb
    obtain ⟨hbRange, hbi⟩ := hb
    obtain ⟨hil, x, hxA, hxrel⟩ := by
      rw [affineWindow, mem_filter, mem_range] at hbi
      exact hbi
    refine ⟨x, hxA, ?_⟩
    dsimp only [base]
    have hsplit : (L - 1 - i) + i = L - 1 := by omega
    have hoff : (L - 1) * d = (L - 1 - i) * d + d * i := by
      calc
        (L - 1) * d = ((L - 1 - i) + i) * d := by rw [hsplit]
        _ = (L - 1 - i) * d + d * i := by
          rw [add_mul]
          ac_rfl
    omega

/-- Exact uniform point incidence for one positive affine difference: summing
pullback sizes over all boundary-allowed shifted bases gives `L * |A|`. -/
theorem sum_card_affineWindow_fixed_difference (A : Finset ℕ) {N L d : ℕ}
    (hAN : A ⊆ Finset.range N) :
    ∑ b ∈ Finset.range (N + (L - 1) * d),
        (affineWindow A L d b).card = L * A.card := by
  calc
    ∑ b ∈ Finset.range (N + (L - 1) * d),
        (affineWindow A L d b).card =
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          ∑ i ∈ Finset.range L, if i ∈ affineWindow A L d b then 1 else 0 := by
      apply sum_congr rfl
      intro b hb
      rw [affineWindow, card_filter]
      apply sum_congr rfl
      intro i hi
      simp only [mem_filter, hi, true_and]
    _ = ∑ i ∈ Finset.range L,
          ∑ b ∈ Finset.range (N + (L - 1) * d),
            if i ∈ affineWindow A L d b then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ i ∈ Finset.range L,
          ((Finset.range (N + (L - 1) * d)).filter fun b =>
            i ∈ affineWindow A L d b).card := by
      apply sum_congr rfl
      intro i hi
      exact (card_filter _ _).symm
    _ = ∑ _i ∈ Finset.range L, A.card := by
      apply sum_congr rfl
      intro i hi
      rw [card_filter_base_affineWindow A hAN (mem_range.mp hi)]
    _ = L * A.card := by simp


/-- The sum of the positive integers at most `D` is `D*(D+1)/2`. -/
theorem sum_Icc_one_id (D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, d = D * (D + 1) / 2 := by
  have hsub : Finset.Icc 1 D ⊆ Finset.range (D + 1) := by
    intro d hd
    simp only [mem_Icc, mem_range] at hd ⊢
    omega
  calc
    (∑ d ∈ Finset.Icc 1 D, d) = ∑ d ∈ Finset.range (D + 1), d := by
      apply sum_subset hsub
      intro d hdRange hdIcc
      simp only [mem_range] at hdRange
      simp only [mem_Icc, not_and_or, not_le] at hdIcc
      omega
    _ = (D + 1) * ((D + 1) - 1) / 2 := sum_range_id (D + 1)
    _ = D * (D + 1) / 2 := by
      congr 1
      simp only [Nat.add_sub_cancel]
      ac_rfl

/-- The number of boundary-allowed shifted bases, summed over differences
`1 ≤ d ≤ D`, is the explicit affine-window count `F`. -/
theorem sum_affineWindow_base_count (N L D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, (N + (L - 1) * d) =
      D * N + (L - 1) * D * (D + 1) / 2 := by
  rw [sum_add_distrib]
  have hconst : (∑ _d ∈ Finset.Icc 1 D, N) = D * N := by simp
  rw [hconst, ← mul_sum, sum_Icc_one_id]
  have hdvd : 2 ∣ D * (D + 1) := (Nat.even_mul_succ_self D).two_dvd
  calc
    D * N + (L - 1) * (D * (D + 1) / 2) =
        D * N + (L - 1) * (D * (D + 1)) / 2 := by
      rw [Nat.mul_div_assoc (L - 1) hdvd]
    _ = D * N + (L - 1) * D * (D + 1) / 2 := by
      congr 1
      ac_rfl

/-- Exact uniform incidence over all boundary-allowed windows and all
positive differences at most `D`.  Every point of `A` has load `L*D`. -/
theorem sum_card_affineWindow (A : Finset ℕ) {N L D : ℕ}
    (hAN : A ⊆ Finset.range N) :
    ∑ d ∈ Finset.Icc 1 D,
      ∑ b ∈ Finset.range (N + (L - 1) * d),
        (affineWindow A L d b).card = L * D * A.card := by
  calc
    ∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          (affineWindow A L d b).card =
        ∑ _d ∈ Finset.Icc 1 D, L * A.card := by
      apply sum_congr rfl
      intro d hd
      exact sum_card_affineWindow_fixed_difference A hAN
    _ = L * D * A.card := by simp [mul_comm, mul_left_comm]

/-- Parameterized affine-window incidence bound.  Once the total number of
local canonical edges is bounded by `M` times the global edge count, exact
uniform point load and the local Roth deletion inequality give the requested
quantitative supersaturation inequality. -/
theorem affineWindow_incidence_bound_of_threeAP_multiplicity
    (A : Finset ℕ) {N L D M : ℕ} (hAN : A ⊆ Finset.range N)
    (hmultiplicity :
      (∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          threeAPCount (affineWindow A L d b)) ≤ M * threeAPCount A) :
    L * D * A.card ≤
      (D * N + (L - 1) * D * (D + 1) / 2) * rothNumberNat L +
        M * threeAPCount A := by
  have hlocal :
      (∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          (affineWindow A L d b).card) ≤
      ∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          (rothNumberNat L + threeAPCount (affineWindow A L d b)) := by
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro b hb
    exact card_le_rothNumberNat_add_threeAPCount
      (affineWindow_subset_range A L d b)
  rw [sum_card_affineWindow A hAN] at hlocal
  have hsplit :
      (∑ d ∈ Finset.Icc 1 D,
        ∑ b ∈ Finset.range (N + (L - 1) * d),
          (rothNumberNat L + threeAPCount (affineWindow A L d b))) =
      (D * N + (L - 1) * D * (D + 1) / 2) * rothNumberNat L +
        ∑ d ∈ Finset.Icc 1 D,
          ∑ b ∈ Finset.range (N + (L - 1) * d),
            threeAPCount (affineWindow A L d b) := by
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
    rw [← sum_mul, sum_affineWindow_base_count]
  rw [hsplit] at hlocal
  exact hlocal.trans (Nat.add_le_add_left hmultiplicity _)


/-- Summing the single-window affine transport bound gives a baseline edge
incidence estimate by the total number `F` of windows. -/
theorem sum_threeAPCount_affineWindow_le (A : Finset ℕ) (N L D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
      ∑ b ∈ Finset.range (N + (L - 1) * d),
        threeAPCount (affineWindow A L d b)) ≤
      (D * N + (L - 1) * D * (D + 1) / 2) * threeAPCount A := by
  calc
    (∑ d ∈ Finset.Icc 1 D,
      ∑ b ∈ Finset.range (N + (L - 1) * d),
        threeAPCount (affineWindow A L d b)) ≤
        ∑ d ∈ Finset.Icc 1 D,
          ∑ _b ∈ Finset.range (N + (L - 1) * d), threeAPCount A := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro b hb
      exact threeAPCount_affineWindow_le A L d b (mem_Icc.mp hd).1
    _ = (D * N + (L - 1) * D * (D + 1) / 2) * threeAPCount A := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
      rw [← sum_mul, sum_affineWindow_base_count]

/-- Unconditional baseline quantitative bound obtained by charging every
global edge once for every affine window.  The sharper target replaces the
second occurrence of `F` by the ordered-gap multiplicity `M`. -/
theorem affineWindow_incidence_bound (A : Finset ℕ) {N L D : ℕ}
    (hAN : A ⊆ Finset.range N) :
    L * D * A.card ≤
      (D * N + (L - 1) * D * (D + 1) / 2) * rothNumberNat L +
        (D * N + (L - 1) * D * (D + 1) / 2) * threeAPCount A := by
  apply affineWindow_incidence_bound_of_threeAP_multiplicity A hAN
  exact sum_threeAPCount_affineWindow_le A N L D

/-- Joint satisfiability of the boundary, positivity, and nontrivial-length
hypotheses used by bounded affine-window applications. -/
example :
    let A : Finset ℕ := {0, 1, 2}
    let N := 3
    let L := 3
    let D := 1
    A ⊆ Finset.range N ∧ L ≤ N ∧ 3 ≤ L ∧ 1 ≤ D ∧
      (∑ b ∈ Finset.range (N + (L - 1)),
        (affineWindow A L 1 b).card) = L * A.card := by
  dsimp only
  have hAN : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range 3 := by decide
  exact ⟨hAN, by omega, by omega, by omega,
    sum_card_affineWindow_fixed_difference _ hAN⟩

/-- The sharp multiplicity parameter is attainable in the smallest
nontrivial model: for `L=N=3` and `D=1`, the unique global edge has total
local multiplicity one. -/
example :
    3 * 1 * ({0, 1, 2} : Finset ℕ).card ≤
      (1 * 3 + (3 - 1) * 1 * (1 + 1) / 2) * rothNumberNat 3 +
        1 * threeAPCount {0, 1, 2} := by
  apply affineWindow_incidence_bound_of_threeAP_multiplicity
    ({0, 1, 2} : Finset ℕ) (N := 3) (L := 3) (D := 1) (M := 1)
  · decide
  · decide

#check @affineWindow
#check @affineWindowValue
#check @mem_affineWindow_iff
#check @affineWindowValue_injOn
#check @exists_ordered_threeAP_of_mem_threeAPEdges
#check @ordered_threeAP_finset_injective
#check @affineWindow_ordered_threeAP_transport
#check @image_mem_threeAPEdges_of_mem_affineWindow
#check @threeAPCount_affineWindow_le
#check @card_affineWindow_le_rothNumberNat_add_threeAPCount
#check @card_filter_base_affineWindow
#check @sum_card_affineWindow_fixed_difference
#check @sum_Icc_one_id
#check @sum_affineWindow_base_count
#check @sum_card_affineWindow
#check @affineWindow_incidence_bound_of_threeAP_multiplicity
#check @sum_threeAPCount_affineWindow_le
#check @affineWindow_incidence_bound

#print axioms exists_ordered_threeAP_of_mem_threeAPEdges
#print axioms affineWindow_ordered_threeAP_transport
#print axioms image_mem_threeAPEdges_of_mem_affineWindow
#print axioms threeAPCount_affineWindow_le
#print axioms card_filter_base_affineWindow
#print axioms sum_card_affineWindow_fixed_difference
#print axioms sum_affineWindow_base_count
#print axioms sum_card_affineWindow
#print axioms affineWindow_incidence_bound_of_threeAP_multiplicity
#print axioms sum_threeAPCount_affineWindow_le
#print axioms affineWindow_incidence_bound

end Erdos142
