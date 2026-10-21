import Combinatorics.Flex86E1Finite
import Combinatorics.Flex86E1BlockRestriction
import Combinatorics.PermutationTwoBlockCounting

set_option autoImplicit false

namespace Flex86E1Finite

open PermutationBoundaryStandardization PermutationTwoAnchorKernel

/-- Binomial theorem divided by factorials. -/
private theorem sum_pow_div_factorial (u v : ℝ) (n : ℕ) :
    ∑ a ∈ Finset.range (n + 1), u ^ a * v ^ (n - a) /
      ((a.factorial : ℝ) * (n - a).factorial) = (u + v) ^ n / n.factorial := by
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.cast_choose ℝ hle]
  have h1 : (a.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n - a).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The three-binomial shuffle term splits into three factorial-normalized factors. -/
private theorem shuffle_term (x y : ℝ) (r a b c d e : ℕ) :
    ((Nat.choose (r + a) r : ℝ) * (Nat.choose (b + c) b : ℝ) * (Nat.choose (d + e) d : ℝ)) *
      (x ^ (r + a) * (y - x) ^ (b + c) * (1 - y) ^ (d + e) /
        (((r + a).factorial : ℝ) * (b + c).factorial * (d + e).factorial)) =
      (x ^ r * (1 - y) ^ e / ((r.factorial : ℝ) * e.factorial)) *
        (x ^ a * (y - x) ^ c / ((a.factorial : ℝ) * c.factorial)) *
        ((y - x) ^ b * (1 - y) ^ d / ((b.factorial : ℝ) * d.factorial)) := by
  have key (i j : ℕ) : ((i + j).factorial : ℝ) =
      (Nat.choose (i + j) i : ℝ) * i.factorial * j.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h.symm
  have hc (i j : ℕ) : (Nat.choose (i + j) i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
  rw [key r a, key b c, key d e]
  have := hc r a
  have := hc b c
  have := hc d e
  field_simp
  ring

/-- The pattern-polynomial monomial weight of a boundary of length `2(s+1)` whose
first label is `i` and last label is `j`. -/
private noncomputable def endpointWeight (s : ℕ) (x y : ℝ) (i j : ℕ) : ℝ :=
  x ^ i * (y - x) ^ (j - i - 1) * (1 - y) ^ (2 * (s + 1) - 1 - j) /
    ((i.factorial : ℝ) * (j - i - 1).factorial * (2 * (s + 1) - 1 - j).factorial)

example (x y : ℝ) : endpointWeight 0 x y 0 1 = 1 := by simp [endpointWeight]

/-- Summing the shuffle-fiber counts against the endpoint weights collapses to the
product of two Bernstein basis polynomials divided by `(s!)^2`. -/
private theorem fiber_weight_sum (s : ℕ) (x y : ℝ) (r t : ℕ) (hr : r ≤ s) (ht : t ≤ s) :
    ∑ a ∈ Finset.range (t + 1), ∑ b ∈ Finset.range (s - r + 1),
      ((Nat.choose (r + a) r * Nat.choose (b + t - a) b *
        Nat.choose (2 * (s + 1) - 1 - (r + b + t + 1)) (s - r - b) : ℕ) : ℝ) *
        endpointWeight s x y (r + a) (r + b + t + 1) =
      ((s.choose r : ℝ) * x ^ r * (1 - x) ^ (s - r)) *
        ((s.choose t : ℝ) * y ^ t * (1 - y) ^ (s - t)) / (s.factorial : ℝ) ^ 2 := by
  let P : ℝ := x ^ r * (1 - y) ^ (s - t) / ((r.factorial : ℝ) * (s - t).factorial)
  have hterm : ∀ a ∈ Finset.range (t + 1), ∀ b ∈ Finset.range (s - r + 1),
      ((Nat.choose (r + a) r * Nat.choose (b + t - a) b *
        Nat.choose (2 * (s + 1) - 1 - (r + b + t + 1)) (s - r - b) : ℕ) : ℝ) *
        endpointWeight s x y (r + a) (r + b + t + 1) =
      P * (x ^ a * (y - x) ^ (t - a) / ((a.factorial : ℝ) * (t - a).factorial)) *
        ((y - x) ^ b * (1 - y) ^ (s - r - b) / ((b.factorial : ℝ) * (s - r - b).factorial)) := by
    intro a ha b hb
    have ha' : a ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' : b ≤ s - r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : b + t - a = b + (t - a) := by omega
    have h2 : r + b + t + 1 - (r + a) - 1 = b + (t - a) := by omega
    have h3 : 2 * (s + 1) - 1 - (r + b + t + 1) = (s - r - b) + (s - t) := by omega
    unfold endpointWeight
    rw [h1, h2, h3]
    push_cast
    exact shuffle_term x y r a b (t - a) (s - r - b) (s - t)
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (hterm a ha))]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_pow_div_factorial, sum_pow_div_factorial]
  have hy : x + (y - x) = y := by ring
  have hx : y - x + (1 - y) = 1 - x := by ring
  rw [hy, hx]
  rw [Nat.cast_choose ℝ hr, Nat.cast_choose ℝ ht]
  have h1 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((s - r).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (t.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((s - t).factorial : ℝ) ≠ 0 := by positivity
  have h5 : (s.factorial : ℝ) ≠ 0 := by positivity
  simp only [P]
  field_simp


/-- Below any label, the selected and unselected labels together number the label. -/
private theorem filter_compl_count' {n : ℕ} (A : Finset (Fin n)) (q : Fin n) :
    (A.filter (fun x => x < q)).card + (Aᶜ.filter (fun x => x < q)).card = q.val := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Iio q) (fun x => x ∈ A)
  have h₁ : (Finset.Iio q).filter (fun x => x ∈ A) = A.filter (fun x => x < q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact and_comm
  have h₂ : (Finset.Iio q).filter (fun x => ¬x ∈ A) = Aᶜ.filter (fun x => x < q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_compl]
    exact and_comm
  simpa only [h₁, h₂, Fin.card_Iio] using h

/-- If the left word's first label lies below the right word's last label, both
endpoint labels decompose with offsets in the ranges indexed by `card_fiber`. -/
private theorem endpoint_offsets (s : ℕ) (σ : Equiv.Perm (Fin (2 * (s + 1))))
    (h : σ (PermutationTwoBlockCounting.leftBlock s 0) <
      σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))) :
    ∃ a b, a ≤ (standardize (PermutationTwoBlockCounting.rightBlock s) σ (Fin.last s)).val ∧
      b ≤ s - (standardize (PermutationTwoBlockCounting.leftBlock s) σ 0).val ∧
      (σ (PermutationTwoBlockCounting.leftBlock s 0)).val =
        (standardize (PermutationTwoBlockCounting.leftBlock s) σ 0).val + a ∧
      (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val =
        (standardize (PermutationTwoBlockCounting.leftBlock s) σ 0).val + b +
          (standardize (PermutationTwoBlockCounting.rightBlock s) σ (Fin.last s)).val + 1 := by
  classical
  set α := standardize (PermutationTwoBlockCounting.leftBlock s) σ with hα
  set β := standardize (PermutationTwoBlockCounting.rightBlock s) σ with hβ
  set p := σ (PermutationTwoBlockCounting.leftBlock s 0) with hp
  set q := σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s)) with hq
  let A := PermutationTwoBlockCounting.fiberSubsetEquiv α β p q ⟨σ, rfl, rfl, rfl, rfl⟩
  have hpA := (orderEmb_eq_iff_filter_card _ _ _ _).mp A.property.1
  have hqA := (orderEmb_eq_iff_filter_card _ _ _ _).mp A.property.2
  have hcp := filter_compl_count' A.val.val p
  have hcq := filter_compl_count' A.val.val q
  have hsub₁ : A.val.valᶜ.filter (fun x => x < p) ⊆ A.val.valᶜ.filter (fun x => x < q) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩
  have hsub₂ : insert p (A.val.val.filter (fun x => x < p)) ⊆
      A.val.val.filter (fun x => x < q) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter] at hx ⊢
    rcases hx with rfl | hx
    · exact ⟨hpA.1, h⟩
    · exact ⟨hx.1, hx.2.trans h⟩
  have hnot : p ∉ A.val.val.filter (fun x => x < p) := by simp
  have hc₁ := Finset.card_le_card hsub₁
  have hc₂ := Finset.card_le_card hsub₂
  rw [Finset.card_insert_of_notMem hnot] at hc₂
  have hc₃ : (A.val.val.filter (fun x => x < q)).card ≤ s + 1 :=
    (Finset.card_filter_le _ _).trans_eq A.val.property
  refine ⟨(A.val.valᶜ.filter (fun x => x < p)).card,
    (A.val.val.filter (fun x => x < q)).card - (α 0).val - 1, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The weighted sum over one standardized two-block fiber with increasing endpoints
regroups by the two endpoint offsets into the shuffle-fiber counts. -/
private theorem fiber_endpoint_sum (s : ℕ) (x y : ℝ) (α β : Equiv.Perm (Fin (s + 1))) :
    ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 * (s + 1))))).filter (fun σ =>
        standardize (PermutationTwoBlockCounting.leftBlock s) σ = α ∧
        standardize (PermutationTwoBlockCounting.rightBlock s) σ = β ∧
        σ (PermutationTwoBlockCounting.leftBlock s 0) <
          σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))),
      endpointWeight s x y (σ (PermutationTwoBlockCounting.leftBlock s 0)).val
        (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val =
    ∑ a ∈ Finset.range ((β (Fin.last s)).val + 1),
      ∑ b ∈ Finset.range (s - (α 0).val + 1),
        ((Nat.choose ((α 0).val + a) (α 0).val *
          Nat.choose (b + (β (Fin.last s)).val - a) b *
          Nat.choose (2 * (s + 1) - 1 - ((α 0).val + b + (β (Fin.last s)).val + 1))
            (s - (α 0).val - b) : ℕ) : ℝ) *
          endpointWeight s x y ((α 0).val + a)
            ((α 0).val + b + (β (Fin.last s)).val + 1) := by
  classical
  set r := (α 0).val with hr
  set t := (β (Fin.last s)).val with ht
  set S := (Finset.univ : Finset (Equiv.Perm (Fin (2 * (s + 1))))).filter (fun σ =>
        standardize (PermutationTwoBlockCounting.leftBlock s) σ = α ∧
        standardize (PermutationTwoBlockCounting.rightBlock s) σ = β ∧
        σ (PermutationTwoBlockCounting.leftBlock s 0) <
          σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))) with hS
  let g : Equiv.Perm (Fin (2 * (s + 1))) → ℕ × ℕ := fun σ =>
    ((σ (PermutationTwoBlockCounting.leftBlock s 0)).val - r,
      (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val - r - t - 1)
  -- membership in `S` pins the offsets
  have hmem : ∀ σ, σ ∈ S ↔ standardize (PermutationTwoBlockCounting.leftBlock s) σ = α ∧
      standardize (PermutationTwoBlockCounting.rightBlock s) σ = β ∧
      σ (PermutationTwoBlockCounting.leftBlock s 0) <
        σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s)) := by
    intro σ
    simp [hS]
  have hoff : ∀ σ ∈ S, ∃ a b, a ≤ t ∧ b ≤ s - r ∧
      (σ (PermutationTwoBlockCounting.leftBlock s 0)).val = r + a ∧
      (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val = r + b + t + 1 := by
    intro σ hσ
    obtain ⟨hα, hβ, hlt⟩ := (hmem σ).mp hσ
    obtain ⟨a, b, ha, hb, hpa, hqb⟩ := endpoint_offsets s σ hlt
    simp only [hα, hβ] at ha hb hpa hqb
    exact ⟨a, b, ha, hb, hpa, hqb⟩
  have hmaps : ∀ σ ∈ S, g σ ∈ Finset.range (t + 1) ×ˢ Finset.range (s - r + 1) := by
    intro σ hσ
    obtain ⟨a, b, ha, hb, hpa, hqb⟩ := hoff σ hσ
    simp only [g, Finset.mem_product, Finset.mem_range, hpa, hqb]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' : a ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb' : b ≤ s - r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  -- the `(a,b)` fiber of `S` is the `card_fiber` subtype
  have hfib : ∀ σ, σ ∈ S.filter (fun σ => g σ = (a, b)) ↔
      (standardize (PermutationTwoBlockCounting.leftBlock s) σ = α ∧
        standardize (PermutationTwoBlockCounting.rightBlock s) σ = β ∧
        (σ (PermutationTwoBlockCounting.leftBlock s 0)).val = (α 0).val + a ∧
        (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val =
          (α 0).val + b + (β (Fin.last s)).val + 1) := by
    intro σ
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hσ, hg⟩
      obtain ⟨a', b', ha'', hb'', hpa, hqb⟩ := hoff σ hσ
      obtain ⟨hα, hβ, -⟩ := (hmem σ).mp hσ
      simp only [g, hpa, hqb, Prod.mk.injEq] at hg
      refine ⟨hα, hβ, ?_, ?_⟩ <;> omega
    · rintro ⟨hα, hβ, hpa, hqb⟩
      have hlt : σ (PermutationTwoBlockCounting.leftBlock s 0) <
          σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s)) := by
        rw [Fin.lt_def, hpa, hqb]
        omega
      refine ⟨(hmem σ).mpr ⟨hα, hβ, hlt⟩, ?_⟩
      simp only [g, hpa, hqb, Prod.mk.injEq]
      omega
  have hconst : ∀ σ ∈ S.filter (fun σ => g σ = (a, b)),
      endpointWeight s x y (σ (PermutationTwoBlockCounting.leftBlock s 0)).val
        (σ (PermutationTwoBlockCounting.rightBlock s (Fin.last s))).val =
      endpointWeight s x y (r + a) (r + b + t + 1) := by
    intro σ hσ
    obtain ⟨-, -, hpa, hqb⟩ := (hfib σ).mp hσ
    rw [hpa, hqb]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← PermutationTwoBlockCounting.card_fiber s α β a b ha' hb', Fintype.card_subtype]
  congr 2
  ext σ
  rw [hfib σ]
  simp

/-- The weight attached to one compatible pair: the product of the Bernstein basis
polynomials at its two endpoint ranks, normalized by the fiber size `(s!)^2`. -/
private noncomputable def pairWeight (s : ℕ) (x y : ℝ)
    (p : Equiv.Perm (Fin (s + 1)) × Equiv.Perm (Fin (s + 1))) : ℝ :=
  bernsteinBasis s (p.1 0) x * bernsteinBasis s (p.2 (Fin.last s)) y /
    (s.factorial : ℝ) ^ 2

example (x y : ℝ) : pairWeight 0 x y (Equiv.refl _, Equiv.refl _) = 1 := by
  simp [pairWeight, bernsteinBasis]

open Classical in
/-- The boundary pattern polynomial with increasing endpoints is the sum of the
pair weights over the compatible pairs of standardized blocks. -/
private theorem patternPolynomial_eq_sum_compatible (s : ℕ) (x y : ℝ) :
    PermutationEndpointProfile.patternPolynomial (s + 2) (2 * (s + 1))
        ⟨0, by omega⟩ ⟨2 * (s + 1) - 1, by omega⟩ x y =
      ∑ p : Equiv.Perm (Fin (s + 1)) × Equiv.Perm (Fin (s + 1)),
        if Compatible p.1 p.2 then pairWeight s x y p else 0 := by
  classical
  have hi : (⟨0, by omega⟩ : Fin (2 * (s + 1))) = PermutationTwoBlockCounting.leftBlock s 0 := by
    ext
    change 0 = ((0 : Fin (s + 1)) : ℕ)
    simp
  have hj : (⟨2 * (s + 1) - 1, by omega⟩ : Fin (2 * (s + 1))) =
      PermutationTwoBlockCounting.rightBlock s (Fin.last s) := by
    ext
    change 2 * (s + 1) - 1 = s + 1 + ((Fin.last s : Fin (s + 1)) : ℕ)
    rw [Fin.val_last]
    omega
  rw [hi, hj]
  set i := PermutationTwoBlockCounting.leftBlock s 0
  set j := PermutationTwoBlockCounting.rightBlock s (Fin.last s)
  have h1 : PermutationEndpointProfile.patternPolynomial (s + 2) (2 * (s + 1)) i j x y =
      ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 * (s + 1))))).filter
        (fun σ => ShortAvoid (s + 2) σ ∧ σ i < σ j),
        endpointWeight s x y (σ i).val (σ j).val := by
    unfold PermutationEndpointProfile.patternPolynomial
    exact (Finset.sum_subtype _ (by simp)
      (fun σ : Equiv.Perm (Fin (2 * (s + 1))) =>
        endpointWeight s x y (σ i).val (σ j).val)).symm
  rw [h1]
  let g : Equiv.Perm (Fin (2 * (s + 1))) →
      Equiv.Perm (Fin (s + 1)) × Equiv.Perm (Fin (s + 1)) := fun σ =>
    (standardize (PermutationTwoBlockCounting.leftBlock s) σ,
      standardize (PermutationTwoBlockCounting.rightBlock s) σ)
  rw [← Finset.sum_fiberwise _ g]
  apply Finset.sum_congr rfl
  rintro ⟨α, β⟩ -
  split_ifs with hc
  · have hset : ((Finset.univ : Finset (Equiv.Perm (Fin (2 * (s + 1))))).filter
          (fun σ => ShortAvoid (s + 2) σ ∧ σ i < σ j)).filter (fun σ => g σ = (α, β)) =
        (Finset.univ : Finset (Equiv.Perm (Fin (2 * (s + 1))))).filter (fun σ =>
          standardize (PermutationTwoBlockCounting.leftBlock s) σ = α ∧
          standardize (PermutationTwoBlockCounting.rightBlock s) σ = β ∧ σ i < σ j) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, hlt⟩, hα, hβ⟩
        exact ⟨hα, hβ, hlt⟩
      · rintro ⟨hα, hβ, hlt⟩
        refine ⟨⟨?_, hlt⟩, hα, hβ⟩
        apply (shortAvoid_iff_compatible_blocks s σ).mpr
        change Compatible (standardize (PermutationTwoBlockCounting.leftBlock s) σ)
          (standardize (PermutationTwoBlockCounting.rightBlock s) σ)
        rw [hα, hβ]
        exact hc
    rw [hset, fiber_endpoint_sum, fiber_weight_sum s x y _ _ (Nat.lt_succ_iff.mp (α 0).isLt)
      (Nat.lt_succ_iff.mp (β (Fin.last s)).isLt)]
    rfl
  · apply Finset.sum_eq_zero
    intro σ hσ
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Prod.mk.injEq] at hσ
    obtain ⟨⟨hsa, -⟩, hα, hβ⟩ := hσ
    apply hc
    have hcomp := (shortAvoid_iff_compatible_blocks s σ).mp hsa
    change Compatible (standardize (PermutationTwoBlockCounting.leftBlock s) σ)
      (standardize (PermutationTwoBlockCounting.rightBlock s) σ) at hcomp
    rwa [hα, hβ] at hcomp

open Classical in
/-- The tensor Bernstein polynomial at cutoff `s+2` is the sum of the pair weights
over all compatible pairs of words. -/
private theorem BernsteinQK_eq_sum_compatible (s : ℕ) (x y : ℝ) :
    BernsteinQK (s + 2) x y =
      ∑ p : Equiv.Perm (Fin (s + 1)) × Equiv.Perm (Fin (s + 1)),
        if Compatible p.1 p.2 then pairWeight s x y p else 0 := by
  classical
  let e : Equiv.Perm (Fin (s + 1)) × Equiv.Perm (Fin (s + 1)) → Fin (s + 1) × Fin (s + 1) :=
    fun p => (p.1 0, p.2 (Fin.last s))
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ e, Fintype.sum_prod_type]
  change ∑ r : Fin (s + 1), ∑ t : Fin (s + 1),
    coefficient s r t * bernsteinBasis s r x * bernsteinBasis s t y = _
  apply Finset.sum_congr rfl
  rintro r -
  apply Finset.sum_congr rfl
  rintro t -
  have hconst : ∀ p ∈ ((Finset.univ : Finset (Equiv.Perm (Fin (s + 1)) ×
        Equiv.Perm (Fin (s + 1)))).filter (fun p => Compatible p.1 p.2)).filter
        (fun p => e p = (r, t)),
      pairWeight s x y p = bernsteinBasis s r x * bernsteinBasis s t y /
        (s.factorial : ℝ) ^ 2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Prod.mk.injEq] at hp
    obtain ⟨-, h0, hl⟩ := hp
    simp only [pairWeight, h0, hl]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ : Finset (Equiv.Perm (Fin (s + 1)) ×
        Equiv.Perm (Fin (s + 1)))).filter (fun p => Compatible p.1 p.2)).filter
        (fun p => e p = (r, t))).card = Fintype.card (CompatiblePairs s r t) := by
    rw [Finset.filter_filter, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact
      { toFun := fun p => ⟨(⟨p.val.1, by
              have h := p.property.2
              simp only [e, Prod.mk.injEq] at h
              exact h.1⟩,
            ⟨p.val.2, by
              have h := p.property.2
              simp only [e, Prod.mk.injEq] at h
              rw [Fin.rev_zero]
              exact h.2⟩), p.property.1⟩
        invFun := fun q => ⟨(q.val.1.val, q.val.2.val), q.property, by
              simp only [e, Prod.mk.injEq]
              refine ⟨q.val.1.property, ?_⟩
              exact (congrArg q.val.2.val (Fin.rev_zero s).symm).trans q.val.2.property⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  rw [hcard, coefficient]
  ring

/-- Transport of the boundary pattern polynomial along an equality of boundary
lengths, with endpoint positions matched by value. -/
private theorem patternPolynomial_congr_length (K L L' : ℕ) (hL : L = L')
    (i j : Fin L) (i' j' : Fin L') (hi : i.val = i'.val) (hj : j.val = j'.val) (x y : ℝ) :
    PermutationEndpointProfile.patternPolynomial K L i j x y =
      PermutationEndpointProfile.patternPolynomial K L' i' j' x y := by
  subst hL
  rw [Fin.ext hi, Fin.ext hj]

/-- UNPROVED global regrouping target: for every cutoff `K≥3`, the actual
pair-count Bernstein polynomial equals the source profile approximation at
index `K-3`, on the whole real plane. This requires the unpaid interleaving /
block-cell regrouping identity, not merely the finite coefficient results. -/
theorem BernsteinQK_eq_profileApprox (K : ℕ) (hK : 3 ≤ K) (x y : ℝ) :
    BernsteinQK K x y = PermutationEndpointProfile.profileApprox (K - 3) (x, y) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hm : m + 3 - 3 = m := by omega
  rw [hm]
  unfold PermutationEndpointProfile.profileApprox
  rw [patternPolynomial_congr_length (m + 3) (2 * (m + 3) - 2) (2 * ((m + 1) + 1))
    (by omega) ⟨0, by omega⟩ ⟨2 * (m + 3) - 2 - 1, by omega⟩
    ⟨0, by omega⟩ ⟨2 * ((m + 1) + 1) - 1, by omega⟩ rfl (by simp only; omega)]
  have hsym : BernsteinQK (m + 3) x y = BernsteinQK (m + 3) (min x y) (max x y) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, BernsteinQK_symm]
  rw [hsym]
  exact (BernsteinQK_eq_sum_compatible (m + 1) _ _).trans
    (patternPolynomial_eq_sum_compatible (m + 1) _ _).symm

example : 3 ≤ 3 ∧ Nonempty ℝ := ⟨by decide, inferInstance⟩

end Flex86E1Finite
