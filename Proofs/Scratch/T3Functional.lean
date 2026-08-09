import Mathlib

/-! Scratch: prototypes for the T3 functional gap (item 2) and the
`X₀X₁ + X₂X₃` separation witness (item 3) of the shear-review remediation.
-/

namespace Scratch.T3Functional

open MvPolynomial

/-! ## Item 2 core: uniqueness of low-total-degree representatives -/

theorem eq_zero_of_eval_eq_zero_of_totalDegree_lt {K : Type*} [Field K] [Fintype K]
    {n : ℕ} {p : MvPolynomial (Fin n) K}
    (h : ∀ x : Fin n → K, eval x p = 0)
    (hdeg : p.totalDegree < Fintype.card K) : p = 0 := by
  classical
  by_contra hp
  have hSZ := schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hfull : {f ∈ Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset K) |
      eval f p = 0} = Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset K) :=
    Finset.filter_true_of_mem fun f _ => h f
  rw [hfull, Fintype.piFinset_univ] at hSZ
  rw [show ((Finset.univ : Finset (Fin n → K)).card : ℚ≥0)
      = ((Finset.univ : Finset K).card : ℚ≥0) ^ n from by
    rw [Finset.card_univ, Finset.card_univ, Fintype.card_pi]
    push_cast
    simp [Fintype.card_fin]] at hSZ
  rw [div_self (by positivity)] at hSZ
  rw [one_le_div (by positivity)] at hSZ
  have : Fintype.card K ≤ p.totalDegree := by
    rw [Finset.card_univ] at hSZ
    exact_mod_cast hSZ
  omega

theorem eq_of_eval_eq_of_totalDegree_lt {K : Type*} [Field K] [Fintype K]
    {n : ℕ} {p q : MvPolynomial (Fin n) K}
    (hp : p.totalDegree < Fintype.card K) (hq : q.totalDegree < Fintype.card K)
    (h : ∀ x, eval x p = eval x q) : p = q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_eq_zero_of_totalDegree_lt (fun x => ?_) ?_
  · rw [map_sub, h x, sub_self]
  · refine lt_of_le_of_lt ?_ (max_lt hp hq)
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans (by rw [totalDegree_neg])

/-! ## Item 3 core: canonical linear forms and the rank-2 witness -/

section Canonical

variable {k : Type*} [CommSemiring k] {n : ℕ}

/-- A monomial of degree `1` is `single i 1`. -/
lemma exists_single_of_degree_eq_one {m : Fin n →₀ ℕ} (hm : m.degree = 1) :
    ∃ i, m = Finsupp.single i 1 := by
  obtain ⟨i, hi⟩ : m.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    simp at hm
  have hile : m i ≤ 1 := hm ▸ Finsupp.le_degree i m
  have hige : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  refine ⟨i, Finsupp.ext fun j => ?_⟩
  rcases eq_or_ne j i with rfl | hj
  · simp only [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hj]
    by_contra hjne
    have hjmem : j ∈ m.support := Finsupp.mem_support_iff.mpr hjne
    have h2 : 2 ≤ m.degree := by
      calc 2 ≤ m i + m j := by omega
        _ = ∑ x ∈ ({i, j} : Finset (Fin n)), m x := (Finset.sum_pair (Ne.symm hj)).symm
        _ ≤ ∑ x ∈ m.support, m x := Finset.sum_le_sum_of_subset (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            exacts [hi, hjmem])
        _ = m.degree := rfl
    omega

/-- Canonical form of a linear form: a homogeneous polynomial of degree `1`
is the linear combination of the variables given by its coefficients. -/
lemma IsHomogeneous.eq_sum_C_mul_X {L : MvPolynomial (Fin n) k}
    (hL : L.IsHomogeneous 1) :
    L = ∑ i, C (L.coeff (Finsupp.single i 1)) * X i := by
  ext m
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases hm : m.degree = 1
  · obtain ⟨i, rfl⟩ := exists_single_of_degree_eq_one hm
    rw [Finset.sum_eq_single i
      (fun j _ hj => by
        rw [if_neg (fun hEq => hj (by
          have := Finsupp.single_left_injective (α := Fin n) one_ne_zero hEq
          exact this)), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, mul_one]
  · rw [hL.coeff_eq_zero hm]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg, mul_zero]
    intro hEq
    exact hm (by rw [← hEq, Finsupp.degree_single])

end Canonical

/-- Sum-eval collapse smoke test. -/
example {K : Type*} [Field K] (a : Fin 4 → K) :
    (∑ i, a i * (Pi.single 0 1 : Fin 4 → K) i) = a 0 := by
  simp [Pi.single_apply]

example {K : Type*} [Field K] (a : Fin 4 → K) :
    (∑ i, a i * (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) i) = a 0 + a 1 := by
  simp [Fin.sum_univ_four, Pi.single_apply]

/-- The scalar core: the bilinear form of `x₀x₁ + x₂x₃` cannot factor through
two linear functionals, over any field. -/
lemma no_rank_one_factorization {K : Type*} [Field K] (a b : Fin 4 → K)
    (heval : ∀ x : Fin 4 → K,
      x 0 * x 1 + x 2 * x 3 = (∑ i, a i * x i) * (∑ i, b i * x i)) : False := by
  have d0 : a 0 * b 0 = 0 := by
    have h := (heval (Pi.single 0 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d1 : a 1 * b 1 = 0 := by
    have h := (heval (Pi.single 1 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d2 : a 2 * b 2 = 0 := by
    have h := (heval (Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d3 : a 3 * b 3 = 0 := by
    have h := (heval (Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p01 : (a 0 + a 1) * (b 0 + b 1) = 1 := by
    have h := (heval (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p23 : (a 2 + a 3) * (b 2 + b 3) = 1 := by
    have h := (heval (Pi.single 2 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p02 : (a 0 + a 2) * (b 0 + b 2) = 0 := by
    have h := (heval (Pi.single 0 1 + Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p03 : (a 0 + a 3) * (b 0 + b 3) = 0 := by
    have h := (heval (Pi.single 0 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p12 : (a 1 + a 2) * (b 1 + b 2) = 0 := by
    have h := (heval (Pi.single 1 1 + Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p13 : (a 1 + a 3) * (b 1 + b 3) = 0 := by
    have h := (heval (Pi.single 1 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have h01 : a 0 * b 1 + a 1 * b 0 = 1 := by linear_combination p01 - d0 - d1
  have h23 : a 2 * b 3 + a 3 * b 2 = 1 := by linear_combination p23 - d2 - d3
  have h02 : a 0 * b 2 + a 2 * b 0 = 0 := by linear_combination p02 - d0 - d2
  have h03 : a 0 * b 3 + a 3 * b 0 = 0 := by linear_combination p03 - d0 - d3
  have h12 : a 1 * b 2 + a 2 * b 1 = 0 := by linear_combination p12 - d1 - d2
  have h13 : a 1 * b 3 + a 3 * b 1 = 0 := by linear_combination p13 - d1 - d3
  rcases eq_or_ne (a 0) 0 with ha0 | ha0
  · have ha1b0 : a 1 * b 0 = 1 := by linear_combination h01 - b 1 * ha0
    have ha1 : a 1 ≠ 0 := left_ne_zero_of_mul_eq_one ha1b0
    have hb1 : b 1 = 0 := (mul_eq_zero.mp d1).resolve_left ha1
    have hb2 : b 2 = 0 := by
      have h : a 1 * b 2 = 0 := by linear_combination h12 - a 2 * hb1
      exact (mul_eq_zero.mp h).resolve_left ha1
    have hb3 : b 3 = 0 := by
      have h : a 1 * b 3 = 0 := by linear_combination h13 - a 3 * hb1
      exact (mul_eq_zero.mp h).resolve_left ha1
    rw [hb2, hb3] at h23
    simp at h23
  · have hb0 : b 0 = 0 := (mul_eq_zero.mp d0).resolve_left ha0
    have ha0b1 : a 0 * b 1 = 1 := by linear_combination h01 - a 1 * hb0
    have hb1 : b 1 ≠ 0 := right_ne_zero_of_mul_eq_one ha0b1
    have hb2 : b 2 = 0 := by
      have h : a 0 * b 2 = 0 := by linear_combination h02 - a 2 * hb0
      exact (mul_eq_zero.mp h).resolve_left ha0
    have hb3 : b 3 = 0 := by
      have h : a 0 * b 3 = 0 := by linear_combination h03 - a 3 * hb0
      exact (mul_eq_zero.mp h).resolve_left ha0
    rw [hb2, hb3] at h23
    simp at h23

/-- Prototype witness: `X₀X₁ + X₂X₃` is not a single product of two linear
forms. -/
theorem no_single_product {K : Type*} [Field K] (L L' : MvPolynomial (Fin 4) K)
    (hL : L.IsHomogeneous 1) (hL' : L'.IsHomogeneous 1)
    (hQ : (X 0 * X 1 + X 2 * X 3 : MvPolynomial (Fin 4) K) = L * L') : False := by
  rw [IsHomogeneous.eq_sum_C_mul_X hL, IsHomogeneous.eq_sum_C_mul_X hL'] at hQ
  refine no_rank_one_factorization (fun i => L.coeff (Finsupp.single i 1))
    (fun i => L'.coeff (Finsupp.single i 1)) fun x => ?_
  have h := congrArg (eval x) hQ
  simpa using h

end Scratch.T3Functional
