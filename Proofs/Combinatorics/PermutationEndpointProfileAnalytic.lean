import Combinatorics.PermutationEndpointProfileLimit
import Analysis.FactorialPolynomialExtension

set_option autoImplicit false

open scoped BigOperators Topology
open Filter Polynomial

namespace PermutationEndpointProfile

attribute [local instance] Classical.propDecidable

/-- Complexification of the actual increasing-endpoint boundary-pattern sum. -/
noncomputable def complexPatternPolynomial (K L : ℕ) (i j : Fin L)
    (z : ℂ × ℂ) : ℂ :=
  ∑ σ : {σ : Equiv.Perm (Fin L) //
      PermutationBoundaryStandardization.ShortAvoid K σ ∧ σ i < σ j},
    z.1 ^ (σ.val i).val * (z.2-z.1) ^ ((σ.val j).val-(σ.val i).val-1) *
      (1-z.2) ^ (L-1-(σ.val j).val) /
      (((σ.val i).val.factorial : ℂ) *
        ((σ.val j).val-(σ.val i).val-1).factorial *
        (L-1-(σ.val j).val).factorial)

/-- On real inputs the complex sum is precisely the production pattern polynomial. -/
theorem complexPatternPolynomial_ofReal (K L : ℕ) (i j : Fin L) (x y : ℝ) :
    complexPatternPolynomial K L i j ((x : ℂ), (y : ℂ)) =
      (patternPolynomial K L i j x y : ℂ) := by
  classical
  simp [complexPatternPolynomial, patternPolynomial]

example (K L : ℕ) (i : Fin L) (z : ℂ × ℂ) :
    complexPatternPolynomial K L i i z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro σ hσ
  exact False.elim ((lt_irrefl (σ.val i)) σ.property.2)

/-- Every complex boundary-pattern sum is entire. -/
theorem differentiable_complexPatternPolynomial (K L : ℕ) (i j : Fin L) :
    Differentiable ℂ (complexPatternPolynomial K L i j) := by
  classical
  unfold complexPatternPolynomial
  fun_prop

/-- Substitution of two affine polynomials into the boundary sum has degree at most
`L-2`; the strict endpoint order pays for both removed anchor ranks. -/
theorem complexPatternPolynomial_affine (K L : ℕ) (i j : Fin L)
    (A B : ℂ[X]) (hA : A.natDegree ≤ 1) (hB : B.natDegree ≤ 1) :
    ∃ p : ℂ[X], p.natDegree ≤ L-2 ∧
      ∀ t, p.eval t = complexPatternPolynomial K L i j (A.eval t, B.eval t) := by
  classical
  let S := {σ : Equiv.Perm (Fin L) //
    PermutationBoundaryStandardization.ShortAvoid K σ ∧ σ i < σ j}
  let term : S → ℂ[X] := fun σ =>
    A ^ (σ.val i).val * (B-A) ^ ((σ.val j).val-(σ.val i).val-1) *
      (1-B) ^ (L-1-(σ.val j).val) *
      C ((((σ.val i).val.factorial : ℂ) *
        ((σ.val j).val-(σ.val i).val-1).factorial *
        (L-1-(σ.val j).val).factorial)⁻¹)
  refine ⟨∑ σ, term σ, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro σ hσ
    have hr : (σ.val i).val < (σ.val j).val := σ.property.2
    have hj : (σ.val j).val < L := (σ.val j).isLt
    have hBA : (B-A).natDegree ≤ 1 := (natDegree_sub_le B A).trans (max_le hB hA)
    have h1B : (1-B).natDegree ≤ 1 :=
      (natDegree_sub_le 1 B).trans (max_le (by simp) hB)
    dsimp only [term]
    calc
      _ ≤ ((σ.val i).val * A.natDegree +
          ((σ.val j).val-(σ.val i).val-1) * (B-A).natDegree) +
          (L-1-(σ.val j).val) * (1-B).natDegree + 0 := by
        apply natDegree_mul_le.trans
        apply Nat.add_le_add
        · apply natDegree_mul_le.trans
          exact Nat.add_le_add (natDegree_mul_le.trans
            (Nat.add_le_add natDegree_pow_le natDegree_pow_le)) natDegree_pow_le
        · simp only [natDegree_C, le_refl]
      _ ≤ (σ.val i).val + ((σ.val j).val-(σ.val i).val-1) +
          (L-1-(σ.val j).val) := by
        simpa only [mul_one, add_zero] using
          Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hBA))
            (Nat.mul_le_mul_left _ h1B)
      _ = L-2 := by omega
  · intro t
    change (evalRingHom t) (∑ σ, term σ) = _
    rw [map_sum]
    simp [term, complexPatternPolynomial, S, div_eq_mul_inv]

/-- The actual uniform endpoint-profile limit has an entire ordered branch agreeing
on the closed triangle, with all of its source bounds and convergence properties. -/
theorem exists_entire_ordered_profile_limit :
    ∃ (P : ℝ × ℝ → ℝ) (Q : ℂ × ℂ → ℂ),
      ContinuousOn P (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      TendstoUniformlyOn profileApprox P atTop
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∧
      (∀ K z, z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 →
        0 ≤ profileApprox K z-P z ∧
          profileApprox K z-P z ≤ 6/((K+3)/3).factorial) ∧
      Differentiable ℂ Q ∧
      ∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → x ≤ y →
        Q ((x : ℂ), (y : ℂ)) = (P (x,y) : ℂ) := by
  obtain ⟨P, hPc, hPu, hconv, htail⟩ := exists_continuous_profile_limit
  let F : ℕ → ℂ × ℂ → ℂ := fun K =>
    complexPatternPolynomial (K+3) (2*(K+3)-2)
      ⟨0, by omega⟩ ⟨2*(K+3)-2-1, by omega⟩
  have hreal (K : ℕ) (x y : ℝ) (hxy : x ≤ y) :
      F K ((x : ℂ), (y : ℂ)) = (profileApprox K (x,y) : ℂ) := by
    simp only [F, complexPatternPolynomial_ofReal, profileApprox,
      min_eq_left hxy, max_eq_right hxy]
  let b : ℕ → ℂ × ℂ → ℂ := fun n z => F (3*n) (z.1/3, (z.2+2)/3)
  let Prect : ℝ × ℝ → ℝ := fun z => P (z.1/3, (z.2+2)/3)
  have hb (n : ℕ) : Differentiable ℂ (b n) := by
    apply (differentiable_complexPatternPolynomial _ _ _ _).comp
    fun_prop
  have hlin (a d : ℂ) : (C a * X + C d).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have hx (n : ℕ) (w : ℂ) : ∃ p : ℂ[X], p.natDegree ≤ 6*n+2 ∧
      ∀ z, p.eval z = b n (z,w) := by
    obtain ⟨p, hp, hep⟩ := complexPatternPolynomial_affine (3*n+3)
      (2*(3*n+3)-2) ⟨0, by omega⟩ ⟨2*(3*n+3)-2-1, by omega⟩
      (C (1/3) * X + C 0) (C ((w+2)/3)) (hlin _ _) (by simp)
    refine ⟨p, hp.trans (by omega), ?_⟩
    intro z
    rw [hep]
    dsimp only [b, F]
    congr 1 <;> simp only [eval_add, eval_mul, eval_C, eval_X, add_zero] <;> congr 1 <;> ring
  have hy (n : ℕ) (z : ℂ) : ∃ p : ℂ[X], p.natDegree ≤ 6*n+2 ∧
      ∀ w, p.eval w = b n (z,w) := by
    obtain ⟨p, hp, hep⟩ := complexPatternPolynomial_affine (3*n+3)
      (2*(3*n+3)-2) ⟨0, by omega⟩ ⟨2*(3*n+3)-2-1, by omega⟩
      (C (z/3)) (C (1/3) * X + C (2/3)) (by simp) (hlin _ _)
    refine ⟨p, hp.trans (by omega), ?_⟩
    intro w
    rw [hep]
    dsimp only [b, F]
    congr 1 <;> simp only [eval_add, eval_mul, eval_C, eval_X, add_zero] <;> congr 1 <;> ring
  have herr (n : ℕ) (x y : ℝ) (hx0 : x ∈ Set.Icc 0 1)
      (hy0 : y ∈ Set.Icc 0 1) :
      ‖b n ((x : ℂ), (y : ℂ)) - (Prect (x,y) : ℂ)‖ ≤ 6/(n.factorial : ℝ) := by
    have hxR : x/3 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hx0.1, hx0.2]
    have hyR : (y+2)/3 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hy0.1, hy0.2]
    have hxy : x/3 ≤ (y+2)/3 := by linarith [hx0.2, hy0.1]
    have he := hreal (3*n) (x/3) ((y+2)/3) hxy
    have he' : b n ((x : ℂ), (y : ℂ)) =
        (profileApprox (3*n) (x/3,(y+2)/3) : ℂ) := by
      simpa only [b, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using he
    have ht := htail (3*n) (x/3,(y+2)/3) ⟨hxR,hyR⟩
    rw [he']
    change ‖(profileApprox (3*n) (x/3,(y+2)/3) : ℂ) -
      (P (x/3,(y+2)/3) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    apply ht.2.trans
    have hcut : (3*n+3)/3 = n+1 := by omega
    rw [hcut]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  obtain ⟨E, hE, hlim, _⟩ :=
    FactorialPolynomialExtension.exists_differentiable_extension_with_tendsto
      6 2 6 (by norm_num) b Prect hb hx hy herr
  let Q : ℂ × ℂ → ℂ := fun z => E (3*z.1, 3*z.2-2)
  refine ⟨P, Q, hPc, hPu, hconv, htail, ?_, ?_⟩
  · apply hE.comp
    fun_prop
  · intro x y hx0 hy0 hxy
    have hsub : Tendsto (fun n : ℕ => 3*n) atTop atTop := by
      apply tendsto_atTop.2
      intro k
      exact eventually_atTop.2 ⟨k, fun n hn => by omega⟩
    have hP := (hconv.tendsto_at (x := (x,y)) ⟨hx0,hy0⟩).comp hsub
    have hPcplx : Tendsto (fun n => (profileApprox (3*n) (x,y) : ℂ))
        atTop (𝓝 (P (x,y) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hP
    have hF : Tendsto (fun n => F (3*n) ((x : ℂ), (y : ℂ)))
        atTop (𝓝 (Q ((x : ℂ), (y : ℂ)))) := by
      have ht := hlim (3*(x : ℂ), 3*(y : ℂ)-2)
      convert ht using 1 <;> simp [b]
    have hFP : Tendsto (fun n => F (3*n) ((x : ℂ), (y : ℂ)))
        atTop (𝓝 (P (x,y) : ℂ)) := by
      simpa only [hreal _ x y hxy] using hPcplx
    exact tendsto_nhds_unique hF hFP

example : ∃ (P : ℝ × ℝ → ℝ) (Q : ℂ × ℂ → ℂ),
    Differentiable ℂ Q ∧ Q (0,0) = (P (0,0) : ℂ) ∧
      Q (0,1) = (P (0,1) : ℂ) ∧ Q (1,1) = (P (1,1) : ℂ) := by
  obtain ⟨P,Q,_,_,_,_,hQ,hagree⟩ := exists_entire_ordered_profile_limit
  refine ⟨P,Q,hQ,?_,?_,?_⟩
  · exact hagree 0 0 (by norm_num) (by norm_num) (by norm_num)
  · exact hagree 0 1 (by norm_num) (by norm_num) (by norm_num)
  · exact hagree 1 1 (by norm_num) (by norm_num) (by norm_num)

example (n : ℕ) : Nonempty (Fin (2*(3*n+3)-2)) := ⟨⟨0, by omega⟩⟩

end PermutationEndpointProfile
