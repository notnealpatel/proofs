import Combinatorics.PermutationEndpointProfileBernstein
import Combinatorics.PermutationEndpointProfileLimit
import Analysis.FactorialPolynomialExtension

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology
open Filter Polynomial

namespace PermutationEndpointProfile

/-- The complex factorial-normalized Bernstein monomial of an anchor rank. -/
def complexAnchorBasis (k : ℕ) (r : Fin k) (t : ℂ) : ℂ :=
  t ^ r.val * (1 - t) ^ (k - 1 - r.val) /
    ((r.val.factorial : ℂ) * ((k - 1 - r.val).factorial : ℂ))

example : complexAnchorBasis 2 (0 : Fin 2) 0 = 1 := by
  norm_num [complexAnchorBasis]
example : complexAnchorBasis 2 (1 : Fin 2) 1 = 1 := by
  norm_num [complexAnchorBasis]

/-- The complex two-anchor Bernstein weight, zero for an empty pattern. -/
def complexBernsteinPatternWeight {k : ℕ} (σ : Equiv.Perm (Fin k))
    (z : ℂ × ℂ) : ℂ :=
  if hk : 0 < k then
    complexAnchorBasis k (σ ⟨0, hk⟩) z.1 *
      complexAnchorBasis k (σ ⟨k - 1, by omega⟩) z.2
  else 0

example : complexBernsteinPatternWeight (Equiv.refl (Fin 0)) (0, 1) = 0 := by
  simp [complexBernsteinPatternWeight]
example : complexBernsteinPatternWeight (Equiv.refl (Fin 2)) (0, 1) = 1 := by
  norm_num [complexBernsteinPatternWeight, complexAnchorBasis]

/-- Complexification of the actual finite avoiding-pattern Bernstein profile. -/
def complexBernsteinProfile (K : ℕ) (z : ℂ × ℂ) : ℂ :=
  1 - ∑ k ∈ Finset.Icc 2 (K + 2),
    ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, complexBernsteinPatternWeight σ z

/-- Complex Bernstein profiles restrict to the real Bernstein formulas. -/
theorem complexBernsteinProfile_ofReal (K : ℕ) (x y : ℝ) :
    complexBernsteinProfile K ((x : ℂ), (y : ℂ)) = (bernsteinProfile K x y : ℂ) := by
  classical
  have hw (k : ℕ) (σ : Equiv.Perm (Fin k)) :
      complexBernsteinPatternWeight σ ((x : ℂ), (y : ℂ)) =
        (bernsteinPatternWeight σ x y : ℂ) := by
    by_cases hk : 0 < k <;>
      simp [complexBernsteinPatternWeight, bernsteinPatternWeight, hk,
        complexAnchorBasis, anchorBasis]
  simp only [complexBernsteinProfile, bernsteinProfile, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_sum, hw]

/-- Every finite complex Bernstein profile is entire on the complex plane squared. -/
theorem differentiable_complexBernsteinProfile (K : ℕ) :
    Differentiable ℂ (complexBernsteinProfile K) := by
  classical
  unfold complexBernsteinProfile
  apply Differentiable.sub (differentiable_const _)
  apply Differentiable.fun_sum
  intro k hk
  apply Differentiable.fun_sum
  intro σ hσ
  unfold complexBernsteinPatternWeight
  split_ifs
  · unfold complexAnchorBasis
    fun_prop
  · exact differentiable_const 0

private theorem anchor_affine (k : ℕ) (r : Fin k) (A : ℂ[X])
    (hA : A.natDegree ≤ 1) :
    ∃ p : ℂ[X], p.natDegree ≤ k - 1 ∧
      ∀ t, p.eval t = complexAnchorBasis k r (A.eval t) := by
  let p : ℂ[X] := A ^ r.val * (1 - A) ^ (k - 1 - r.val) *
    C (((r.val.factorial : ℂ) * ((k - 1 - r.val).factorial : ℂ))⁻¹)
  have h1A : (1 - A).natDegree ≤ 1 :=
    (natDegree_sub_le 1 A).trans (max_le (by simp) hA)
  refine ⟨p, ?_, ?_⟩
  · dsimp only [p]
    calc
      _ ≤ (r.val * A.natDegree + (k - 1 - r.val) * (1 - A).natDegree) + 0 :=
        natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le natDegree_pow_le))
          (by rw [natDegree_C]))
      _ ≤ r.val + (k - 1 - r.val) := by
        simpa using Nat.add_le_add (Nat.mul_le_mul_left r.val hA)
          (Nat.mul_le_mul_left (k - 1 - r.val) h1A)
      _ = k - 1 := by have hr := r.isLt; omega
  · intro t
    simp [p, complexAnchorBasis, div_eq_mul_inv]

/-- Affine substitutions in both coordinates have degree at most `2*K+2`.
This loose total-degree bound also bounds each separate degree. -/
theorem complexBernsteinProfile_affine (K : ℕ) (A B : ℂ[X])
    (hA : A.natDegree ≤ 1) (hB : B.natDegree ≤ 1) :
    ∃ p : ℂ[X], p.natDegree ≤ 2 * K + 2 ∧
      ∀ t, p.eval t = complexBernsteinProfile K (A.eval t, B.eval t) := by
  classical
  have hterm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
      ∃ p : ℂ[X], p.natDegree ≤ 2 * (k - 1) ∧
        ∀ t, p.eval t = complexBernsteinPatternWeight σ (A.eval t, B.eval t) := by
    by_cases hk : 0 < k
    · obtain ⟨p, hp, hep⟩ := anchor_affine k (σ ⟨0, hk⟩) A hA
      obtain ⟨q, hq, heq⟩ := anchor_affine k (σ ⟨k - 1, by omega⟩) B hB
      refine ⟨p * q, natDegree_mul_le.trans ((Nat.add_le_add hp hq).trans (by omega)), ?_⟩
      intro t
      simp [complexBernsteinPatternWeight, hk, hep, heq]
    · exact ⟨0, by simp, by simp [complexBernsteinPatternWeight, hk]⟩
  choose term hdeg heval using hterm
  refine ⟨1 - ∑ k ∈ Finset.Icc 2 (K + 2),
    ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, term k σ, ?_, ?_⟩
  · apply (natDegree_sub_le _ _).trans
    apply max_le (by simp)
    apply natDegree_sum_le_of_forall_le
    intro k hk
    apply natDegree_sum_le_of_forall_le
    intro σ hσ
    exact (hdeg k σ).trans (by have hk' := (Finset.mem_Icc.mp hk).2; omega)
  · intro t
    simp only [eval_sub, eval_one]
    change 1 - (evalRingHom t) (∑ k ∈ Finset.Icc 2 (K + 2),
      ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, term k σ) = _
    simp [complexBernsteinProfile, heval]

/-- The actual endpoint-profile limit has an entire extension agreeing on the whole
closed square, retaining its uniform convergence and factorial one-sided tail bound. -/
theorem exists_entire_profile_limit :
    ∃ (P : ℝ × ℝ → ℝ) (Q : ℂ × ℂ → ℂ),
      ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      TendstoUniformlyOn profileApprox P atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
        0 ≤ profileApprox K z - P z ∧
          profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial) ∧
      Differentiable ℂ Q ∧
      ∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        Q ((x : ℂ), (y : ℂ)) = (P (x, y) : ℂ) := by
  obtain ⟨P, hPc, hPu, hconv, htail⟩ := exists_continuous_profile_limit
  let b : ℕ → ℂ × ℂ → ℂ := fun n => complexBernsteinProfile (3 * n)
  have hb (n : ℕ) : Differentiable ℂ (b n) := differentiable_complexBernsteinProfile _
  have hx (n : ℕ) (w : ℂ) : ∃ p : ℂ[X], p.natDegree ≤ 6 * n + 2 ∧
      ∀ z, p.eval z = b n (z, w) := by
    obtain ⟨p, hp, hep⟩ := complexBernsteinProfile_affine (3 * n) X (C w)
      (by simp) (by simp)
    refine ⟨p, hp.trans (by omega), ?_⟩
    simpa [b] using hep
  have hy (n : ℕ) (z : ℂ) : ∃ p : ℂ[X], p.natDegree ≤ 6 * n + 2 ∧
      ∀ w, p.eval w = b n (z, w) := by
    obtain ⟨p, hp, hep⟩ := complexBernsteinProfile_affine (3 * n) (C z) X
      (by simp) (by simp)
    refine ⟨p, hp.trans (by omega), ?_⟩
    simpa [b] using hep
  have herr (n : ℕ) (x y : ℝ) (hx0 : x ∈ Set.Icc 0 1)
      (hy0 : y ∈ Set.Icc 0 1) :
      ‖b n ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ)‖ ≤ 6 / (n.factorial : ℝ) := by
    have ht := htail (3 * n) (x, y) ⟨hx0, hy0⟩
    have he : b n ((x : ℂ), (y : ℂ)) = (profileApprox (3 * n) (x, y) : ℂ) := by
      change complexBernsteinProfile (3 * n) ((x : ℂ), (y : ℂ)) =
        (profileApprox (3 * n) (x, y) : ℂ)
      rw [complexBernsteinProfile_ofReal,
        profileApprox_eq_bernsteinProfile (3 * n) x y hx0 hy0]
    rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    apply ht.2.trans
    have hcut : (3 * n + 3) / 3 = n + 1 := by omega
    rw [hcut]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  obtain ⟨Q, hQ, _, hagree⟩ :=
    FactorialPolynomialExtension.exists_differentiable_extension_with_tendsto
      6 2 6 (by norm_num) b P hb hx hy herr
  exact ⟨P, Q, hPc, hPu, hconv, htail, hQ, hagree⟩

example : ∃ (P : ℝ × ℝ → ℝ) (Q : ℂ × ℂ → ℂ),
    TendstoUniformlyOn profileApprox P atTop
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
    Differentiable ℂ Q ∧
    Q (((3 / 4 : ℝ) : ℂ), ((1 / 4 : ℝ) : ℂ)) = (P (3 / 4, 1 / 4) : ℂ) := by
  obtain ⟨P, Q, _, _, hconv, _, hQ, hagree⟩ := exists_entire_profile_limit
  exact ⟨P, Q, hconv, hQ, hagree (3 / 4) (1 / 4) (by norm_num) (by norm_num)⟩

example : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (1 / 4 : ℝ) < 3 / 4 := by
  norm_num

end PermutationEndpointProfile
