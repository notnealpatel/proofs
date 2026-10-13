import GroupTPP.MonomialRealization

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

open GroupTPP.TPP Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}

/-- Injective index maps into a left-quotient TPP triple give a monomial
realization with quotient index maps and unit scalar coefficients. The
construction also permits zero matrix dimensions. -/
theorem p1_c8 [Fintype G] {S T U : Finset G} (hTPP : TripleProductProperty S T U)
    (s : Fin n → G) (t : Fin m → G) (u : Fin p → G)
    (hs : Function.Injective s) (ht : Function.Injective t)
    (hu : Function.Injective u)
    (hsS : ∀ i, s i ∈ S) (htT : ∀ j, t j ∈ T) (huU : ∀ k, u k ∈ U) :
    IsMonomialRealization (F := F)
      (fun i j => s i * (t j)⁻¹)
      (fun j k => t j * (u k)⁻¹)
      (fun k i => u k * (s i)⁻¹)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) where
  alpha_ne_zero _ _ := one_ne_zero
  beta_ne_zero _ _ := one_ne_zero
  gamma_ne_zero _ _ := one_ne_zero
  coeff_identity := by
    intro i i' j j' k k'
    by_cases hcol : (s i * (t j)⁻¹) * (t j' * (u k)⁻¹) *
        (u k' * (s i')⁻¹) = 1
    · have hquot : (s i')⁻¹ * s i * (t j)⁻¹ * t j' * (u k)⁻¹ * u k' = 1 := by
        have hconj := congrArg (fun x : G => (s i')⁻¹ * x * s i') hcol
        simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hconj
      have heq := hTPP (s i) (hsS i) (s i') (hsS i')
        (t j') (htT j') (t j) (htT j)
        (u k') (huU k') (u k) (huU k) hquot
      have hdiag : j = j' ∧ k = k' ∧ i = i' :=
        ⟨(ht heq.2.1).symm, (hu heq.2.2).symm, hs heq.1⟩
      simp [hdiag]
    · have hdiag : ¬(j = j' ∧ k = k' ∧ i = i') := by
        rintro ⟨hj, hk, hi⟩
        apply hcol
        rw [hj, hk, hi]
        group
      simp [hcol, hdiag]

-- A nonempty concrete model jointly witnesses all three identical maps and sets.
example : ∃ (S : Finset (Multiplicative (ZMod 2)))
    (s : Fin 1 → Multiplicative (ZMod 2)),
    TripleProductProperty S S S ∧ Function.Injective s ∧ ∀ i, s i ∈ S := by
  refine ⟨{1}, fun _ => 1, ?_, ?_, ?_⟩
  · simp [TripleProductProperty]
  · intro i j _
    exact Subsingleton.elim i j
  · intro i
    exact mem_singleton_self 1

end GroupTPP.MonomialRealization
