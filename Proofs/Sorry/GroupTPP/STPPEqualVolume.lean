import Sorry.Quarantine.GroupTPP.STPPWreath
import Sorry.GroupTPP.CharDegreesMul

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.STPPWreath

open GroupTPP.TPP GroupTPP.CUCapacity GroupTPP.CharDegrees GroupTPP.CharDegreesMul

/-- Equal-volume selected STPP words satisfy the amplified factorial inequality,
with the wreath lift and character-degree bound kept as explicit premises. -/
theorem stpp_equal_volume_factorial_chain
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {n : ℕ} (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C)
    (htpp : ∀ (ℓ : ℕ) (m : ℕ) (A' B' C' : Fin m → Finset (Fin ℓ → G)),
      SimultaneousTPP A' B' C' →
      ∃ S T U : Finset (ImprimitiveWreathProduct (Fin ℓ → G) m),
        TripleProductProperty S T U
        ∧ S.card = m.factorial * ∏ i, (A' i).card
        ∧ T.card = m.factorial * ∏ i, (B' i).card
        ∧ U.card = m.factorial * ∏ i, (C' i).card)
    (hbound : ∀ (ℓ m : ℕ),
      charDegreeSumReal (ImprimitiveWreathProduct (Fin ℓ → G) m) ω
        ≤ (Nat.factorial m : ℝ) ^ (ω - 1)
          * (charDegreeSumReal (Fin ℓ → G) ω) ^ m)
    (L m : ℕ) (hm : 1 ≤ m)
    (Φ : Fin m → Fin L → Fin n) (hΦ : Function.Injective Φ)
    (V : ℕ)
    (hV : ∀ p, ∏ j : Fin L,
      ((A (Φ p j)).card * (B (Φ p j)).card * (C (Φ p j)).card) = V)
    (t : ℕ) (ht : 1 ≤ t) :
    (Nat.factorial (m ^ t) : ℝ) *
        ((V : ℝ) ^ (ω / 3)) ^ (t * m ^ t)
      ≤ ((charDegreeSumReal G ω) ^ L) ^ (t * m ^ t) := by
  let e : Fin (m ^ t) ≃ (Fin t → Fin m) := finFunctionFinEquiv.symm
  let q : Fin t × Fin L ≃ Fin (t * L) := finProdFinEquiv
  let Ψ : Fin (m ^ t) → Fin (t * L) → Fin n :=
    fun p k => Φ (e p (q.symm k).1) (q.symm k).2
  have hΨ : Function.Injective Ψ := by
    intro p r hpr
    apply e.injective
    funext b
    apply hΦ
    funext j
    have hk := congr_fun hpr (q (b, j))
    simpa only [Ψ, Equiv.symm_apply_apply] using hk
  let A' : Fin (m ^ t) → Finset (Fin (t * L) → G) :=
    fun p => Fintype.piFinset fun k => A (Ψ p k)
  let B' : Fin (m ^ t) → Finset (Fin (t * L) → G) :=
    fun p => Fintype.piFinset fun k => B (Ψ p k)
  let C' : Fin (m ^ t) → Finset (Fin (t * L) → G) :=
    fun p => Fintype.piFinset fun k => C (Ψ p k)
  have hword (p : Fin (m ^ t)) :
      (A' p).card * (B' p).card * (C' p).card = V ^ t := by
    simp only [A', B', C', Fintype.card_piFinset, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_equiv q
      (fun bj => (A (Φ (e p bj.1) bj.2)).card *
        (B (Φ (e p bj.1) bj.2)).card * (C (Φ (e p bj.1) bj.2)).card)
      _ (fun bj => by simp only [Ψ, Equiv.symm_apply_apply])]
    rw [Fintype.prod_prod_type]
    simp only [hV, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨S, T, U, hSTU, hS, hT, hU⟩ :=
    htpp (t * L) (m ^ t) A' B' C' (h.pow Ψ hΨ)
  have hvol : S.card * T.card * U.card =
      (Nat.factorial (m ^ t)) ^ 3 * V ^ (t * m ^ t) := by
    rw [hS, hT, hU]
    calc
      _ = (Nat.factorial (m ^ t)) ^ 3 *
          (∏ p, (A' p).card * (B' p).card * (C' p).card) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring
      _ = _ := by simp only [hword, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul]
  have hw : (0 : ℝ) ≤ ω / 3 := by
    have htwo := two_le_matrixExponent
    linarith
  have hcap : ((S.card * T.card * U.card : ℕ) : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal (ImprimitiveWreathProduct (Fin (t * L) → G) (m ^ t)) ω :=
    (Real.rpow_le_rpow (by positivity) (Nat.cast_le.mpr (le_tppCapacity hSTU)) hw).trans
      (capacity_rpow_le_charDegreeSumReal _)
  have hf : (0 : ℝ) < (Nat.factorial (m ^ t) : ℝ) := by positivity
  have hleft : ((S.card * T.card * U.card : ℕ) : ℝ) ^ (ω / 3) =
      (Nat.factorial (m ^ t) : ℝ) ^ ω *
        ((V : ℝ) ^ (ω / 3)) ^ (t * m ^ t) := by
    rw [hvol, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Real.mul_rpow (by positivity) (by positivity)]
    have hcube : ((Nat.factorial (m ^ t) : ℝ) ^ 3) ^ (ω / 3) =
        (Nat.factorial (m ^ t) : ℝ) ^ ω := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (le_of_lt hf)]
      congr 1
      push_cast
      ring
    rw [hcube, ← Real.rpow_pow_comm (by positivity)]
  have hright : (charDegreeSumReal (Fin (t * L) → G) ω) ^ (m ^ t) =
      ((charDegreeSumReal G ω) ^ L) ^ (t * m ^ t) := by
    rw [charDegreeSumReal_pi_fin, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hchain := hcap.trans (hbound (t * L) (m ^ t))
  rw [hleft, hright] at hchain
  have hfactor : (Nat.factorial (m ^ t) : ℝ) ^ ω =
      (Nat.factorial (m ^ t) : ℝ) ^ (ω - 1) * (Nat.factorial (m ^ t) : ℝ) := by
    calc
      _ = (Nat.factorial (m ^ t) : ℝ) ^ ((ω - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hf, Real.rpow_one]
  rw [hfactor, mul_assoc] at hchain
  exact le_of_mul_le_mul_left hchain (Real.rpow_pos_of_pos hf (ω - 1))

-- A concrete nonempty selected family jointly instantiates all premises,
-- including the lift and bound, in a nontrivial group.
example : (1 : ℝ) ≤ charDegreeSumReal (Multiplicative (ZMod 2)) ω := by
  let A : Fin 1 → Finset (Multiplicative (ZMod 2)) := fun _ => {1}
  have h : SimultaneousTPP A A A := by
    constructor
    · intro i
      simp [A, TripleProductPropertyR]
    · intro i j k a ha a' ha' b hb b' hb' c hc c' hc' heq
      exact ⟨Subsingleton.elim i j, Subsingleton.elim j k⟩
  have hΦ : Function.Injective (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) := by
    intro p q hpq
    exact Subsingleton.elim p q
  have hV : ∀ p : Fin 1, ∏ j : Fin 1,
      (A (0 : Fin 1)).card * (A (0 : Fin 1)).card * (A (0 : Fin 1)).card = 1 := by
    intro p
    simp [A]
  have hchain := stpp_equal_volume_factorial_chain A A A h
    (fun ℓ M A' B' C' hs => stpp_to_tpp_wreath_card A' B' C' hs)
    (fun ℓ M => wreath_charDegree_bound (H := Fin ℓ → Multiplicative (ZMod 2)) M)
    1 1 (by decide) (fun _ _ => (0 : Fin 1)) hΦ 1 hV 1 (by decide)
  simpa using hchain

end GroupTPP.STPPWreath
