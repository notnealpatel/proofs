import Sorry.Flex86E1Finite

set_option autoImplicit false

namespace Flex86E1Finite

open PermutationBoundaryStandardization

/-- The left named block of a boundary with two words of length `s+1`. -/
def leftBlock (s : ℕ) : Fin (s + 1) ↪ Fin (2 * (s + 1)) where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin (2 * (s + 1)) => z.val) h

/-- The right named block, in increasing position order. -/
def rightBlock (s : ℕ) : Fin (s + 1) ↪ Fin (2 * (s + 1)) where
  toFun i := ⟨s + 1 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change s + 1 + i.val = s + 1 + j.val at hv
    omega

example (s : ℕ) (i : Fin (s + 1)) : (leftBlock s i).val = i.val := rfl
example (s : ℕ) (i : Fin (s + 1)) : (rightBlock s i).val = s + 1 + i.val := rfl
example : leftBlock 1 0 ≠ rightBlock 1 0 := by decide

/-- Restricting to the two named blocks preserves exactly the short overlap
comparison event; the suffix is not reversed. -/
theorem pairOverlap_standardize_blocks_iff {s k : ℕ} (hk : k ≤ s + 1)
    (hkL : k < 2 * (s + 1)) (σ : Equiv.Perm (Fin (2 * (s + 1)))) :
    PairOverlap hk (standardize (leftBlock s) σ) (standardize (rightBlock s) σ) ↔
      PermutationOverlapBound.Overlap hkL σ := by
  have hp (i : Fin k) : leftBlock s (prefixPos hk i) =
      (⟨i.val, by omega⟩ : Fin (2 * (s + 1))) := rfl
  have hs (i : Fin k) : rightBlock s (suffix hk i) =
      (⟨i.val + (2 * (s + 1) - k), by omega⟩ : Fin (2 * (s + 1))) := by
    apply Fin.ext
    change s + 1 + (suffix hk i).val = i.val + (2 * (s + 1) - k)
    rw [suffix_val]
    omega
  unfold PairOverlap PermutationOverlapBound.Overlap
  simp only [standardize_lt_iff, hp, hs]

/-- For cutoff `s+2`, global short avoidance is precisely compatibility of
its two standardized words. This is the event bridge needed before weighted
shuffle-fiber regrouping. -/
theorem shortAvoid_iff_compatible_blocks (s : ℕ)
    (σ : Equiv.Perm (Fin (2 * (s + 1)))) :
    ShortAvoid (s + 2) σ ↔
      Compatible (standardize (leftBlock s) σ) (standardize (rightBlock s) σ) := by
  constructor
  · intro h k h₂ hk ho
    exact h k h₂ hk (by omega)
      ((pairOverlap_standardize_blocks_iff (by omega) (by omega) σ).mp ho)
  · intro h k h₂ hk hkL ho
    exact h k h₂ hk
      ((pairOverlap_standardize_blocks_iff (by omega) hkL σ).mpr ho)

/-- At cutoff three, swapping the last two labels gives a genuinely
short-avoiding boundary of length four. -/
theorem shortAvoid_three_swap : ShortAvoid 3 (Equiv.swap (2 : Fin 4) 3) := by
  intro k h₂ hk hkL ho
  have he : k = 2 := by omega
  subst k
  have hc := ho (0 : Fin 2) (1 : Fin 2)
  norm_num [Equiv.swap_apply_def, Fin.ext_iff] at hc
  exact (by decide : ¬ ((3 : Fin 4) < 2)) hc

example : Nonempty (Fin (2 * (1 + 1))) ∧ 3 ≤ 1 + 2 :=
  ⟨inferInstance, by decide⟩

end Flex86E1Finite
