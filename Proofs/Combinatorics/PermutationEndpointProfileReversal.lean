import Combinatorics.PermutationSameEdgeLimit

set_option autoImplicit false

namespace PermutationEndpointProfile

open PermutationOverlapBound PermutationEndpointCounting

/-- Reverse positions without changing labels. -/
def reversePositions {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans π

example {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    reversePositions π i = π i.rev := rfl

/-- Position reversal applied twice is the identity. -/
theorem reversePositions_involutive {n : ℕ} :
    Function.Involutive (@reversePositions n) := by
  intro π
  apply Equiv.ext
  intro i
  exact congrArg π (Fin.rev_rev i)

private theorem rev_prefix {n k : ℕ} (hkn : k < n) (i : Fin k) :
    (⟨i.val, lt_trans i.isLt hkn⟩ : Fin n).rev =
      ⟨i.rev.val + (n - k), by have hi := i.rev.isLt; omega⟩ := by
  apply Fin.ext
  simp only [Fin.val_rev]
  have hi := i.isLt
  omega

private theorem rev_suffix {n k : ℕ} (hkn : k < n) (i : Fin k) :
    (⟨i.val + (n - k), by omega⟩ : Fin n).rev =
      ⟨i.rev.val, lt_trans i.rev.isLt hkn⟩ := by
  apply Fin.ext
  simp only [Fin.val_rev]
  have hi := i.isLt
  omega

/-- Position reversal preserves the actual overlap event, including zero length. -/
theorem overlap_reversePositions_iff {n k : ℕ} (hkn : k < n)
    (π : Equiv.Perm (Fin n)) :
    Overlap hkn (reversePositions π) ↔ Overlap hkn π := by
  have forward (ρ : Equiv.Perm (Fin n)) (h : Overlap hkn ρ) :
      Overlap hkn (reversePositions ρ) := by
    intro i j
    change ρ _ < ρ _ ↔ ρ _ < ρ _
    simp only [Fin.revPerm_apply]
    rw [rev_prefix hkn i, rev_prefix hkn j, rev_suffix hkn i, rev_suffix hkn j]
    exact (h i.rev j.rev).symm
  constructor
  · intro h
    simpa only [reversePositions_involutive π] using forward (reversePositions π) h
  · exact forward π

/-- Position reversal exchanges the two prescribed endpoint labels. -/
def fixedTwoReverseEquiv {n : ℕ} [NeZero n] (a b : Fin n) :
    FixedTwo (0 : Fin n) (0 : Fin n).rev a b ≃
      FixedTwo (0 : Fin n) (0 : Fin n).rev b a where
  toFun π := ⟨reversePositions π.val, by
    change π.val (0 : Fin n).rev = b ∧ π.val (0 : Fin n).rev.rev = a
    exact ⟨π.property.2, by simpa using π.property.1⟩⟩
  invFun π := ⟨reversePositions π.val, by
    change π.val (0 : Fin n).rev = a ∧ π.val (0 : Fin n).rev.rev = b
    exact ⟨π.property.2, by simpa using π.property.1⟩⟩
  left_inv π := Subtype.ext (reversePositions_involutive π.val)
  right_inv π := Subtype.ext (reversePositions_involutive π.val)

example : Nonempty (FixedTwo (0 : Fin 2) 1 0 1) :=
  fixedTwo_nonempty 0 1 0 1 (by decide) (by decide)

end PermutationEndpointProfile
