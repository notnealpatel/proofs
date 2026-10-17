import Combinatorics.PermutationEndpointZeroTwoExact

set_option autoImplicit false

namespace PermutationOppositeTripleBounds

open PermutationOrderCounting PermutationOverlapBound PermutationEndpointCounting
open PermutationEndpointZeroTwoExact

attribute [local instance] Classical.propDecidable

/-- Under three prescribed labels, an overlap captured by two disjoint blocks
has at most reciprocal-factorial mass if the shuffled block avoids the anchors. -/
theorem card_overlap_mul_factorial_le {n k t : ℕ} (hkn : k < n)
    (p q r a b c : Fin n) (u v : Fin t ↪ Fin n)
    (hp : p ∉ Set.range u) (hq : q ∉ Set.range u) (hr : r ∉ Set.range u)
    (huv : Disjoint (Set.range u) (Set.range v))
    (hcapture : ∀ π : Equiv.Perm (Fin n), Overlap hkn π → SameOrder π u v) :
    Fintype.card {π : FixedThree p q r a b c // Overlap hkn π.val} * t.factorial ≤
      Fintype.card (FixedThree p q r a b c) := by
  let f : {π : FixedThree p q r a b c // Overlap hkn π.val} →
      AgreementThree p q r a b c u v := fun π =>
    ⟨π.val.val, π.val.property, hcapture π.val.val π.property⟩
  have hf : Function.Injective f := by
    intro π ρ he
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : AgreementThree p q r a b c u v => z.val) he))
  calc
    _ ≤ Fintype.card (AgreementThree p q r a b c u v) * t.factorial :=
      Nat.mul_le_mul_right _ (Fintype.card_le_of_injective f hf)
    _ = _ := card_agreementThree_mul_factorial p q r a b c u v hp hq hr huv

/-- For disjoint prefix and suffix, deleting their last coordinate leaves a
free suffix block of length `k-1`; this gives the conditional short-overlap bound. -/
theorem card_short_overlap_mul_factorial_le {n k : ℕ} (hk : 3 ≤ k)
    (hshort : 2 * k ≤ n) (a r b : Fin n) :
    Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b // Overlap (by omega : k < n) π.val} *
        (k - 1).factorial ≤
      Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r b) := by
  let u := segment (n := n) (n - k) (k - 1) (by omega)
  let v := segment (n := n) 0 (k - 1) (by omega)
  have hu0 : (⟨0, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = 0 at hv
    omega
  have hu1 : (⟨1, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = 1 at hv
    omega
  have hulast : (⟨n - 1, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = n - 1 at hv
    have hi' := i.isLt
    omega
  have huv : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, hi⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val (hi.trans hj.symm)
    change i.val + (n - k) = j.val + 0 at hv
    have hj' := j.isLt
    omega
  apply card_overlap_mul_factorial_le (by omega) _ _ _ a r b u v hu0 hu1 hulast huv
  intro π hov i j
  exact (hov ⟨i.val, by omega⟩ ⟨j.val, by omega⟩).symm

/-- Every long overlap of deficit `d` captures the first two disjoint blocks
of length `d`. The second block avoids the three anchors, even when `n=2d+1`. -/
theorem card_long_overlap_mul_factorial_le {n d : ℕ} (hd : 2 ≤ d)
    (hlong : 2 * d < n) (a r b : Fin n) :
    Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b // Overlap (by omega : n - d < n) π.val} *
        d.factorial ≤
      Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r b) := by
  let u := segment (n := n) d d (by omega)
  let v := segment (n := n) 0 d (by omega)
  have hu0 : (⟨0, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + d = 0 at hv
    omega
  have hu1 : (⟨1, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + d = 1 at hv
    omega
  have hulast : (⟨n - 1, by omega⟩ : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + d = n - 1 at hv
    have hi' := i.isLt
    omega
  have huv : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, hi⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val (hi.trans hj.symm)
    change i.val + d = j.val + 0 at hv
    have hj' := j.isLt
    omega
  apply card_overlap_mul_factorial_le (by omega) _ _ _ a r b u v hu0 hu1 hulast huv
  intro π hov i j
  have h := (hov ⟨i.val, by omega⟩ ⟨j.val, by omega⟩).symm
  have hshift : n - (n - d) = d := by omega
  change (π ⟨i.val + d, by omega⟩ < π ⟨j.val + d, by omega⟩) ↔
    (π ⟨i.val + 0, by omega⟩ < π ⟨j.val + 0, by omega⟩)
  simpa only [Nat.add_zero, hshift] using h

example : Nonempty (FixedThree (0 : Fin 6) 1 5 1 0 5) := by
  exact ⟨⟨Equiv.swap 0 1, by decide, by decide⟩⟩

example : 3 ≤ 3 ∧ 2 * 3 ≤ 6 := by decide
example : 2 ≤ 2 ∧ 2 * 2 < 5 := by decide

end PermutationOppositeTripleBounds
