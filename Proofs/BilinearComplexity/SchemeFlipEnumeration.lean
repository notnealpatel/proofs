import BilinearComplexity.SchemeFlipReduction

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace FlipReduction

variable {a b c : ℕ}

private instance schemeDecidableEqF2 : DecidableEq (Scheme (ZMod 2) a b c 2) :=
  Function.Injective.decidableEq (f := Scheme.term) (by
    intro S R h
    cases S
    cases R
    cases h
    rfl)

/-- Enumerate the distinct ordered ordinary F2 shear targets at the three repeated-factor
positions, retaining only changed presentations whose two evaluated terms are nonzero. -/
def ordinaryFlipTargetsF2 (S : Scheme (ZMod 2) a b c 2) :
    Finset (Scheme (ZMod 2) a b c 2) :=
  ((repeatedFactorIndexF2 S).toFinset.image (fun p => flipPair S p 1)).filter
    (fun R => (∀ s, (R.term s).eval ≠ 0) ∧ S ≠ R)

/-- For a source with two nonzero evaluated terms, the executable target enumeration is
sound and complete for the existing ordered nontrivial ordinary two-term flip wrapper. -/
theorem mem_ordinaryFlipTargetsF2_iff (S : Scheme (ZMod 2) a b c 2)
    (hsource : ∀ s, (S.term s).eval ≠ 0) (R : Scheme (ZMod 2) a b c 2) :
    R ∈ ordinaryFlipTargetsF2 S ↔ Nonempty (NontrivialOrdinaryTwoTermFlip S R) := by
  constructor
  · intro hmem
    obtain ⟨himage, htarget, hne⟩ := Finset.mem_filter.mp hmem
    obtain ⟨p, hp, hflip⟩ := Finset.mem_image.mp himage
    have hrep : RepeatedNonzeroFactor S p :=
      (mem_repeatedFactorIndexF2_iff S p).mp (List.mem_toFinset.mp hp)
    refine ⟨{
      position := p
      coefficient := 1
      coefficient_ne_zero := one_ne_zero
      target_eq := hflip.symm
      tensor_eq := ?_
      source_term_ne_zero := hsource
      target_term_ne_zero := htarget
      source_ne_target := hne }⟩
    rw [← hflip]
    exact sumTensor_flipPair S p 1 hrep
  · rintro ⟨h⟩
    have hq : h.coefficient = 1 :=
      zmod2_eq_one_of_ne_zero h.coefficient h.coefficient_ne_zero
    have hp : h.position ∈ (repeatedFactorIndexF2 S).toFinset :=
      List.mem_toFinset.mpr ((mem_repeatedFactorIndexF2_iff S h.position).mpr h.repeated)
    have hflip : flipPair S h.position 1 = R := by
      simpa only [hq] using h.target_eq.symm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨h.position, hp, hflip⟩,
        h.target_term_ne_zero, h.source_ne_target⟩

/-! Concrete checks use positive dimensions, including a nonempty target set and a
source whose candidate shears all produce a zero evaluated term. -/

example :
    let S : Scheme (ZMod 2) 1 2 2 2 :=
      pairScheme ((fun _ => 1), (fun j => if j = 0 then 1 else 0),
        (fun l => if l = 0 then 1 else 0))
        ((fun _ => 1), (fun j => if j = 1 then 1 else 0),
          (fun l => if l = 1 then 1 else 0))
    (∀ s, (S.term s).eval ≠ 0) ∧
      ordinaryFlipTargetsF2 S = {flipPair S .first 1} ∧
      Nonempty (NontrivialOrdinaryTwoTermFlip S (flipPair S .first 1)) := by
  dsimp only
  refine ⟨by decide, by decide, ?_⟩
  exact (mem_ordinaryFlipTargetsF2_iff _ (by decide) _).mp (by decide)

example :
    let S : Scheme (ZMod 2) 1 1 1 2 :=
      pairScheme ((fun _ => 1), (fun _ => 1), (fun _ => 1))
        ((fun _ => 1), (fun _ => 1), (fun _ => 1))
    (∀ s, (S.term s).eval ≠ 0) ∧
      ordinaryFlipTargetsF2 S = ∅ := by
  decide

end FlipReduction
end Scheme
end BilinearComplexity
