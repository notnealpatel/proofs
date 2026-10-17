import Combinatorics.NoncommutingFiber

set_option autoImplicit false

namespace NoncommutingProjectionHoles

/-- The two nonzero coordinates of `L0`, in their original order. -/
def p0 (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.2.1, -t.1)

/-- The two nonzero coordinates of `L1`, in their original order. -/
def p1 (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.2.2, -t.1)

/-- The two nonzero coordinates of `L2`, in their original order. -/
def p2 (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.2.2, -t.2.1)

/-- The first actual projection grid of a coordinate box. -/
def G0 (I1 I2 : Finset ℤ) : Finset (ℤ × ℤ) := I2 ×ˢ (I1.image Neg.neg)

/-- The second actual projection grid of a coordinate box. -/
def G1 (I1 I3 : Finset ℤ) : Finset (ℤ × ℤ) := I3 ×ˢ (I1.image Neg.neg)

/-- The third actual projection grid of a coordinate box. -/
def G2 (I2 I3 : Finset ℤ) : Finset (ℤ × ℤ) := I3 ×ˢ (I2.image Neg.neg)

/-- Pairs in the first grid not attained by the actual first projection of `A`. -/
def H0 (I1 I2 : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  G0 I1 I2 \ A.image p0

/-- Pairs in the second grid not attained by the actual second projection of `A`. -/
def H1 (I1 I3 : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  G1 I1 I3 \ A.image p1

/-- Pairs in the third grid not attained by the actual third projection of `A`. -/
def H2 (I2 I3 : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  G2 I2 I3 \ A.image p2

/-- The first projection is precisely the first two coordinates of `L0`. -/
@[simp] theorem p0_eq_L0 (t : ℤ × ℤ × ℤ) :
    p0 t = ((NoncommutingFiber.L0 t).1, (NoncommutingFiber.L0 t).2.1) := rfl

/-- The second projection is precisely coordinates one and three of `L1`. -/
@[simp] theorem p1_eq_L1 (t : ℤ × ℤ × ℤ) :
    p1 t = ((NoncommutingFiber.L1 t).1, (NoncommutingFiber.L1 t).2.2) := rfl

/-- The third projection is precisely the last two coordinates of `L2`. -/
@[simp] theorem p2_eq_L2 (t : ℤ × ℤ × ℤ) :
    p2 t = ((NoncommutingFiber.L2 t).2.1, (NoncommutingFiber.L2 t).2.2) := rfl

example : p0 (1,2,3) = (2,-1) := rfl
example : p1 (1,2,3) = (3,-1) := rfl
example : p2 (1,2,3) = (3,-2) := rfl
example : G0 {1} {2} = {(2,-1)} := by decide
example : G1 {1} {3} = {(3,-1)} := by decide
example : G2 {2} {3} = {(3,-2)} := by decide
example : H0 {1} {2} {(1,2,3)} = ∅ := by decide
example : H1 {1} {3} {(1,2,3)} = ∅ := by decide
example : H2 {2} {3} {(1,2,3)} = ∅ := by decide

/-- Each first-projection hole accounts for an entire absent `I3` fiber.
No side needs to be nonempty. -/
theorem card_mul_H0_le_missing (I1 I2 I3 : Finset ℤ)
    (A : Finset (ℤ × ℤ × ℤ)) (_hA : A ⊆ I1 ×ˢ (I2 ×ˢ I3)) :
    I3.card * (H0 I1 I2 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
  have hcount : ((H0 I1 I2 A) ×ˢ I3).card ≤
      ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
    apply Finset.card_le_card_of_injOn
      (fun u : (ℤ × ℤ) × ℤ => (-u.1.2, u.1.1, u.2))
    · rintro ⟨⟨y,b⟩,z⟩ hu
      obtain ⟨hh,hz⟩ := Finset.mem_product.mp hu
      obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hh
      obtain ⟨hy,hb⟩ := Finset.mem_product.mp hg
      obtain ⟨x,hx,hxb⟩ := Finset.mem_image.mp hb
      change -x = b at hxb
      subst b
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Finset.mem_product, neg_neg] using And.intro hx (And.intro hy hz)
      · intro ha
        apply hn
        simpa [p0] using Finset.mem_image_of_mem p0 ha
    · rintro ⟨⟨y,b⟩,z⟩ _ ⟨⟨y',b'⟩,z'⟩ _ he
      simpa only [Prod.mk.injEq, neg_inj, and_assoc, and_left_comm, and_comm] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- Each second-projection hole accounts for an entire absent `I2` fiber. -/
theorem card_mul_H1_le_missing (I1 I2 I3 : Finset ℤ)
    (A : Finset (ℤ × ℤ × ℤ)) (_hA : A ⊆ I1 ×ˢ (I2 ×ˢ I3)) :
    I2.card * (H1 I1 I3 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
  have hcount : ((H1 I1 I3 A) ×ˢ I2).card ≤
      ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
    apply Finset.card_le_card_of_injOn
      (fun u : (ℤ × ℤ) × ℤ => (-u.1.2, u.2, u.1.1))
    · rintro ⟨⟨z,b⟩,y⟩ hu
      obtain ⟨hh,hy⟩ := Finset.mem_product.mp hu
      obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hh
      obtain ⟨hz,hb⟩ := Finset.mem_product.mp hg
      obtain ⟨x,hx,hxb⟩ := Finset.mem_image.mp hb
      change -x = b at hxb
      subst b
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Finset.mem_product, neg_neg] using And.intro hx (And.intro hy hz)
      · intro ha
        apply hn
        simpa [p1] using Finset.mem_image_of_mem p1 ha
    · rintro ⟨⟨z,b⟩,y⟩ _ ⟨⟨z',b'⟩,y'⟩ _ he
      simpa only [Prod.mk.injEq, neg_inj, and_assoc, and_left_comm, and_comm] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- Each third-projection hole accounts for an entire absent `I1` fiber. -/
theorem card_mul_H2_le_missing (I1 I2 I3 : Finset ℤ)
    (A : Finset (ℤ × ℤ × ℤ)) (_hA : A ⊆ I1 ×ˢ (I2 ×ˢ I3)) :
    I1.card * (H2 I2 I3 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
  have hcount : ((H2 I2 I3 A) ×ˢ I1).card ≤
      ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card := by
    apply Finset.card_le_card_of_injOn
      (fun u : (ℤ × ℤ) × ℤ => (u.2, -u.1.2, u.1.1))
    · rintro ⟨⟨z,b⟩,x⟩ hu
      obtain ⟨hh,hx⟩ := Finset.mem_product.mp hu
      obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hh
      obtain ⟨hz,hb⟩ := Finset.mem_product.mp hg
      obtain ⟨y,hy,hyb⟩ := Finset.mem_image.mp hb
      change -y = b at hyb
      subst b
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Finset.mem_product, neg_neg] using And.intro hx (And.intro hy hz)
      · intro ha
        apply hn
        simpa [p2] using Finset.mem_image_of_mem p2 ha
    · rintro ⟨⟨z,b⟩,x⟩ _ ⟨⟨z',b'⟩,x'⟩ _ he
      simpa only [Prod.mk.injEq, neg_inj, and_assoc, and_left_comm, and_comm] using he
  simpa only [Finset.card_product, Nat.mul_comm] using hcount

/-- The three actual projection-hole bounds, bundled for downstream consumers. -/
theorem projection_hole_bounds (I1 I2 I3 : Finset ℤ)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ I1 ×ˢ (I2 ×ˢ I3)) :
    I3.card * (H0 I1 I2 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card ∧
    I2.card * (H1 I1 I3 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card ∧
    I1.card * (H2 I2 I3 A).card ≤ ((I1 ×ˢ (I2 ×ˢ I3)) \ A).card :=
  ⟨card_mul_H0_le_missing I1 I2 I3 A hA,
    card_mul_H1_le_missing I1 I2 I3 A hA,
    card_mul_H2_le_missing I1 I2 I3 A hA⟩

example : ({(1,2,3)} : Finset (ℤ × ℤ × ℤ)) ⊆ {1} ×ˢ ({2} ×ˢ {3}) := by decide

example : H0 {1} {2} ∅ = {(2,-1)} ∧
    H1 {1} {3} ∅ = {(3,-1)} ∧ H2 {2} {3} ∅ = {(3,-2)} := by decide

end NoncommutingProjectionHoles
