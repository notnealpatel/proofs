import Combinatorics.PermutationOppositeEdgeLimit

set_option autoImplicit false

open Filter Topology

namespace PermutationEndpointReflection

open PermutationOverlapBound PermutationEndpointCounting
  PermutationMixedEndpointBound PermutationOppositeEdgeLimit

attribute [local instance] Classical.propDecidable

/-- Complement the labels of a permutation, leaving all positions unchanged. -/
def complement {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.trans Fin.revPerm

example {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    complement π i = (π i).rev := rfl

/-- Label complementation is an involution, including in dimension zero. -/
theorem complement_involutive {n : ℕ} : Function.Involutive (@complement n) := by
  intro π
  apply Equiv.ext
  intro i
  exact Fin.rev_rev (π i)

/-- Complementation reverses both comparisons in each overlap equivalence. -/
theorem overlap_complement_iff {n k : ℕ} (hkn : k < n)
    (π : Equiv.Perm (Fin n)) : Overlap hkn (complement π) ↔ Overlap hkn π := by
  have forward (ρ : Equiv.Perm (Fin n)) (h : Overlap hkn ρ) :
      Overlap hkn (complement ρ) := by
    intro i j
    change (ρ _).rev < (ρ _).rev ↔ (ρ _).rev < (ρ _).rev
    simpa only [Fin.rev_lt_rev] using h j i
  constructor
  · intro h
    simpa only [complement_involutive π] using forward (complement π) h
  · exact forward π

/-- Complementation gives an actual equivalence of the two prescribed-label fibers. -/
def fixedTwoComplementEquiv {n : ℕ} (p q m l : Fin n) :
    FixedTwo p q m l ≃ FixedTwo p q m.rev l.rev where
  toFun π := ⟨complement π.val, by
    change (π.val p).rev = m.rev ∧ (π.val q).rev = l.rev
    exact ⟨congrArg Fin.rev π.property.1, congrArg Fin.rev π.property.2⟩⟩
  invFun π := ⟨complement π.val, by
    change (π.val p).rev = m ∧ (π.val q).rev = l
    simp only [π.property.1, π.property.2, Fin.rev_rev, and_self]⟩
  left_inv π := Subtype.ext (complement_involutive π.val)
  right_inv π := Subtype.ext (complement_involutive π.val)

example {n : ℕ} (p q m l : Fin n) (π : FixedTwo p q m l) :
    (fixedTwoComplementEquiv p q m l π).val = complement π.val := rfl

/-- Complementation preserves avoidance at every proper length, with endpoints complemented. -/
def avoidTwoComplementEquiv {n : ℕ} [NeZero n] (q m l : Fin n) :
    AvoidTwo q m l ≃ AvoidTwo q m.rev l.rev where
  toFun π := ⟨complement π.val, by
    refine ⟨?_, ?_⟩
    · change (π.val 0).rev = m.rev ∧ (π.val q).rev = l.rev
      exact ⟨congrArg Fin.rev π.property.1.1, congrArg Fin.rev π.property.1.2⟩
    · intro k hk hkn h
      exact π.property.2 k hk hkn ((overlap_complement_iff hkn π.val).mp h)⟩
  invFun π := ⟨complement π.val, by
    refine ⟨?_, ?_⟩
    · change (π.val 0).rev = m ∧ (π.val q).rev = l
      simp only [π.property.1.1, π.property.1.2, Fin.rev_rev, and_self]
    · intro k hk hkn h
      exact π.property.2 k hk hkn ((overlap_complement_iff hkn π.val).mp h)⟩
  left_inv π := Subtype.ext (complement_involutive π.val)
  right_inv π := Subtype.ext (complement_involutive π.val)

example {n : ℕ} [NeZero n] (q m l : Fin n) (π : AvoidTwo q m l) :
    (avoidTwoComplementEquiv q m l π).val = complement π.val := rfl

/-- The cardinality of a prescribed-label fiber is unchanged by label complementation. -/
theorem card_fixedTwo_complement {n : ℕ} (p q m l : Fin n) :
    Fintype.card (FixedTwo p q m l) = Fintype.card (FixedTwo p q m.rev l.rev) :=
  Fintype.card_congr (fixedTwoComplementEquiv p q m l)

/-- The number of actual avoiding permutations is unchanged by label complementation. -/
theorem card_avoidTwo_complement {n : ℕ} [NeZero n] (q m l : Fin n) :
    Fintype.card (AvoidTwo q m l) = Fintype.card (AvoidTwo q m.rev l.rev) :=
  Fintype.card_congr (avoidTwoComplementEquiv q m l)

/-- Complementation preserves the actual conditional fraction; distinct endpoints
ensure that both conditioning fibers have positive cardinality. -/
theorem actualAvoidFraction_complement (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) (hml : ∀ t, m t ≠ l t) :
    actualAvoidFraction N m l =
      actualAvoidFraction N (fun t => (m t).rev) (fun t => (l t).rev) := by
  funext t
  have hpos := fixedTwo_card_pos N m l hml t
  unfold actualAvoidFraction
  rw [card_avoidTwo_complement, card_fixedTwo_complement]

/-- The value of the reversed label is its natural upper codistance. -/
theorem val_rev_eq_codist {n : ℕ} (i : Fin n) : i.rev.val = n - 1 - i.val := by
  rw [Fin.val_rev]
  omega

/-- The upper codistance of the reversed label is the original value.
The existence of `i : Fin n` supplies the bound needed for natural subtraction. -/
theorem codist_rev_eq_val {n : ℕ} (i : Fin n) : n - 1 - i.rev.val = i.val := by
  rw [val_rev_eq_codist]
  have hi := i.isLt
  omega

/-- Upper-first and lower-last labels with sublinear endpoint distances force
vanishing avoidance, by complementing labels (not reversing positions). -/
theorem tendsto_actualAvoidFraction_zero_reverse (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (m l : (t : ℕ) → Fin (N t + 3))
    (hml : ∀ t, m t ≠ l t)
    (hm : Tendsto (fun t => ((N t + 2 - (m t).val : ℕ) : ℝ) /
      ((N t : ℝ) + 3)) atTop (𝓝 0))
    (hl : Tendsto (fun t => ((l t).val : ℝ) / ((N t : ℝ) + 3)) atTop (𝓝 0)) :
    Tendsto (actualAvoidFraction N m l) atTop (𝓝 0) := by
  rw [actualAvoidFraction_complement N m l hml]
  apply tendsto_actualAvoidFraction_zero N hN
    (fun t => (m t).rev) (fun t => (l t).rev)
  · intro t he
    apply hml t
    simpa only [Fin.rev_rev] using congrArg Fin.rev he
  · have hval (t : ℕ) : (m t).rev.val = N t + 2 - (m t).val := by
      have hn : N t + 3 - 1 = N t + 2 := by omega
      simpa only [hn] using val_rev_eq_codist (m t)
    simpa only [hval] using hm
  · have hcodist (t : ℕ) : N t + 2 - (l t).rev.val = (l t).val := by
      have hn : N t + 3 - 1 = N t + 2 := by omega
      simpa only [hn] using codist_rev_eq_val (l t)
    simpa only [hcodist] using hl

/-- Eventually bounded upper distance of the first label and lower distance of
the last label suffice for vanishing avoidance. -/
theorem tendsto_actualAvoidFraction_zero_reverse_of_bounded_distance (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (m l : (t : ℕ) → Fin (N t + 3))
    (hml : ∀ t, m t ≠ l t)
    (hbounded : ∃ A B : ℕ, ∀ᶠ t in atTop,
      N t + 2 - (m t).val ≤ A ∧ (l t).val ≤ B) :
    Tendsto (actualAvoidFraction N m l) atTop (𝓝 0) := by
  rw [actualAvoidFraction_complement N m l hml]
  apply tendsto_actualAvoidFraction_zero_of_bounded_distance N hN
    (fun t => (m t).rev) (fun t => (l t).rev)
  · intro t he
    exact hml t (Fin.rev_injective he)
  · obtain ⟨A, B, hAB⟩ := hbounded
    refine ⟨A, B, hAB.mono ?_⟩
    intro t ht
    have hn : N t + 3 - 1 = N t + 2 := by omega
    have hmval : (m t).rev.val = N t + 2 - (m t).val := by
      simpa only [hn] using val_rev_eq_codist (m t)
    have hlval : N t + 2 - (l t).rev.val = (l t).val := by
      simpa only [hn] using codist_rev_eq_val (l t)
    simpa only [hmval, hlval] using ht

example : Nonempty (AvoidTwo (0 : Fin 1) 0 0) := by
  refine ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩
  intro k hk hkn
  omega

example : Nonempty (FixedTwo (0 : Fin 2) 1 1 0) :=
  fixedTwo_nonempty 0 1 1 0 (by decide) (by decide)

example :
    Tendsto (fun t : ℕ => t) atTop atTop ∧
    (∀ t : ℕ, (⟨t + 2, by omega⟩ : Fin (t + 3)) ≠ 0) ∧
    Tendsto (fun t : ℕ => ((t + 2 - (t + 2) : ℕ) : ℝ) /
      ((t : ℝ) + 3)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℕ => ((0 : Fin (t + 3)).val : ℝ) /
      ((t : ℝ) + 3)) atTop (𝓝 0) := by
  refine ⟨tendsto_id, ?_, ?_, ?_⟩
  · intro t he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    change t + 2 = 0 at hv
    omega
  · simp
  · simp

example :
    Tendsto (actualAvoidFraction (fun t => t)
      (fun t => ⟨t + 2, by omega⟩) (fun _ => 0)) atTop (𝓝 0) := by
  apply tendsto_actualAvoidFraction_zero_reverse_of_bounded_distance _ tendsto_id
  · intro t he
    have hv := congrArg Fin.val he
    change t + 2 = 0 at hv
    omega
  · exact ⟨0, 0, Eventually.of_forall (fun t => by simp)⟩

end PermutationEndpointReflection
