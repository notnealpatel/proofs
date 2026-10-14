import NumberComplexity.AdditionChain

/-!
# Eventual doubling stability of addition-chain length

This formalizes the ordinary-addition-chain case of part (1) of the theorem
labelled `cj1` in
Harry Altman, *Internal Structure of Addition Chains: Well-Ordering*,
arXiv:1409.1627. The proof uses a least attained natural-number slack and
provides no effective bound on the stabilization index.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- For a positive input, sufficiently many initial doublings make every
further doubling increase the shortest addition-chain length by exactly one. -/
theorem l_eventually_double_stable (n : ℕ) (hn : 0 < n) :
    ∃ K : ℕ, ∀ j : ℕ, l (2 ^ (K + j) * n) = l (2 ^ K * n) + j := by
  classical
  let a : ℕ → ℕ := fun k => l (2 ^ k * n)
  have hbound (k : ℕ) : k ≤ a k := by
    have hpos : 0 < 2 ^ k * n := Nat.mul_pos (Nat.two_pow_pos k) hn
    have hpow : 2 ^ k ≤ 2 ^ a k := calc
      2 ^ k ≤ 2 ^ k * n := Nat.le_mul_of_pos_right _ hn
      _ ≤ 2 ^ a k := le_two_pow_l (2 ^ k * n) hpos
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow
  have hstep (k : ℕ) : a (k + 1) ≤ a k + 1 := by
    dsimp only [a]
    have hnorm : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [hnorm]
    exact l_two_mul_le (2 ^ k * n)
  let s : ℕ → ℕ := fun k => a k - k
  have hanti : Antitone s := by
    apply antitone_nat_of_succ_le
    intro k
    have hb := hbound k
    have hb' := hbound (k + 1)
    have hs := hstep k
    dsimp only [s]
    omega
  have hex : ∃ t : ℕ, ∃ k : ℕ, s k = t := ⟨s 0, 0, rfl⟩
  obtain ⟨K, hK⟩ := Nat.find_spec hex
  refine ⟨K, ?_⟩
  intro j
  have hmin : s K ≤ s (K + j) := by
    rw [hK]
    exact Nat.find_min' hex ⟨K + j, rfl⟩
  have hmax : s (K + j) ≤ s K := hanti (Nat.le_add_right K j)
  have heq : s (K + j) = s K := Nat.le_antisymm hmax hmin
  have hb := hbound K
  have hb' := hbound (K + j)
  change a (K + j) = a K + j
  dsimp only [s] at heq
  omega

example : 0 < (1 : ℕ) ∧
    ∀ j : ℕ, l (2 ^ (0 + j) * 1) = l (2 ^ 0 * 1) + j := by
  constructor
  · decide
  · intro j
    simp [l_two_pow]

end NumberComplexity
