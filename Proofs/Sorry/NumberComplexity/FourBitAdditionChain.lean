import Sorry.NumberComplexity.ThreeBitAdditionChain

/-!
# A four-bit family with optimal addition chains

Altman, arXiv:1409.1627v2, Theorem 7.2, family (4), lists this family
in a classification attributed to Knuth, without supplying a proof there.
Here we independently construct chains for this sufficient family only:
build `q = 1 + 2^u`, double it `v` times retaining `q`, add `q`,
and double `a` times. No classification of weight-four numbers is asserted.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- Extend a chain by `k` doublings of its head, retaining every old member
and increasing its number of steps by exactly `k`. -/
theorem exists_doubling_extension (x : ℕ) (s : List ℕ)
    (hc : IsAddChain (x :: s)) (k : ℕ) :
    ∃ t : List ℕ, IsAddChain ((2 ^ k * x) :: t) ∧
      t.length = s.length + k ∧
      ∀ y ∈ x :: s, y ∈ (2 ^ k * x) :: t := by
  induction k with
  | zero => exact ⟨s, by simpa using hc, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨t, ht, hlen, hmem⟩ := ih
    have heq : 2 ^ (k + 1) * x = 2 ^ k * x + 2 ^ k * x := by
      rw [pow_succ]
      ring
    refine ⟨(2 ^ k * x) :: t, ?_, ?_, ?_⟩
    · rw [heq]
      exact .add (List.mem_cons_self ..) (List.mem_cons_self ..) ht
    · simp only [List.length_cons, hlen]
      omega
    · intro y hy
      exact List.mem_cons_of_mem _ (hmem y hy)

/-- Four increasing positions in the parallelogram family have weight four.
The strict inequalities ensure `c < b + c - a`, so no binary carries occur. -/
theorem binaryWeight_four_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    binaryWeight (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a)) = 4 := by
  have hcd : c < b + c - a := by omega
  have hsorted : ([a, b, c, b + c - a] : List ℕ).SortedLT := by
    simp [List.sortedLT_iff_pairwise, hab, hbc, hcd,
      lt_trans hab hbc, lt_trans hbc hcd, lt_trans (lt_trans hab hbc) hcd]
  have hbits : (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a) : ℕ).bitIndices =
      [a, b, c, b + c - a] := by
    simpa [Nat.add_assoc] using Nat.bitIndices_sum_map_two_pow hsorted
  change (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a) : ℕ).bitIndices.length = 4
  rw [hbits]
  rfl

/-- The logarithm of the four-bit family is its largest exponent `b + c - a`. -/
theorem log_four_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    Nat.log 2 (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a)) = b + c - a := by
  have hcd : c < b + c - a := by omega
  have habpow : (2 : ℕ) ^ a < 2 ^ b :=
    (Nat.pow_lt_pow_iff_right (by decide)).mpr hab
  have hbcPow : (2 : ℕ) ^ (b + 1) ≤ 2 ^ c :=
    Nat.pow_le_pow_right (by decide) hbc
  have hcdPow : (2 : ℕ) ^ (c + 1) ≤ 2 ^ (b + c - a) :=
    Nat.pow_le_pow_right (by decide) hcd
  rw [pow_succ] at hbcPow hcdPow
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact Nat.le_add_left _ _
  · rw [pow_succ]
    omega

private theorem fourBit_upper (a u v : ℕ) :
    l (2 ^ a * (1 + 2 ^ u) * (1 + 2 ^ v)) ≤ a + u + v + 2 := by
  let q := 1 + 2 ^ u
  have hq : IsAddChain (q :: twoPowChain u) :=
    .add (isAddChain_twoPowChain u).one_mem (two_pow_mem_twoPowChain u)
      (isAddChain_twoPowChain u)
  obtain ⟨t, ht, hlen, hmem⟩ := exists_doubling_extension q (twoPowChain u) hq v
  have hqmem : q ∈ (2 ^ v * q) :: t := hmem q (List.mem_cons_self ..)
  have hsum : IsAddChain ((2 ^ v * q + q) :: (2 ^ v * q) :: t) :=
    .add (List.mem_cons_self ..) hqmem ht
  obtain ⟨r, hr, hrlen, _⟩ :=
    exists_doubling_extension (2 ^ v * q + q) ((2 ^ v * q) :: t) hsum a
  have hupper : l (2 ^ a * (2 ^ v * q + q)) ≤ a + u + v + 2 :=
    l_le_of_isAddChain _ hr rfl (by
      rw [chainSteps_cons, hrlen, List.length_cons, hlen, length_twoPowChain]
      omega)
  have heq : 2 ^ a * (2 ^ v * q + q) = 2 ^ a * (1 + 2 ^ u) * (1 + 2 ^ v) := by
    dsimp [q]
    ring
  simpa only [heq] using hupper

/-- For `a < b < c`, the four distinct powers with fourth position `b+c-a`
have optimal chain length `b+c-a+2`. This is one sufficient family only. -/
theorem l_four_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    l (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a)) = b + c - a + 2 := by
  let u := b - a
  let v := c - a
  have hb : b = a + u := by dsimp [u]; omega
  have hc : c = a + v := by dsimp [v]; omega
  have hd : b + c - a = a + u + v := by omega
  have heq : (2 : ℕ) ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a) =
      2 ^ a * (1 + 2 ^ u) * (1 + 2 ^ v) := by
    rw [hd, hb, hc, pow_add, pow_add, pow_add, pow_add]
    ring
  have hupper : l (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a)) ≤ b + c - a + 2 := by
    rw [heq, hd]
    exact fourBit_upper a u v
  have hlower := log_add_two_le_l_of_three_le_binaryWeight
    (show 0 < 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a) by positivity)
    (show 3 ≤ binaryWeight (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (b + c - a)) by
      rw [binaryWeight_four_two_pow a b c hab hbc]; decide)
  rw [log_four_two_pow a b c hab hbc] at hlower
  exact Nat.le_antisymm hupper hlower

/-! The parameter domain `ℕ` is nonempty. The triples `(0,1,2)` and
`(1,3,6)` jointly realize all strict inequalities, with positive endpoints
`15` and `330`. The first also checks the smallest member of the family. -/

example : (0 : ℕ) < 1 ∧ (1 : ℕ) < 2 ∧ binaryWeight 15 = 4 ∧
    Nat.log 2 15 = 3 ∧ l 15 = 5 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · exact binaryWeight_four_two_pow 0 1 2 (by decide) (by decide)
  · exact log_four_two_pow 0 1 2 (by decide) (by decide)
  · exact l_four_two_pow 0 1 2 (by decide) (by decide)

example : (1 : ℕ) < 3 ∧ (3 : ℕ) < 6 ∧ binaryWeight 330 = 4 ∧
    Nat.log 2 330 = 8 ∧ l 330 = 10 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · exact binaryWeight_four_two_pow 1 3 6 (by decide) (by decide)
  · exact log_four_two_pow 1 3 6 (by decide) (by decide)
  · exact l_four_two_pow 1 3 6 (by decide) (by decide)

example : ∃ t : List ℕ, IsAddChain ((2 ^ 0 * 1) :: t) ∧
    t.length = ([] : List ℕ).length + 0 ∧ ∀ y ∈ (1 :: [] : List ℕ), y ∈ (2 ^ 0 * 1) :: t :=
  exists_doubling_extension 1 [] .one 0

end NumberComplexity
