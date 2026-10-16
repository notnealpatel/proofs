import NumberComplexity.TwoBitAdditionChain

/-!
# Addition chains with at most one small step

An ascending addition chain with at most `Nat.log 2 n + 1` additions ends at
an integer of binary weight at most two. The dyadic argument is expressed
through an equivalent index invariant: an endpoint at least half the full
doubling maximum forces the same bound on every prefix. Strong induction then
classifies each entry as a power or a sum of two powers.

The sequence helper only assumes nondecreasing entries. The consumer theorem
uses the existing strictly ascending addition-chain predicate and derives all
helper assumptions from its fields, including the earlier-summand equations.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- Iterating the doubling bound from an arbitrary entry bounds every later entry. -/
theorem asc_doubling_iterate (a : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ i, i < r → a (i + 1) ≤ 2 * a i)
    (i d : ℕ) (hid : i + d ≤ r) : a (i + d) ≤ 2 ^ d * a i := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprefix : i + d ≤ r := by omega
    have hnext := hstep (i + d) (by omega)
    have hbound := ih hprefix
    calc
      a (i + (d + 1)) ≤ 2 * a (i + d) := by simpa [Nat.add_assoc] using hnext
      _ ≤ 2 * (2 ^ d * a i) := Nat.mul_le_mul_left 2 hbound
      _ = 2 ^ (d + 1) * a i := by rw [pow_succ]; ring

/-- The initial value one and the doubling bound give the standard exponential bound. -/
theorem asc_doubling_upper (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 1)
    (hstep : ∀ i, i < r → a (i + 1) ≤ 2 * a i)
    (i : ℕ) (hi : i ≤ r) : a i ≤ 2 ^ i := by
  simpa [hzero] using asc_doubling_iterate a r hstep 0 i (by omega)

/-- If the endpoint is at least half the full doubling bound, every prefix is too.
The formulation uses multiplication rather than truncated exponents at index zero. -/
theorem asc_doubling_prefix_lower (a : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ i, i < r → a (i + 1) ≤ 2 * a i)
    (hend : 2 ^ r ≤ 2 * a r) (i : ℕ) (hi : i ≤ r) : 2 ^ i ≤ 2 * a i := by
  have hbound := asc_doubling_iterate a r hstep i (r - i) (by omega)
  have hexp : i + (r - i) = r := by omega
  rw [hexp] at hbound
  have hprod : 2 ^ (r - i) * 2 ^ i ≤ 2 ^ (r - i) * (2 * a i) := by
    calc
      2 ^ (r - i) * 2 ^ i = 2 ^ r := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 * a r := hend
      _ ≤ 2 * (2 ^ (r - i) * a i) := Nat.mul_le_mul_left 2 hbound
      _ = 2 ^ (r - i) * (2 * a i) := by ring
  exact Nat.le_of_mul_le_mul_left hprod (Nat.two_pow_pos _)

example : (fun i : ℕ => 2 ^ i) 0 = 1 ∧
    (∀ i : ℕ, i < 4 → (2 : ℕ) ^ (i + 1) ≤ 2 * 2 ^ i) ∧
    (2 : ℕ) ^ 4 ≤ 2 * 2 ^ 4 := by
  refine ⟨rfl, ?_, by decide⟩
  intro i _
  rw [pow_succ]
  omega

/-- Equality in the full doubling bound forces equality at every prefix. -/
theorem asc_doubling_rigidity (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 1)
    (hstep : ∀ i, i < r → a (i + 1) ≤ 2 * a i)
    (hend : a r = 2 ^ r) (i : ℕ) (hi : i ≤ r) : a i = 2 ^ i := by
  have hbound := asc_doubling_iterate a r hstep i (r - i) (by omega)
  have hexp : i + (r - i) = r := by omega
  rw [hexp, hend] at hbound
  have hprod : 2 ^ (r - i) * 2 ^ i ≤ 2 ^ (r - i) * a i := by
    calc
      2 ^ (r - i) * 2 ^ i = 2 ^ r := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (r - i) * a i := hbound
  exact Nat.le_antisymm (asc_doubling_upper a r hzero hstep i hi)
    (Nat.le_of_mul_le_mul_left hprod (Nat.two_pow_pos _))

/-- The proposed near-logarithmic length bound places the endpoint at least halfway
up the full doubling interval. Positivity guards the logarithm. -/
theorem two_pow_steps_le_two_mul {n r : ℕ} (hn : 0 < n)
    (hr : r ≤ Nat.log 2 n + 1) : 2 ^ r ≤ 2 * n := by
  calc
    2 ^ r ≤ 2 ^ (Nat.log 2 n + 1) := Nat.pow_le_pow_right (by decide) hr
    _ = 2 * 2 ^ Nat.log 2 n := by rw [pow_succ]; omega
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

example : (0 : ℕ) < 5 ∧ 3 ≤ Nat.log 2 5 + 1 := by decide

/-- A nondecreasing addition sequence reaching at least half its doubling maximum
has at most two binary positions at each positive index. -/
theorem asc_half_max_classification (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 1)
    (hmono : ∀ i j, i ≤ j → j ≤ r → a i ≤ a j)
    (hsum : ∀ i, 0 < i → i ≤ r →
      ∃ j < i, ∃ k < i, a i = a j + a k)
    (hend : 2 ^ r ≤ 2 * a r) :
    ∀ i, 0 < i → i ≤ r →
      a i = 2 ^ i ∨ a i = 2 ^ (i - 1) ∨
        ∃ v < i - 1, a i = 2 ^ (i - 1) + 2 ^ v := by
  have hstep : ∀ i, i < r → a (i + 1) ≤ 2 * a i := by
    intro i hi
    obtain ⟨j, hj, k, hk, heq⟩ := hsum (i + 1) (by omega) (by omega)
    have hjle := hmono j i (by omega) (by omega)
    have hkle := hmono k i (by omega) (by omega)
    omega
  have hup := asc_doubling_upper a r hzero hstep
  have hlo := asc_doubling_prefix_lower a r hstep hend
  have hrig : ∀ j, j ≤ r → a j = 2 ^ j → ∀ k, k ≤ j → a k = 2 ^ k := by
    intro j hj heq k hk
    exact asc_doubling_rigidity a j hzero
      (fun t ht => hstep t (by omega)) heq k hk
  have hone : 1 ≤ r → a 1 = 2 := by
    intro hr
    obtain ⟨j, hj, k, hk, heq⟩ := hsum 1 (by decide) hr
    have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    simpa [hj0, hk0, hzero] using heq
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hip hir
    by_cases hsmall : i < 4
    · interval_cases i
      · exact Or.inl (by simpa using hone hir)
      · have hu := hup 2 hir
        have hl := hlo 2 hir
        norm_num at hu hl ⊢
        rcases (show a 2 = 2 ∨ a 2 = 3 ∨ a 2 = 4 by omega) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      · have ha1 := hone (by omega)
        have hu := hup 2 (by omega)
        have hl := hlo 3 hir
        obtain ⟨j, hj, k, hk, heq⟩ := hsum 3 (by decide) hir
        have hvals : a 3 = 4 ∨ a 3 = 5 ∨ a 3 = 6 ∨ a 3 = 8 := by
          interval_cases j <;> interval_cases k <;>
            norm_num [hzero, ha1] at heq hu hl <;> omega
        rcases hvals with h | h | h | h
        · exact Or.inr (Or.inl (by simpa using h))
        · exact Or.inr (Or.inr ⟨0, by omega, by simpa using h⟩)
        · exact Or.inr (Or.inr ⟨1, by omega, by simpa using h⟩)
        · exact Or.inl (by simpa using h)
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 4 := ⟨i - 4, by omega⟩
      have hp := ih (m + 3) (by omega) (by omega) (by omega)
      have hq := ih (m + 2) (by omega) (by omega) (by omega)
      have hlow := hlo (m + 4) hir
      have hpstep := hstep (m + 2) (by omega)
      have hqbound := hup (m + 2) (by omega)
      have hpow1 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      have hpow2 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, hpow1]; ring
      have hpow3 : (2 : ℕ) ^ (m + 3) = 8 * 2 ^ m := by
        rw [show m + 3 = (m + 2) + 1 by omega, pow_succ, hpow2]; ring
      have hpow4 : (2 : ℕ) ^ (m + 4) = 16 * 2 ^ m := by
        rw [show m + 4 = (m + 3) + 1 by omega, pow_succ, hpow3]; ring
      have hpos := Nat.two_pow_pos m
      have hshape_power (heq : a (m + 4) = 2 ^ (m + 3)) :
          a (m + 4) = 2 ^ (m + 4) ∨ a (m + 4) = 2 ^ (m + 4 - 1) ∨
            ∃ v < m + 4 - 1, a (m + 4) = 2 ^ (m + 4 - 1) + 2 ^ v := by
        exact Or.inr (Or.inl (by simpa using heq))
      have hshape_sum (v : ℕ) (hv : v < m + 3)
          (heq : a (m + 4) = 2 ^ (m + 3) + 2 ^ v) :
          a (m + 4) = 2 ^ (m + 4) ∨ a (m + 4) = 2 ^ (m + 4 - 1) ∨
            ∃ v < m + 4 - 1, a (m + 4) = 2 ^ (m + 4 - 1) + 2 ^ v := by
        exact Or.inr (Or.inr ⟨v, by simpa using hv, by simpa using heq⟩)
      obtain ⟨j, hj, k, hk, heq⟩ := hsum (m + 4) (by omega) hir
      wlog hjk : k ≤ j generalizing j k
      · exact this k hk j hj (by omega) (by omega)
      by_cases hjprev : j = m + 3
      · subst j
        rcases hp with hpfull | hppure | ⟨v, hv, hpform⟩
        · have hkfull := hrig (m + 3) (by omega) hpfull k (by omega)
          by_cases hkprev : k = m + 3
          · left
            rw [heq, hpfull, hkfull, hkprev, hpow3, hpow4]
            omega
          · exact hshape_sum k (by omega) (by rw [heq, hpfull, hkfull])
        · have hkbound := hmono k (m + 3) (by omega) (by omega)
          apply hshape_power
          simp only [show m + 3 - 1 = m + 2 by omega] at hppure
          rw [hpow4] at hlow
          rw [hpow2] at hppure
          rw [hpow3]
          omega
        · simp only [show m + 3 - 1 = m + 2 by omega] at hv hpform
          have hb : 2 ^ v ≤ 2 * 2 ^ m := by
            rw [← hpow1]
            exact Nat.pow_le_pow_right (by decide) (by omega)
          by_cases hkprev : k = m + 3
          · apply hshape_sum (v + 1) (by omega)
            rw [heq, hkprev, hpform, hpow2, hpow3, pow_succ]
            omega
          · have hkq : k ≤ m + 2 := by omega
            have hxq := hmono k (m + 2) hkq (by omega)
            by_cases hqfull : a (m + 2) = 2 ^ (m + 2)
            · have hkfull := hrig (m + 2) (by omega) hqfull k hkq
              by_cases hkqeq : k = m + 2
              · apply hshape_sum v (by omega)
                rw [heq, hkqeq, hqfull, hpform, hpow2, hpow3]
                omega
              · have hx : a k ≤ 2 * 2 ^ m := by
                  rw [hkfull, ← hpow1]
                  exact Nat.pow_le_pow_right (by decide) (by omega)
                apply hshape_power
                rw [hpow4] at hlow
                rw [hpow3]
                rw [hpow2] at hpform
                omega
            · have hqsmall : a (m + 2) ≤ 3 * 2 ^ m := by
                rcases hq with h | h | ⟨w, hw, h⟩
                · exact False.elim (hqfull h)
                · simp only [show m + 2 - 1 = m + 1 by omega] at h
                  rw [h, hpow1]; omega
                · simp only [show m + 2 - 1 = m + 1 by omega] at hw h
                  have hwbound : (2 : ℕ) ^ w ≤ 2 ^ m :=
                    Nat.pow_le_pow_right (by decide) (by omega)
                  rw [h, hpow1]; omega
              have hbmin : 2 ^ m ≤ 2 ^ v := by
                rw [hpow4] at hlow
                rw [hpow2] at hpform
                omega
              have hmv : m ≤ v := (Nat.pow_le_pow_iff_right (by decide)).mp hbmin
              have hvcase : v = m ∨ v = m + 1 := by omega
              rcases hvcase with rfl | rfl
              · apply hshape_power
                rw [hpow4] at hlow
                rw [hpow2] at hpform
                rw [hpow3]
                omega
              · have hqexact : a (m + 2) = 3 * 2 ^ m := by
                  rw [hpform, hpow2, hpow1] at hpstep
                  omega
                by_cases hkqeq : k = m + 2
                · apply hshape_sum m (by omega)
                  rw [heq, hkqeq, hqexact, hpform, hpow2, hpow1, hpow3]
                  omega
                · have hx : a k ≤ 2 * 2 ^ m := by
                    have hku := hup k (by omega)
                    have hkp : (2 : ℕ) ^ k ≤ 2 ^ (m + 1) :=
                      Nat.pow_le_pow_right (by decide) (by omega)
                    rw [hpow1] at hkp
                    omega
                  apply hshape_power
                  rw [hpow4] at hlow
                  rw [hpow2, hpow1] at hpform
                  rw [hpow3]
                  omega
      · have hjq : j ≤ m + 2 := by omega
        have hjbound := hmono j (m + 2) hjq (by omega)
        have hkbound := hmono k (m + 2) (by omega) (by omega)
        apply hshape_power
        rw [hpow4] at hlow
        rw [hpow2] at hqbound
        rw [hpow3]
        omega

/-- An ascending addition chain within one step of the logarithmic bound ends at
a number with at most two binary ones. -/
theorem binaryWeight_le_two_of_asc_chainSteps_le_log_add_one {n : ℕ} {s : List ℕ}
    (hn : 0 < n) (hs : IsAscAddChain n s)
    (hsteps : chainSteps s ≤ Nat.log 2 n + 1) : binaryWeight n ≤ 2 := by
  let r := chainSteps s
  let a : ℕ → ℕ := fun i => s[i]?.getD 0
  have hlen : s.length = r + 1 := by
    have hpos := List.length_pos_iff.mpr hs.ne_nil
    dsimp [r, chainSteps]
    rw [List.length_tail]
    omega
  have haget (i : Fin s.length) : a i.val = s.get i := by
    dsimp [a]
    rw [List.getElem?_eq_getElem i.isLt]
    rfl
  have hzero : a 0 = 1 := by
    obtain ⟨x, t, hst⟩ := List.exists_cons_of_ne_nil hs.ne_nil
    have hx := hs.head_eq_one
    simp only [hst, List.head?_cons, Option.some.injEq] at hx
    simp [a, hst, hx]
  have hlast : a r = n := by
    have hlast' : s.getLast hs.ne_nil = n := by
      have heq := hs.getLast_eq
      rw [List.getLast?_eq_some_getLast hs.ne_nil] at heq
      exact Option.some.inj heq
    have hidx : r < s.length := by omega
    rw [haget ⟨r, hidx⟩, List.get_eq_getElem]
    rw [List.getLast_eq_getElem] at hlast'
    simpa only [show s.length - 1 = r by omega] using hlast'
  have hmono : ∀ i j, i ≤ j → j ≤ r → a i ≤ a j := by
    intro i j hij hj
    have hjlt : j < s.length := by omega
    have hilt : i < s.length := by omega
    rw [haget ⟨i, hilt⟩, haget ⟨j, hjlt⟩]
    exact hs.sortedLT.strictMono_get.monotone (show (⟨i, hilt⟩ : Fin s.length) ≤ ⟨j, hjlt⟩ from hij)
  have hsum : ∀ i, 0 < i → i ≤ r → ∃ j < i, ∃ k < i, a i = a j + a k := by
    intro i hip hir
    have hilt : i < s.length := by omega
    obtain ⟨j, k, hj, hk, heq⟩ := hs.get_eq_add ⟨i, hilt⟩ hip
    refine ⟨j.val, hj, k.val, hk, ?_⟩
    rw [haget ⟨i, hilt⟩, haget j, haget k]
    exact heq
  have hend : 2 ^ r ≤ 2 * a r := by
    rw [hlast]
    exact two_pow_steps_le_two_mul hn hsteps
  by_cases hr : r = 0
  · have hn1 : n = 1 := by rw [hr, hzero] at hlast; omega
    rw [hn1]
    decide
  · obtain h | h | ⟨v, hv, h⟩ :=
      asc_half_max_classification a r hzero hmono hsum hend r (by omega) (by omega)
    · rw [hlast] at h
      rw [h, binaryWeight_two_pow]
      decide
    · rw [hlast] at h
      rw [h, binaryWeight_two_pow]
      decide
    · rw [hlast] at h
      rw [h, Nat.add_comm, binaryWeight_two_pow_add_two_pow v (r - 1) hv]

/-- A positive integer whose shortest addition chain is within one step of the
logarithmic lower bound has binary weight at most two. -/
theorem binaryWeight_le_two_of_l_le_log_add_one {n : ℕ} (hn : 0 < n)
    (hl : l n ≤ Nat.log 2 n + 1) : binaryWeight n ≤ 2 := by
  obtain ⟨s, hs⟩ := exists_chainSteps_eq_lAsc (by omega : n ≠ 0)
  apply binaryWeight_le_two_of_asc_chainSteps_le_log_add_one hn s.property
  rw [hs, ← l_eq_lAsc]
  exact hl

/-- Three or more binary ones force at least two steps beyond the logarithmic
lower bound for every positive endpoint. -/
theorem log_add_two_le_l_of_three_le_binaryWeight {n : ℕ} (hn : 0 < n)
    (hw : 3 ≤ binaryWeight n) : Nat.log 2 n + 2 ≤ l n := by
  by_contra h
  have hl : l n ≤ Nat.log 2 n + 1 := by omega
  have hb := binaryWeight_le_two_of_l_le_log_add_one hn hl
  omega

example : 0 < 5 ∧ IsAscAddChain 5 [1, 2, 4, 5] ∧
    chainSteps [1, 2, 4, 5] ≤ Nat.log 2 5 + 1 := by decide

example : 0 < 5 ∧ l 5 ≤ Nat.log 2 5 + 1 := by decide

example : 0 < 7 ∧ 3 ≤ binaryWeight 7 := by decide

example :
    (fun i : ℕ => 2 ^ i) 0 = 1 ∧
    (∀ i j : ℕ, i ≤ j → j ≤ 4 → (2 : ℕ) ^ i ≤ 2 ^ j) ∧
    (∀ i : ℕ, 0 < i → i ≤ 4 →
      ∃ j < i, ∃ k < i, (2 : ℕ) ^ i = 2 ^ j + 2 ^ k) ∧
    (2 : ℕ) ^ 4 ≤ 2 * 2 ^ 4 := by
  refine ⟨rfl, ?_, ?_, by decide⟩
  · intro i j hij _
    exact Nat.pow_le_pow_right (by decide) hij
  · intro i hi _
    refine ⟨i - 1, by omega, i - 1, by omega, ?_⟩
    calc
      (2 : ℕ) ^ i = 2 ^ (i - 1 + 1) := by congr 1; omega
      _ = 2 ^ (i - 1) + 2 ^ (i - 1) := by rw [pow_succ]; omega

example : binaryWeight 1 ≤ 2 :=
  binaryWeight_le_two_of_asc_chainSteps_le_log_add_one
    (by decide) (show IsAscAddChain 1 [1] by decide) (by decide)

example : Nat.log 2 7 + 2 ≤ l 7 :=
  log_add_two_le_l_of_three_le_binaryWeight (by decide) (by decide)

end NumberComplexity
