/-
# A064796 — McCranie: minimax adjacent product over cyclic arrangements

Jud McCranie's conjecture in OEIS A064796 (October 25, 2001) gives the
minimax adjacent product as `(n+1)(n+3)/4` for odd `n` and `n(n+4)/4`
for even `n`. David Wasserman's formula (August 19, 2002) restricts this
to `n > 2`: at `n = 2` the value is 2, not 3.

The lower bound uses double counting on the largest values of the cycle;
the upper bound uses the zigzag arrangement `1, n, 2, n-1, 3, ...`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A064796MinCyclicArrangements

open Finset

/-! ## Definition layer

Positions are `Fin n`; the arrangement is a permutation `σ` of `Fin n`, and the
entry's `p_i` is `σ i + 1` (so values run over `1, ..., n`).  The cyclic
successor of position `i` is `finRotate n i` (`n - 1 ↦ 0`), which encodes
`p_{n+1} = p_1`. -/

/-- The product `p_i * p_{i+1}` of the values at position `i` and its cyclic
successor, for the arrangement `p_j = σ j + 1` of `1, ..., n`. -/
def adjProd (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  ((σ i : ℕ) + 1) * ((σ (finRotate n i) : ℕ) + 1)

/-- OEIS A064796, verbatim definition: the largest integer `m` such that every
permutation `(p_1, ..., p_n)` of `(1, ..., n)` has some cyclically adjacent
product `p_i * p_{i+1} ≥ m`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ σ : Equiv.Perm (Fin n), ∃ i : Fin n, m ≤ adjProd n σ i}

/-- Characterization of `a n` by a matching lower and upper bound: if every
arrangement has an adjacent product `≥ M`, and some arrangement has all
adjacent products `≤ M`, then `a n = M`. -/
theorem a_eq_of_bounds (n M : ℕ)
    (hlow : ∀ σ : Equiv.Perm (Fin n), ∃ i : Fin n, M ≤ adjProd n σ i)
    (hup : ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, adjProd n σ i ≤ M) : a n = M := by
  apply IsGreatest.csSup_eq
  refine ⟨hlow, ?_⟩
  intro m hm
  obtain ⟨σ₀, hσ₀⟩ := hup
  obtain ⟨i, hi⟩ := hm σ₀
  exact hi.trans (hσ₀ i)

/-! ## Examples: the first listed terms `1, 2, 6, 8` -/

example : a 1 = 1 := by
  apply a_eq_of_bounds
  · decide
  · decide

example : a 2 = 2 := by
  apply a_eq_of_bounds
  · decide
  · decide

example : a 3 = 6 := by
  apply a_eq_of_bounds
  · decide
  · decide

example : a 4 = 8 := by
  apply a_eq_of_bounds
  · decide
  · decide

/-! ## Cyclic rotation facts -/

/-- The value of the cyclic successor `finRotate n i`. -/
theorem val_finRotate (n : ℕ) (i : Fin n) :
    ((finRotate n i : Fin n) : ℕ) = if (i : ℕ) + 1 = n then 0 else (i : ℕ) + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    have hlast : i = Fin.last m ↔ (i : ℕ) + 1 = m + 1 := by
      rw [Fin.ext_iff, Fin.val_last]; omega
    by_cases h : (i : ℕ) + 1 = m + 1
    · rw [if_pos (hlast.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hlast.mp h')), if_neg h]

/-- On a cycle of length at least `2`, a position differs from its successor. -/
theorem finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_finRotate] at hv
  have hi := i.isLt
  split_ifs at hv <;> omega

/-- On a cycle of length at least `3`, a position differs from its second
successor. -/
theorem finRotate_finRotate_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_finRotate, val_finRotate] at hv
  have hi := i.isLt
  split_ifs at hv <;> omega

/-! ## Lower bound: double counting -/

/-- Double counting on a cycle: if `B` is the set of positions satisfying `P`,
then `2 |B| ≤ n + #{i | i ∈ B and its successor ∈ B}`. -/
theorem two_mul_card_le (n : ℕ) (P : Fin n → Prop) [DecidablePred P] :
    2 * #{i | P i} ≤ n + #{i | P i ∧ P (finRotate n i)} := by
  have hrot : (∑ i : Fin n, if P (finRotate n i) then 1 else 0) =
      ∑ i : Fin n, if P i then 1 else 0 :=
    Equiv.sum_comp (finRotate n) (fun i => if P i then 1 else 0)
  have hpt : ∀ i : Fin n, ((if P i then 1 else 0) + if P (finRotate n i) then 1 else 0) ≤
      1 + if P i ∧ P (finRotate n i) then 1 else 0 := by
    intro i
    generalize finRotate n i = j
    by_cases h1 : P i <;> by_cases h2 : P j <;> simp [h1, h2]
  calc 2 * #{i | P i}
      = ∑ i : Fin n, ((if P i then 1 else 0) + if P (finRotate n i) then 1 else 0) := by
        rw [Finset.sum_add_distrib, hrot, Finset.card_filter]; ring
    _ ≤ ∑ i : Fin n, (1 + if P i ∧ P (finRotate n i) then 1 else 0) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = n + #{i | P i ∧ P (finRotate n i)} := by
        rw [Finset.sum_add_distrib, Finset.card_filter]; simp

/-- Exactly `n - t` positions carry a (0-based) value `≥ t`. -/
theorem card_le_val (n t : ℕ) (σ : Equiv.Perm (Fin n)) :
    #{i | t ≤ ((σ i : Fin n) : ℕ)} = n - t := by
  rw [Finset.card_filter]
  rw [Equiv.sum_comp σ (fun v : Fin n => if t ≤ (v : ℕ) then 1 else 0)]
  rw [Fin.sum_univ_eq_sum_range (fun v => if t ≤ v then 1 else 0) n, ← Finset.card_filter]
  have hset : ({v ∈ range n | t ≤ v} : Finset ℕ) = Ico t n := by
    ext v; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hset, Nat.card_Ico]

/-- Two distinct naturals `≥ k` have `(x+1)(y+1) ≥ (k+1)(k+2)`. -/
theorem le_mul_of_ne (k x y : ℕ) (hx : k ≤ x) (hy : k ≤ y) (hxy : x ≠ y) :
    (k + 1) * (k + 2) ≤ (x + 1) * (y + 1) := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact Nat.mul_le_mul (by omega) (by omega)
  · calc (k + 1) * (k + 2) = (k + 2) * (k + 1) := by ring
      _ ≤ (x + 1) * (y + 1) := Nat.mul_le_mul (by omega) (by omega)

/-- Two distinct naturals `≥ m` with `(x+1)(y+1) < (m+1)(m+3)` are `{m, m+1}`. -/
theorem eq_of_mul_lt (m x y : ℕ) (hx : m ≤ x) (hy : m ≤ y) (hxy : x ≠ y)
    (hlt : (x + 1) * (y + 1) < (m + 1) * (m + 3)) :
    (x = m ∧ y = m + 1) ∨ (x = m + 1 ∧ y = m) := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · left
    by_contra hne
    have hx' : m + 1 ≤ x + 1 := by omega
    have hy' : m + 3 ≤ y + 1 := by omega
    have hmul := Nat.mul_le_mul hx' hy'
    omega
  · right
    by_contra hne
    have hx' : m + 3 ≤ x + 1 := by omega
    have hy' : m + 1 ≤ y + 1 := by omega
    have hmul := Nat.mul_le_mul hy' hx'
    rw [Nat.mul_comm (y + 1)] at hmul
    omega

/-- Lower bound, odd case `n = 2k+1 ≥ 3`: every arrangement has an adjacent
product `≥ (k+1)(k+2)`.  The `k+1` values `k+1, ..., 2k+1` cannot be pairwise
non-adjacent on a cycle of length `2k+1`. -/
theorem lower_odd (k : ℕ) (hk : 1 ≤ k) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    ∃ i, (k + 1) * (k + 2) ≤ adjProd (2 * k + 1) σ i := by
  have hcount := two_mul_card_le (2 * k + 1) (fun i => k ≤ ((σ i : Fin _) : ℕ))
  rw [card_le_val] at hcount
  have hpos : 0 < #{i | k ≤ ((σ i : Fin _) : ℕ) ∧
      k ≤ ((σ (finRotate (2 * k + 1) i) : Fin _) : ℕ)} := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [mem_filter] at hi
  refine ⟨i, ?_⟩
  have hne : ((σ i : Fin _) : ℕ) ≠ σ (finRotate (2 * k + 1) i) := by
    intro h
    exact finRotate_ne_self (by omega) i (σ.injective (Fin.ext h)).symm
  exact le_mul_of_ne k _ _ hi.2.1 hi.2.2 hne

/-- Lower bound, even case `n = 2m+2 ≥ 4`: every arrangement has an adjacent
product `≥ (m+1)(m+3)`.  The `m+2` values `m+1, ..., 2m+2` span at least two
adjacent pairs; on a cycle of length `≥ 3` they cannot both be `{m+1, m+2}`. -/
theorem lower_even (m : ℕ) (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (2 * m + 2))) :
    ∃ i, (m + 1) * (m + 3) ≤ adjProd (2 * m + 2) σ i := by
  have hcount := two_mul_card_le (2 * m + 2) (fun i => m ≤ ((σ i : Fin _) : ℕ))
  rw [card_le_val] at hcount
  have htwo : 1 < #{i | m ≤ ((σ i : Fin _) : ℕ) ∧
      m ≤ ((σ (finRotate (2 * m + 2) i) : Fin _) : ℕ)} := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
  rw [mem_filter] at hi hj
  by_contra hcon
  push Not at hcon
  have hinj : ∀ p q : Fin (2 * m + 2), ((σ p : Fin _) : ℕ) = σ q → p = q :=
    fun p q h => σ.injective (Fin.ext h)
  have hbad : ∀ p : Fin (2 * m + 2), m ≤ ((σ p : Fin _) : ℕ) →
      m ≤ ((σ (finRotate (2 * m + 2) p) : Fin _) : ℕ) →
      (((σ p : Fin _) : ℕ) = m ∧ ((σ (finRotate (2 * m + 2) p) : Fin _) : ℕ) = m + 1) ∨
      (((σ p : Fin _) : ℕ) = m + 1 ∧ ((σ (finRotate (2 * m + 2) p) : Fin _) : ℕ) = m) := by
    intro p hp1 hp2
    have hne : ((σ p : Fin _) : ℕ) ≠ σ (finRotate (2 * m + 2) p) := by
      intro h
      exact finRotate_ne_self (by omega) p (hinj _ _ h).symm
    exact eq_of_mul_lt m _ _ hp1 hp2 hne (hcon p)
  have h3 : 3 ≤ 2 * m + 2 := by omega
  rcases hbad i hi.2.1 hi.2.2 with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
    rcases hbad j hj.2.1 hj.2.2 with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · exact hij (hinj _ _ (hi1.trans hj1.symm))
  · have hij1 : i = finRotate _ j := hinj _ _ (hi1.trans hj2.symm)
    have hij2 : finRotate _ i = j := hinj _ _ (hi2.trans hj1.symm)
    rw [hij1] at hij2
    exact finRotate_finRotate_ne_self h3 j hij2
  · have hij1 : i = finRotate _ j := hinj _ _ (hi1.trans hj2.symm)
    have hij2 : finRotate _ i = j := hinj _ _ (hi2.trans hj1.symm)
    rw [hij1] at hij2
    exact finRotate_finRotate_ne_self h3 j hij2
  · exact hij (hinj _ _ (hi1.trans hj1.symm))

/-! ## Upper bound: the zigzag arrangement `1, n, 2, n-1, 3, n-2, ...` -/

/-- The 0-based value placed at position `p` by the zigzag arrangement:
`p / 2` at even positions, `n - 1 - p / 2` at odd positions. -/
def zz (n p : ℕ) : ℕ := if p % 2 = 0 then p / 2 else n - 1 - p / 2

/-- The zigzag arrangement as a map `Fin n → Fin n`. -/
def zigzag (n : ℕ) (p : Fin n) : Fin n :=
  ⟨zz n p, by have hp := p.isLt; unfold zz; split_ifs <;> omega⟩

/-- The zigzag map is injective: even positions take the values
`0, ..., ⌈n/2⌉ - 1` and odd positions the values above them. -/
theorem zigzag_injective (n : ℕ) : Function.Injective (zigzag n) := by
  intro p q h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  have hq := q.isLt
  simp only [zigzag, zz] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The zigzag arrangement `1, n, 2, n-1, 3, ...` as a permutation of `Fin n`. -/
noncomputable def zigzagPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (zigzag n) (Finite.injective_iff_bijective.mp (zigzag_injective n))

/-- Adjacent products of the zigzag arrangement in closed form. -/
theorem adjProd_zigzagPerm (n : ℕ) (i : Fin n) :
    adjProd n (zigzagPerm n) i =
      (zz n i + 1) * (zz n (if (i : ℕ) + 1 = n then 0 else (i : ℕ) + 1) + 1) := by
  simp only [adjProd, zigzagPerm, Equiv.ofBijective_apply, zigzag]
  rw [val_finRotate]

/-- Upper bound arithmetic, even case `n = 2m+2`. -/
theorem upper_even (m p : ℕ) (hp : p < 2 * m + 2) :
    (zz (2 * m + 2) p + 1) * (zz (2 * m + 2) (if p + 1 = 2 * m + 2 then 0 else p + 1) + 1)
      ≤ (m + 1) * (m + 3) := by
  by_cases hlast : p + 1 = 2 * m + 2
  · rw [if_pos hlast]
    have h1 : zz (2 * m + 2) p = m + 1 := by unfold zz; split_ifs <;> omega
    have h0 : zz (2 * m + 2) 0 = 0 := by unfold zz; simp
    rw [h1, h0]; nlinarith
  · rw [if_neg hlast]
    rcases Nat.even_or_odd' p with ⟨q, hq | hq⟩
    · have h1 : zz (2 * m + 2) p = q := by unfold zz; split_ifs <;> omega
      have h2 : zz (2 * m + 2) (p + 1) = 2 * m + 1 - q := by unfold zz; split_ifs <;> omega
      obtain ⟨d, rfl⟩ : ∃ d, m = q + d := ⟨m - q, by omega⟩
      have h2' : 2 * (q + d) + 1 - q = q + 2 * d + 1 := by omega
      rw [h1, h2, h2']; nlinarith
    · have h1 : zz (2 * m + 2) p = 2 * m + 1 - q := by unfold zz; split_ifs <;> omega
      have h2 : zz (2 * m + 2) (p + 1) = q + 1 := by unfold zz; split_ifs <;> omega
      obtain ⟨d, rfl⟩ : ∃ d, m = q + 1 + d := ⟨m - q - 1, by omega⟩
      have h1' : 2 * (q + 1 + d) + 1 - q = q + 2 * d + 3 := by omega
      rw [h1, h2, h1']; nlinarith

/-- Upper bound arithmetic, odd case `n = 2k+1`. -/
theorem upper_odd (k p : ℕ) (hk : 1 ≤ k) (hp : p < 2 * k + 1) :
    (zz (2 * k + 1) p + 1) * (zz (2 * k + 1) (if p + 1 = 2 * k + 1 then 0 else p + 1) + 1)
      ≤ (k + 1) * (k + 2) := by
  by_cases hlast : p + 1 = 2 * k + 1
  · rw [if_pos hlast]
    have h1 : zz (2 * k + 1) p = k := by unfold zz; split_ifs <;> omega
    have h0 : zz (2 * k + 1) 0 = 0 := by unfold zz; simp
    rw [h1, h0]; nlinarith
  · rw [if_neg hlast]
    rcases Nat.even_or_odd' p with ⟨q, hq | hq⟩
    · have h1 : zz (2 * k + 1) p = q := by unfold zz; split_ifs <;> omega
      have h2 : zz (2 * k + 1) (p + 1) = 2 * k - q := by unfold zz; split_ifs <;> omega
      obtain ⟨d, rfl⟩ : ∃ d, k = q + 1 + d := ⟨k - q - 1, by omega⟩
      have h2' : 2 * (q + 1 + d) - q = q + 2 * d + 2 := by omega
      rw [h1, h2, h2']; nlinarith
    · have h1 : zz (2 * k + 1) p = 2 * k - q := by unfold zz; split_ifs <;> omega
      have h2 : zz (2 * k + 1) (p + 1) = q + 1 := by unfold zz; split_ifs <;> omega
      obtain ⟨d, rfl⟩ : ∃ d, k = q + 1 + d := ⟨k - q - 1, by omega⟩
      have h1' : 2 * (q + 1 + d) - q = q + 2 * d + 2 := by omega
      rw [h1, h2, h1']; nlinarith

/-! ## The conjecture -/

/-- **Odd case.** For `n = 2k+1 ≥ 3`, `a(n) = (k+1)(k+2)`. -/
theorem a_odd (k : ℕ) (hk : 1 ≤ k) : a (2 * k + 1) = (k + 1) * (k + 2) :=
  a_eq_of_bounds _ _ (lower_odd k hk)
    ⟨zigzagPerm _, fun i => by rw [adjProd_zigzagPerm]; exact upper_odd k i hk i.isLt⟩

/-- **Even case.** For `n = 2m+2 ≥ 4`, `a(n) = (m+1)(m+3)`. -/
theorem a_even (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 2) = (m + 1) * (m + 3) :=
  a_eq_of_bounds _ _ (lower_even m hm)
    ⟨zigzagPerm _, fun i => by rw [adjProd_zigzagPerm]; exact upper_even m i i.isLt⟩

/-- McCranie's conjecture (OEIS A064796, October 25, 2001), with
Wasserman's restriction `3 ≤ n` (August 19, 2002): the minimax cyclic
adjacent product is `(n+1)(n+3)/4` for odd `n` and `n(n+4)/4` for even `n`.
The divisions are exact in their respective parity cases. At `n = 2`
the formula gives 3, whereas `a 2 = 2`. -/
theorem a_eq_formula (n : ℕ) (hn : 3 ≤ n) :
    a n = if Odd n then (n + 1) * (n + 3) / 4 else n * (n + 4) / 4 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hnot : ¬ Odd (2 * k) := Nat.not_odd_iff_even.mpr (even_two_mul k)
    rw [if_neg hnot]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hn' : 2 * (m + 1) = 2 * m + 2 := by ring
    have hval : 2 * (m + 1) * (2 * (m + 1) + 4) = 4 * ((m + 1) * (m + 3)) := by ring
    rw [hval, Nat.mul_div_cancel_left _ (by norm_num), hn', a_even m (by omega)]
  · have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
    rw [if_pos hodd]
    have hval : (2 * k + 1 + 1) * (2 * k + 1 + 3) = 4 * ((k + 1) * (k + 2)) := by ring
    rw [hval, Nat.mul_div_cancel_left _ (by norm_num), a_odd k (by omega)]

end Candidates.A064796MinCyclicArrangements
