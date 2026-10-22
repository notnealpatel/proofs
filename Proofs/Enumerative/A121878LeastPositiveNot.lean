/-
The greedy squarefree-sum permutation (OEIS A121878; Derek Orr, Jun 01 2015).

Starting with a(1)=1, choose the least unused positive integer a(n) with
a(n-1)+a(n) squarefree. The exact least-admissible recurrence is established,
and a is a bijection from positive indices to positive integers.
A two-residue squarefree sieve supplies candidates; if a positive integer
were omitted, the resulting bounds would contradict injectivity.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A121878LeastPositiveNot

open Finset

/-- In a window `[B, B + L)`, at most `L / q + 2` numbers `y` satisfy `q ∣ y + c`. -/
theorem card_filter_dvd_add_le (q c B L : ℕ) (hq : 0 < q) :
    #{y ∈ Ico B (B + L) | q ∣ y + c} ≤ L / q + 2 := by
  set s := (B + c) / q with hs
  have hmaps : Set.MapsTo (fun y => (y + c) / q)
      (({y ∈ Ico B (B + L) | q ∣ y + c} : Finset ℕ) : Set ℕ) (Icc s (s + L / q + 1)) := by
    intro y hy
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨hBy, hyL⟩, ⟨t, ht⟩⟩ := hy
    simp only [coe_Icc, Set.mem_Icc]
    rw [ht, Nat.mul_div_cancel_left t hq]
    constructor
    · rw [← Nat.mul_div_cancel_left t hq, ← ht]
      exact Nat.div_le_div_right (by omega)
    · by_contra hcon
      push Not at hcon
      have hmul : q * (s + L / q + 2) ≤ q * t := Nat.mul_le_mul_left q hcon
      have h1 := Nat.div_add_mod (B + c) q
      have h2 := Nat.div_add_mod L q
      have h3 := Nat.mod_lt (B + c) hq
      have h4 := Nat.mod_lt L hq
      rw [← hs] at h1
      nlinarith
  have hinj : Set.InjOn (fun y => (y + c) / q)
      (({y ∈ Ico B (B + L) | q ∣ y + c} : Finset ℕ) : Set ℕ) := by
    intro y hy y' hy' heq
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hy hy'
    have e1 := Nat.div_mul_cancel hy.2
    have e2 := Nat.div_mul_cancel hy'.2
    simp only at heq
    rw [heq] at e1
    omega
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc, show s + L / q + 1 + 1 = s + (L / q + 2) by ring, Nat.add_sub_cancel_left]
    at hcard
  exact hcard

/-- Telescoping bound: `∑_{k < R+1} 1/(2k+3)^2 + 1/(4(R+2)) ≤ 1/9 + 1/8`. -/
theorem sum_inv_odd_sq_le_aux (R : ℕ) :
    ∑ k ∈ range (R + 1), (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2 + 1 / (4 * ((R : ℚ) + 2)) ≤
      1 / 9 + 1 / 8 := by
  induction R with
  | zero => norm_num
  | succ R ih =>
    rw [sum_range_succ]
    have hstep : (1 : ℚ) / ((2 * (R + 1) + 3 : ℕ) : ℚ) ^ 2 + 1 / (4 * (((R + 1 : ℕ) : ℚ) + 2)) ≤
        1 / (4 * ((R : ℚ) + 2)) := by
      push_cast
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `∑_{k < R} 1/(2k+3)^2 ≤ 1/9 + 1/8`: the odd squares `3², 5², …`. -/
theorem sum_inv_odd_sq_le (R : ℕ) :
    ∑ k ∈ range R, (1 : ℚ) / ((2 * k + 3 : ℕ) : ℚ) ^ 2 ≤ 1 / 9 + 1 / 8 := by
  cases R with
  | zero => norm_num
  | succ R =>
    have h := sum_inv_odd_sq_le_aux R
    have hpos : (0 : ℚ) ≤ 1 / (4 * ((R : ℚ) + 2)) := by positivity
    linarith

/-- A non-squarefree `n` with `0 < n ≤ X` is divisible by `4` or by `(2k+3)^2` for some
`k < Nat.sqrt X`. -/
theorem four_dvd_or_exists_odd_sq_dvd (n X : ℕ) (hn : 0 < n) (hnX : n ≤ X)
    (hsq : ¬ Squarefree n) :
    4 ∣ n ∨ ∃ k < Nat.sqrt X, (2 * k + 3) ^ 2 ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  have hle : p * p ≤ X := (Nat.le_of_dvd hn hpp).trans hnX
  have hpX : p ≤ Nat.sqrt X := Nat.le_sqrt.mpr hle
  rcases hp.eq_two_or_odd' with h2 | hodd
  · left
    subst h2
    simpa using hpp
  · right
    obtain ⟨j, hj⟩ := hodd
    have hp2 := hp.two_le
    refine ⟨j - 1, by omega, ?_⟩
    have hpk : 2 * (j - 1) + 3 = p := by omega
    rw [hpk, sq]
    exact hpp

/-- **Sieve lemma.** For `0 < B` and a window length `L` with
`144 * (Nat.sqrt (B + L + m + x) + 1) < L`, some `y ∈ [B, B + L)` makes both `y + m` and
`y + x` squarefree. -/
theorem exists_squarefree_pair (m x B L : ℕ) (hB : 0 < B)
    (hL : 144 * (Nat.sqrt (B + L + m + x) + 1) < L) :
    ∃ y, B ≤ y ∧ y < B + L ∧ Squarefree (y + m) ∧ Squarefree (y + x) := by
  set R := Nat.sqrt (B + L + m + x) with hR
  set I : Finset ℕ := Ico B (B + L) with hI
  set A : ℕ → Finset ℕ := fun q => {y ∈ I | q ∣ y + m} ∪ {y ∈ I | q ∣ y + x} with hAdef
  have hA : ∀ q, 0 < q → (#(A q) : ℚ) ≤ 2 * (L : ℚ) * (1 / (q : ℚ)) + 4 := by
    intro q hq
    have h1 := card_filter_dvd_add_le q m B L hq
    have h2 := card_filter_dvd_add_le q x B L hq
    have h3 := card_union_le {y ∈ I | q ∣ y + m} {y ∈ I | q ∣ y + x}
    have h4 : ((L / q : ℕ) : ℚ) ≤ (L : ℚ) / q := Nat.cast_div_le
    rw [← hI] at h1 h2
    have h5 : #(A q) ≤ 2 * (L / q) + 4 := by
      simp only [hAdef]
      omega
    have h6 : (#(A q) : ℚ) ≤ 2 * ((L / q : ℕ) : ℚ) + 4 := by exact_mod_cast h5
    have h7 : 2 * ((L / q : ℕ) : ℚ) ≤ 2 * (L : ℚ) * (1 / q) := by
      rw [mul_one_div, mul_div_assoc]
      linarith
    linarith
  by_contra hno
  push Not at hno
  have hcover : I ⊆ A 4 ∪ (range R).biUnion (fun k => A ((2 * k + 3) ^ 2)) := by
    intro y hy
    have hy' := mem_Ico.mp hy
    have hmemA : ∀ q, (q ∣ y + m ∨ q ∣ y + x) → y ∈ A q := by
      intro q hq
      simp only [hAdef, mem_union, mem_filter]
      tauto
    have hbad : ∃ c, (c = m ∨ c = x) ∧ ¬ Squarefree (y + c) := by
      by_cases h : Squarefree (y + m)
      · exact ⟨x, Or.inr rfl, hno y hy'.1 hy'.2 h⟩
      · exact ⟨m, Or.inl rfl, h⟩
    obtain ⟨c, hc, hcsq⟩ := hbad
    have hcX : y + c ≤ B + L + m + x := by omega
    rcases four_dvd_or_exists_odd_sq_dvd (y + c) _ (by omega) hcX hcsq with h4 | ⟨k, hk, hkd⟩
    · apply mem_union_left
      apply hmemA
      rcases hc with rfl | rfl
      · exact Or.inl h4
      · exact Or.inr h4
    · apply mem_union_right
      rw [mem_biUnion]
      refine ⟨k, mem_range.mpr hk, hmemA _ ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl hkd
      · exact Or.inr hkd
  have hcardI : #I = L := by simp [hI]
  have hcard : (L : ℚ) ≤ #(A 4) + ∑ k ∈ range R, (#(A ((2 * k + 3) ^ 2)) : ℚ) := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (A 4) ((range R).biUnion (fun k => A ((2 * k + 3) ^ 2)))
    have h3 := card_biUnion_le (s := range R) (t := fun k => A ((2 * k + 3) ^ 2))
    have h4 : L ≤ #(A 4) + ∑ k ∈ range R, #(A ((2 * k + 3) ^ 2)) := by omega
    exact_mod_cast h4
  have hsum : ∑ k ∈ range R, (#(A ((2 * k + 3) ^ 2)) : ℚ) ≤
      ∑ k ∈ range R, (2 * (L : ℚ) * (1 / ((2 * k + 3 : ℕ) : ℚ) ^ 2) + 4) := by
    apply sum_le_sum
    intro k _
    have h := hA ((2 * k + 3) ^ 2) (by positivity)
    push_cast at h ⊢
    exact h
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  have hodd := sum_inv_odd_sq_le R
  have h4 := hA 4 (by norm_num)
  have hLq : (144 : ℚ) * ((R : ℚ) + 1) < L := by exact_mod_cast hL
  have hL0 : (0 : ℚ) ≤ L := by positivity
  have hprod := mul_le_mul_of_nonneg_left hodd hL0
  linarith

/-! ## The sequence -/

/-- `y` is an admissible next term after the term `x` when the set of used terms is `s`:
`y` is positive, not yet used, and `x + y` is squarefree. -/
def Admissible (s : Finset ℕ) (x y : ℕ) : Prop :=
  0 < y ∧ y ∉ s ∧ Squarefree (x + y)

/-- Admissibility is decidable (used by `Nat.find`). -/
instance (s : Finset ℕ) (x : ℕ) : DecidablePred (Admissible s x) := fun y => by
  unfold Admissible
  infer_instance

/-- An admissible next term always exists: take `y = p - x` for a large prime `p`. -/
theorem exists_admissible (s : Finset ℕ) (x : ℕ) : ∃ y, Admissible s x y := by
  obtain ⟨p, hp_le, hp⟩ := Nat.exists_infinite_primes (x + s.sup id + 2)
  refine ⟨p - x, by omega, ?_, ?_⟩
  · intro hmem
    have hle : id (p - x) ≤ s.sup id := Finset.le_sup hmem
    simp only [id] at hle
    omega
  · rw [show x + (p - x) = p by omega]
    exact hp.prime.irreducible.squarefree

/-- The greedy step: the least admissible next term after `x` given used set `s`. -/
noncomputable def nextTerm (s : Finset ℕ) (x : ℕ) : ℕ :=
  Nat.find (exists_admissible s x)

/-- The state after `k + 1` terms: the last term `a(k+1)` and the set `{a(1), …, a(k+1)}`. -/
noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (1, {1})
  | k + 1 => (nextTerm (state k).2 (state k).1,
      insert (nextTerm (state k).2 (state k).1) (state k).2)

/-- OEIS A121878 with offset `1`: `a 1 = 1` and `a (n + 1)` is the least positive integer not
occurring earlier with `a n + a (n + 1)` squarefree. The value `a 0 = 0` lies outside the
OEIS domain and is never used. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | k + 1 => (state k).1

/-! ## Structural lemmas -/

/-- The used set after `k + 1` terms is exactly `{a(1), …, a(k+1)}`. -/
theorem mem_state_snd_iff (k y : ℕ) : y ∈ (state k).2 ↔ ∃ j ≤ k, (state j).1 = y := by
  induction k with
  | zero =>
    simp only [state, Finset.mem_singleton, Nat.le_zero, exists_eq_left]
    exact eq_comm
  | succ k ih =>
    simp only [state, Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨j, hj, hjy⟩)
      · exact ⟨k + 1, le_rfl, by simp only [state]; exact h.symm⟩
      · exact ⟨j, by omega, hjy⟩
    · rintro ⟨j, hj, hjy⟩
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · exact Or.inr ⟨j, by omega, hjy⟩
      · subst heq
        left
        simp only [state] at hjy
        exact hjy.symm

/-- Each greedy step is admissible. -/
theorem admissible_state_succ (k : ℕ) :
    Admissible (state k).2 (state k).1 (state (k + 1)).1 :=
  Nat.find_spec (exists_admissible (state k).2 (state k).1)

/-- Each greedy step is minimal among admissible candidates. -/
theorem state_succ_le (k y : ℕ) (hy : Admissible (state k).2 (state k).1 y) :
    (state (k + 1)).1 ≤ y :=
  Nat.find_min' (exists_admissible (state k).2 (state k).1) hy

/-- All terms are positive. -/
theorem state_fst_pos (k : ℕ) : 0 < (state k).1 := by
  cases k with
  | zero => simp [state]
  | succ k => exact (admissible_state_succ k).1

/-- The terms are pairwise distinct. -/
theorem state_fst_injective : Function.Injective (fun k => (state k).1) := by
  have hlt : ∀ i j, i < j → (state i).1 ≠ (state j).1 := by
    intro i j hij heq
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hnot := (admissible_state_succ k).2.1
    exact hnot ((mem_state_snd_iff k _).mpr ⟨i, by omega, heq⟩)
  intro i j hij
  simp only at hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (hlt i j h)
  · exact h
  · exact absurd hij.symm (hlt j i h)

/-! ## Surjectivity -/

/-- For every base point `B` and shift `m` there is a window `[B, T)` of length `L = T - B` to
which the sieve lemma applies uniformly for every `x ≤ T`. -/
theorem exists_window (B m : ℕ) :
    ∃ T L, B + L = T ∧ ∀ x ≤ T, 144 * (Nat.sqrt (B + L + m + x) + 1) < L := by
  set N := B + m + 300 with hN
  have hBN : B ≤ N ^ 2 := le_trans (by omega : B ≤ N) (Nat.le_self_pow two_ne_zero N)
  obtain ⟨L, hL⟩ : ∃ L, B + L = N ^ 2 := ⟨N ^ 2 - B, by omega⟩
  refine ⟨N ^ 2, L, hL, fun x hx => ?_⟩
  have hsq : Nat.sqrt (B + L + m + x) < 2 * N + 1 := by
    rw [Nat.sqrt_lt']
    nlinarith
  have hLbig : 144 * (2 * N + 1) < L := by nlinarith
  omega

/-- If `m` never occurs, then from some point on `a(k) + m` is never squarefree. -/
theorem eventually_not_squarefree (m : ℕ) (hm : 0 < m) (hne : ∀ k, (state k).1 ≠ m) :
    ∃ K, ∀ k, K < k → ¬ Squarefree ((state k).1 + m) := by
  have hinj : Function.Injective (fun k => (state (k + 1)).1) :=
    state_fst_injective.comp (fun i j h => Nat.succ_injective h)
  have hfin : ((fun k => (state (k + 1)).1) ⁻¹' Set.Iic m).Finite :=
    (Set.finite_Iic m).preimage hinj.injOn
  obtain ⟨K, hK⟩ := hfin.bddAbove
  refine ⟨K, fun k hk hsf => ?_⟩
  have hmnot : m ∉ (state k).2 := by
    rw [mem_state_snd_iff]
    rintro ⟨j, -, hj⟩
    exact hne j hj
  have hle : (state (k + 1)).1 ≤ m := state_succ_le k m ⟨hm, hmnot, hsf⟩
  have hkK : k ≤ K := hK (show k ∈ (fun k => (state (k + 1)).1) ⁻¹' Set.Iic m from hle)
  omega

/-- Every positive integer occurs among the terms. -/
theorem exists_state_fst_eq (m : ℕ) (hm : 0 < m) : ∃ k, (state k).1 = m := by
  by_contra hne
  push Not at hne
  obtain ⟨K, hK⟩ := eventually_not_squarefree m hm hne
  set B := (Finset.range (K + 1)).sup (fun j => (state j).1) + 1 with hB
  have hsmall : ∀ j ≤ K, (state j).1 < B := by
    intro j hj
    have hle : (state j).1 ≤ (Finset.range (K + 1)).sup (fun j => (state j).1) :=
      Finset.le_sup (f := fun j => (state j).1) (Finset.mem_range.mpr (by omega))
    omega
  obtain ⟨T, L, hBL, hwin⟩ := exists_window B m
  -- One greedy step from a term `≤ T` lands below `T`
  have hstep : ∀ k, (state k).1 ≤ T → (state (k + 1)).1 < T := by
    intro k hk
    obtain ⟨y, hBy, hyL, hsm, hsx⟩ :=
      exists_squarefree_pair m (state k).1 B L (by omega) (hwin _ hk)
    have hynot : y ∉ (state k).2 := by
      rw [mem_state_snd_iff]
      rintro ⟨j, -, hjy⟩
      by_cases hjK : j ≤ K
      · have := hsmall j hjK
        omega
      · exact hK j (by omega) (hjy ▸ hsm)
    have hle := state_succ_le k y ⟨by omega, hynot, by rwa [add_comm]⟩
    omega
  have hbounded : ∀ k, K ≤ k → (state k).1 ≤ T := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => have := hsmall K le_rfl; omega
    | succ k _ ih => exact (hstep k ih).le
  -- Pigeonhole: `T + 2` distinct terms cannot all lie in `[0, T]`
  have hcard := Finset.card_le_card_of_injOn (fun k => (state k).1)
    (s := Finset.Ico K (K + T + 2)) (t := Finset.range (T + 1))
    (fun k hk => by
      simp only [Finset.coe_Ico, Set.mem_Ico] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      have := hbounded k hk.1
      omega)
    (state_fst_injective.injOn)
  simp only [Nat.card_Ico, Finset.card_range] at hcard
  omega

/-! ## Fidelity: `a` satisfies the defining property of the entry -/

/-- `a (k + 1)` is the `(k + 1)`-st greedy term. -/
theorem a_succ (k : ℕ) : a (k + 1) = (state k).1 := rfl

/-- The first term is `a 1 = 1`. -/
theorem a_one : a 1 = 1 := rfl

/-- A value is unused after `k + 1` terms iff it differs from `a 1, …, a (k + 1)`. -/
theorem not_mem_state_snd_iff (k y : ℕ) :
    y ∉ (state k).2 ↔ ∀ j ∈ Finset.Icc 1 (k + 1), a j ≠ y := by
  rw [mem_state_snd_iff]
  constructor
  · intro h j hj hjy
    rw [Finset.mem_Icc] at hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact h ⟨i, by omega, hjy⟩
  · rintro h ⟨j, hj, hjy⟩
    exact h (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hjy

/-- **Defining property.** For `n ≥ 1`, `a (n + 1)` is the least positive integer `y` not
among `a 1, …, a n` such that `a n + y` is squarefree. -/
theorem isLeast_a_succ (n : ℕ) (hn : 0 < n) :
    IsLeast {y | 0 < y ∧ (∀ j ∈ Finset.Icc 1 n, a j ≠ y) ∧ Squarefree (a n + y)}
      (a (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hiff : ∀ y, y ∈ {y | 0 < y ∧ (∀ j ∈ Finset.Icc 1 (k + 1), a j ≠ y) ∧
      Squarefree (a (k + 1) + y)} ↔ Admissible (state k).2 (state k).1 y := by
    intro y
    simp only [Set.mem_ofPred_eq, Admissible, not_mem_state_snd_iff, a_succ]
  refine ⟨(hiff _).mpr (admissible_state_succ k), fun y hy => ?_⟩
  exact state_succ_le k y ((hiff y).mp hy)

/-! ## Examples -/

/-- For positive `n`, squarefreeness is the bounded condition that no `d * d` with
`2 ≤ d ≤ n` divides `n`; this form is decidable by kernel reduction. -/
theorem squarefree_iff_forall_lt (n : ℕ) (hn : 0 < n) :
    Squarefree n ↔ ∀ d < n + 1, 2 ≤ d → ¬ d * d ∣ n := by
  constructor
  · intro hsf d _ hd hdvd
    have hunit := hsf d hdvd
    rw [Nat.isUnit_iff] at hunit
    omega
  · intro h x hx
    rw [Nat.isUnit_iff]
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp only [mul_zero, zero_dvd_iff] at hx
      omega
    by_contra hx1
    have hle : x * x ≤ n := Nat.le_of_dvd hn hx
    have hxx : x ≤ x * x := Nat.le_mul_of_pos_right x (by omega)
    exact h x (by omega) (by omega) hx

/-- One greedy step, certified by decidable data: if the state is `(x, s)`, `y` is admissible,
and every smaller positive unused `z` has a square factor `d * d` in `x + z`, then the next
state is `(y, insert y s)`. -/
theorem state_succ_eq_of (k x y : ℕ) (s : Finset ℕ) (hk : state k = (x, s)) (hx : 0 < x)
    (hy : 0 < y) (hys : y ∉ s) (hsf : ∀ d < x + y + 1, 2 ≤ d → ¬ d * d ∣ x + y)
    (hmin : ∀ z < y, 0 < z → z ∉ s → ∃ d < x + z + 1, 2 ≤ d ∧ d * d ∣ x + z) :
    state (k + 1) = (y, insert y s) := by
  have hadm : Admissible s x y := ⟨hy, hys, (squarefree_iff_forall_lt _ (by omega)).mpr hsf⟩
  have hnext : nextTerm s x = y := by
    apply le_antisymm (Nat.find_min' _ hadm)
    by_contra hlt
    push Not at hlt
    obtain ⟨hz0, hzs, hzsf⟩ := Nat.find_spec (exists_admissible s x)
    obtain ⟨d, hd, hd2, hdvd⟩ := hmin _ hlt hz0 hzs
    exact ((squarefree_iff_forall_lt _ (by omega)).mp hzsf) d hd hd2 hdvd
  simp only [state, hk, hnext]

/-- The first twelve terms `1, 2, 3, 4, 6, 5, 8, 7, 10, 9, 12, 11` of A121878. -/
theorem first_terms :
    a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 4 ∧ a 5 = 6 ∧ a 6 = 5 ∧ a 7 = 8 ∧ a 8 = 7 ∧
      a 9 = 10 ∧ a 10 = 9 ∧ a 11 = 12 ∧ a 12 = 11 := by
  have h0 : state 0 = (1, {1}) := rfl
  have h1 := state_succ_eq_of 0 1 2 _ h0 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h2 := state_succ_eq_of 1 2 3 _ h1 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h3 := state_succ_eq_of 2 3 4 _ h2 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h4 := state_succ_eq_of 3 4 6 _ h3 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h5 := state_succ_eq_of 4 6 5 _ h4 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h6 := state_succ_eq_of 5 5 8 _ h5 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h7 := state_succ_eq_of 6 8 7 _ h6 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h8 := state_succ_eq_of 7 7 10 _ h7 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h9 := state_succ_eq_of 8 10 9 _ h8 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h10 := state_succ_eq_of 9 9 12 _ h9 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h11 := state_succ_eq_of 10 12 11 _ h10 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  simp only [a_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, and_self]

/-! ## The conjecture -/

/-- **Orr's conjecture (A121878, Derek Orr, Jun 01 2015), proved.** "Conjectured to be a
permutation of the natural numbers": the sequence `a` (with `a 1 = 1` and `a (n + 1)` the least
positive integer not occurring earlier with `a n + a (n + 1)` squarefree) is a bijection from
the positive indices onto the positive integers. -/
theorem a_bijOn : Set.BijOn a {n | 0 < n} {m | 0 < m} := by
  refine ⟨fun n hn => ?_, fun n₁ hn₁ n₂ hn₂ h => ?_, fun m hm => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp only [Set.mem_ofPred_eq] at hn; omega⟩
    exact state_fst_pos k
  · simp only [Set.mem_ofPred_eq] at hn₁ hn₂
    obtain ⟨k₁, rfl⟩ : ∃ k, n₁ = k + 1 := ⟨n₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k, n₂ = k + 1 := ⟨n₂ - 1, by omega⟩
    rw [state_fst_injective h]
  · obtain ⟨k, hk⟩ := exists_state_fst_eq m hm
    exact ⟨k + 1, Nat.succ_pos k, hk⟩

end Candidates.A121878LeastPositiveNot
