/-
# A counterexample to the Beck-Sam-Woods minimum-period conjecture

Feihu Liu, Jinlong Tang, Guoce Xin and Chen Zhang, "Counterexamples to the
Minimum Period Conjecture for Restricted Partition Functions", arXiv:2608.02085,
Conjecture 1.1 (Beck-Sam-Woods, JCTA 115 (2008), Conjecture 11),
Theorem 1.3 and Section 4, Theorem 4.3.
For `a = (1,1,2,2,2,2,13)`, the denumerant has an explicit quasi-polynomial
expansion, unique among periodic complex expansions on nonnegative arguments.
Its constant coefficient has minimum period `13`, whereas the conjecture
predicts `26`. This proves the `(u,M) = (2,13)` instance, not the whole
infinite family. The expansion is verified by first-part recurrences,
polynomial identities and finite base values.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BeckSamWoodsCounterexamples

/-! ## The restricted partition function and its closed form -/

/-- The restricted partition function (Sylvester's denumerant) of the paper:
`q_a(k) = #{u ∈ ℕⁿ : a₁u₁ + ⋯ + aₙuₙ = k}`, as the `Set.ncard` of the solution set
(which is finite when every `aᵢ` is positive, see `finite_solutions`). -/
noncomputable def denumerant {n : ℕ} (a : Fin n → ℕ) (k : ℕ) : ℕ :=
  Set.ncard {u : Fin n → ℕ | ∑ i, a i * u i = k}

/-- For positive weights the solution set of `∑ aᵢ uᵢ = k` is finite
(every `uᵢ ≤ k`). -/
theorem finite_solutions {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ) :
    {u : Fin n → ℕ | ∑ i, a i * u i = k}.Finite := by
  apply (Set.Finite.pi (t := fun _ => Set.Iic k) (fun _ => Set.finite_Iic k)).subset
  intro u hu
  simp only [Set.mem_ofPred_eq] at hu
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
  intro i
  have h1 : u i ≤ a i * u i := Nat.le_mul_of_pos_left _ (ha i)
  have h2 : a i * u i ≤ ∑ j, a j * u j :=
    Finset.single_le_sum (f := fun j => a j * u j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

/-- The empty list: `q_∅(k) = 1` if `k = 0` and `0` otherwise. -/
theorem denumerant_fin_zero (a : Fin 0 → ℕ) (k : ℕ) :
    denumerant a k = if k = 0 then 1 else 0 := by
  unfold denumerant
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  split_ifs with hk
  · subst hk
    simp
  · have : {u : Fin 0 → ℕ | 0 = k} = ∅ := by
      ext u; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; omega
    rw [this, Set.ncard_empty]

/-- Splitting off the first weight of `Fin.cons m a`. -/
theorem sum_cons {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (u : Fin (n + 1) → ℕ) :
    ∑ i, (Fin.cons m a : Fin (n + 1) → ℕ) i * u i = m * u 0 + ∑ i, a i * u i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- First-part recursion: for `m > 0` and positive `a`,
`q_{(m, a)}(k) = q_a(k) + [m ≤ k] · q_{(m, a)}(k - m)`
(split on whether the first coordinate vanishes). -/
theorem denumerant_cons {n : ℕ} (m : ℕ) (hm : 0 < m) (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (k : ℕ) :
    denumerant (Fin.cons m a : Fin (n + 1) → ℕ) k =
      denumerant a k + if m ≤ k then denumerant (Fin.cons m a : Fin (n + 1) → ℕ) (k - m)
        else 0 := by
  have hpos : ∀ i, 0 < (Fin.cons m a : Fin (n + 1) → ℕ) i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hm
    · intro j; simpa using ha j
  set S := {u : Fin (n + 1) → ℕ | ∑ i, (Fin.cons m a : Fin (n + 1) → ℕ) i * u i = k} with hSdef
  have hS : S.Finite := finite_solutions _ hpos k
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard S {u | u 0 = 0} hS
  unfold denumerant
  rw [← hSdef, ← hsplit]
  congr 1
  · apply Set.ncard_congr (fun u _ => Fin.tail u)
    · intro u hu
      simp only [hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq, sum_cons] at hu ⊢
      rw [hu.2, mul_zero, zero_add] at hu
      exact hu.1
    · intro u v hu hv huv
      simp only [hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hu hv
      rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, huv, hu.2, hv.2]
    · intro w hw
      refine ⟨Fin.cons 0 w, ?_, Fin.tail_cons _ _⟩
      simp only [hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq, sum_cons, Fin.cons_zero,
        Fin.cons_succ] at hw ⊢
      simpa using hw
  · split_ifs with hmk
    · apply Set.ncard_congr (fun u _ => (Fin.cons (u 0 - 1) (Fin.tail u) : Fin (n + 1) → ℕ))
      · intro u hu
        simp only [hSdef, Set.mem_sdiff, Set.mem_ofPred_eq, sum_cons] at hu ⊢
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
        obtain ⟨h1, h2⟩ := hu
        have h3 : m * (u 0 - 1) + m = m * u 0 := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      · intro u v hu hv huv
        simp only [hSdef, Set.mem_sdiff, Set.mem_ofPred_eq] at hu hv
        have h0 := congrFun huv 0
        have ht : Fin.tail u = Fin.tail v := by
          funext i; have := congrFun huv i.succ; simpa using this
        simp only [Fin.cons_zero] at h0
        rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, ht]
        congr 1
        omega
      · intro w hw
        refine ⟨Fin.cons (w 0 + 1) (Fin.tail w), ?_, ?_⟩
        · simp only [hSdef, Set.mem_sdiff, Set.mem_ofPred_eq, sum_cons, Fin.cons_zero,
            Fin.cons_succ] at hw ⊢
          refine ⟨?_, by omega⟩
          simp only [Fin.tail] at hw ⊢
          rw [Nat.mul_succ]
          omega
        · simp
    · rw [Set.ncard_eq_zero (hs := hS.sdiff)]
      ext u
      simp only [hSdef, Set.mem_sdiff, Set.mem_ofPred_eq, sum_cons, Set.mem_empty_iff_false,
        iff_false, not_and, not_not]
      intro hu
      by_contra h0
      have : m ≤ m * u 0 := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
      omega


/-- `q_a` is invariant under reordering the parts. -/
theorem denumerant_comp_equiv {n : ℕ} (a : Fin n → ℕ) (σ : Fin n ≃ Fin n) (k : ℕ) :
    denumerant (a ∘ σ) k = denumerant a k := by
  unfold denumerant
  have hsum : ∀ u : Fin n → ℕ, ∑ i, a i * u (σ.symm i) = ∑ i, (a ∘ σ) i * u i := by
    intro u
    simpa using (Equiv.sum_comp σ (fun i => a i * u (σ.symm i))).symm
  apply Set.ncard_congr (fun u _ => u ∘ σ.symm)
  · intro u hu
    simp only [Set.mem_ofPred_eq, Function.comp_apply] at hu ⊢
    rw [hsum]
    exact hu
  · intro u v _ _ huv
    funext i
    simpa using congrFun huv (σ i)
  · intro w hw
    refine ⟨w ∘ σ, ?_, by funext i; simp⟩
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [← hsum]
    simpa using hw

/-- Two functions satisfying the same recurrence `F k = G k + [m ≤ k] F (k - m)`
with `m > 0` coincide. -/
theorem eq_of_recurrence (m : ℕ) (hm : 0 < m) (G F H : ℕ → ℚ)
    (hF : ∀ k, F k = G k + if m ≤ k then F (k - m) else 0)
    (hH : ∀ k, H k = G k + if m ≤ k then H (k - m) else 0) : ∀ k, F k = H k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [hF, hH]
    split_ifs with hk
    · rw [ih (k - m) (by omega)]
    · rfl

/-- Closed form of `q_{(2)}`. -/
def H1 (k : ℕ) : ℚ := (1 + (-1) ^ k) / 2
/-- Closed form of `q_{(2,2)}`. -/
def H2 (k : ℕ) : ℚ := ((k : ℚ) / 4 + 1 / 2) * (1 + (-1) ^ k)
/-- Closed form of `q_{(2,2,2)}`. -/
def H3 (k : ℕ) : ℚ := ((k : ℚ) ^ 2 / 16 + 3 / 8 * k + 1 / 2) * (1 + (-1) ^ k)
/-- Closed form of `q_{(2,2,2,2)}`. -/
def H4 (k : ℕ) : ℚ := ((k : ℚ) ^ 3 / 96 + (k : ℚ) ^ 2 / 8 + 11 / 24 * k + 1 / 2) * (1 + (-1) ^ k)
/-- Closed form of `q_{(1,2,2,2,2)}` (Sage fit, verified below). -/
def H5 (k : ℕ) : ℚ :=
  ((k : ℚ) ^ 4 / 384 + 3 / 64 * (k : ℚ) ^ 3 + 113 / 384 * (k : ℚ) ^ 2 + 3 / 4 * k + 163 / 256) +
  (-1) ^ k * ((k : ℚ) ^ 3 / 192 + 9 / 128 * (k : ℚ) ^ 2 + 7 / 24 * k + 93 / 256)
/-- Closed form of `q_{(1,1,2,2,2,2)}` (Sage fit, verified below). -/
def H6 (k : ℕ) : ℚ :=
  ((k : ℚ) ^ 5 / 1920 + 5 / 384 * (k : ℚ) ^ 4 + 47 / 384 * (k : ℚ) ^ 3 + 205 / 384 * (k : ℚ) ^ 2
    + 4073 / 3840 * k + 191 / 256) +
  (-1) ^ k * ((k : ℚ) ^ 3 / 384 + 5 / 128 * (k : ℚ) ^ 2 + 139 / 768 * k + 65 / 256)

/-- `H1` satisfies the recurrence for adding the part `2` to the empty list. -/
theorem H1_rec (k : ℕ) : H1 k = (if k = 0 then 1 else 0) + if 2 ≤ k then H1 (k - 2) else 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num [H1]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_neg (by omega : j + 2 ≠ 0), if_pos (by omega : 2 ≤ j + 2), Nat.add_sub_cancel]
    simp only [H1, pow_add]
    ring

/-- `H2` satisfies the recurrence for adding a part `2` to `(2)`. -/
theorem H2_rec (k : ℕ) : H2 k = H1 k + if 2 ≤ k then H2 (k - 2) else 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num [H1, H2]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    simp only [H1, H2, pow_add]
    push_cast
    ring

/-- `H3` satisfies the recurrence for adding a part `2` to `(2,2)`. -/
theorem H3_rec (k : ℕ) : H3 k = H2 k + if 2 ≤ k then H3 (k - 2) else 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num [H3, H2]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    simp only [H3, H2, pow_add]
    push_cast
    ring

/-- `H4` satisfies the recurrence for adding a part `2` to `(2,2,2)`. -/
theorem H4_rec (k : ℕ) : H4 k = H3 k + if 2 ≤ k then H4 (k - 2) else 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num [H3, H4]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    simp only [H3, H4, pow_add]
    push_cast
    ring

/-- `H5` satisfies the recurrence for adding a part `1` to `(2,2,2,2)`. -/
theorem H5_rec (k : ℕ) : H5 k = H4 k + if 1 ≤ k then H5 (k - 1) else 0 := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · interval_cases k; norm_num [H5, H4]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    rcases Nat.even_or_odd j with hj | hj
    · simp only [H5, H4, pow_add, hj.neg_one_pow]
      push_cast
      ring
    · simp only [H5, H4, pow_add, hj.neg_one_pow]
      push_cast
      ring

/-- `H6` satisfies the recurrence for adding a part `1` to `(1,2,2,2,2)`. -/
theorem H6_rec (k : ℕ) : H6 k = H5 k + if 1 ≤ k then H6 (k - 1) else 0 := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · interval_cases k; norm_num [H5, H6]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    rcases Nat.even_or_odd j with hj | hj
    · simp only [H5, H6, pow_add, hj.neg_one_pow]
      push_cast
      ring
    · simp only [H5, H6, pow_add, hj.neg_one_pow]
      push_cast
      ring


/-- Values `c₀(0), …, c₀(12)` of the constant coefficient function for
`a = (1,1,2,2,2,2,13)` (Sage fit; the fit shows `c₀` is `13`-periodic). -/
def c0nat : ℕ → ℚ
  | 0 => 1
  | 1 => 11 / 13
  | 2 => 11 / 13
  | 3 => 1
  | 4 => 0
  | 5 => 7 / 13
  | 6 => -14 / 13
  | 7 => 0
  | 8 => -21 / 13
  | 9 => 0
  | 10 => -14 / 13
  | 11 => 7 / 13
  | _ => 0

/-- The constant coefficient function `c₀ : ℤ → ℚ`, extended `13`-periodically. -/
def c0tab (k : ℤ) : ℚ := c0nat (k % 13).toNat

/-- `c₀` at a natural number reads the table at its residue mod `13`. -/
theorem c0tab_natCast (n : ℕ) : c0tab n = c0nat (n % 13) := by
  unfold c0tab
  rw [show (13 : ℤ) = ((13 : ℕ) : ℤ) from rfl, ← Int.natCast_mod, Int.toNat_natCast]

/-- Explicit coefficient functions `c₀, …, c₆ : ℤ → ℚ` of the quasi-polynomial
`q_{(1,1,2,2,2,2,13)}(k) = ∑ⱼ cⱼ(k) kʲ`; `c₁, c₂, c₃` depend on the parity of `k`,
`c₄, c₅, c₆` are constant and `c₀` is `13`-periodic. -/
def bswCoeff : Fin 7 → ℤ → ℚ
  | 0, k => c0tab k
  | 1, k => if Even k then 1771 / 1560 else 7429 / 16640
  | 2, k => if Even k then 12263 / 18720 else 84649 / 149760
  | 3, k => if Even k then 331 / 2496 else 649 / 4992
  | 4, _ => 175 / 14976
  | 5, _ => 23 / 49920
  | 6, _ => 1 / 149760

/-- The candidate quasi-polynomial `∑ⱼ cⱼ(k) kʲ` for `a = (1,1,2,2,2,2,13)`. -/
def H7 (k : ℕ) : ℚ := ∑ j : Fin 7, bswCoeff j k * (k : ℚ) ^ (j : ℕ)

/-- `c₀` has period `13`. -/
theorem c0tab_add_13 (k : ℤ) : c0tab (k + 13) = c0tab k := by
  unfold c0tab
  rw [Int.add_emod_right]

/-- `H7` satisfies the recurrence for adding the part `13` to `(1,1,2,2,2,2)`;
the `c₀` terms cancel because `c₀(k + 13) = c₀(k)`. -/
theorem H7_rec (k : ℕ) : H7 k = H6 k + if 13 ≤ k then H7 (k - 13) else 0 := by
  rcases Nat.lt_or_ge k 13 with hk | hk
  · rw [if_neg (by omega)]
    simp only [H7, Fin.sum_univ_seven, bswCoeff, c0tab_natCast]
    interval_cases k <;> norm_num [H6, c0nat, Int.even_iff]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [if_pos (by omega), Nat.add_sub_cancel]
    have hc0 : c0tab ((j + 13 : ℕ) : ℤ) = c0tab (j : ℤ) := by
      push_cast; exact c0tab_add_13 _
    rcases Nat.even_or_odd j with hj | hj
    · have he : Even ((j : ℕ) : ℤ) := by simpa using hj
      have ho : ¬ Even (((j + 13 : ℕ)) : ℤ) := by
        push_cast; rw [Int.even_add]; simp [he]; decide
      simp only [H7, H6, Fin.sum_univ_seven, bswCoeff, hc0, if_pos he, if_neg ho, pow_add,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod,
        hj.neg_one_pow]
      push_cast
      ring
    · have he : ¬ Even ((j : ℕ) : ℤ) := by simpa [Nat.not_even_iff_odd] using hj
      have ho : Even (((j + 13 : ℕ)) : ℤ) := by
        push_cast; rw [Int.even_add]; simp [he]; decide
      simp only [H7, H6, Fin.sum_univ_seven, bswCoeff, hc0, if_neg he, if_pos ho, pow_add,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod,
        hj.neg_one_pow]
      push_cast
      ring


/-- One level of the inductive construction: a closed form for `q_a` and a
function satisfying the `m`-recurrence give a closed form for `q_{(m, a)}`. -/
theorem level_step {n : ℕ} (m : ℕ) (hm : 0 < m) (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (G H : ℕ → ℚ) (hG : ∀ k, (denumerant a k : ℚ) = G k)
    (hH : ∀ k, H k = G k + if m ≤ k then H (k - m) else 0) :
    ∀ k, (denumerant (Fin.cons m a : Fin (n + 1) → ℕ) k : ℚ) = H k := by
  apply eq_of_recurrence m hm G _ H _ hH
  intro k
  rw [denumerant_cons m hm a ha k]
  push_cast
  rw [hG]

/-- `denumerant_fin_zero` cast to `ℚ`. -/
theorem denumerant_fin_zero_cast (a : Fin 0 → ℕ) (k : ℕ) :
    (denumerant a k : ℚ) = if k = 0 then 1 else 0 := by
  rw [denumerant_fin_zero]; split_ifs <;> simp

/-- Closed form of `q_{(13,1,1,2,2,2,2)}`. -/
theorem denumerant_rotated (k : ℕ) :
    (denumerant ![13, 1, 1, 2, 2, 2, 2] k : ℚ) = H7 k := by
  have l1 : ∀ k, (denumerant ![2] k : ℚ) = H1 k :=
    level_step 2 (by norm_num) ![] (fun i => i.elim0) _ H1 (denumerant_fin_zero_cast _) H1_rec
  have l2 : ∀ k, (denumerant ![2, 2] k : ℚ) = H2 k :=
    level_step 2 (by norm_num) ![2] (by decide) _ H2 l1 H2_rec
  have l3 : ∀ k, (denumerant ![2, 2, 2] k : ℚ) = H3 k :=
    level_step 2 (by norm_num) ![2, 2] (by decide) _ H3 l2 H3_rec
  have l4 : ∀ k, (denumerant ![2, 2, 2, 2] k : ℚ) = H4 k :=
    level_step 2 (by norm_num) ![2, 2, 2] (by decide) _ H4 l3 H4_rec
  have l5 : ∀ k, (denumerant ![1, 2, 2, 2, 2] k : ℚ) = H5 k :=
    level_step 1 (by norm_num) ![2, 2, 2, 2] (by decide) _ H5 l4 H5_rec
  have l6 : ∀ k, (denumerant ![1, 1, 2, 2, 2, 2] k : ℚ) = H6 k :=
    level_step 1 (by norm_num) ![1, 2, 2, 2, 2] (by decide) _ H6 l5 H6_rec
  exact level_step 13 (by norm_num) ![1, 1, 2, 2, 2, 2] (by decide) _ H7 l6 H7_rec k

/-- The reordering `(1,1,2,2,2,2,13) ↦ (13,1,1,2,2,2,2)`. -/
theorem rotate_eq : (![1, 1, 2, 2, 2, 2, 13] : Fin 7 → ℕ) ∘ (finRotate 7).symm =
    ![13, 1, 1, 2, 2, 2, 2] := by
  funext i; fin_cases i <;> rfl

/-- **The explicit expansion.** For every `k : ℕ`,
`q_{(1,1,2,2,2,2,13)}(k) = ∑_{j<7} cⱼ(k) kʲ` with the explicit `cⱼ = bswCoeff j`. -/
theorem expansion_rat (k : ℕ) :
    (denumerant ![1, 1, 2, 2, 2, 2, 13] k : ℚ) = ∑ j : Fin 7, bswCoeff j k * (k : ℚ) ^ (j : ℕ) := by
  rw [← denumerant_comp_equiv _ (finRotate 7).symm, rotate_eq, denumerant_rotated]
  rfl

/-- Every `cⱼ` has period `26`. -/
theorem bswCoeff_periodic (j : Fin 7) : Function.Periodic (bswCoeff j) 26 := by
  intro k
  have he : Even (k + 26) ↔ Even k := by
    simp [Int.even_add, show Even (26 : ℤ) from ⟨13, rfl⟩]
  fin_cases j
  · show c0tab (k + 26) = c0tab k
    rw [show k + 26 = k + 13 + 13 by ring, c0tab_add_13, c0tab_add_13]
  all_goals simp [bswCoeff, he]

/-- The constant coefficient `c₀` has period `13`. -/
theorem bswCoeff_zero_periodic : Function.Periodic (bswCoeff 0) 13 := c0tab_add_13


/-- A function with period `N` has every multiple of `N` as a period. -/
theorem periodic_of_dvd {f : ℤ → ℂ} {N M : ℕ} (hf : Function.Periodic f (N : ℤ)) (h : N ∣ M) :
    Function.Periodic f (M : ℤ) := by
  obtain ⟨d, rfl⟩ := h
  have := hf.nat_mul d
  simpa [Nat.cast_mul, mul_comm] using this

/-- **Uniqueness of the quasi-polynomial coefficients** (paper, Section 1):
if `w₀, …, w_{n-1} : ℤ → ℂ` are periodic and `∑ⱼ wⱼ(k) kʲ = 0` for all `k ≥ 0`,
then every `wⱼ` vanishes identically. -/
theorem expansion_unique {n : ℕ} (w : Fin n → ℤ → ℂ)
    (hw : ∀ j, ∃ N : ℕ, 0 < N ∧ Function.Periodic (w j) (N : ℤ))
    (h : ∀ k : ℕ, ∑ j, w j k * (k : ℂ) ^ (j : ℕ) = 0) : ∀ j k, w j k = 0 := by
  choose N hNpos hNper using hw
  set P : ℕ := ∏ j, N j with hP
  have hPpos : 0 < P := Finset.prod_pos (fun j _ => hNpos j)
  have hper : ∀ j, Function.Periodic (w j) (P : ℤ) := fun j =>
    periodic_of_dvd (hNper j) (Finset.dvd_prod_of_mem N (Finset.mem_univ j))
  -- each residue class
  have hres : ∀ r : ℕ, ∀ j, w j r = 0 := by
    intro r
    let p : Polynomial ℂ := ∑ j : Fin n, Polynomial.C (w j r) * Polynomial.X ^ (j : ℕ)
    have hroot : ∀ t : ℕ, p.IsRoot ((r + P * t : ℕ) : ℂ) := by
      intro t
      have hk := h (r + P * t)
      simp only [Polynomial.IsRoot, p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← hk]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      have := (hper j).nat_mul t (r : ℤ)
      push_cast at this ⊢
      rw [show (r : ℤ) + (P : ℤ) * t = r + t * P by ring, this]
    have hp : p = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => ((r + P * t : ℕ) : ℂ))
      · intro t t' htt
        simp only at htt
        have h1 : r + P * t = r + P * t' := by exact_mod_cast htt
        have h2 : P * t = P * t' := by omega
        exact Nat.eq_of_mul_eq_mul_left hPpos h2
      · exact hroot
    intro j
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff j) hp
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j (fun b _ hb => if_neg (fun hjb => hb (Fin.ext hjb.symm)))
      (fun hj => absurd (Finset.mem_univ j) hj), if_pos rfl] at hc
    exact hc
  intro j k
  have hkdecomp : k = (((k % (P : ℤ)).toNat : ℕ) : ℤ) + (k / P) * P := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hPpos.ne'))]
    rw [mul_comm]; exact (Int.emod_add_mul_ediv k P).symm
  have hshift := (hper j).int_mul (k / P) (((k % (P : ℤ)).toNat : ℕ) : ℤ)
  simp only [Int.cast_id] at hshift
  rw [hkdecomp, hshift]
  exact hres _ j

/-! ## The Beck–Sam–Woods conjecture -/

/-- `b_m = #{i : m ∣ aᵢ}`. -/
def bCount {n : ℕ} (a : Fin n → ℕ) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => m ∣ a i)).card

/-- The index set `{m ∈ ℤ_{>0} : b_m > j}` of `p_j`, cut off at `max aᵢ`; for
positive weights the cut-off loses nothing (`mem_bswSupport_iff`). -/
def bswSupport {n : ℕ} (a : Fin n → ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Finset.univ.sup a)).filter (fun m => j < bCount a m)

/-- The Beck–Sam–Woods predicted period `p_j = lcm{m ∈ ℤ_{>0} : b_m > j}`. -/
def bswP {n : ℕ} (a : Fin n → ℕ) (j : ℕ) : ℕ :=
  (bswSupport a j).lcm id

/-- For positive weights, `bswSupport a j` is exactly `{m : 0 < m ∧ j < b_m}`. -/
theorem mem_bswSupport_iff {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (j m : ℕ) :
    m ∈ bswSupport a j ↔ 0 < m ∧ j < bCount a m := by
  unfold bswSupport
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have hne : (Finset.univ.filter (fun i => m ∣ a i)).Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le j) h2)
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_filter] at hi
    exact (Nat.le_of_dvd (ha i) hi.2).trans (Finset.le_sup (f := a) (Finset.mem_univ i))

/-- `c : Fin n → ℤ → ℂ` is a quasi-polynomial expansion of `q_a`: every `cⱼ` is
periodic and `q_a(k) = ∑_{j<n} cⱼ(k) kʲ` for every `k ≥ 0`. -/
def IsQuasiPolyExpansion {n : ℕ} (a : Fin n → ℕ) (c : Fin n → ℤ → ℂ) : Prop :=
  (∀ j, ∃ N : ℕ, 0 < N ∧ Function.Periodic (c j) (N : ℤ)) ∧
    ∀ k : ℕ, (denumerant a k : ℂ) = ∑ j, c j k * (k : ℂ) ^ (j : ℕ)

/-- `T` is the minimum (positive) period of `f : ℤ → ℂ`. -/
def IsMinPeriod (f : ℤ → ℂ) (T : ℕ) : Prop :=
  0 < T ∧ Function.Periodic f (T : ℤ) ∧
    ∀ T' : ℕ, 0 < T' → Function.Periodic f (T' : ℤ) → T ≤ T'

/-- **Conjecture 1.1 (Beck–Sam–Woods 2008, Conjecture 11)** for the weight vector `a`:
the coefficient functions `cⱼ` of `q_a` have minimum period `p_j`. -/
def BSWConjecture {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∀ c : Fin n → ℤ → ℂ, IsQuasiPolyExpansion a c → ∀ j : Fin n, IsMinPeriod (c j) (bswP a j)

/-- The paper's counterexample `a = (1,1,2,2,2,2,13)`, i.e. `(u, M) = (2, 13)`. -/
def bswA : Fin 7 → ℕ := ![1, 1, 2, 2, 2, 2, 13]

example : bCount bswA 1 = 7 := by decide
example : bCount bswA 2 = 4 := by decide
example : bCount bswA 13 = 1 := by decide
example : bswP bswA 1 = 2 := by decide
example : bswP bswA 4 = 1 := by decide
example : (denumerant bswA 2 : ℚ) = 7 := by
  rw [bswA, expansion_rat]
  simp only [Fin.sum_univ_seven, bswCoeff, c0tab_natCast]
  norm_num [c0nat, Int.even_iff]
example : (denumerant bswA 13 : ℚ) = 925 := by
  rw [bswA, expansion_rat]
  simp only [Fin.sum_univ_seven, bswCoeff, c0tab_natCast]
  norm_num [c0nat, Int.even_iff]
example : bswCoeff 0 1 = 11 / 13 := by norm_num [bswCoeff, c0tab, c0nat]
example : bswCoeff 1 3 = 7429 / 16640 := by norm_num [bswCoeff, Int.even_iff]

/-- `p_0 = lcm{1, 2, 13} = 26` for `a = (1,1,2,2,2,2,13)`. -/
theorem bswP_bswA_zero : bswP bswA 0 = 26 := by decide

/-- The explicit coefficients form a quasi-polynomial expansion of `q_{(1,1,2,2,2,2,13)}`. -/
theorem isQuasiPolyExpansion_bswCoeff :
    IsQuasiPolyExpansion bswA (fun j k => (bswCoeff j k : ℂ)) := by
  refine ⟨fun j => ⟨26, by norm_num, ?_⟩, fun k => ?_⟩
  · intro x
    simp only
    rw [show ((26 : ℕ) : ℤ) = 26 from rfl, bswCoeff_periodic j x]
  · have h := congrArg (fun q : ℚ => (q : ℂ)) (expansion_rat k)
    simp only [Rat.cast_natCast, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow] at h
    simpa [bswA] using h

/-- Every quasi-polynomial expansion of `q_{(1,1,2,2,2,2,13)}` equals the explicit one. -/
theorem eq_bswCoeff_of_isQuasiPolyExpansion (c : Fin 7 → ℤ → ℂ)
    (hc : IsQuasiPolyExpansion bswA c) : ∀ j k, c j k = (bswCoeff j k : ℂ) := by
  obtain ⟨hper, hexp⟩ := hc
  obtain ⟨-, hexp'⟩ := isQuasiPolyExpansion_bswCoeff
  have hzero := expansion_unique (fun j k => c j k - (bswCoeff j k : ℂ)) ?_ ?_
  · intro j k
    exact sub_eq_zero.mp (hzero j k)
  · intro j
    obtain ⟨N, hN, hNper⟩ := hper j
    refine ⟨N * 26, by positivity, ?_⟩
    intro x
    have h1 : c j (x + ((N * 26 : ℕ) : ℤ)) = c j x :=
      periodic_of_dvd hNper (Dvd.intro 26 rfl) x
    have h2 : bswCoeff j (x + ((N * 26 : ℕ) : ℤ)) = bswCoeff j x := by
      have := (bswCoeff_periodic j).nat_mul N x
      simpa [Nat.cast_mul] using this
    simp only [h1, h2]
  · intro k
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← hexp k, ← hexp' k, sub_self]

/-- A period that is coprime to a known period forces period `1`. -/
theorem periodic_one_of_coprime {f : ℤ → ℂ} {S T : ℕ} (hS : Function.Periodic f (S : ℤ))
    (hT : Function.Periodic f (T : ℤ)) (hST : Nat.Coprime S T) : Function.Periodic f 1 := by
  have hgcd : ((Nat.gcd S T : ℕ) : ℤ) = S * Nat.gcdA S T + T * Nat.gcdB S T :=
    Nat.gcd_eq_gcd_ab S T
  rw [hST.gcd_eq_one, Nat.cast_one] at hgcd
  have h := (hS.int_mul (Nat.gcdA S T)).add_period (hT.int_mul (Nat.gcdB S T))
  simp only [Int.cast_id] at h
  have e : (S : ℤ) * Nat.gcdA S T + T * Nat.gcdB S T =
      Nat.gcdA S T * S + Nat.gcdB S T * T := by ring
  rw [hgcd, e]
  exact h

/-- **Theorem 1.3 at `(u, M) = (2, 13)` (arXiv:2608.02085).**  For every
quasi-polynomial expansion `q_{(1,1,2,2,2,2,13)}(k) = ∑ⱼ cⱼ(k) kʲ`, the constant
coefficient `c₀` has minimum period `13`. -/
theorem isMinPeriod_thirteen (c : Fin 7 → ℤ → ℂ) (hc : IsQuasiPolyExpansion bswA c) :
    IsMinPeriod (c 0) 13 := by
  have hcE := eq_bswCoeff_of_isQuasiPolyExpansion c hc
  have h13 : Function.Periodic (c 0) ((13 : ℕ) : ℤ) := by
    intro x
    rw [hcE, hcE]
    exact congrArg (fun q : ℚ => (q : ℂ)) (bswCoeff_zero_periodic x)
  refine ⟨by norm_num, h13, fun T hT hTper => ?_⟩
  by_contra hlt
  push Not at hlt
  have hcop : Nat.Coprime T 13 := by
    interval_cases T <;> decide
  have h1 := periodic_one_of_coprime hTper h13 hcop 0
  rw [zero_add, hcE, hcE] at h1
  have hv0 : bswCoeff 0 0 = 1 := by norm_num [bswCoeff, c0tab, c0nat]
  have hv1 : bswCoeff 0 1 = 11 / 13 := by norm_num [bswCoeff, c0tab, c0nat]
  rw [hv0, hv1] at h1
  norm_num at h1

/-- **Counterexample to the Beck–Sam–Woods conjecture (arXiv:2608.02085, Theorem 1.3
with `(u, M) = (2, 13)`).**  For `a = (1,1,2,2,2,2,13)`: a quasi-polynomial
expansion of `q_a` exists, every such expansion has `per(c₀) = 13`, and the
conjectured value is `p₀ = 26`. -/
theorem thm_1_3_two_thirteen :
    (∃ c : Fin 7 → ℤ → ℂ, IsQuasiPolyExpansion bswA c) ∧
      (∀ c : Fin 7 → ℤ → ℂ, IsQuasiPolyExpansion bswA c → IsMinPeriod (c 0) 13) ∧
      bswP bswA 0 = 26 :=
  ⟨⟨_, isQuasiPolyExpansion_bswCoeff⟩, isMinPeriod_thirteen, bswP_bswA_zero⟩

/-- **The Beck–Sam–Woods minimum-period conjecture is false** (arXiv:2608.02085):
it fails for `a = (1,1,2,2,2,2,13)` and `j = 0`. -/
theorem not_bswConjecture : ¬ BSWConjecture bswA := by
  intro h
  obtain ⟨c, hc⟩ := thm_1_3_two_thirteen.1
  have h26 := h c hc 0
  rw [show ((0 : Fin 7) : ℕ) = 0 from rfl, bswP_bswA_zero] at h26
  have h13 := isMinPeriod_thirteen c hc
  have hle := h13.2.2 26 (by norm_num) h26.2.1
  have hle' := h26.2.2 13 (by norm_num) h13.2.1
  omega

end Candidates.BeckSamWoodsCounterexamples
