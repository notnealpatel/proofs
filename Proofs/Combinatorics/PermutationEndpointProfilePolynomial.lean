import Combinatorics.PermutationEndpointProfileCoefficient
import Combinatorics.PermutationTwoAnchorFraction

set_option autoImplicit false

namespace PermutationEndpointProfile

attribute [local instance] Classical.propDecidable

/-- Binomial weights divided by the actual descending denominator approximate
three continuous powers, including populations below their selected ranks. -/
theorem choose_three_error (m₀ m₁ m₂ r q h s n : ℕ)
    (hn : 2 ≤ n) (hs : s ≤ n - 2) (hlarge : s * (s + 3) ≤ n)
    (hm₀ : m₀ ≤ n) (hm₁ : m₁ + 1 ≤ n) (hm₂ : m₂ + 1 ≤ n)
    (hrs : r + q + h = s) :
    |((m₀.choose r : ℝ) * (m₁.choose q : ℝ) * (m₂.choose h : ℝ)) /
        ((n - 2).descFactorial s : ℝ) -
      (((m₀ : ℝ)/n)^r * (((m₁ : ℝ)+1)/n)^q * (((m₂ : ℝ)+1)/n)^h) /
        ((r.factorial : ℝ) * q.factorial * h.factorial)| ≤
      2 * (s : ℝ) * ((s : ℝ)+2) / n := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hd : ((n - 2).descFactorial s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hs).ne'
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hh : (h.factorial : ℝ) ≠ 0 := by positivity
  have hw : 1 ≤ (r.factorial : ℝ) * q.factorial * h.factorial := by
    have hr1 : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hq1 : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    have hh1 : (1 : ℝ) ≤ h.factorial := by exact_mod_cast Nat.factorial_pos h
    nlinarith [mul_le_mul hr1 hq1 (by positivity : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ r.factorial)]
  have he := three_block_normalized_error m₀ m₁ m₂ r q h s n hn hs hlarge hm₀ hm₁ hm₂ hrs
  have hp : (n : ℝ)^s = (n : ℝ)^r * (n : ℝ)^q * (n : ℝ)^h := by
    rw [← hrs, pow_add, pow_add]
  have hid :
      (((m₀.descFactorial r : ℝ)/(n:ℝ)^r) *
        ((m₁.descFactorial q : ℝ)/(n:ℝ)^q) *
        ((m₂.descFactorial h : ℝ)/(n:ℝ)^h)) /
        (((n-2).descFactorial s : ℝ)/(n:ℝ)^s) =
      ((r.factorial : ℝ) * q.factorial * h.factorial) *
        (((m₀.choose r : ℝ) * (m₁.choose q : ℝ) * (m₂.choose h : ℝ)) /
          ((n-2).descFactorial s : ℝ)) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    rw [hp]
    field_simp
  rw [hid] at he
  let W : ℝ := (r.factorial : ℝ) * q.factorial * h.factorial
  have hW : 0 < W := by dsimp [W]; positivity
  have he' := div_le_div_of_nonneg_right he hW.le
  have hid' (A U : ℝ) : |W*A-U|/W = |A-U/W| := by
    have ha := abs_div (W*A-U) W
    rw [abs_of_pos hW] at ha
    rw [← ha]
    congr 1
    field_simp
  rw [hid'] at he'
  exact he'.trans (div_le_self (by positivity) hw)

example : 2 ≤ 10 ∧ 2 ≤ 10 - 2 ∧ 2 * (2 + 3) ≤ 10 ∧
    0 ≤ 10 ∧ 0 + 1 ≤ 10 ∧ 0 + 1 ≤ 10 ∧ 1 + 1 + 0 = 2 := by decide

/-- Continuous polynomial obtained from the actual increasing-endpoint safe
patterns in the boundary of size `L`, at prescribed first and last positions. -/
noncomputable def patternPolynomial (K L : ℕ) (i j : Fin L) (x y : ℝ) : ℝ :=
  ∑ σ : {σ : Equiv.Perm (Fin L) //
      PermutationBoundaryStandardization.ShortAvoid K σ ∧ σ i < σ j},
    x ^ (σ.val i).val * (y-x) ^ ((σ.val j).val - (σ.val i).val - 1) *
      (1-y) ^ (L-1-(σ.val j).val) /
      (((σ.val i).val.factorial : ℝ) *
        ((σ.val j).val - (σ.val i).val - 1).factorial *
        (L-1-(σ.val j).val).factorial)

example (K L : ℕ) (i : Fin L) (x y : ℝ) :
    patternPolynomial K L i i x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro σ hσ
  exact False.elim ((lt_irrefl (σ.val i)) σ.property.2)

/-- Each actual boundary polynomial is continuous, including on the diagonal. -/
theorem continuous_patternPolynomial (K L : ℕ) (i j : Fin L) :
    Continuous (fun z : ℝ × ℝ => patternPolynomial K L i j z.1 z.2) := by
  classical
  unfold patternPolynomial
  fun_prop

/-- Specializing the polynomial to minimum and maximum coordinates gives a
continuous symmetric function on the entire plane. -/
theorem continuous_patternPolynomial_min_max (K L : ℕ) (i j : Fin L) :
    Continuous (fun z : ℝ × ℝ =>
      patternPolynomial K L i j (min z.1 z.2) (max z.1 z.2)) := by
  exact (continuous_patternPolynomial K L i j).comp
    ((continuous_fst.min continuous_snd).prodMk (continuous_fst.max continuous_snd))

/-- The ordered endpoint binomial sum approximates its continuous polynomial
uniformly in both labels with at most `L!` summands. -/
theorem binomial_sum_error (K L n : ℕ) (hL : 2 ≤ L) (hLn : L ≤ n)
    (hlarge : (L-2) * (L-2+3) ≤ n) (i j : Fin L) (a b : Fin n) (hab : a < b) :
    |((∑ σ : {σ : Equiv.Perm (Fin L) //
        PermutationBoundaryStandardization.ShortAvoid K σ ∧ σ i < σ j},
      a.val.choose (σ.val i).val *
        (b.val-a.val-1).choose ((σ.val j).val-(σ.val i).val-1) *
        (n-1-b.val).choose (L-1-(σ.val j).val) : ℕ) : ℝ) /
        ((n-2).descFactorial (L-2) : ℝ) -
      patternPolynomial K L i j ((a.val : ℝ)/n) ((b.val : ℝ)/n)| ≤
      (L.factorial : ℝ) * (2 * (L-2 : ℕ) * ((L-2 : ℕ)+2) / n) := by
  classical
  let S := {σ : Equiv.Perm (Fin L) //
    PermutationBoundaryStandardization.ShortAvoid K σ ∧ σ i < σ j}
  have habv : a.val < b.val := hab
  have hbv : b.val < n := b.isLt
  have h₁ : ((b.val-a.val-1 : ℕ) : ℝ)+1 = (b.val : ℝ)-a.val := by
    rw [Nat.cast_sub (by omega : 1 ≤ b.val-a.val), Nat.cast_sub (by omega : a.val ≤ b.val)]
    norm_num
  have h₂ : ((n-1-b.val : ℕ) : ℝ)+1 = (n : ℝ)-b.val := by
    rw [Nat.cast_sub (by omega : b.val ≤ n-1), Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    ring
  have hterm (σ : S) :
      |((a.val.choose (σ.val i).val : ℝ) *
        ((b.val-a.val-1).choose ((σ.val j).val-(σ.val i).val-1) : ℝ) *
        ((n-1-b.val).choose (L-1-(σ.val j).val) : ℝ)) /
          ((n-2).descFactorial (L-2) : ℝ) -
        (((a.val : ℝ)/n) ^ (σ.val i).val *
          ((b.val : ℝ)/n-(a.val : ℝ)/n) ^ ((σ.val j).val-(σ.val i).val-1) *
          (1-(b.val : ℝ)/n) ^ (L-1-(σ.val j).val)) /
          (((σ.val i).val.factorial : ℝ) *
            ((σ.val j).val-(σ.val i).val-1).factorial *
            (L-1-(σ.val j).val).factorial)| ≤
        2 * (L-2 : ℕ) * ((L-2 : ℕ)+2) / n := by
    have hrank := σ.property.2
    have hrankv : (σ.val i).val < (σ.val j).val := hrank
    have ht := (σ.val j).isLt
    have he := choose_three_error a.val (b.val-a.val-1) (n-1-b.val)
      (σ.val i).val ((σ.val j).val-(σ.val i).val-1) (L-1-(σ.val j).val)
      (L-2) n (by omega) (by omega) hlarge (by omega) (by omega) (by omega)
      (by omega)
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [h₁, h₂, sub_div, sub_div, div_self hnR] at he
    exact he
  unfold patternPolynomial
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : S, _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : S, (2 * (L-2 : ℕ) * ((L-2 : ℕ)+2) / (n:ℝ)) :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Fintype.card S : ℝ) * (2 * (L-2 : ℕ) * ((L-2 : ℕ)+2) / n) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Nat.cast_le.mpr
      exact (Fintype.card_subtype_le _).trans (by simp [Fintype.card_perm])

example : Nonempty (Fin 4) ∧ 2 ≤ 4 ∧ 4 ≤ 10 ∧ (4-2)*(4-2+3) ≤ 10 := by
  exact ⟨inferInstance, by decide, by decide, by decide⟩

end PermutationEndpointProfile
