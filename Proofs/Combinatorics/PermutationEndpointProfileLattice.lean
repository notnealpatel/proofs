import Combinatorics.PermutationEndpointProfileFinite

set_option autoImplicit false

namespace PermutationEndpointProfile

/-- A clipped natural floor gives a valid endpoint within one lattice spacing
of any point in the closed unit interval, including both endpoints. -/
theorem exists_lattice_endpoint (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∃ a : Fin n, |(a.val : ℝ)/n-x| ≤ 1/(n:ℝ) := by
  let m := ⌊(n:ℝ)*x⌋₊
  let a := min (n-1) m
  have ha : a < n := by dsimp [a]; omega
  refine ⟨⟨a, ha⟩, ?_⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hf : (m:ℝ) ≤ (n:ℝ)*x := Nat.floor_le (mul_nonneg hnR.le hx.1)
  have hg : (n:ℝ)*x < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hnx : (n:ℝ)*x ≤ n := by nlinarith [hx.2]
  have hdiff : |(a:ℝ)-(n:ℝ)*x| ≤ 1 := by
    by_cases hm : m ≤ n-1
    · have he : a = m := min_eq_right hm
      rw [he, abs_of_nonpos (by linarith)]
      linarith
    · have he : a = n-1 := min_eq_left (by omega)
      rw [he, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num only [Nat.cast_one]
      rw [abs_le]
      have hmR : (n:ℝ) ≤ m := by exact_mod_cast (show n ≤ m by omega)
      constructor <;> linarith
  have hid : (a:ℝ)/(n:ℝ)-x = ((a:ℝ)-(n:ℝ)*x)/n := by field_simp
  rw [hid, abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right hdiff hnR.le

/-- Every point of the closed square has jointly valid, distinct lattice
endpoints within two lattice spacings. Equal coordinates and corners are allowed. -/
theorem exists_distinct_lattice_endpoints (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ∃ a b : Fin n, a ≠ b ∧ |(a.val : ℝ)/n-x| ≤ 2/(n:ℝ) ∧
      |(b.val : ℝ)/n-y| ≤ 2/(n:ℝ) := by
  obtain ⟨a, ha⟩ := exists_lattice_endpoint n hn x hx
  obtain ⟨b, hb⟩ := exists_lattice_endpoint n hn y hy
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h12 : 1/(n:ℝ) ≤ 2/(n:ℝ) := div_le_div_of_nonneg_right (by norm_num) hnR.le
  by_cases hab : a = b
  · subst b
    let c : Fin n := if a.val = 0 then ⟨1, by omega⟩ else ⟨a.val-1, by omega⟩
    have hac : a ≠ c := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [c] at hv
      split_ifs at hv with hz
      · simp only [Fin.val_mk] at hv
        omega
      · simp only [Fin.val_mk] at hv
        omega
    have hca : |(c.val:ℝ)-(a.val:ℝ)| ≤ 1 := by
      dsimp [c]
      split_ifs with hz
      · simp [hz]
      · rw [Nat.cast_sub (by omega : 1 ≤ a.val)]
        norm_num
    refine ⟨a, c, hac, ha.trans h12, ?_⟩
    calc
      _ ≤ |(c.val:ℝ)/n-(a.val:ℝ)/n| + |(a.val:ℝ)/n-y| := abs_sub_le _ _ _
      _ ≤ 1/(n:ℝ)+1/(n:ℝ) := by
        apply add_le_add _ hb
        rw [← sub_div, abs_div, abs_of_pos hnR]
        exact div_le_div_of_nonneg_right hca hnR.le
      _ = 2/(n:ℝ) := by ring
  · exact ⟨a,b,hab,ha.trans h12,hb.trans h12⟩

example : ∃ a b : Fin 2, a ≠ b ∧ |(a.val:ℝ)/2-0| ≤ 2/2 ∧
    |(b.val:ℝ)/2-0| ≤ 2/2 := by
  exact exists_distinct_lattice_endpoints 2 (by decide) 0 0 (by constructor <;> norm_num)
    (by constructor <;> norm_num)

end PermutationEndpointProfile
