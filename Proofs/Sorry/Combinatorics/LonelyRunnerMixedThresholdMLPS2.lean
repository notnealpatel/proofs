/-
# Mixed thresholds in the Lonely Runner Conjecture: the exact space `MLPS₂`

## Source

* Alathea Jensen, "Mixed thresholds in the Lonely Runner Conjecture",
  arXiv:2605.27941.  Statement: Theorem A (`thm:MLPS2`) in the introduction;
  proof in Section 4.2 ("Proof of Theorem A"); definitions of `MLRC(d)` and
  `MLPS_k` in Section 2.1.

## Informal claim (verbatim from the paper)

"Theorem A. The mixed loneliness parameter space `MLPS_2` is exactly
`MLPS_2 = {(d_1,d_2) ∈ (0,1/2]^2 : 2d_1+d_2 ≤ 1 and d_1+2d_2 ≤ 1}`."

Here, for `d = (d_1, …, d_k) ∈ (0,1/2]^k`, `MLRC(d)` is the statement "for every
tuple of distinct positive integer speeds `(s_1,…,s_k)` there exists a time
`t ∈ ℝ` such that `‖s_i t‖ ≥ d_i` for each `i`", where `‖x‖` is the distance from
`x` to the nearest integer, and `MLPS_k = {d ∈ (0,1/2]^k : MLRC(d) holds}`.

Recorded 2026-10-21.  Status: proved in the paper (Theorem A).  The equal
threshold point `(1/3, 1/3)` is the three-runner lonely runner theorem
(Wills 1967), formalized in `Proofs/Combinatorics/LonelyRunnerThree.lean`.

## Proof sketch (following the paper)

Sufficiency: divide both speeds by their gcd.  For coprime distinct `a, b`,
pick odd `x, y` with `a x - b y = e ∈ {0, 1}` (`x = b, y = a, e = 0` if both
speeds are odd; otherwise Bezout and a parity correction give `e = 1`).  The
safe centers `y/(2a)` and `x/(2b)` are at distance `e/(2ab)`, and a time on the
segment between them works because `1 ≤ b(1-2d_1) + a(1-2d_2)` on the polygon.
Necessity: `‖2t‖ ≤ 1 - 2‖t‖` for every real `t`, so the speeds `(1,2)` and
`(2,1)` force `2d_1 + d_2 ≤ 1` and `d_1 + 2d_2 ≤ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.LonelyRunnerMixedThresholdMLPS2

/-- The distance `‖x‖` from a real number `x` to the nearest integer. -/
noncomputable def distToInt (x : ℝ) : ℝ := |x - round x|

/-- The mixed lonely runner statement `MLRC(d₁, d₂)`: for every pair of distinct
positive integer speeds `s₁, s₂` there is a time `t ∈ ℝ` with `‖s₁ t‖ ≥ d₁` and
`‖s₂ t‖ ≥ d₂`. -/
def MLRC2 (d₁ d₂ : ℝ) : Prop :=
  ∀ s₁ s₂ : ℕ, 0 < s₁ → 0 < s₂ → s₁ ≠ s₂ →
    ∃ t : ℝ, d₁ ≤ distToInt (s₁ * t) ∧ d₂ ≤ distToInt (s₂ * t)

/-- The two-dimensional mixed loneliness parameter space
`MLPS₂ = {(d₁, d₂) ∈ (0,1/2]² : MLRC(d₁, d₂) holds}`. -/
def MLPS2 : Set (ℝ × ℝ) :=
  {d | (0 < d.1 ∧ d.1 ≤ 1 / 2) ∧ (0 < d.2 ∧ d.2 ≤ 1 / 2) ∧ MLRC2 d.1 d.2}

/-! ### Ground truth for `distToInt` -/

/-- Ground truth: `‖1/3‖ = 1/3`. -/
example : distToInt (1 / 3) = 1 / 3 := by
  have h : round (1 / 3 : ℝ) = 0 := by rw [round_eq_zero_iff]; norm_num
  rw [distToInt, h]; norm_num [abs_of_pos]

/-- Ground truth: `‖5/2‖ = 1/2`. -/
example : distToInt (5 / 2) = 1 / 2 := by
  have h : round (5 / 2 : ℝ) = 3 := by rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [distToInt, h]; norm_num [abs_of_neg]

/-- Ground truth: `‖3‖ = 0`. -/
example : distToInt 3 = 0 := by
  have h : round (3 : ℝ) = 3 := by exact_mod_cast round_natCast 3
  rw [distToInt, h]; norm_num

/-! ### Elementary helper lemmas -/

/-- If `d ≤ q ≤ 1 - d`, then `q` is at distance at least `d` from every integer. -/
theorem le_abs_sub_intCast {d q : ℝ} (h₁ : d ≤ q) (h₂ : q ≤ 1 - d) (k : ℤ) :
    d ≤ |q - k| := by
  rcases le_or_gt k 0 with hk | hk
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    exact le_abs.mpr (Or.inl (by linarith))
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact le_abs.mpr (Or.inr (by linarith))

/-- If `x = z + q` with `z ∈ ℤ` and `d ≤ q ≤ 1 - d`, then `d ≤ ‖x‖`. -/
theorem le_distToInt_of_eq {d q x : ℝ} (z : ℤ) (hx : x = z + q) (h₁ : d ≤ q)
    (h₂ : q ≤ 1 - d) : d ≤ distToInt x := by
  have hk := le_abs_sub_intCast h₁ h₂ (round x - z)
  rw [distToInt]
  convert hk using 2
  rw [hx]; push_cast; ring

/-- The doubling inequality `‖2t‖ ≤ 1 - 2‖t‖`. -/
theorem distToInt_two_mul_le (t : ℝ) : distToInt (2 * t) ≤ 1 - 2 * distToInt t := by
  set x : ℝ := t - round t with hx
  have hhalf : |x| ≤ 1 / 2 := abs_sub_round t
  rw [distToInt, distToInt]
  rcases le_total 0 x with h0 | h0
  · have hle := round_le (2 * t) (2 * round t + 1)
    have heq : 2 * t - ((2 * round t + 1 : ℤ) : ℝ) = 2 * x - 1 := by
      rw [hx]; push_cast; ring
    rw [heq, abs_of_nonpos (a := 2 * x - 1) (by linarith [(abs_le.mp hhalf).2])] at hle
    rw [← hx, abs_of_nonneg h0]
    linarith
  · have hle := round_le (2 * t) (2 * round t - 1)
    have heq : 2 * t - ((2 * round t - 1 : ℤ) : ℝ) = 2 * x + 1 := by
      rw [hx]; push_cast; ring
    rw [heq, abs_of_nonneg (a := 2 * x + 1) (by linarith [(abs_le.mp hhalf).1])] at hle
    rw [← hx, abs_of_nonpos h0]
    linarith

/-- Parity correction of a Bezout identity: if `a u - b v = 1` and `a, b` are
not both odd, then there are odd `x, y` with `a x - b y = 1`. -/
theorem exists_odd_odd_of_sub_eq_one {a b u v : ℤ} (h : a * u - b * v = 1)
    (hab : ¬(Odd a ∧ Odd b)) : ∃ x y : ℤ, Odd x ∧ Odd y ∧ a * x - b * y = 1 := by
  have key : ∀ A B U V : ZMod 2, A * U - B * V = 1 → ¬(A = 1 ∧ B = 1) →
      (U = 1 ∧ V = 1) ∨ (U + B = 1 ∧ V + A = 1) := by decide
  have h2 : (a : ZMod 2) * u - b * v = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) h
  simp only [← ZMod.intCast_eq_one_iff_odd] at hab ⊢
  rcases key _ _ _ _ h2 hab with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact ⟨u, v, hu, hv, h⟩
  · refine ⟨u + b, v + a, by push_cast; exact hu, by push_cast; exact hv, by linear_combination h⟩


/-- Safe-interval overlap.  Let `a, b` be positive integers and `x, y` odd integers
with `a x - b y = e`, where `0 ≤ e ≤ 1`, so that the safe centers `y/(2a)` and
`x/(2b)` are at distance `e/(2ab)`.  If `d₁, d₂ ≤ 1/2` and
`1 ≤ b(1-2d₁) + a(1-2d₂)`, then some time `t` has `‖a t‖ ≥ d₁` and `‖b t‖ ≥ d₂`. -/
theorem exists_time_of_odd_odd {a b x y : ℤ} {e d₁ d₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : Odd x) (hy : Odd y) (he₀ : 0 ≤ e) (he₁ : e ≤ 1) (hxy : (a : ℝ) * x - b * y = e)
    (hd₁ : d₁ ≤ 1 / 2) (hd₂ : d₂ ≤ 1 / 2) (hkey : 1 ≤ b * (1 - 2 * d₁) + a * (1 - 2 * d₂)) :
    ∃ t : ℝ, d₁ ≤ distToInt (a * t) ∧ d₂ ≤ distToInt (b * t) := by
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set lam : ℝ := min 1 (b * (1 - 2 * d₁)) with hlam
  have hlam₀ : 0 ≤ lam := le_min zero_le_one (mul_nonneg hbR.le (by linarith))
  have hlam₁ : lam ≤ 1 := min_le_left _ _
  have hlamb : lam ≤ b * (1 - 2 * d₁) := min_le_right _ _
  have hlama : 1 - lam ≤ a * (1 - 2 * d₂) := by
    rcases min_choice 1 ((b : ℝ) * (1 - 2 * d₁)) with h | h
    · rw [hlam, h]; nlinarith
    · rw [hlam, h]; linarith
  refine ⟨(2 * m + 1 : ℝ) / (2 * a) + lam * e / (2 * a * b), ?_, ?_⟩
  · -- `a t = m + (1/2 + lam e/(2b))`
    refine le_distToInt_of_eq m ?_ (q := 1 / 2 + lam * e / (2 * b)) ?_ ?_
    · field_simp; ring
    · have : 0 ≤ lam * e / (2 * b) := by positivity
      linarith
    · have hle : lam * e ≤ b * (1 - 2 * d₁) := by nlinarith
      have : lam * e / (2 * b) ≤ 1 / 2 - d₁ := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  · -- `b t = n + (1/2 - (1 - lam) e/(2a))`
    refine le_distToInt_of_eq n ?_ (q := 1 / 2 - (1 - lam) * e / (2 * a)) ?_ ?_
    · have hbm : (b : ℝ) * (2 * m + 1) = a * (2 * n + 1) - e := by
        push_cast at hxy; linarith
      field_simp
      linear_combination hbm
    · have hle : (1 - lam) * e ≤ a * (1 - 2 * d₂) := by nlinarith
      have : (1 - lam) * e / (2 * a) ≤ 1 / 2 - d₂ := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · have : 0 ≤ (1 - lam) * e / (2 * a) := by
        apply div_nonneg (mul_nonneg (by linarith) he₀) (by positivity)
      linarith

/-- The vertex check of the paper: on the polygon `0 ≤ dᵢ`, `2d₁ + d₂ ≤ 1`,
`d₁ + 2d₂ ≤ 1`, distinct positive integers `a, b` satisfy
`1 ≤ b(1-2d₁) + a(1-2d₂)`. -/
theorem one_le_key {a b : ℕ} {d₁ d₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (h₁ : 2 * d₁ + d₂ ≤ 1) (h₂ : d₁ + 2 * d₂ ≤ 1) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    1 ≤ (b : ℝ) * (1 - 2 * d₁) + a * (1 - 2 * d₂) := by
  have hp : 0 ≤ 1 - 2 * d₁ := by linarith
  have hq : 0 ≤ 1 - 2 * d₂ := by linarith
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · -- `b ≥ 2`, `a ≥ 1`
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (by omega : 2 ≤ b)
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  · have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (by omega : 2 ≤ a)
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith


/-- Sufficiency for coprime speeds: if `a, b` are distinct coprime positive
integers and `(d₁, d₂)` lies in the polygon `0 ≤ dᵢ`, `2d₁ + d₂ ≤ 1`,
`d₁ + 2d₂ ≤ 1`, then some time `t` has `‖a t‖ ≥ d₁` and `‖b t‖ ≥ d₂`. -/
theorem exists_time_of_coprime {a b : ℕ} {d₁ d₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hcop : Nat.Coprime a b) (h₁ : 2 * d₁ + d₂ ≤ 1) (h₂ : d₁ + 2 * d₂ ≤ 1) (hd₁ : 0 ≤ d₁)
    (hd₂ : 0 ≤ d₂) : ∃ t : ℝ, d₁ ≤ distToInt (a * t) ∧ d₂ ≤ distToInt (b * t) := by
  have hkey := one_le_key ha hb hab h₁ h₂ hd₁ hd₂
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < b := by exact_mod_cast hb
  have hd₁' : d₁ ≤ 1 / 2 := by linarith
  have hd₂' : d₂ ≤ 1 / 2 := by linarith
  have hkeyZ : 1 ≤ ((b : ℤ) : ℝ) * (1 - 2 * d₁) + ((a : ℤ) : ℝ) * (1 - 2 * d₂) := by
    simpa only [Int.cast_natCast] using hkey
  have hcast : ∀ n : ℕ, ((n : ℤ) : ℝ) = (n : ℝ) := fun n => Int.cast_natCast n
  by_cases hodd : Odd (a : ℤ) ∧ Odd (b : ℤ)
  · -- both speeds odd: the common safe center `t = 1/2` (here `x = b`, `y = a`, `e = 0`)
    obtain ⟨t, ht⟩ := exists_time_of_odd_odd (e := 0) haZ hbZ hodd.2 hodd.1 le_rfl zero_le_one
      (by ring) hd₁' hd₂' hkeyZ
    exact ⟨t, by simpa only [hcast] using ht⟩
  · -- Bezout with a parity correction gives `e = 1`
    have hbez : (a : ℤ) * Nat.gcdA a b - b * (-Nat.gcdB a b) = 1 := by
      have h := Nat.gcd_eq_gcd_ab a b
      rw [hcop.gcd_eq_one] at h
      push_cast at h
      linear_combination -h
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_odd_odd_of_sub_eq_one hbez hodd
    have hxyR : ((a : ℤ) : ℝ) * x - ((b : ℤ) : ℝ) * y = 1 := by exact_mod_cast hxy
    obtain ⟨t, ht⟩ := exists_time_of_odd_odd haZ hbZ hx hy zero_le_one le_rfl hxyR hd₁' hd₂'
      hkeyZ
    exact ⟨t, by simpa only [hcast] using ht⟩

/-- Sufficiency (first half of Theorem A): every point of the polygon
`0 ≤ dᵢ`, `2d₁ + d₂ ≤ 1`, `d₁ + 2d₂ ≤ 1` satisfies `MLRC(d₁, d₂)`. -/
theorem mlrc2_of_le {d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (h₁ : 2 * d₁ + d₂ ≤ 1)
    (h₂ : d₁ + 2 * d₂ ≤ 1) : MLRC2 d₁ d₂ := by
  intro s₁ s₂ hs₁ hs₂ hne
  set g : ℕ := Nat.gcd s₁ s₂ with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left s₂ hs₁
  set a : ℕ := s₁ / g with ha
  set b : ℕ := s₂ / g with hb
  have hsa : s₁ = g * a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left s₁ s₂)).symm
  have hsb : s₂ = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)).symm
  have hapos : 0 < a := Nat.div_pos (Nat.gcd_le_left s₂ hs₁) hgpos
  have hbpos : 0 < b := Nat.div_pos (Nat.gcd_le_right (m := s₁) hs₂) hgpos
  have hab : a ≠ b := by
    intro h
    exact hne (by rw [hsa, hsb, h])
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hgpos
  obtain ⟨t, ht₁, ht₂⟩ := exists_time_of_coprime hapos hbpos hab hcop h₁ h₂ hd₁ hd₂
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  refine ⟨t / g, ?_, ?_⟩
  · have heq : (s₁ : ℝ) * (t / g) = a * t := by
      rw [hsa]; push_cast; field_simp
    rw [heq]; exact ht₁
  · have heq : (s₂ : ℝ) * (t / g) = b * t := by
      rw [hsb]; push_cast; field_simp
    rw [heq]; exact ht₂

/-- Necessity (second half of Theorem A): `MLRC(d₁, d₂)` forces `2d₁ + d₂ ≤ 1`
(speeds `(1, 2)`) and `d₁ + 2d₂ ≤ 1` (speeds `(2, 1)`). -/
theorem le_of_mlrc2 {d₁ d₂ : ℝ} (h : MLRC2 d₁ d₂) :
    2 * d₁ + d₂ ≤ 1 ∧ d₁ + 2 * d₂ ≤ 1 := by
  constructor
  · obtain ⟨t, ht₁, ht₂⟩ := h 1 2 one_pos two_pos (by decide)
    have hdbl := distToInt_two_mul_le t
    simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at ht₁ ht₂
    linarith
  · obtain ⟨t, ht₁, ht₂⟩ := h 2 1 two_pos one_pos (by decide)
    have hdbl := distToInt_two_mul_le t
    simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at ht₁ ht₂
    linarith

/-- **Theorem A** (Jensen, arXiv:2605.27941, `thm:MLPS2`): the two-dimensional
mixed loneliness parameter space is exactly
`MLPS₂ = {(d₁, d₂) ∈ (0,1/2]² : 2d₁ + d₂ ≤ 1 ∧ d₁ + 2d₂ ≤ 1}`. -/
theorem thm_A :
    MLPS2 = {d : ℝ × ℝ | (0 < d.1 ∧ d.1 ≤ 1 / 2) ∧ (0 < d.2 ∧ d.2 ≤ 1 / 2) ∧
      2 * d.1 + d.2 ≤ 1 ∧ d.1 + 2 * d.2 ≤ 1} := by
  ext ⟨d₁, d₂⟩
  simp only [MLPS2, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb₁, hb₂, h⟩
    exact ⟨hb₁, hb₂, le_of_mlrc2 h⟩
  · rintro ⟨hb₁, hb₂, h₁, h₂⟩
    exact ⟨hb₁, hb₂, mlrc2_of_le hb₁.1.le hb₂.1.le h₁ h₂⟩

/-- Equivalent pointwise form of Theorem A: for `d₁, d₂ ∈ (0, 1/2]`,
`MLRC(d₁, d₂)` holds iff `2d₁ + d₂ ≤ 1` and `d₁ + 2d₂ ≤ 1`. -/
theorem mlrc2_iff {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    MLRC2 d₁ d₂ ↔ 2 * d₁ + d₂ ≤ 1 ∧ d₁ + 2 * d₂ ≤ 1 :=
  ⟨le_of_mlrc2, fun h => mlrc2_of_le hd₁.le hd₂.le h.1 h.2⟩

/-! ### Non-vacuity checks -/

/-- The classical three-runner point `(1/3, 1/3)` lies in `MLPS₂`
(the lonely runner theorem for three runners, Wills 1967). -/
example : ((1 / 3 : ℝ), (1 / 3 : ℝ)) ∈ MLPS2 := by
  rw [thm_A]; norm_num

/-- An off-diagonal vertex-adjacent point `(2/5, 1/5)` lies in `MLPS₂`. -/
example : ((2 / 5 : ℝ), (1 / 5 : ℝ)) ∈ MLPS2 := by
  rw [thm_A]; norm_num

/-- The point `(1/2, 1/4)` violates `2d₁ + d₂ ≤ 1` and so is not in `MLPS₂`. -/
example : ((1 / 2 : ℝ), (1 / 4 : ℝ)) ∉ MLPS2 := by
  rw [thm_A]; norm_num

/-- The quantified speed domain of `MLRC2` is nonempty: `(1, 2)` is a pair of
distinct positive speeds. -/
example : 0 < (1 : ℕ) ∧ 0 < (2 : ℕ) ∧ (1 : ℕ) ≠ 2 := by decide

end Candidates.LonelyRunnerMixedThresholdMLPS2
