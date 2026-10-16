import Combinatorics.PermutationEndpointBoundaryLower
import Combinatorics.PermutationSameEdgeLimit
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

open Filter Topology

namespace PermutationEndpointPositivity

/-- A fixed falling factorial, normalized by the size to its degree, has the
expected power limit, even when the limiting coordinate is zero. -/
theorem tendsto_descFactorial_scaled (n x : ℕ → ℕ) (ρ : ℝ) (s : ℕ)
    (hn : Tendsto n atTop atTop)
    (hx : Tendsto (fun t => (x t : ℝ) / (n t : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun t => ((x t).descFactorial s : ℝ) / (n t : ℝ) ^ s)
      atTop (𝓝 (ρ ^ s)) := by
  have hnR : Tendsto (fun t => (n t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hi (i : ℕ) : Tendsto (fun t => (x t : ℝ) / (n t : ℝ) -
      (i : ℝ) / (n t : ℝ)) atTop (𝓝 ρ) := by
    simpa using hx.sub (tendsto_const_nhds.div_atTop hnR :
      Tendsto (fun t => (i : ℝ) / (n t : ℝ)) atTop (𝓝 0))
  have hp := tendsto_finsetProd (Finset.range s) (fun i _ => hi i)
  have hid (t : ℕ) : ((x t).descFactorial s : ℝ) / (n t : ℝ) ^ s =
      ∏ i ∈ Finset.range s, ((x t : ℝ) / (n t : ℝ) - (i : ℝ) / (n t : ℝ)) := by
    simp_rw [← sub_div]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_range]
    rw [← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial]
  simpa only [← hid, Finset.prod_const, Finset.card_range] using hp

/-- Removing a fixed number of labels changes the normalized size by a vanishing
amount. The natural subtraction is used only eventually above its cutoff. -/
theorem tendsto_sub_normalized (n : ℕ → ℕ) (k : ℕ)
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun t => ((n t - k : ℕ) : ℝ) / (n t : ℝ)) atTop (𝓝 1) := by
  have hnR : Tendsto (fun t => (n t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hlim : Tendsto (fun t => 1 - (k : ℝ) / (n t : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hnR :
      Tendsto (fun t => (k : ℝ) / (n t : ℝ)) atTop (𝓝 0))
  apply hlim.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop k),
    hn.eventually (eventually_ge_atTop 1)] with t hk hp
  rw [Nat.cast_sub hk, sub_div, div_self (by exact_mod_cast (by omega : n t ≠ 0))]

/-- A fixed falling-factorial ratio has its power limit without a positive
lower bound on the numerator coordinate. -/
theorem tendsto_descFactorial_ratio (n x : ℕ → ℕ) (ρ : ℝ) (s : ℕ)
    (hn : Tendsto n atTop atTop)
    (hx : Tendsto (fun t => (x t : ℝ) / (n t : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun t => ((x t).descFactorial s : ℝ) /
      ((n t - 2).descFactorial s : ℝ)) atTop (𝓝 (ρ ^ s)) := by
  have hnum := tendsto_descFactorial_scaled n x ρ s hn hx
  have hden := tendsto_descFactorial_scaled n (fun t => n t - 2) 1 s hn
    (tendsto_sub_normalized n 2 hn)
  have hlim := hnum.div hden (by simp : (1 : ℝ) ^ s ≠ 0)
  simp only [one_pow, div_one] at hlim
  apply hlim.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with t ht
  have hn0 : (n t : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n t ≠ 0))
  exact div_div_div_cancel_right₀ hn0 _ _

/-- An ordinary factorial tail can be made smaller than the exponentially small
boundary certificate at some cutoff divisible by three. -/
theorem exists_cutoff (d : ℝ) (hd : 0 < d) :
    ∃ K : ℕ, 3 ≤ K ∧ (6 : ℝ) / (K / 3).factorial < d ^ (2 * K - 4) := by
  have hzero := (Real.summable_pow_div_factorial ((d ^ 6)⁻¹)).tendsto_atTop_zero
  have hlim : Tendsto (fun j : ℕ => 6 * d ^ 4 * ((d ^ 6)⁻¹ ^ j / j.factorial))
      atTop (𝓝 0) := by
    simpa using hzero.const_mul (6 * d ^ 4)
  have he := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨j, hj, hj1⟩ := (he.and (eventually_ge_atTop 1)).exists
  have hs : 0 < d ^ (6 * j - 4) := pow_pos hd _
  have hp : d ^ (6 * j) = d ^ (6 * j - 4) * d ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  have hid : (6 * d ^ 4 * ((d ^ 6)⁻¹ ^ j / j.factorial)) * d ^ (6 * j - 4) =
      6 / (j.factorial : ℝ) := by
    rw [inv_pow, ← pow_mul]
    rw [hp]
    field_simp
  refine ⟨3 * j, by omega, ?_⟩
  have hlt := mul_lt_mul_of_pos_right hj hs
  rw [hid, one_mul] at hlt
  simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 3), show 2 * (3 * j) = 6 * j by omega]
    using hlt

/-- The two boundary-label populations converge to their geometric lengths;
no ordering or separation of the limiting anchors is required. -/
theorem tendsto_boundary_populations (n a b : ℕ → ℕ) (θ φ : ℝ)
    (hn : Tendsto n atTop atTop)
    (hv : ∀ᶠ t in atTop, a t < n t ∧ b t < n t)
    (ha : Tendsto (fun t => (a t : ℝ) / (n t : ℝ)) atTop (𝓝 θ))
    (hb : Tendsto (fun t => (b t : ℝ) / (n t : ℝ)) atTop (𝓝 φ)) :
    Tendsto (fun t => ((n t - 1 - max (a t) (b t) : ℕ) : ℝ) / (n t : ℝ))
        atTop (𝓝 (1 - max θ φ)) ∧
      Tendsto (fun t => ((min (a t) (b t) : ℕ) : ℝ) / (n t : ℝ))
        atTop (𝓝 (min θ φ)) := by
  have hmax : Tendsto (fun t => ((max (a t) (b t) : ℕ) : ℝ) / (n t : ℝ))
      atTop (𝓝 (max θ φ)) := by
    simpa only [Nat.cast_max, max_div_div_right (Nat.cast_nonneg _)] using ha.max hb
  have hmin : Tendsto (fun t => ((min (a t) (b t) : ℕ) : ℝ) / (n t : ℝ))
      atTop (𝓝 (min θ φ)) := by
    simpa only [Nat.cast_min, min_div_div_right (Nat.cast_nonneg _)] using ha.min hb
  refine ⟨?_, hmin⟩
  have hnR : Tendsto (fun t => (n t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hone : Tendsto (fun t => (1 : ℝ) / (n t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnR
  have hlim : Tendsto (fun t => 1 - 1 / (n t : ℝ) -
      ((max (a t) (b t) : ℕ) : ℝ) / (n t : ℝ))
      atTop (𝓝 (1 - 0 - max θ φ)) := (tendsto_const_nhds.sub hone).sub hmax
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [hv, hn.eventually (eventually_ge_atTop 1)] with t ht hn1
  have hM : max (a t) (b t) ≤ n t - 1 := by omega
  rw [Nat.cast_sub hM, Nat.cast_sub hn1, Nat.cast_one, sub_div, sub_div,
    div_self (by exact_mod_cast (by omega : n t ≠ 0))]

/-- Outside the two opposite corners, at least one exterior interval has
strictly positive length, including when the limiting coordinates coincide. -/
theorem boundary_length_pos (θ φ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1)
    (h01 : ¬ (θ = 0 ∧ φ = 1)) (h10 : ¬ (θ = 1 ∧ φ = 0)) :
    0 < max (1 - max θ φ) (min θ φ) := by
  by_cases h : θ ≤ φ
  · rw [max_eq_right h, min_eq_left h, lt_max_iff]
    by_contra hn
    push Not at hn
    have hφ1 : φ = 1 := by rcases hφ with ⟨_, _⟩; linarith
    have hθ0 : θ = 0 := by rcases hθ with ⟨_, _⟩; linarith
    exact h01 ⟨hθ0, hφ1⟩
  · have h' : φ ≤ θ := le_of_not_ge h
    rw [max_eq_left h', min_eq_right h', lt_max_iff]
    by_contra hn
    push Not at hn
    have hθ1 : θ = 1 := by rcases hθ with ⟨_, _⟩; linarith
    have hφ0 : φ = 0 := by rcases hφ with ⟨_, _⟩; linarith
    exact h10 ⟨hθ1, hφ0⟩

/-- The exact boundary-certificate lower bound applies to the actual totalized
endpoint fraction on every valid experiment above the cutoff. -/
theorem boundary_lower {n a b K : ℕ} (hK : 3 ≤ K) (hn : 2 * K - 2 ≤ n)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ((n - 1 - max a b).descFactorial (2 * K - 4) : ℝ) /
        (n - 2).descFactorial (2 * K - 4) +
      ((min a b).descFactorial (2 * K - 4) : ℝ) /
        (n - 2).descFactorial (2 * K - 4) -
      6 / (K / 3).factorial ≤ PermutationSameEdgeLimit.F n a b := by
  letI : NeZero n := ⟨by omega⟩
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) ha hb hab]
  exact PermutationEndpointBoundaryLower.avoidTwo_fraction_lower K hK hn
    ⟨n - 1, by omega⟩ (by dsimp; omega) ⟨a, ha⟩ ⟨b, hb⟩
    (fun he => hab (congrArg Fin.val he))

/-- Actual endpoint avoidance stays uniformly positive along every growing-size
sequence with converging normalized distinct anchors, except at the two opposite
corners. Equal limiting coordinates are allowed; no profile premise is used. -/
theorem eventually_F_pos (n a b : ℕ → ℕ) (θ φ : ℝ)
    (hn : Tendsto n atTop atTop)
    (hv : ∀ᶠ t in atTop, a t < n t ∧ b t < n t ∧ a t ≠ b t)
    (ha : Tendsto (fun t => (a t : ℝ) / (n t : ℝ)) atTop (𝓝 θ))
    (hb : Tendsto (fun t => (b t : ℝ) / (n t : ℝ)) atTop (𝓝 φ))
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1)
    (h01 : ¬ (θ = 0 ∧ φ = 1)) (h10 : ¬ (θ = 1 ∧ φ = 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in atTop, c ≤ PermutationSameEdgeLimit.F (n t) (a t) (b t) := by
  let u : ℝ := 1 - max θ φ
  let v : ℝ := min θ φ
  let d : ℝ := max u v
  have hu : 0 ≤ u := sub_nonneg.mpr (max_le hθ.2 hφ.2)
  have hv0 : 0 ≤ v := le_min hθ.1 hφ.1
  have hd : 0 < d := boundary_length_pos θ φ hθ hφ h01 h10
  obtain ⟨K, hK, htail⟩ := exists_cutoff d hd
  let s : ℕ := 2 * K - 4
  have hcert : d ^ s ≤ u ^ s + v ^ s := by
    rcases le_total u v with huv | hvu
    · have hpow : d ^ s = v ^ s := by simp only [d, max_eq_right huv]
      rw [hpow]
      exact le_add_of_nonneg_left (pow_nonneg hu _)
    · have hpow : d ^ s = u ^ s := by simp only [d, max_eq_left hvu]
      rw [hpow]
      exact le_add_of_nonneg_right (pow_nonneg hv0 _)
  let L : ℝ := u ^ s + v ^ s - 6 / (K / 3).factorial
  have hL : 0 < L := by
    dsimp only [L]
    exact sub_pos.mpr (lt_of_lt_of_le htail hcert)
  obtain ⟨hupper, hlower⟩ := tendsto_boundary_populations n a b θ φ hn
    (hv.mono (fun _ ht => ⟨ht.1, ht.2.1⟩)) ha hb
  have hup := tendsto_descFactorial_ratio n (fun t => n t - 1 - max (a t) (b t)) u s hn hupper
  have hlo := tendsto_descFactorial_ratio n (fun t => min (a t) (b t)) v s hn hlower
  have hlim : Tendsto (fun t =>
      ((n t - 1 - max (a t) (b t)).descFactorial s : ℝ) / (n t - 2).descFactorial s +
        ((min (a t) (b t)).descFactorial s : ℝ) / (n t - 2).descFactorial s -
        6 / (K / 3).factorial) atTop (𝓝 L) :=
    (hup.add hlo).sub_const _
  have he := hlim.eventually (eventually_gt_nhds (show L / 2 < L by linarith))
  refine ⟨L / 2, by positivity, ?_⟩
  filter_upwards [he, hv, hn.eventually (eventually_ge_atTop (2 * K - 2))] with t ht hvalid hsize
  exact ht.le.trans (boundary_lower hK hsize hvalid.1 hvalid.2.1 hvalid.2.2)

/-- The hypotheses are jointly realized by distinct labels zero and one in
growing experiments; both normalized coordinates converge to zero. -/
theorem eventually_F_pos_zero_one :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c ≤ PermutationSameEdgeLimit.F (t + 2) 0 1 := by
  have hn : Tendsto (fun t : ℕ => t + 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with t ht
    omega
  have ha : Tendsto (fun t : ℕ => (0 : ℝ) / (t + 2 : ℕ)) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hb : Tendsto (fun t : ℕ => (1 : ℝ) / (t + 2 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  exact eventually_F_pos (fun t => t + 2) (fun _ => 0) (fun _ => 1) 0 0 hn
    (Eventually.of_forall (fun t => by omega)) (by simpa using ha) (by simpa using hb)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end PermutationEndpointPositivity
