/-
Erdős Problem #124 archive. The second question and the two research claims
below remain admitted. Their historical source descriptions and proof sketches
are not independently verified here, and no inherited source-fidelity verdict
is asserted by this file.

The exact shared definitions and the global partial-sum completeness criterion
are formalized in Enumerative.E124. The two elementary arithmetic sanity checks
below are proved; they do not establish the archived completeness or necessity
claims. In particular no density estimate or BEGL proof is certified here.
-/
import Enumerative.E124

set_option autoImplicit false

/-- Archive-only compatibility: a sorted list has every earlier element
related to every later element. For natural `<`, this means strictly increasing. -/
abbrev List.Sorted {α : Type*} (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

example (l : List ℕ) : l.Sorted (· < ·) ↔ l.SortedLT := by
  exact List.sortedLT_iff_pairwise.symm

namespace ErdosCandidates.E124

/-- `12 = 3^1 + 3^2` uses distinct exponents at least one. Every such
sum is divisible by three, so `4` cannot be represented. -/
example : (12 : ℕ) ∈ PowSumSet 3 1 ∧ (4 : ℕ) ∉ PowSumSet 3 1 := by
  constructor
  · refine ⟨{1, 2}, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> norm_num
    · norm_num
  · rintro ⟨S, hS, heq⟩
    have hdiv : 3 ∣ ∑ i ∈ S, (3 : ℕ) ^ i := by
      apply Finset.dvd_sum
      intro i hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i) (by
        intro hi0
        have hpos := hS i hi
        omega)
      rw [pow_succ]
      exact dvd_mul_left 3 (3 ^ j)
    rw [← heq] at hdiv
    norm_num at hdiv

/-- Archived second-question conjecture for sorted bases at least three,
with the rational reciprocal-sum and gcd conditions. This remains admitted. -/
theorem erdos_124_second (ds : List ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hsort : ds.Sorted (· < ·)) (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : 1 ≤ ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1))
    (hgcd : ds.foldr Nat.gcd 0 = 1) :
    CompleteFor ds k := by
  sorry

/-- Archived `{3,4,7}` completeness claim at every positive level.
The arithmetic checks below do not prove this claim; it remains admitted. -/
theorem begl_347 (k : ℕ) (hk : 1 ≤ k) : CompleteFor [3, 4, 7] k := by
  sorry

/-- The reciprocal sum and nested gcd for `{3,4,7}` have the required
arithmetic values; this does not certify a completeness theorem. -/
example : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 ∧
    Nat.gcd 3 (Nat.gcd 4 7) = 1 := by
  norm_num

/-- Two nonnegative reals with the same bucket `⌊B·x⌋₊` differ by less than `1/B`. -/
private lemma abs_sub_lt_of_floor_mul_eq {B : ℕ} (hB : 0 < B) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : ⌊(B : ℝ) * x⌋₊ = ⌊(B : ℝ) * y⌋₊) : |x - y| < 1 / B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 := Nat.floor_le (mul_nonneg hBpos.le hx)
  have h2 := Nat.lt_floor_add_one ((B : ℝ) * x)
  have h3 := Nat.floor_le (mul_nonneg hBpos.le hy)
  have h4 := Nat.lt_floor_add_one ((B : ℝ) * y)
  rw [h] at h1 h2
  rw [abs_sub_lt_iff, lt_div_iff₀ hBpos, lt_div_iff₀ hBpos]
  constructor <;> nlinarith

/-- Simultaneous Dirichlet approximation by pigeonhole: for nonnegative reals
`β i` and a resolution `B`, there are arbitrarily large reals `t` such that every
`t * β i` lies within `1/B` of a natural number. -/
private lemma simultaneous_approx (r B : ℕ) (hB : 0 < B) (β : Fin r → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (L : ℝ) :
    ∃ t : ℝ, L ≤ t ∧ ∃ e : Fin r → ℕ, ∀ i, |t * β i - e i| < 1 / B := by
  set L' : ℝ := max L 1 with hL'
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let x : ℕ → Fin r → ℝ := fun m i => (m : ℝ) * L' * β i
  have hx0 : ∀ m i, 0 ≤ x m i := fun m i => by
    have := hβ i
    positivity
  have hfr0 : ∀ m i, 0 ≤ x m i - ⌊x m i⌋₊ := fun m i => sub_nonneg.2 (Nat.floor_le (hx0 m i))
  have hfr1 : ∀ m i, x m i - ⌊x m i⌋₊ < 1 := fun m i => by
    have := Nat.lt_floor_add_one (x m i)
    linarith
  let g : ℕ → Fin r → ℕ := fun m i => ⌊(B : ℝ) * (x m i - ⌊x m i⌋₊)⌋₊
  have hmaps : ∀ m ∈ Finset.range (B ^ r + 1),
      g m ∈ Fintype.piFinset (fun _ : Fin r => Finset.range B) := by
    intro m _
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    apply (Nat.floor_lt (mul_nonneg hBpos.le (hfr0 m i))).2
    calc (B : ℝ) * (x m i - ⌊x m i⌋₊) < B * 1 := mul_lt_mul_of_pos_left (hfr1 m i) hBpos
      _ = B := mul_one _
  have hcard : (Fintype.piFinset (fun _ : Fin r => Finset.range B)).card <
      (Finset.range (B ^ r + 1)).card := by
    simp [Fintype.card_piFinset]
  have key : ∀ a b : ℕ, a < b → g a = g b →
      ∃ t : ℝ, L ≤ t ∧ ∃ e : Fin r → ℕ, ∀ i, |t * β i - e i| < 1 / B := by
    intro a b hlt hg
    refine ⟨((b : ℝ) - a) * L', ?_, fun i => ⌊x b i⌋₊ - ⌊x a i⌋₊, ?_⟩
    · have hba : (1 : ℝ) ≤ (b : ℝ) - a := by
        have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
        linarith
      calc L ≤ L' := le_max_left _ _
        _ = 1 * L' := (one_mul _).symm
        _ ≤ ((b : ℝ) - a) * L' := mul_le_mul_of_nonneg_right hba hL'pos.le
    · intro i
      have hxab : x a i ≤ x b i := by
        have hab : (a : ℝ) ≤ b := by exact_mod_cast hlt.le
        have := hβ i
        simp only [x]
        gcongr
      have hmono : ⌊x a i⌋₊ ≤ ⌊x b i⌋₊ := Nat.floor_le_floor hxab
      have hgi : ⌊(B : ℝ) * (x b i - ⌊x b i⌋₊)⌋₊ = ⌊(B : ℝ) * (x a i - ⌊x a i⌋₊)⌋₊ :=
        (congrFun hg i).symm
      have habs := abs_sub_lt_of_floor_mul_eq hB (hfr0 b i) (hfr0 a i) hgi
      have heq : ((b : ℝ) - a) * L' * β i - ((⌊x b i⌋₊ - ⌊x a i⌋₊ : ℕ) : ℝ) =
          (x b i - ⌊x b i⌋₊) - (x a i - ⌊x a i⌋₊) := by
        rw [Nat.cast_sub hmono]
        simp only [x]
        ring
      rw [heq]
      exact habs
  obtain ⟨a, ha, b, hb, hne, hab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key a b hlt hab
  · exact key b a hlt hab.symm

/-- A sum of distinct powers of `d ≥ 2` that is below `d ^ e` is at most the
full geometric sum `∑_{k<e} d^k`, so `(d - 1)` times it is at most `d ^ e - 1`. -/
private lemma sub_one_mul_powSum_le {d e : ℕ} (hd : 2 ≤ d) (S : Finset ℕ)
    (h : ∑ k ∈ S, d ^ k < d ^ e) :
    ((d : ℝ) - 1) * ((∑ k ∈ S, d ^ k : ℕ) : ℝ) ≤ (d : ℝ) ^ e - 1 := by
  have hsub : S ⊆ Finset.range e := by
    intro k hk
    rw [Finset.mem_range]
    have hk' : d ^ k ≤ ∑ k ∈ S, d ^ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 (lt_of_le_of_lt hk' h)
  have hle : ∑ k ∈ S, d ^ k ≤ ∑ k ∈ Finset.range e, d ^ k := Finset.sum_le_sum_of_subset hsub
  have hgeom : (∑ k ∈ Finset.range e, (d : ℝ) ^ k) * ((d : ℝ) - 1) = (d : ℝ) ^ e - 1 :=
    geom_sum_mul _ _
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc ((d : ℝ) - 1) * ((∑ k ∈ S, d ^ k : ℕ) : ℝ)
      ≤ ((d : ℝ) - 1) * ((∑ k ∈ Finset.range e, d ^ k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hd1
    _ = (d : ℝ) ^ e - 1 := by
        push_cast
        rw [mul_comm]
        exact hgeom

/-- Archived necessity claim for a reciprocal sum below one.
No density or counting argument is formalized here; this remains admitted. -/
theorem pomerance_necessity (ds : List ℕ) (hsort : ds.Sorted (· < ·))
    (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1) < 1) :
    ¬ CompleteFor ds 0 := by
  rintro ⟨N, hN⟩
  set r := ds.length with hr
  set d : ℕ → ℕ := fun j => ds.getD j 0 with hd
  have hd3 : ∀ j < r, 3 ≤ d j := by
    intro j hj
    apply h3
    simp only [d, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · obtain ⟨f, -, heq⟩ := hN (N + 1) (by omega)
    rw [hr0] at heq
    simp at heq
  have hne : (Finset.range r).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  have hdR : ∀ j < r, (3 : ℝ) ≤ d j := fun j hj => by exact_mod_cast hd3 j hj
  have hdpos : ∀ j < r, (0 : ℝ) < (d j : ℝ) - 1 := fun j hj => by
    have := hdR j hj
    linarith
  set s : ℝ := ∑ j ∈ Finset.range r, 1 / ((d j : ℝ) - 1) with hs_def
  have hs1 : s < 1 := by
    have hcast := (Rat.cast_lt (K := ℝ)).2 hsum
    push_cast at hcast
    exact hcast
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j hj =>
    (one_div_pos.2 (hdpos j (Finset.mem_range.1 hj))).le
  set c : ℝ := 2 / (1 + s) with hc
  have hc1 : 1 < c := by
    rw [hc, lt_div_iff₀ (by linarith)]
    linarith
  set δ : ℝ := Real.log c / 2 with hδ_def
  have hδ : 0 < δ := by
    have := Real.log_pos hc1
    positivity
  have hexp2δ : Real.exp δ * Real.exp δ = c := by
    rw [← Real.exp_add, show δ + δ = Real.log c by rw [hδ_def]; ring,
      Real.exp_log (by linarith)]
  set M : ℝ := N + 1 + (1 + s) / (1 - s) with hM_def
  have hM1 : 0 ≤ (1 + s) / (1 - s) := div_nonneg (by linarith) (by linarith)
  have hM : 0 < M := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hlog : ∀ j < r, 0 < Real.log (d j) := fun j hj =>
    Real.log_pos (by linarith [hdR j hj])
  set Λ : ℝ := ∑ j ∈ Finset.range r, Real.log (d j) with hΛ
  set B : ℕ := ⌈Λ / δ⌉₊ + 1 with hB_def
  have hB : 0 < B := by omega
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBbound : ∀ j < r, Real.log (d j) / B < δ := by
    intro j hj
    have hle : Real.log (d j) ≤ Λ :=
      Finset.single_le_sum (f := fun j => Real.log (d j))
        (fun i hi => (hlog i (Finset.mem_range.1 hi)).le) (Finset.mem_range.2 hj)
    have hceil : Λ / δ < B := by
      have := Nat.le_ceil (Λ / δ)
      rw [hB_def]
      push_cast
      linarith
    rw [div_lt_iff₀ hBpos]
    rw [div_lt_iff₀ hδ] at hceil
    linarith
  obtain ⟨t, ht, e', he'⟩ := simultaneous_approx r B hB
    (fun i => 1 / Real.log (d i)) (fun i => (one_div_pos.2 (hlog i i.2)).le)
    (δ + Real.log M)
  let e : ℕ → ℕ := fun j => if h : j < r then e' ⟨j, h⟩ else 0
  have hclose : ∀ j < r, |t - e j * Real.log (d j)| < δ := by
    intro j hj
    have h1 := he' ⟨j, hj⟩
    have hej : e j = e' ⟨j, hj⟩ := dif_pos hj
    have hl := hlog j hj
    have hrw : t - e j * Real.log (d j) =
        (t * (1 / Real.log (d j)) - e' ⟨j, hj⟩) * Real.log (d j) := by
      rw [hej]
      field_simp
    rw [hrw, abs_mul, abs_of_pos hl]
    calc |t * (1 / Real.log (d j)) - e' ⟨j, hj⟩| * Real.log (d j)
        < 1 / B * Real.log (d j) := mul_lt_mul_of_pos_right h1 hl
      _ = Real.log (d j) / B := by ring
      _ < δ := hBbound j hj
  have hpow : ∀ j < r, Real.exp (t - δ) < (d j : ℝ) ^ e j ∧
      (d j : ℝ) ^ e j < Real.exp (t + δ) := by
    intro j hj
    have hdj : (0 : ℝ) < d j := by linarith [hdR j hj]
    have hrepr : (d j : ℝ) ^ e j = Real.exp (e j * Real.log (d j)) := by
      rw [Real.exp_nat_mul, Real.exp_log hdj]
    rw [hrepr]
    have h := abs_sub_lt_iff.1 (hclose j hj)
    exact ⟨Real.exp_lt_exp.2 (by linarith), Real.exp_lt_exp.2 (by linarith)⟩
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (Finset.range r) (fun j => d j ^ e j) hne
  have hj0r : j0 < r := Finset.mem_range.1 hj0
  set P : ℕ := d j0 ^ e j0 with hP_def
  have hPM : M < (P : ℝ) := by
    have hlow := (hpow j0 hj0r).1
    have hexpM : M ≤ Real.exp (t - δ) := by
      rw [← Real.exp_log hM]
      exact Real.exp_le_exp.2 (by linarith)
    rw [hP_def]
    push_cast
    linarith
  have hPN : N + 1 ≤ P := by
    have : (N : ℝ) + 1 < P := by linarith
    exact_mod_cast this.le
  obtain ⟨f, hf, heq⟩ := hN (P - 1) (by omega)
  have hfj : ∀ j < r, ((d j : ℝ) - 1) * f j < c * P := by
    intro j hj
    obtain ⟨S, -, hS⟩ := hf j hj
    have hfle : f j ≤ P - 1 := by
      rw [heq]
      exact Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
    have hPj : P ≤ d j ^ e j := hmin j (Finset.mem_range.2 hj)
    have hlt : ∑ k ∈ S, d j ^ k < d j ^ e j := by
      rw [← hS]
      omega
    have hgeo := sub_one_mul_powSum_le (by linarith [hd3 j hj] : 2 ≤ d j) S hlt
    rw [← hS] at hgeo
    have hup := (hpow j hj).2
    have hlow := (hpow j0 hj0r).1
    have hPR : (P : ℝ) = (d j0 : ℝ) ^ e j0 := by rw [hP_def]; push_cast; rfl
    calc ((d j : ℝ) - 1) * f j ≤ (d j : ℝ) ^ e j - 1 := hgeo
      _ < Real.exp (t + δ) := by linarith
      _ = Real.exp (t - δ) * c := by
          rw [← hexp2δ, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ ≤ (P : ℝ) * c := by
          rw [hPR]
          exact mul_le_mul_of_nonneg_right hlow.le (by linarith)
      _ = c * P := mul_comm _ _
  have hsumlt : ((P - 1 : ℕ) : ℝ) < c * P * s := by
    rw [heq]
    push_cast
    rw [hs_def, Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty hne
    intro j hj
    have hjr := Finset.mem_range.1 hj
    rw [mul_one_div, lt_div_iff₀ (hdpos j hjr), mul_comm]
    exact hfj j hjr
  have hfinal : c * P * s ≤ (P : ℝ) - 1 := by
    have hq : (1 + s) / (1 - s) < P := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    rw [div_lt_iff₀ (by linarith)] at hq
    have hcPs : c * P * s = 2 * P * s / (1 + s) := by
      rw [hc]
      ring
    rw [hcPs, div_le_iff₀ (by linarith)]
    nlinarith
  have hcastP : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  linarith

end ErdosCandidates.E124
