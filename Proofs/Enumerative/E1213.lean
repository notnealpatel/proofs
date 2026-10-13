/-
Erdős problem 1213: equal sums on two distinct intervals in a bounded-gap prefix.
The Erdős problem archive attributes the affirmative exponential-bound result
to Hegyvári (1986). His primary proof was unavailable for this formalization.
The elementary route used here follows the secondary public argument in
sweetsky123/erdos-problem-1213, independently checked at the mathematical gate
and formalized below. No historical-proof or novelty identification is asserted.

Take M = 2^(2K), W = K*M², X the first M terms' sum. Each length r ≤ M
crosses each level X + qKr for q < M²/r with overshoot less than Kr.
The slots occupy a common interval [X,X+W); dyadic counting supplies more
than W slots. Equal sums cannot come from different bins of the same length,
so the resulting endpoint intervals are distinct. Finally the required last
term bound follows from M*a₀ + 2W ≤ a₀*64^K.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1213

/-- The sum over the nonempty endpoint interval, when `i ≤ j`. -/
def intervalSum (a : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc i j, a t

example : intervalSum id 1 3 = 6 := by decide

/-- Two distinct nonempty endpoint intervals inside the prefix have equal sums. -/
def HasEqualIntervalSums (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ i j i' j' : ℕ, i ≤ j ∧ j < s ∧ i' ≤ j' ∧ j' < s ∧
    (i, j) ≠ (i', j') ∧ intervalSum a i j = intervalSum a i' j'

example : HasEqualIntervalSums (fun t => t + 1) 3 := by
  refine ⟨0, 1, 2, 2, by omega, by omega, by omega, by omega, by decide, ?_⟩
  decide

/-- Bounded adjacent gaps telescope throughout the inspected prefix. -/
theorem prefix_gap_bound (a : ℕ → ℕ) (s K : ℕ)
    (hmono : ∀ t u : ℕ, t < u → u < s → a t < a u)
    (hgap : ∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K)
    (i d : ℕ) (hid : i + d < s) : a (i + d) ≤ a i + K * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprev : i + d < s := by omega
    have hstep := hgap (i + d) (by omega)
    have hinc := hmono (i + d) (i + d + 1) (by omega) (by omega)
    have hbase := ih hprev
    rw [Nat.mul_succ]
    simp only [Nat.add_succ, Nat.add_zero] at hstep hinc ⊢
    omega

/-- Translating a length-`r` window replaces exactly its first and last entries. -/
theorem window_step (a : ℕ → ℕ) (i r : ℕ) :
    (∑ t ∈ Finset.range r, a (i + 1 + t)) + a i =
      (∑ t ∈ Finset.range r, a (i + t)) + a (i + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Finset.sum_range_succ]
    have heq : i + 1 + r = i + (r + 1) := by omega
    rw [heq]
    omega

/-- A first crossing of an integer level overshoots by less than one jump.
The initial value is allowed to equal the level. -/
theorem first_crossing_bin (T : ℕ → ℕ) (n L D : ℕ)
    (hD : 0 < D) (hstart : T 0 ≤ L) (hend : L ≤ T n)
    (hstep : ∀ i, i < n → T (i + 1) ≤ T i + D) :
    ∃ i, i ≤ n ∧ L ≤ T i ∧ T i < L + D := by
  let P : ℕ → Prop := fun i => i ≤ n ∧ L ≤ T i
  have hex : ∃ i, P i := ⟨n, le_rfl, hend⟩
  let i := Nat.find hex
  have hi : i ≤ n ∧ L ≤ T i := Nat.find_spec hex
  refine ⟨i, hi.1, hi.2, ?_⟩
  by_cases hz : i = 0
  · have ht : T i ≤ L := by simpa only [hz] using hstart
    omega
  · have hip : i - 1 < i := by omega
    have hp := Nat.find_min hex hip
    have hpn : i - 1 ≤ n := by omega
    have hlt : T (i - 1) < L := by
      dsimp [P] at hp
      omega
    have hs := hstep (i - 1) (by omega)
    have heq : i - 1 + 1 = i := by omega
    rw [heq] at hs
    omega

/-- Dyadic blocks give a lower bound for the integer harmonic sum.
The denominator indices are positive, and `n < d` guards the exponent subtraction. -/
theorem dyadic_slot_count (d n : ℕ) (hnd : n < d) :
    2 ^ d + n * 2 ^ (d - 1) ≤
      ∑ r ∈ Finset.range (2 ^ n), 2 ^ d / (r + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n < d := by omega
    have hbase := ih hn
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]
      omega
    rw [hpow, Finset.sum_range_add]
    have hfactor : 2 ^ (d - (n + 1)) * 2 ^ (n + 1) = 2 ^ d :=
      Nat.pow_sub_mul_pow 2 (by omega)
    have hblock : 2 ^ (d - 1) ≤
        ∑ r ∈ Finset.range (2 ^ n), 2 ^ d / (2 ^ n + r + 1) := by
      have hterm : ∀ r ∈ Finset.range (2 ^ n),
          2 ^ (d - (n + 1)) ≤ 2 ^ d / (2 ^ n + r + 1) := by
        intro r hr
        have hrn := Finset.mem_range.mp hr
        apply (Nat.le_div_iff_mul_le (by omega)).mpr
        calc
          2 ^ (d - (n + 1)) * (2 ^ n + r + 1) ≤
              2 ^ (d - (n + 1)) * 2 ^ (n + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ d := hfactor
      have hs := Finset.sum_le_sum hterm
      have hexp : n + (d - (n + 1)) = d - 1 := by omega
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul,
        ← pow_add, hexp] using hs
    rw [Nat.succ_mul]
    omega

/-- Each positive window length and valid bin admits a crossing window.
All selected sums lie in the common interval of width `K * M * M`. -/
theorem window_bin (a : ℕ → ℕ) (s K M : ℕ)
    (hK : 0 < K) (hM : M < s)
    (hmono : ∀ t u : ℕ, t < u → u < s → a t < a u)
    (hgap : ∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K)
    (hend : (∑ t ∈ Finset.range M, a t) + K * (M * M) < a (s - 1))
    (r q : ℕ) (hr : 0 < r) (hrM : r ≤ M) (hq : q < M * M / r) :
    ∃ i, i + r ≤ s ∧
      (∑ t ∈ Finset.range M, a t) + q * (K * r) ≤
        (∑ t ∈ Finset.range r, a (i + t)) ∧
      (∑ t ∈ Finset.range r, a (i + t)) <
        (∑ t ∈ Finset.range M, a t) + (q + 1) * (K * r) := by
  let X := ∑ t ∈ Finset.range M, a t
  let T := fun i => ∑ t ∈ Finset.range r, a (i + t)
  have hqr : (q + 1) * r ≤ M * M :=
    (Nat.le_div_iff_mul_le hr).mp (by omega)
  have hbin : (q + 1) * (K * r) ≤ K * (M * M) := by
    nlinarith
  have hstart : T 0 ≤ X + q * (K * r) := by
    have hs : (∑ t ∈ Finset.range r, a t) ≤ X :=
      Finset.sum_le_sum_of_subset (Finset.range_mono hrM)
    simpa only [T, Nat.zero_add] using hs.trans (Nat.le_add_right X _)
  have hlast : a (s - 1) ≤ T (s - r) := by
    have hmem : r - 1 ∈ Finset.range r := Finset.mem_range.mpr (by omega)
    have hs := Finset.single_le_sum (fun t _ => Nat.zero_le (a (s - r + t))) hmem
    have heq : s - r + (r - 1) = s - 1 := by omega
    simpa only [heq, T] using hs
  have hfinish : X + q * (K * r) ≤ T (s - r) := by
    dsimp [X] at hlast ⊢
    nlinarith
  have hstep : ∀ i, i < s - r → T (i + 1) ≤ T i + K * r := by
    intro i hi
    have hb := prefix_gap_bound a s K hmono hgap i r (by omega)
    have hw := window_step a i r
    dsimp [T]
    omega
  obtain ⟨i, hin, hlo, hup⟩ := first_crossing_bin T (s - r)
    (X + q * (K * r)) (K * r) (Nat.mul_pos hK hr) hstart hfinish hstep
  refine ⟨i, by omega, hlo, ?_⟩
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hup

/-- The range representation agrees with the original endpoint interval sum. -/
theorem intervalSum_window (a : ℕ → ℕ) (i r : ℕ) (hr : 0 < r) :
    intervalSum a i (i + r - 1) = ∑ t ∈ Finset.range r, a (i + t) := by
  unfold intervalSum
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have heq : i + r - 1 + 1 - i = r := by omega
  rw [heq]

/-- More crossing slots than values in the common bin force equal interval sums.
This is the sliding-window certificate, rather than a prefix-sum pigeonhole assumption. -/
theorem equal_intervals_of_slot_count (a : ℕ → ℕ) (s K M : ℕ)
    (hK : 0 < K) (hM : M < s)
    (hmono : ∀ t u : ℕ, t < u → u < s → a t < a u)
    (hgap : ∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K)
    (hend : (∑ t ∈ Finset.range M, a t) + K * (M * M) < a (s - 1))
    (hcount : K * (M * M) <
      ∑ r ∈ Finset.range M, M * M / (r + 1)) : HasEqualIntervalSums a s := by
  classical
  let S : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.range M).sigma (fun r => Finset.range (M * M / (r + 1)))
  let X := ∑ t ∈ Finset.range M, a t
  have hbins : ∀ p ∈ S, ∃ i, i + (p.1 + 1) ≤ s ∧
      X + p.2 * (K * (p.1 + 1)) ≤ (∑ t ∈ Finset.range (p.1 + 1), a (i + t)) ∧
      (∑ t ∈ Finset.range (p.1 + 1), a (i + t)) <
        X + (p.2 + 1) * (K * (p.1 + 1)) := by
    intro p hp
    have hm := Finset.mem_sigma.mp hp
    exact window_bin a s K M hK hM hmono hgap hend (p.1 + 1) p.2
      (by omega) (by simpa using Finset.mem_range.mp hm.1)
      (Finset.mem_range.mp hm.2)
  let g : (Sigma fun _ : ℕ => ℕ) → ℕ :=
    fun p => if hp : p ∈ S then (hbins p hp).choose else 0
  have gspec : ∀ p ∈ S, g p + (p.1 + 1) ≤ s ∧
      X + p.2 * (K * (p.1 + 1)) ≤ (∑ t ∈ Finset.range (p.1 + 1), a (g p + t)) ∧
      (∑ t ∈ Finset.range (p.1 + 1), a (g p + t)) <
        X + (p.2 + 1) * (K * (p.1 + 1)) := by
    intro p hp
    simpa only [g, dif_pos hp] using (hbins p hp).choose_spec
  let f : (Sigma fun _ : ℕ => ℕ) → ℕ :=
    fun p => ∑ t ∈ Finset.range (p.1 + 1), a (g p + t)
  have hmaps : Set.MapsTo f (↑S) (↑(Finset.Ico X (X + K * (M * M)))) := by
    intro p hp
    have hm := Finset.mem_sigma.mp hp
    have hq := Finset.mem_range.mp hm.2
    have hqr : (p.2 + 1) * (p.1 + 1) ≤ M * M :=
      (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
    have hs := gspec p hp
    have hb : (p.2 + 1) * (K * (p.1 + 1)) ≤ K * (M * M) := by nlinarith
    apply Finset.mem_Ico.mpr
    dsimp [f]
    constructor <;> omega
  have hcard : (Finset.Ico X (X + K * (M * M))).card < S.card := by
    simpa only [S, Finset.card_sigma, Finset.card_range, Nat.card_Ico,
      Nat.add_sub_cancel_left] using hcount
  obtain ⟨p, hp, p', hp', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hs := gspec p hp
  have hs' := gspec p' hp'
  have hlength : p.1 ≠ p'.1 := by
    intro hl
    have hD : 0 < K * (p.1 + 1) := Nat.mul_pos hK (by omega)
    have hq : p.2 = p'.2 := by
      dsimp [f] at heq
      rw [← hl] at hs' heq
      nlinarith [hs.2.1, hs.2.2, hs'.2.1, hs'.2.2]
    apply hne
    exact Sigma.ext hl (by simpa only [heq_iff_eq] using hq)
  refine ⟨g p, g p + (p.1 + 1) - 1, g p', g p' + (p'.1 + 1) - 1,
    by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro he
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    change g p = g p' at hi
    change g p + (p.1 + 1) - 1 = g p' + (p'.1 + 1) - 1 at hj
    apply hlength
    omega
  · rw [intervalSum_window a (g p) (p.1 + 1) (by omega),
      intervalSum_window a (g p') (p'.1 + 1) (by omega)]
    exact heq

/-- For positive gap bounds, the linear factor `2K` is bounded by `2^K`. -/
theorem twice_le_two_pow (K : ℕ) (hK : 1 ≤ K) : 2 * K ≤ 2 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => decide
  | succ K hK ih =>
    rw [pow_succ]
    nlinarith

/-- Two exponential terms used in the window threshold fit under `64^K`. -/
theorem four_pow_add_thirtytwo_pow_le (K : ℕ) (hK : 1 ≤ K) :
    4 ^ K + 32 ^ K ≤ 64 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => decide
  | succ K hK ih =>
    simp only [pow_succ]
    omega

/-- The elementary sliding-window threshold is at most `a₀ * 64^K`. -/
theorem window_threshold_le (a₀ K : ℕ) (ha : 1 ≤ a₀) (hK : 1 ≤ K) :
    2 ^ (2 * K) * a₀ + 2 * K * (2 ^ (2 * K) * 2 ^ (2 * K)) ≤ a₀ * 64 ^ K := by
  let M := 2 ^ (2 * K)
  have hm : M = 4 ^ K := by
    dsimp [M]
    rw [pow_mul]
    norm_num
  have hp : 2 ^ K * (M * M) = 32 ^ K := by
    dsimp [M]
    rw [← pow_add, ← pow_add]
    have he : K + (2 * K + 2 * K) = 5 * K := by omega
    rw [he, pow_mul]
    norm_num
  have hk := twice_le_two_pow K hK
  have hb := four_pow_add_thirtytwo_pow_le K hK
  change M * a₀ + 2 * K * (M * M) ≤ a₀ * 64 ^ K
  calc
    M * a₀ + 2 * K * (M * M) ≤ a₀ * (M + 2 ^ K * (M * M)) := by
      have hmul := Nat.mul_le_mul_right (M * M) hk
      have hscale := Nat.mul_le_mul_left (2 ^ K * (M * M)) ha
      nlinarith
    _ = a₀ * (4 ^ K + 32 ^ K) := by rw [hp, hm]
    _ ≤ a₀ * 64 ^ K := Nat.mul_le_mul_left a₀ hb

/-- The explicit dyadic window has strictly more slots than its bin width. -/
theorem window_slot_count (K : ℕ) (hK : 1 ≤ K) :
    K * (2 ^ (2 * K) * 2 ^ (2 * K)) <
      ∑ r ∈ Finset.range (2 ^ (2 * K)),
        (2 ^ (2 * K) * 2 ^ (2 * K)) / (r + 1) := by
  have hc := dyadic_slot_count (4 * K) (2 * K) (by omega)
  have hm : 2 ^ (2 * K) * 2 ^ (2 * K) = 2 ^ (4 * K) := by
    rw [← pow_add]
    congr 1
    omega
  have hd : 2 ^ (4 * K) = 2 ^ (4 * K - 1) * 2 := by
    have he : 4 * K = (4 * K - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
  have hp : 0 < 2 ^ (4 * K) := by positivity
  rw [hm]
  nlinarith

/-- The elementary sliding-window argument gives the explicit constant `64`.
Monotonicity and adjacent-gap bounds are required only within the prefix. -/
theorem equal_intervals_of_large_last (a₀ K : ℕ) (ha : 1 ≤ a₀) (hK : 1 ≤ K)
    (a : ℕ → ℕ) (s : ℕ) (hzero : a 0 = a₀)
    (hmono : ∀ t u : ℕ, t < u → u < s → a t < a u)
    (hgap : ∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K)
    (hs : 0 < s) (hlast : a₀ * 64 ^ K < a (s - 1)) :
    HasEqualIntervalSums a s := by
  let M := 2 ^ (2 * K)
  have hpos : 1 ≤ M := by
    have hp : 0 < M := by dsimp [M]; positivity
    omega
  have hthreshold : M * a₀ + 2 * K * (M * M) < a (s - 1) :=
    lt_of_le_of_lt (window_threshold_le a₀ K ha hK) hlast
  have hM : M < s := by
    by_contra hnot
    have hsm : s ≤ M := by omega
    have hb := prefix_gap_bound a s K hmono hgap 0 (s - 1) (by omega)
    simp only [Nat.zero_add, hzero] at hb
    have hb' : a (s - 1) ≤ a₀ + K * M :=
      hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K (by omega)) a₀)
    have hbound : a₀ + K * M ≤ M * a₀ + 2 * K * (M * M) := by
      have haM := Nat.mul_le_mul_right a₀ hpos
      have hMM : M ≤ M * M := by nlinarith
      have hkM := Nat.mul_le_mul_left K hMM
      nlinarith
    exact (not_lt_of_ge (hb'.trans hbound)) hthreshold
  have hsum : (∑ t ∈ Finset.range M, a t) ≤ M * (a₀ + K * M) := by
    have hterms : ∀ t ∈ Finset.range M, a t ≤ a₀ + K * M := by
      intro t ht
      have htm := Finset.mem_range.mp ht
      have hb := prefix_gap_bound a s K hmono hgap 0 t (by omega)
      simp only [Nat.zero_add, hzero] at hb
      exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K (by omega)) a₀)
    have hsum' := Finset.sum_le_sum hterms
    simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using hsum'
  have hend : (∑ t ∈ Finset.range M, a t) + K * (M * M) < a (s - 1) := by
    nlinarith
  exact equal_intervals_of_slot_count a s K M (by omega) hM hmono hgap hend
    (window_slot_count K hK)

/-- Erdős #1213, attributed to Hegyvári (1986) by the Erdős problem archive:
there is a threshold forcing two distinct equal-sum nonempty intervals.
The proof here is an independently checked elementary sliding-window argument;
it does not claim to reproduce the unavailable Hegyvári primary text. -/
theorem hegyvari_equal_interval_sums (a₀ K : ℕ) (ha : 1 ≤ a₀) (hK : 1 ≤ K) :
    ∃ F : ℕ, ∀ (a : ℕ → ℕ) (s : ℕ),
      a 0 = a₀ →
      (∀ t u : ℕ, t < u → u < s → a t < a u) →
      (∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K) →
      0 < s → F < a (s - 1) →
      HasEqualIntervalSums a s := by
  exact ⟨a₀ * 64 ^ K, equal_intervals_of_large_last a₀ K ha hK⟩

/-- The quantitative exponential threshold holds with the explicit absolute
constant `C = 64`, by the independently checked sliding-window/counting route. -/
theorem hegyvari_quantitative :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (a₀ K : ℕ), 1 ≤ a₀ → 1 ≤ K →
      ∀ (a : ℕ → ℕ) (s : ℕ),
        a 0 = a₀ →
        (∀ t u : ℕ, t < u → u < s → a t < a u) →
        (∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K) →
        0 < s → a₀ * C ^ K < a (s - 1) →
        HasEqualIntervalSums a s := by
  exact ⟨64, by decide, equal_intervals_of_large_last⟩

/-- A joint concrete model of all archived prefix and quantitative hypotheses.
In particular the prefix is nonempty and the strict threshold is satisfiable. -/
example : 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    (fun t : ℕ => t + 1) 0 = 1 ∧
    (∀ t u : ℕ, t < u → u < 66 → t + 1 < u + 1) ∧
    (∀ t : ℕ, t + 1 < 66 → (t + 1 + 1) - (t + 1) ≤ 1) ∧
    0 < (66 : ℕ) ∧ 1 * 64 ^ 1 < (fun t : ℕ => t + 1) (66 - 1) := by
  refine ⟨by decide, by decide, rfl, ?_, ?_, by decide, by decide⟩
  · intro t u htu hu
    omega
  · intro t ht
    omega

/-- A concrete first-crossing model, with a nonzero step and a nonempty index domain. -/
example : ∃ i, i ≤ 4 ∧ 2 ≤ i ∧ i < 2 + 1 := by
  exact first_crossing_bin id 4 2 1 (by decide) (by decide) (by decide)
    (fun i hi => by simp)

/-- The dyadic lower bound is already nontrivial at the smallest gap bound. -/
example : 1 * (2 ^ (2 * 1) * 2 ^ (2 * 1)) <
    ∑ r ∈ Finset.range (2 ^ (2 * 1)),
      (2 ^ (2 * 1) * 2 ^ (2 * 1)) / (r + 1) := by
  exact window_slot_count 1 (by decide)

/-- The sliding-window certificate's assumptions are jointly satisfiable. -/
example : HasEqualIntervalSums (fun t => t + 1) 66 := by
  apply equal_intervals_of_slot_count (fun t => t + 1) 66 1 4
      (by decide) (by decide)
  · intro t u htu hu
    omega
  · intro t ht
    omega
  · decide
  · decide

/-- A concrete endpoint/range translation at positive length. -/
example : intervalSum (fun t => t + 1) 2 (2 + 3 - 1) =
    ∑ t ∈ Finset.range 3, (2 + t + 1) := by
  exact intervalSum_window (fun t => t + 1) 2 3 (by decide)

end ErdosCandidates.E1213
