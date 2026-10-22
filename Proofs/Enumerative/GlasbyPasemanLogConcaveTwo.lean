/-
# Generalized Glasby-Paseman sequences for exponent two

Seok Hyun Byun and Svetlana Poznanović, "Unimodality and log-concavity of
Generalized Glasby-Paseman sequences", arXiv:2604.14639, equation (BP3),
Conjecture 1.1(a),(b) and Theorem 1.2(a).
For `l = 2`, every real `a > 0` and every natural `m`, the quotient
`(Σ_{i≤r}(C(m,i)a^i)^2)/(Σ_{i≤r}(C(r,i)a^i)^2)` is log-concave and
unimodal on `0 ≤ r ≤ m`. The numerator is log-concave and the positive
denominator log-convex. General `l` and the peak-location/asymptotic
claims in Conjecture 1.1(c),(d) are outside this module's scope.
-/
import Mathlib

set_option autoImplicit false

namespace GlasbyPasemanLogConcaveTwo

open Finset

/-- The generalized Glasby-Paseman sequence (BP3) of arXiv:2604.14639:
`g_{m,l,a}(r) = (∑_{i ≤ r} (C(m,i) a^i)^l) / (∑_{i ≤ r} (C(r,i) a^i)^l)`. -/
noncomputable def gpSeq (l m r : ℕ) (a : ℝ) : ℝ :=
  (∑ i ∈ range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
    (∑ i ∈ range (r + 1), ((r.choose i : ℝ) * a ^ i) ^ l)

/-- The partial power sum `∑_{i ≤ r} (C(m,i) a^i)^2`; the numerator of
`g_{m,2,a}(r)` is `partialSq m r a` and its denominator is `partialSq r r a`. -/
noncomputable def partialSq (m r : ℕ) (a : ℝ) : ℝ :=
  ∑ i ∈ range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ 2

/-- For `l = 2` the sequence is the quotient of two partial power sums. -/
theorem gpSeq_two_eq (m r : ℕ) (a : ℝ) : gpSeq 2 m r a = partialSq m r a / partialSq r r a :=
  rfl

/-- Example (paper, eq. (BP4)): for `a = 1`, `g_4(1) = (1 + 4^2) / C(2,1) = 17/2`. -/
example : gpSeq 2 4 1 1 = 17 / 2 := by
  norm_num [gpSeq, sum_range_succ]

/-- Examples with `a = 2`: `g_{3,2,2}(2) = (1 + 6^2 + 12^2) / (1 + 4^2 + 4^2) = 181/33`. -/
example : gpSeq 2 3 2 2 = 181 / 33 := by
  norm_num [gpSeq, sum_range_succ, Nat.choose]

/-- Examples for `l = 1, a = 1` (the original Glasby-Paseman sequence
`2^{-r} ∑_{i ≤ r} C(m,i)`): `g_{3,1,1}(1) = (1 + 3)/2 = 2`. -/
example : gpSeq 1 3 1 1 = 2 := by
  norm_num [gpSeq, sum_range_succ]

/-- Log-concavity of binomial coefficients: `C(m,i) C(m,i+2) ≤ C(m,i+1)^2`. -/
theorem choose_mul_choose_add_two_le (m i : ℕ) :
    m.choose i * m.choose (i + 2) ≤ m.choose (i + 1) ^ 2 := by
  have h1 : m.choose (i + 1) * (i + 1) = m.choose i * (m - i) := Nat.choose_succ_right_eq m i
  have h2 : m.choose (i + 2) * (i + 2) = m.choose (i + 1) * (m - (i + 1)) :=
    Nat.choose_succ_right_eq m (i + 1)
  have key : m.choose i * m.choose (i + 2) * ((i + 1) * (i + 2)) ≤
      m.choose (i + 1) ^ 2 * ((i + 1) * (i + 2)) := by
    calc m.choose i * m.choose (i + 2) * ((i + 1) * (i + 2))
        = (m.choose i * (i + 1)) * (m.choose (i + 2) * (i + 2)) := by ring
      _ = (m.choose i * (i + 1)) * (m.choose (i + 1) * (m - (i + 1))) := by rw [h2]
      _ ≤ (m.choose i * (i + 2)) * (m.choose (i + 1) * (m - i)) := by gcongr <;> omega
      _ = m.choose (i + 1) * (m.choose i * (m - i)) * (i + 2) := by ring
      _ = m.choose (i + 1) ^ 2 * ((i + 1) * (i + 2)) := by rw [← h1]; ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- Inductive invariant behind `partialSum_logConcave`: with `z_k = ∑_{i ≤ k} w_i`,
`z_k w_{k+2} ≤ z_{k+1} w_{k+1}` whenever `k + 2 ≤ M`. -/
theorem partialSum_shift (w : ℕ → ℝ) (M : ℕ) (hpos : ∀ i, i ≤ M → 0 < w i)
    (hlc : ∀ i, i + 2 ≤ M → w i * w (i + 2) ≤ w (i + 1) ^ 2) :
    ∀ k, k + 2 ≤ M →
      (∑ i ∈ range (k + 1), w i) * w (k + 2) ≤ (∑ i ∈ range (k + 2), w i) * w (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro hM
    have h0 := hpos 0 (by omega)
    have h1 := hpos 1 (by omega)
    have hl := hlc 0 hM
    simp only [sum_range_succ, sum_range_zero, zero_add] at hl ⊢
    nlinarith
  | succ k ih =>
    intro hM
    have hQ := ih (by omega)
    have hw1 := hpos (k + 1) (by omega)
    have hl := hlc (k + 1) hM
    set S := ∑ i ∈ range (k + 1), w i with hS
    have hS1 : ∑ i ∈ range (k + 2), w i = S + w (k + 1) := sum_range_succ _ _
    have hS2 : ∑ i ∈ range (k + 3), w i = S + w (k + 1) + w (k + 2) := by
      rw [sum_range_succ, hS1]
    have hSnn : 0 ≤ S := sum_nonneg fun i hi => (hpos i (by simp at hi; omega)).le
    rw [hS1] at hQ
    rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring, hS1, hS2]
    -- derived: (S + w(k+1)) w(k+2) ≤ w(k+1) (S + w(k+1) + w(k+2))
    have hD : (S + w (k + 1)) * w (k + 2) ≤ w (k + 1) * (S + w (k + 1) + w (k + 2)) := by
      nlinarith
    have hT : w (k + 1) * ((S + w (k + 1)) * w (k + 3)) ≤
        w (k + 1) * ((S + w (k + 1) + w (k + 2)) * w (k + 2)) := by
      have hA : 0 ≤ S + w (k + 1) := by linarith
      calc w (k + 1) * ((S + w (k + 1)) * w (k + 3))
          = (S + w (k + 1)) * (w (k + 1) * w (k + 1 + 2)) := by ring
        _ ≤ (S + w (k + 1)) * (w (k + 1 + 1) ^ 2) := by gcongr
        _ = ((S + w (k + 1)) * w (k + 2)) * w (k + 2) := by ring
        _ ≤ (w (k + 1) * (S + w (k + 1) + w (k + 2))) * w (k + 2) := by
          gcongr
          exact (hpos (k + 2) (by omega)).le
        _ = w (k + 1) * ((S + w (k + 1) + w (k + 2)) * w (k + 2)) := by ring
    exact le_of_mul_le_mul_left hT hw1

/-- Partial sums of a sequence positive on `0..M` and log-concave there are
log-concave: `z_k z_{k+2} ≤ z_{k+1}^2` for `k + 2 ≤ M`, where `z_k = ∑_{i ≤ k} w_i`
(a division-free form of Lemma 2.1 of arXiv:2604.14639). -/
theorem partialSum_logConcave (w : ℕ → ℝ) (M : ℕ) (hpos : ∀ i, i ≤ M → 0 < w i)
    (hlc : ∀ i, i + 2 ≤ M → w i * w (i + 2) ≤ w (i + 1) ^ 2) (k : ℕ) (hk : k + 2 ≤ M) :
    (∑ i ∈ range (k + 1), w i) * (∑ i ∈ range (k + 3), w i) ≤
      (∑ i ∈ range (k + 2), w i) ^ 2 := by
  have hQ := partialSum_shift w M hpos hlc k hk
  set S := ∑ i ∈ range (k + 1), w i with hS
  have h1 : ∑ i ∈ range (k + 2), w i = S + w (k + 1) := sum_range_succ _ _
  have h2 : ∑ i ∈ range (k + 3), w i = S + w (k + 1) + w (k + 2) := by
    rw [sum_range_succ, h1]
  rw [h1] at hQ
  rw [h1, h2]
  -- `(S + w₁)^2 - S (S + w₁ + w₂) = (S + w₁) w₁ - S w₂ ≥ 0`
  nlinarith [hQ]

/-- Cauchy-Schwarz identity, left factor: `∑_{i ≤ n+1} (C(n,i) a^i)^2 = D_n`. -/
theorem sum_sq_left (n : ℕ) (a : ℝ) :
    ∑ i ∈ range (n + 2), ((n.choose i : ℝ) * a ^ i) ^ 2 = partialSq n n a := by
  rw [sum_range_succ, Nat.choose_succ_self]
  simp [partialSq]

/-- Cauchy-Schwarz identity, cross term (Pascal reindexing):
`∑_{i ≤ n+1} C(n,i) a^i · a^i (C(n+1,i) + a^2 C(n+1,i+1)) = D_{n+1}`. -/
theorem sum_mul_cross (n : ℕ) (a : ℝ) :
    ∑ i ∈ range (n + 2), ((n.choose i : ℝ) * a ^ i) *
      (a ^ i * (((n + 1).choose i : ℝ) + a ^ 2 * ((n + 1).choose (i + 1) : ℝ))) =
      partialSq (n + 1) (n + 1) a := by
  have hsplit : ∑ i ∈ range (n + 2), ((n.choose i : ℝ) * a ^ i) *
      (a ^ i * (((n + 1).choose i : ℝ) + a ^ 2 * ((n + 1).choose (i + 1) : ℝ))) =
      ∑ i ∈ range (n + 2), (n.choose i : ℝ) * ((n + 1).choose i : ℝ) * a ^ (2 * i) +
      ∑ i ∈ range (n + 2), (n.choose i : ℝ) * ((n + 1).choose (i + 1) : ℝ) * a ^ (2 * i + 2) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, partialSq,
    sum_range_succ' (fun i => (((n + 1).choose i : ℝ) * a ^ i) ^ 2) (n + 1),
    sum_range_succ' (fun i => (n.choose i : ℝ) * ((n + 1).choose i : ℝ) * a ^ (2 * i)) (n + 1),
    sum_range_succ (fun i => (n.choose i : ℝ) * ((n + 1).choose (i + 1) : ℝ) * a ^ (2 * i + 2))
      (n + 1), Nat.choose_succ_self]
  have hmain : ∑ k ∈ range (n + 1),
      (n.choose (k + 1) : ℝ) * ((n + 1).choose (k + 1) : ℝ) * a ^ (2 * (k + 1)) +
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * ((n + 1).choose (k + 1) : ℝ) * a ^ (2 * k + 2) =
      ∑ k ∈ range (n + 1), (((n + 1).choose (k + 1) : ℝ) * a ^ (k + 1)) ^ 2 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ' n k]
    push_cast
    ring
  rw [← hmain]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, pow_zero, mul_one,
    zero_mul, add_zero, mul_zero, one_pow]
  ring

/-- Cauchy-Schwarz identity, right factor (Pascal reindexing):
`∑_{i ≤ n+1} (a^i (C(n+1,i) + a^2 C(n+1,i+1)))^2 = D_{n+2} - a^2`. -/
theorem sum_sq_right (n : ℕ) (a : ℝ) :
    ∑ i ∈ range (n + 2),
      (a ^ i * (((n + 1).choose i : ℝ) + a ^ 2 * ((n + 1).choose (i + 1) : ℝ))) ^ 2 =
      partialSq (n + 2) (n + 2) a - a ^ 2 := by
  set X := ∑ i ∈ range (n + 2), ((n + 1).choose i : ℝ) ^ 2 * a ^ (2 * i) with hX
  set Y := ∑ i ∈ range (n + 2),
    2 * ((n + 1).choose i : ℝ) * ((n + 1).choose (i + 1) : ℝ) * a ^ (2 * i + 2) with hY
  set Z := ∑ i ∈ range (n + 2), ((n + 1).choose (i + 1) : ℝ) ^ 2 * a ^ (2 * i + 4) with hZ
  set P := ∑ i ∈ range (n + 2), ((n + 1).choose i : ℝ) ^ 2 * a ^ (2 * i + 2) with hP
  set R := ∑ i ∈ range (n + 2), ((n + 1).choose (i + 1) : ℝ) ^ 2 * a ^ (2 * i + 2) with hR
  have hL : ∑ i ∈ range (n + 2),
      (a ^ i * (((n + 1).choose i : ℝ) + a ^ 2 * ((n + 1).choose (i + 1) : ℝ))) ^ 2 =
      X + Y + Z := by
    rw [hX, hY, hZ, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hRHS : partialSq (n + 2) (n + 2) a = P + Y + R + 1 := by
    rw [partialSq, sum_range_succ' (fun i => (((n + 2).choose i : ℝ) * a ^ i) ^ 2) (n + 2),
      hP, hY, hR, ← sum_add_distrib, ← sum_add_distrib]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_pow]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ' (n + 1) k]
    push_cast
    ring
  have hXR : X = R + 1 := by
    rw [hX, hR, sum_range_succ' _ (n + 1), sum_range_succ _ (n + 1), Nat.choose_succ_self]
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, mul_zero, pow_zero,
      one_mul]
    congr 1
  have hZP : Z + a ^ 2 = P := by
    rw [hZ, hP,
      sum_range_succ (fun i => ((n + 1).choose (i + 1) : ℝ) ^ 2 * a ^ (2 * i + 4)) (n + 1),
      sum_range_succ' (fun i => ((n + 1).choose i : ℝ) ^ 2 * a ^ (2 * i + 2)) (n + 1),
      Nat.choose_succ_self]
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, one_pow, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, mul_zero,
      zero_add]
    congr 1
  rw [hL, hRHS]
  linarith

/-- Log-convexity of the type-B Narayana polynomials in `a^2`:
`D_{n+1}^2 ≤ D_n (D_{n+2} - a^2)` where `D_s = ∑_{i ≤ s} (C(s,i) a^i)^2`,
by Cauchy-Schwarz; valid for every real `a`. -/
theorem partialSq_diag_sq_le_sub (a : ℝ) (n : ℕ) :
    partialSq (n + 1) (n + 1) a ^ 2 ≤
      partialSq n n a * (partialSq (n + 2) (n + 2) a - a ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq (range (n + 2))
    (fun i => (n.choose i : ℝ) * a ^ i)
    (fun i => a ^ i * (((n + 1).choose i : ℝ) + a ^ 2 * ((n + 1).choose (i + 1) : ℝ)))
  rw [sum_mul_cross, sum_sq_left, sum_sq_right] at hcs
  exact hcs

/-- Every partial power sum is at least its `i = 0` term `1`, hence positive. -/
theorem one_le_partialSq (m r : ℕ) (a : ℝ) : 1 ≤ partialSq m r a := by
  rw [partialSq, sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_pow]
  have h : 0 ≤ ∑ i ∈ range r, ((m.choose (i + 1) : ℝ) * a ^ (i + 1)) ^ 2 :=
    sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- Log-convexity of the denominators: `D_{n+1}^2 ≤ D_n D_{n+2}`. -/
theorem partialSq_diag_logConvex (a : ℝ) (n : ℕ) :
    partialSq (n + 1) (n + 1) a ^ 2 ≤ partialSq n n a * partialSq (n + 2) (n + 2) a := by
  have h := partialSq_diag_sq_le_sub a n
  have hD := one_le_partialSq n n a
  nlinarith [sq_nonneg a]

/-- Log-concavity of the numerators: for `a ≠ 0` and `r + 2 ≤ m`,
`N_r N_{r+2} ≤ N_{r+1}^2` where `N_r = ∑_{i ≤ r} (C(m,i) a^i)^2`. -/
theorem partialSq_logConcave {a : ℝ} (ha : a ≠ 0) {m r : ℕ} (hrm : r + 2 ≤ m) :
    partialSq m r a * partialSq m (r + 2) a ≤ partialSq m (r + 1) a ^ 2 := by
  set w : ℕ → ℝ := fun i => ((m.choose i : ℝ) * a ^ i) ^ 2 with hw
  have hpos : ∀ i, i ≤ m → 0 < w i := fun i hi => by
    have hc : (0 : ℝ) < m.choose i := by exact_mod_cast Nat.choose_pos hi
    have hai : a ^ i ≠ 0 := pow_ne_zero i ha
    positivity
  have hlc : ∀ i, i + 2 ≤ m → w i * w (i + 2) ≤ w (i + 1) ^ 2 := fun i _ => by
    have hc : ((m.choose i : ℝ) * (m.choose (i + 2) : ℝ)) ≤ (m.choose (i + 1) : ℝ) ^ 2 := by
      exact_mod_cast choose_mul_choose_add_two_le m i
    have hc0 : 0 ≤ ((m.choose i : ℝ) * (m.choose (i + 2) : ℝ)) := by positivity
    calc w i * w (i + 2)
        = (((m.choose i : ℝ) * (m.choose (i + 2) : ℝ)) * (a ^ 2) ^ (i + 1)) ^ 2 := by
          simp only [hw]; ring
      _ ≤ ((m.choose (i + 1) : ℝ) ^ 2 * (a ^ 2) ^ (i + 1)) ^ 2 := by gcongr
      _ = w (i + 1) ^ 2 := by simp only [hw]; ring
  have key := partialSum_logConcave w m hpos hlc r hrm
  simpa only [partialSq, hw, show r + 1 + 1 = r + 2 by ring, show r + 2 + 1 = r + 3 by ring]
    using key

/-- For `l = 2` and every real `a > 0`, the quotient sequence is log-concave:
`g(r)g(r+2) ≤ g(r+1)^2` whenever `r+2 ≤ m`.
This is Conjecture 1.1(b) of arXiv:2604.14639 for `l = 2`, with no exceptional `m`. -/
theorem gpSeq_two_logConcave {a : ℝ} (ha : 0 < a) {m r : ℕ} (hrm : r + 2 ≤ m) :
    gpSeq 2 m r a * gpSeq 2 m (r + 2) a ≤ gpSeq 2 m (r + 1) a ^ 2 := by
  rw [gpSeq_two_eq, gpSeq_two_eq, gpSeq_two_eq]
  have hN := partialSq_logConcave ha.ne' hrm
  have hD := partialSq_diag_logConvex a r
  have hD0 := one_le_partialSq r r a
  have hD1 := one_le_partialSq (r + 1) (r + 1) a
  have hD2 := one_le_partialSq (r + 2) (r + 2) a
  have hN0 := one_le_partialSq m r a
  have hN2 := one_le_partialSq m (r + 2) a
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc partialSq m r a * partialSq m (r + 2) a * partialSq (r + 1) (r + 1) a ^ 2
      ≤ partialSq m (r + 1) a ^ 2 * (partialSq r r a * partialSq (r + 2) (r + 2) a) := by
        gcongr

/-- A sequence positive on `0..m` and log-concave there is unimodal: it weakly
increases up to some `j ≤ m` and weakly decreases on `j..m`. -/
theorem unimodal_of_logConcave (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ r, r ≤ m → 0 < g r)
    (hlc : ∀ r, r + 2 ≤ m → g r * g (r + 2) ≤ g (r + 1) ^ 2) :
    ∃ j ≤ m, MonotoneOn g (Set.Iic j) ∧ AntitoneOn g (Set.Icc j m) := by
  classical
  have hex : ∃ j, m ≤ j ∨ g (j + 1) ≤ g j := ⟨m, Or.inl le_rfl⟩
  have hjm : Nat.find hex ≤ m := Nat.find_min' hex (Or.inl le_rfl)
  have hup : ∀ r < Nat.find hex, g r ≤ g (r + 1) := fun r hr => by
    have hn := Nat.find_min hex hr
    simp only [not_or, not_le] at hn
    exact hn.2.le
  have hdown : ∀ r, Nat.find hex ≤ r → r < m → g (r + 1) ≤ g r := by
    intro r hjr
    induction r, hjr using Nat.le_induction with
    | base =>
      intro hrm
      rcases Nat.find_spec hex with h | h
      · omega
      · exact h
    | succ r hjr ih =>
      intro hrm
      have ih' := ih (by omega)
      have hl := hlc r (by omega)
      have hp := hpos r (by omega)
      have hp1 := hpos (r + 1) (by omega)
      have hstep : g r * g (r + 1 + 1) ≤ g r * g (r + 1) :=
        calc g r * g (r + 1 + 1) ≤ g (r + 1) ^ 2 := hl
          _ = g (r + 1) * g (r + 1) := sq _
          _ ≤ g (r + 1) * g r := mul_le_mul_of_nonneg_left ih' hp1.le
          _ = g r * g (r + 1) := mul_comm _ _
      exact le_of_mul_le_mul_left hstep hp
  refine ⟨Nat.find hex, hjm, ?_, ?_⟩
  · refine monotoneOn_of_le_succ Set.ordConnected_Iic fun r _ _ hr1 => ?_
    rw [Order.succ_eq_add_one] at hr1 ⊢
    exact hup r (by simp only [Set.mem_Iic] at hr1; omega)
  · refine antitoneOn_of_succ_le Set.ordConnected_Icc fun r _ hr hr1 => ?_
    rw [Order.succ_eq_add_one] at hr1 ⊢
    simp only [Set.mem_Icc] at hr hr1
    exact hdown r hr.1 (by omega)

/-- For `l = 2`, every real `a > 0` and every `m`, there is `j ≤ m` such
that the quotient sequence increases weakly on `0..j` and decreases weakly
on `j..m` (Conjecture 1.1(a) of arXiv:2604.14639 for `l = 2`). -/
theorem gpSeq_two_unimodal {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ j ≤ m, MonotoneOn (fun r => gpSeq 2 m r a) (Set.Iic j) ∧
      AntitoneOn (fun r => gpSeq 2 m r a) (Set.Icc j m) := by
  refine unimodal_of_logConcave (fun r => gpSeq 2 m r a) m (fun r _ => ?_)
    (fun r hr => gpSeq_two_logConcave ha hr)
  rw [gpSeq_two_eq]
  have h1 := one_le_partialSq m r a
  have h2 := one_le_partialSq r r a
  positivity

/-- Non-vacuity: the hypotheses of `gpSeq_two_logConcave` are met at
`a = 2, m = 3, r = 0`. -/
example : gpSeq 2 3 0 2 * gpSeq 2 3 2 2 ≤ gpSeq 2 3 1 2 ^ 2 :=
  gpSeq_two_logConcave (by norm_num) (by norm_num)

end GlasbyPasemanLogConcaveTwo
