/-
  Erdős Problem #20 — THE SPREAD LEMMA, machine-checked (MNSZ second-moment
  route), and the resulting unconditional sunflower bound
  |F| > (C·s·(log₂ k + 1))^k  ⟹  F contains an s-sunflower.

  Primary source: Mossel–Niles-Weed–Sun–Zadik, "A second moment proof of the
  spread lemma", arXiv:2209.11347 (published as "A Bayesian proof of the
  spread lemma", RSA 2025). The extraction step follows
  Bell–Chueluecha–Warnke, "Note on Sunflowers", arXiv:2009.09327 (the
  2s-classes + linearity-of-expectation twist that removes the log s), with
  Rao, "Coding for Sunflowers", arXiv:1909.04774 as comparison text.

  Everything is finite counting over ℚ: probability measures are weight
  functions `Finset (Fin n) → ℚ`, expectations are `Finset.sum` over the
  `Fintype` of all subsets, and product measures are iterated products of
  weights. No measure theory, no entropy, no real analysis.

  PAPER ↔ LEAN MAP (MNSZ numbering):
    π (R-spread measure)          → `w` with `IsProbW w`, `IsSpreadW R w`
    Q_p (p-biased subset law)     → `biasedW q` (§1)
    planted model P_p(A,Y,A')     → `cplW w q a v b` (§3; Y = a ∪ v)
    Z_Y (eq. 2.3, partition fn)   → `partZ w q y`
    Z_Y(A,δ) (truncated Z)        → `partZcut w q c a y`
    posterior P_p(A'=b | Y)       → `postW w q y b`
    Lemma 2.2 (planted-to-null)   → `cut_prob_eq` (§3)
    Lemma 2.3 (planting trick)    → `cut_prob_le` (§3; ε := (5/2)·c)
    Lemma 2.4 + Thm 2.1 proof     → `sum_cplW_cut_eq`, `second_moment_bound`
    Theorem 2.1 (one-step)        → `one_step` : E[|B\V|/|A|] ≤ 6c
    π_ℓ (conditional laws)        → `nextW` iterates (§4)
    the m-step coupling P         → `trajW`/`fullW` on `Traj n m` (§4)
    Thm 1.2 iteration             → `fail_prob_le` (§5)
    sunflower extraction          → `spread_lemma_core` (§6; BCW form)

  DELIBERATE DIVERGENCES from the paper (all loss-free for the headline):
  · the irrational contraction scale δ = (pR)^{-1/3} is replaced by a free
    rational parameter `c` with `1 ≤ c³·(q·R)`; call sites use c = 1/48;
  · ε := √6·δ in Lemma 2.3 is replaced by ε := (5/2)·c (2.5² ≥ 6);
  · the binomial-coefficient bound C(N,ℓ) ≤ (eN/ℓ)^ℓ is replaced by the
    rational C(N,ℓ) ≤ N^ℓ/ℓ! ≤ (3N/ℓ)^ℓ via ℓ! ≥ (ℓ/3)^ℓ;
  · the Hölder/(1/m)-th-moment aggregation of Thm 1.2 is replaced by a
    bad-round count: on failure, rounds with ratio < 1/2 number at most
    log₂ k, so Σ ratios ≥ (m - log₂ k)/2, and plain Markov finishes; this
    avoids real exponents entirely (cost: a factor 2 in m and 48³ vs 700);
  · the per-petal failure 0.1 of MNSZ Thm 1.2 is replaced by the BCW
    extraction: 2s classes at per-class failure ≤ 1/2 + linearity +
    integer pigeonhole (no union bound, no ε = 1/s).

  CONSTANTS (not optimized; the headline constant is C = 884736 = 8·48³):
    c = 1/48, per-round E[ratio] ≤ 6c = 1/8, L = log₂ k + 1 (so k ≤ 2^L,
    as required by `sum_xRatio_ge`), m = 2(L+1) = 2(log₂ k + 2) rounds,
    per-class density δ = 1/(2s), per-round density q = δ/m, spread
    requirement r ≥ 48³·2s·m = 442368·s·(log₂ k + 2), absorbed into
    884736·s·(log₂ k + 1) via log₂ k + 2 ≤ 2(log₂ k + 1).

  STATEMENT-SHAPE NOTE (divergence from the task card's goal sketch): the
  card sketches `C·s·Nat.log 2 k ≤ r`, which is vacuous at k = 1
  (Nat.log 2 1 = 0) where the lemma is false as sketched; this file uses
  `C·s·(Nat.log 2 k + 1) ≤ r` throughout, which is the same Θ(s·log k)
  for k ≥ 2 and correct at k = 1.

  WIRING NOTE: the final unconditional theorem goes through the committed
  link-local reduction `hasSunflower_of_forall_linkAt_isRSpread`
  (SpreadDefect.lean), NOT the universal interface
  `hasSunflower_of_forall_isRSpread` (Spread.lean): the latter quantifies
  the spread lemma over ALL uniformities k', which no fixed r satisfies;
  the link-local form only demands levels k' = k - |Z| ≤ k, where
  monotonicity of Nat.log closes the gap.

  Novelty framing: no machine-checked proof of the ALWZ-type spread lemma
  in any proof assistant was found as of 2026-06 (AFP's `Sunflowers` entry
  is the classical Erdős–Rado bound; Mathlib has neither). Phrased against
  the refereed state of the art (BCW: best refereed bound (Cp log k)^k).
-/

import Mathlib.Algebra.Order.Field.GeomSum
import Proofs.Erdos20.SpreadDefect

open Finset

namespace SpreadLemma

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- §1 BIASED WEIGHTS AND THE POWERSET ENGINE
-- ════════════════════════════════════════════════════════════════════

/-- The `q`-biased product weight of `v ⊆ Fin n`: each element present
    with probability `q` independently. MNSZ's `Q_p`. -/
def biasedW (q : ℚ) (v : Finset (Fin n)) : ℚ :=
  q ^ v.card * (1 - q) ^ (n - v.card)

theorem biasedW_nonneg {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (v : Finset (Fin n)) : 0 ≤ biasedW q v := by
  have h1 : (0:ℚ) ≤ 1 - q := by linarith
  exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg h1 _)

/-- Powerset engine: the binomial expansion over subsets of `s`. -/
theorem sum_pow_mul_pow_powerset {α : Type*} [DecidableEq α]
    (s : Finset α) (x y : ℚ) :
    ∑ t ∈ s.powerset, x ^ t.card * y ^ (s.card - t.card) = (x + y) ^ s.card := by
  have h := Finset.prod_add (fun _ : α => x) (fun _ : α => y) s
  simp only [Finset.prod_const] at h
  rw [h]
  exact Finset.sum_congr rfl fun t ht => by
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht)]

/-- Interval-slice mass: the biased weight of `{v : lo ⊆ v ⊆ hi}` is
    `q^|lo| (1-q)^(n-|hi|)` — elements of `lo` are forced in, elements
    outside `hi` are forced out, the rest are free. -/
theorem sum_biasedW_between {q : ℚ} {lo hi : Finset (Fin n)} (hlh : lo ⊆ hi) :
    ∑ v : Finset (Fin n), (if lo ⊆ v ∧ v ⊆ hi then biasedW q v else 0)
      = q ^ lo.card * (1 - q) ^ (n - hi.card) := by
  rw [← Finset.sum_filter]
  have hbij : ∑ v ∈ univ.filter (fun v => lo ⊆ v ∧ v ⊆ hi), biasedW q v
      = ∑ u ∈ (hi \ lo).powerset, biasedW q (lo ∪ u) := by
    refine Finset.sum_nbij' (i := fun v => v \ lo) (j := fun u => lo ∪ u)
      ?_ ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨hlov, hvhi⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset_sdiff hvhi (Finset.Subset.refl lo))
    · intro u hu
      have huhl : u ⊆ hi \ lo := Finset.mem_powerset.mp hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.subset_union_left, ?_⟩
      exact Finset.union_subset hlh (huhl.trans Finset.sdiff_subset)
    · intro v hv
      exact Finset.union_sdiff_of_subset (Finset.mem_filter.mp hv).2.1
    · intro u hu
      have huhl : u ⊆ hi \ lo := Finset.mem_powerset.mp hu
      exact Finset.union_sdiff_cancel_left
        (Finset.disjoint_left.mpr fun x hxlo hxu =>
          (Finset.mem_sdiff.mp (huhl hxu)).2 hxlo)
    · intro v hv
      rw [Finset.union_sdiff_of_subset (Finset.mem_filter.mp hv).2.1]
  rw [hbij]
  have hterm : ∀ u ∈ (hi \ lo).powerset,
      biasedW q (lo ∪ u)
        = (q ^ lo.card * (1 - q) ^ (n - hi.card)) *
            (q ^ u.card * (1 - q) ^ ((hi \ lo).card - u.card)) := by
    intro u hu
    have huhl : u ⊆ hi \ lo := Finset.mem_powerset.mp hu
    have hdisj : Disjoint lo u := Finset.disjoint_left.mpr
      fun x hxlo hxu => (Finset.mem_sdiff.mp (huhl hxu)).2 hxlo
    have hcard : (lo ∪ u).card = lo.card + u.card :=
      Finset.card_union_of_disjoint hdisj
    have hhin : hi.card ≤ n := by
      calc hi.card ≤ (univ : Finset (Fin n)).card := Finset.card_le_card
            (Finset.subset_univ hi)
        _ = n := Finset.card_fin n
    have hcards : (hi \ lo).card = hi.card - lo.card :=
      Finset.card_sdiff_of_subset hlh
    have hulo : u.card ≤ hi.card - lo.card := by
      calc u.card ≤ (hi \ lo).card := Finset.card_le_card huhl
        _ = hi.card - lo.card := hcards
    have hloh : lo.card ≤ hi.card := Finset.card_le_card hlh
    unfold biasedW
    rw [hcard, hcards, pow_add]
    have hexp : n - (lo.card + u.card)
        = (n - hi.card) + ((hi.card - lo.card) - u.card) := by omega
    rw [hexp, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_pow_mul_pow_powerset]
  norm_num

/-- Total mass of the biased weight is 1. -/
theorem sum_biasedW (q : ℚ) :
    ∑ v : Finset (Fin n), biasedW q v = 1 := by
  have h := sum_biasedW_between (q := q)
    (Finset.empty_subset (univ : Finset (Fin n)))
  simp only [Finset.empty_subset, Finset.subset_univ, and_self, if_true,
    Finset.card_empty, pow_zero, one_mul, Finset.card_fin, Nat.sub_self] at h
  rw [h]

/-- Superset mass: the probability that a biased set contains `b`. -/
theorem sum_biasedW_superset (q : ℚ) (b : Finset (Fin n)) :
    ∑ v : Finset (Fin n), (if b ⊆ v then biasedW q v else 0) = q ^ b.card := by
  have h := sum_biasedW_between (q := q) (Finset.subset_univ b)
  simp only [Finset.subset_univ, and_true, Finset.card_fin, Nat.sub_self,
    pow_zero, mul_one] at h
  rw [← h]

/-- Union-fiber mass: the probability that `a ∪ V = y`, for `a ⊆ y`. -/
theorem sum_biasedW_union_fiber (q : ℚ) {a y : Finset (Fin n)} (hay : a ⊆ y) :
    ∑ v : Finset (Fin n), (if a ∪ v = y then biasedW q v else 0)
      = q ^ (y.card - a.card) * (1 - q) ^ (n - y.card) := by
  have hiff : ∀ v : Finset (Fin n), (a ∪ v = y) ↔ (y \ a ⊆ v ∧ v ⊆ y) := by
    intro v
    constructor
    · intro h
      constructor
      · intro x hx
        obtain ⟨hxy, hxa⟩ := Finset.mem_sdiff.mp hx
        rcases Finset.mem_union.mp (h ▸ hxy) with h' | h'
        · exact absurd h' hxa
        · exact h'
      · exact h ▸ Finset.subset_union_right
    · rintro ⟨h1, h2⟩
      apply Finset.Subset.antisymm
      · exact Finset.union_subset hay h2
      · intro x hxy
        by_cases hxa : x ∈ a
        · exact Finset.mem_union.mpr (Or.inl hxa)
        · exact Finset.mem_union.mpr
            (Or.inr (h1 (Finset.mem_sdiff.mpr ⟨hxy, hxa⟩)))
  have hcards : (y \ a).card = y.card - a.card := Finset.card_sdiff_of_subset hay
  calc ∑ v : Finset (Fin n), (if a ∪ v = y then biasedW q v else 0)
      = ∑ v : Finset (Fin n), (if y \ a ⊆ v ∧ v ⊆ y then biasedW q v else 0) :=
        Finset.sum_congr rfl fun v _ => by rw [if_congr (hiff v) rfl rfl]
    _ = q ^ (y \ a).card * (1 - q) ^ (n - y.card) :=
        sum_biasedW_between Finset.sdiff_subset
    _ = q ^ (y.card - a.card) * (1 - q) ^ (n - y.card) := by rw [hcards]

-- ════════════════════════════════════════════════════════════════════
-- §2 WEIGHT MEASURES, SPREADNESS, AND THE UNIFORM BRIDGE
-- ════════════════════════════════════════════════════════════════════

/-- A probability weight on subsets of `Fin n`. -/
def IsProbW (w : Finset (Fin n) → ℚ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a : Finset (Fin n), w a = 1

/-- `R`-spreadness of a weight (MNSZ Definition 1.1), division-free:
    the mass above any nonempty `Z` is at most `R^{-|Z|}`. -/
def IsSpreadW (R : ℚ) (w : Finset (Fin n) → ℚ) : Prop :=
  ∀ Z : Finset (Fin n), Z.Nonempty →
    (∑ a : Finset (Fin n), if Z ⊆ a then w a else 0) * R ^ Z.card ≤ 1

/-- The uniform weight on a family. -/
def uniformW (F : Finset (Finset (Fin n))) (a : Finset (Fin n)) : ℚ :=
  if a ∈ F then (F.card : ℚ)⁻¹ else 0

theorem uniformW_isProbW {F : Finset (Finset (Fin n))} (hF : F.Nonempty) :
    IsProbW (uniformW F) := by
  have hFpos : (0 : ℚ) < (F.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hF
  constructor
  · intro a
    unfold uniformW
    by_cases h : a ∈ F
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  · unfold uniformW
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    exact mul_inv_cancel₀ hFpos.ne'

/-- The committed counting spreadness transfers to the uniform weight. -/
theorem uniformW_isSpreadW {r : ℚ} {F : Finset (Finset (Fin n))}
    (hF : F.Nonempty) (hspread : IsRSpread r F) :
    IsSpreadW r (uniformW F) := by
  intro Z hZ
  have h := hspread Z hZ
  have hFpos : (0 : ℚ) < (F.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hF
  have hsum : (∑ a : Finset (Fin n), if Z ⊆ a then uniformW F a else 0)
      = ((F.filter fun S => Z ⊆ S).card : ℚ) * (F.card : ℚ)⁻¹ := by
    have hper : ∀ a : Finset (Fin n),
        (if Z ⊆ a then uniformW F a else 0)
        = (if a ∈ F.filter (fun S => Z ⊆ S) then (F.card : ℚ)⁻¹ else 0) := by
      intro a
      unfold uniformW
      by_cases hZa : Z ⊆ a <;> by_cases haF : a ∈ F <;>
        simp [hZa, haF, Finset.mem_filter]
    rw [Finset.sum_congr rfl fun a _ => hper a, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  calc ((F.filter fun S => Z ⊆ S).card : ℚ) * (F.card : ℚ)⁻¹ * r ^ Z.card
      = ((F.filter fun S => Z ⊆ S).card : ℚ) * r ^ Z.card * (F.card : ℚ)⁻¹ := by
        ring
    _ ≤ (F.card : ℚ) * (F.card : ℚ)⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hFpos.le)
    _ = 1 := mul_inv_cancel₀ hFpos.ne'

theorem uniformW_support {F : Finset (Finset (Fin n))} {a : Finset (Fin n)}
    (h : uniformW F a ≠ 0) : a ∈ F := by
  by_cases hm : a ∈ F
  · exact hm
  · unfold uniformW at h
    rw [if_neg hm] at h
    exact absurd rfl h

-- ════════════════════════════════════════════════════════════════════
-- §3 M1 — THE ONE-STEP CONTRACTION (MNSZ Theorem 2.1)
--    Planted model, posterior, planting trick, truncated second moment.
-- ════════════════════════════════════════════════════════════════════

/-- Partition function `Z_Y` (MNSZ eq. 2.3): the likelihood ratio of the
    planted vs null model at observation `y`. -/
def partZ (w : Finset (Fin n) → ℚ) (q : ℚ) (y : Finset (Fin n)) : ℚ :=
  ∑ b : Finset (Fin n), if b ⊆ y then w b * (1/q) ^ b.card else 0

/-- Truncated partition function `Z_Y(A,δ)`: the contribution to `Z_Y`
    from sets meeting `a` in more than `c·|a|` elements. -/
def partZcut (w : Finset (Fin n) → ℚ) (q c : ℚ) (a y : Finset (Fin n)) : ℚ :=
  ∑ b : Finset (Fin n),
    if b ⊆ y ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
    then w b * (1/q) ^ b.card else 0

/-- Posterior weight of `b` given observation `y` (Bayes). -/
def postW (w : Finset (Fin n) → ℚ) (q : ℚ) (y b : Finset (Fin n)) : ℚ :=
  (if b ⊆ y then w b * (1/q) ^ b.card else 0) / partZ w q y

/-- The planted coupling `P_p(A = a, V = v, A' = b)`:
    signal `a ~ w`, independent noise `v ~ biasedW q`, posterior resample
    `b` given the observation `y = a ∪ v`. -/
def cplW (w : Finset (Fin n) → ℚ) (q : ℚ) (a v b : Finset (Fin n)) : ℚ :=
  w a * biasedW q v * postW w q (a ∪ v) b

/-- The contraction statistic `|A'\V| / |A|` (0 when `A = ∅`). -/
def ratioX (a v b : Finset (Fin n)) : ℚ :=
  if a = ∅ then 0 else ((b \ v).card : ℚ) / (a.card : ℚ)

section OneStep

variable {w : Finset (Fin n) → ℚ} {q c R : ℚ}

theorem partZ_nonneg (hw : ∀ a, 0 ≤ w a) (hq : 0 < q) (y : Finset (Fin n)) :
    0 ≤ partZ w q y := by
  apply Finset.sum_nonneg
  intro b _
  by_cases h : b ⊆ y
  · rw [if_pos h]
    have := hw b
    positivity
  · rw [if_neg h]

/-- On the planted support the partition function is positive: the signal
    itself contributes. -/
theorem partZ_pos (hw : ∀ a, 0 ≤ w a) (hq : 0 < q)
    {a y : Finset (Fin n)} (ha : w a ≠ 0) (hay : a ⊆ y) :
    0 < partZ w q y := by
  have hwa : 0 < w a := lt_of_le_of_ne (hw a) (Ne.symm ha)
  have hterm : 0 < (if a ⊆ y then w a * (1/q) ^ a.card else 0) := by
    rw [if_pos hay]
    positivity
  calc (0 : ℚ) < (if a ⊆ y then w a * (1/q) ^ a.card else 0) := hterm
    _ ≤ partZ w q y := by
        apply Finset.single_le_sum
          (f := fun b => if b ⊆ y then w b * (1/q) ^ b.card else 0)
        · intro b _
          by_cases h : b ⊆ y
          · rw [if_pos h]
            have := hw b
            positivity
          · rw [if_neg h]
        · exact Finset.mem_univ a

theorem postW_nonneg (hw : ∀ a, 0 ≤ w a) (hq : 0 < q)
    (y b : Finset (Fin n)) : 0 ≤ postW w q y b := by
  unfold postW
  apply div_nonneg _ (partZ_nonneg hw hq y)
  by_cases h : b ⊆ y
  · rw [if_pos h]
    have := hw b
    positivity
  · rw [if_neg h]

/-- The posterior is a probability whenever the partition function is
    positive. -/
theorem sum_postW {y : Finset (Fin n)} (hZ : 0 < partZ w q y) :
    ∑ b : Finset (Fin n), postW w q y b = 1 := by
  unfold postW
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

theorem postW_support {y b : Finset (Fin n)} (h : postW w q y b ≠ 0) :
    w b ≠ 0 ∧ b ⊆ y := by
  unfold postW at h
  have hnum : (if b ⊆ y then w b * (1/q) ^ b.card else 0) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h
    exact h rfl
  by_cases hby : b ⊆ y
  · rw [if_pos hby] at hnum
    refine ⟨fun h0 => hnum ?_, hby⟩
    rw [h0, zero_mul]
  · rw [if_neg hby] at hnum
    exact absurd rfl hnum

theorem cplW_nonneg (hw : ∀ a, 0 ≤ w a) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (a v b : Finset (Fin n)) : 0 ≤ cplW w q a v b :=
  mul_nonneg
    (mul_nonneg (hw a) (biasedW_nonneg hq0.le hq1 v))
    (postW_nonneg hw hq0 (a ∪ v) b)

theorem cplW_support {a v b : Finset (Fin n)} (h : cplW w q a v b ≠ 0) :
    w a ≠ 0 ∧ w b ≠ 0 ∧ b ⊆ a ∪ v := by
  unfold cplW at h
  have ha : w a ≠ 0 := fun h0 => h (by rw [h0, zero_mul, zero_mul])
  have hpost : postW w q (a ∪ v) b ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
  obtain ⟨hb, hby⟩ := postW_support hpost
  exact ⟨ha, hb, hby⟩

/-- The coupling is a probability (MNSZ §2.1: the planted model is
    well-defined). -/
theorem sum_cplW (hw : IsProbW w) (hq0 : 0 < q) :
    ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
      cplW w q a v b = 1 := by
  have key : ∀ a : Finset (Fin n),
      ∑ v : Finset (Fin n), ∑ b : Finset (Fin n), cplW w q a v b = w a := by
    intro a
    by_cases ha : w a = 0
    · simp [cplW, ha]
    · have hinner : ∀ v : Finset (Fin n),
          ∑ b : Finset (Fin n), cplW w q a v b = w a * biasedW q v := by
        intro v
        unfold cplW
        rw [← Finset.mul_sum,
          sum_postW (partZ_pos hw.1 hq0 ha Finset.subset_union_left),
          mul_one]
      rw [Finset.sum_congr rfl fun v _ => hinner v, ← Finset.mul_sum,
        sum_biasedW, mul_one]
  rw [Finset.sum_congr rfl fun a _ => key a, hw.2]

/-- Planted marginal of the observation `Y = A ∪ V` (MNSZ eq. 2.5):
    `P_p(Y = y) = Q_p(y) · Z_y`. The planting trick's pivot. -/
theorem sum_cplW_obs (hq0 : 0 < q) (y : Finset (Fin n)) :
    ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      (if a ∪ v = y then w a * biasedW q v else 0)
      = biasedW q y * partZ w q y := by
  have hstep : ∀ a : Finset (Fin n),
      (∑ v : Finset (Fin n), if a ∪ v = y then w a * biasedW q v else 0)
      = if a ⊆ y
        then w a * (q ^ (y.card - a.card) * (1 - q) ^ (n - y.card)) else 0 := by
    intro a
    by_cases hay : a ⊆ y
    · rw [if_pos hay, ← sum_biasedW_union_fiber q hay, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by
        by_cases h : a ∪ v = y
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
    · rw [if_neg hay]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (fun h : a ∪ v = y => hay (h ▸ Finset.subset_union_left))]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  unfold biasedW partZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hay : a ⊆ y
  · rw [if_pos hay, if_pos hay]
    have hcard : a.card ≤ y.card := Finset.card_le_card hay
    have hpow : q ^ (y.card - a.card) = q ^ y.card / q ^ a.card :=
      pow_sub₀ q hq0.ne' hcard
    rw [hpow, div_pow, one_pow]
    have hqa : q ^ a.card ≠ 0 := by positivity
    field_simp
  · rw [if_neg hay, if_neg hay, mul_zero]

/-- MNSZ Lemma 2.2 (planted-to-null): the probability that the posterior
    sample meets the signal in more than `c·|A|` elements equals the
    planted expectation of `Z_Y(A,c)/Z_Y`. -/
theorem cut_prob_eq :
    (∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
      cplW w q a v b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0))
    = ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
        w a * biasedW q v *
          (partZcut w q c a (a ∪ v) / partZ w q (a ∪ v)) := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => ?_
  have hper : ∀ b : Finset (Fin n),
      cplW w q a v b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0)
      = w a * biasedW q v *
          ((if b ⊆ a ∪ v ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
            then w b * (1/q) ^ b.card else 0) / partZ w q (a ∪ v)) := by
    intro b
    unfold cplW postW
    by_cases hP : b ⊆ a ∪ v <;>
      by_cases hQ : (a.card : ℚ) * c < ((b ∩ a).card : ℚ) <;>
      simp [hP, hQ]
  rw [Finset.sum_congr rfl fun b _ => hper b, ← Finset.mul_sum,
    ← Finset.sum_div]
  rfl

/-- The `V`-integrated truncated second moment (MNSZ Lemma 2.4): the
    planted expectation of `Z_Y(A,c)` collapses to a pair expectation
    under `w ⊗ w` with weight `q^{-|A∩B|}` over the cut. -/
theorem sum_cplW_cut_eq (hq0 : 0 < q) :
    ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * partZcut w q c a (a ∪ v)
    = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
        w a * w b *
          (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
           then (1/q) ^ ((b ∩ a).card) else 0) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  -- expand the truncated partition function and swap the sums
  have hexpand : ∑ v : Finset (Fin n),
      w a * biasedW q v * partZcut w q c a (a ∪ v)
      = ∑ b : Finset (Fin n), ∑ v : Finset (Fin n),
          w a * biasedW q v *
            (if b ⊆ a ∪ v ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
             then w b * (1/q) ^ b.card else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold partZcut
    rw [Finset.mul_sum]
  rw [hexpand]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- the cut does not depend on `v`; integrate the noise out
  by_cases hcut : (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
  · -- condition `b ⊆ a ∪ v` is `b \ a ⊆ v`
    have hcond : ∀ v : Finset (Fin n), (b ⊆ a ∪ v) ↔ (b \ a ⊆ v) := by
      intro v
      constructor
      · intro h x hx
        obtain ⟨hxb, hxa⟩ := Finset.mem_sdiff.mp hx
        rcases Finset.mem_union.mp (h hxb) with h' | h'
        · exact absurd h' hxa
        · exact h'
      · intro h x hxb
        by_cases hxa : x ∈ a
        · exact Finset.mem_union.mpr (Or.inl hxa)
        · exact Finset.mem_union.mpr
            (Or.inr (h (Finset.mem_sdiff.mpr ⟨hxb, hxa⟩)))
    have hper : ∀ v : Finset (Fin n),
        w a * biasedW q v *
          (if b ⊆ a ∪ v ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
           then w b * (1/q) ^ b.card else 0)
        = (w a * (w b * (1/q) ^ b.card)) *
            (if b \ a ⊆ v then biasedW q v else 0) := by
      intro v
      by_cases hv : b \ a ⊆ v
      · rw [if_pos ⟨(hcond v).mpr hv, hcut⟩, if_pos hv]
        ring
      · rw [if_neg fun hand => hv ((hcond v).mp hand.1), if_neg hv]
        ring
    rw [Finset.sum_congr rfl fun v _ => hper v, ← Finset.mul_sum,
      sum_biasedW_superset, if_pos hcut]
    -- (1/q)^|b| · q^|b\a| = (1/q)^|b∩a|
    have hsplit : b.card = (b ∩ a).card + (b \ a).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      · exact Finset.disjoint_left.mpr fun x hx1 hx2 =>
          (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
    have hpows : (1/q) ^ b.card * q ^ (b \ a).card = (1/q) ^ ((b ∩ a).card) := by
      rw [hsplit, pow_add]
      have hq' : q ≠ 0 := hq0.ne'
      rw [mul_assoc, ← mul_pow, one_div_mul_cancel hq', one_pow, mul_one]
    calc w a * (w b * (1/q) ^ b.card) * q ^ (b \ a).card
        = w a * w b * ((1/q) ^ b.card * q ^ (b \ a).card) := by ring
      _ = w a * w b * (1/q) ^ ((b ∩ a).card) := by rw [hpows]
  · -- no cut: both sides vanish
    rw [if_neg hcut]
    rw [Finset.sum_eq_zero, mul_zero]
    intro v _
    rw [if_neg fun hand => hcut hand.2, mul_zero]

/-- `2^{j-1} ≤ j!` for `j ≥ 1`. -/
theorem two_pow_pred_le_factorial : ∀ {j : ℕ}, 1 ≤ j → 2 ^ (j - 1) ≤ j.factorial
  | 1, _ => le_refl _
  | j + 2, _ => by
    have ih := two_pow_pred_le_factorial (j := j + 1) (Nat.le_add_left _ _)
    have h1 : j + 2 - 1 = (j + 1 - 1) + 1 := by omega
    calc 2 ^ (j + 2 - 1) = 2 ^ (j + 1 - 1) * 2 := by rw [h1, pow_succ]
      _ ≤ (j + 1).factorial * 2 := by omega
      _ ≤ (j + 1).factorial * (j + 2) := by
          have : (j + 1).factorial ≥ 1 := Nat.one_le_iff_ne_zero.mpr
            (Nat.factorial_ne_zero _)
          nlinarith
      _ = (j + 2).factorial := by rw [Nat.factorial_succ (j + 1), Nat.mul_comm]

/-- `(ℓ+1)^ℓ ≤ 3·ℓ^ℓ` over ℚ (the rational core of `(1+1/ℓ)^ℓ ≤ e < 3`),
    by the binomial expansion with `C(ℓ,j)·j! ≤ ℓ^j` and `2^{j-1} ≤ j!`. -/
theorem succ_pow_le_three_mul_pow (ℓ : ℕ) :
    ((ℓ : ℚ) + 1) ^ ℓ ≤ 3 * (ℓ : ℚ) ^ ℓ := by
  have hexp : ((ℓ : ℚ) + 1) ^ ℓ
      = ∑ k ∈ Finset.range (ℓ + 1), (ℓ.choose k : ℚ) * (ℓ : ℚ) ^ (ℓ - k) := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun k _ => by rw [one_pow, one_mul, mul_comm]
  rw [hexp, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have hbound : ∀ k ∈ Finset.range ℓ,
      (ℓ.choose (k + 1) : ℚ) * (ℓ : ℚ) ^ (ℓ - (k + 1))
        ≤ (ℓ : ℚ) ^ ℓ * (1/2) ^ k := by
    intro k hk
    have hkℓ : k + 1 ≤ ℓ := Finset.mem_range.mp hk
    have hfac : (0 : ℚ) < ((k + 1).factorial : ℚ) := by
      exact_mod_cast (k + 1).factorial_pos
    have h2k : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
    have hℓpow : (0 : ℚ) ≤ (ℓ : ℚ) ^ (ℓ - (k + 1)) := by positivity
    have h1 : (ℓ.choose (k + 1) : ℚ) ≤ (ℓ : ℚ) ^ (k + 1) / ((k + 1).factorial : ℚ) := by
      exact_mod_cast Nat.choose_le_pow_div (k + 1) ℓ
    have h2 : (2 : ℚ) ^ k ≤ ((k + 1).factorial : ℚ) := by
      have := two_pow_pred_le_factorial (j := k + 1) (Nat.le_add_left 1 k)
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub] at this
      exact_mod_cast this
    calc (ℓ.choose (k + 1) : ℚ) * (ℓ : ℚ) ^ (ℓ - (k + 1))
        ≤ ((ℓ : ℚ) ^ (k + 1) / ((k + 1).factorial : ℚ)) * (ℓ : ℚ) ^ (ℓ - (k + 1)) :=
          mul_le_mul_of_nonneg_right h1 hℓpow
      _ = (ℓ : ℚ) ^ ℓ / ((k + 1).factorial : ℚ) := by
          rw [div_mul_eq_mul_div, ← pow_add]
          congr 2
          omega
      _ ≤ (ℓ : ℚ) ^ ℓ / (2 : ℚ) ^ k := by
          apply div_le_div_of_nonneg_left (by positivity) h2k h2
      _ = (ℓ : ℚ) ^ ℓ * (1/2) ^ k := by
          rw [div_pow, one_pow]
          ring
  have hgeom : ∑ k ∈ Finset.range ℓ, ((1 : ℚ)/2) ^ k ≤ 2 := by
    have hclosed : ∀ m : ℕ,
        ∑ k ∈ Finset.range m, ((1 : ℚ)/2) ^ k = 2 - 2 * (1/2) ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ p ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hclosed]
    have : (0 : ℚ) ≤ (1/2 : ℚ) ^ ℓ := by positivity
    linarith
  calc (∑ k ∈ Finset.range ℓ, (ℓ.choose (k + 1) : ℚ) * (ℓ : ℚ) ^ (ℓ - (k + 1)))
        + (ℓ : ℚ) ^ ℓ
      ≤ (∑ k ∈ Finset.range ℓ, (ℓ : ℚ) ^ ℓ * (1/2) ^ k) + (ℓ : ℚ) ^ ℓ := by
        have := Finset.sum_le_sum hbound
        linarith
    _ = (ℓ : ℚ) ^ ℓ * (∑ k ∈ Finset.range ℓ, ((1 : ℚ)/2) ^ k) + (ℓ : ℚ) ^ ℓ := by
        rw [Finset.mul_sum]
    _ ≤ (ℓ : ℚ) ^ ℓ * 2 + (ℓ : ℚ) ^ ℓ := by
        have hp : (0 : ℚ) ≤ (ℓ : ℚ) ^ ℓ := by positivity
        nlinarith
    _ = 3 * (ℓ : ℚ) ^ ℓ := by ring

/-- Rational factorial lower bound `ℓ! ≥ (ℓ/3)^ℓ`, in the division-free
    form `ℓ^ℓ ≤ 3^ℓ · ℓ!`. -/
theorem pow_self_le_three_pow_mul_factorial (ℓ : ℕ) :
    ((ℓ : ℚ)) ^ ℓ ≤ 3 ^ ℓ * (ℓ.factorial : ℚ) := by
  induction ℓ with
  | zero => norm_num
  | succ m ih =>
    have h1 : ((m : ℚ) + 1) ^ m ≤ 3 * (m : ℚ) ^ m := succ_pow_le_three_mul_pow m
    have hm : (0 : ℚ) ≤ (m : ℚ) + 1 := by positivity
    calc ((m + 1 : ℕ) : ℚ) ^ (m + 1)
        = ((m : ℚ) + 1) ^ m * ((m : ℚ) + 1) := by push_cast; ring
      _ ≤ 3 * (m : ℚ) ^ m * ((m : ℚ) + 1) := by
          exact mul_le_mul_of_nonneg_right h1 hm
      _ ≤ 3 * (3 ^ m * (m.factorial : ℚ)) * ((m : ℚ) + 1) := by
          have := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℚ) ≤ 3)
          exact mul_le_mul_of_nonneg_right this hm
      _ = 3 ^ (m + 1) * (((m + 1) * m.factorial : ℕ) : ℚ) := by push_cast; ring
      _ = 3 ^ (m + 1) * (((m + 1).factorial : ℕ) : ℚ) := by
          rw [Nat.factorial_succ]

/-- The truncated second moment is small (MNSZ proof of Theorem 2.1):
    spreadness caps each intersection level `ℓ` by `C(|a|,ℓ)·R^{-ℓ}`, the
    cut forces `|a|/ℓ < 1/c`, and `1 ≤ c³qR` turns the level-`ℓ` term
    into `(3c²)^ℓ`; the geometric series sums to at most `6c²`. -/
theorem second_moment_bound (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R)) :
    ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
      w a * w b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
         then (1/q) ^ ((b ∩ a).card) else 0)
    ≤ 6 * c ^ 2 := by
  have hqR : (0 : ℚ) < q * R := mul_pos hq0 hR
  -- the inner expectation over `b` is at most `6c²` for every signal `a`
  have inner : ∀ a : Finset (Fin n),
      (∑ b : Finset (Fin n), w b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
         then (1/q) ^ ((b ∩ a).card) else 0)) ≤ 6 * c ^ 2 := by
    intro a
    -- (i) group `b` by its trace `Z = b ∩ a ∈ a.powerset`
    have hmaps : ∀ b ∈ (univ : Finset (Finset (Fin n))), b ∩ a ∈ a.powerset :=
      fun b _ => mem_powerset.mpr inter_subset_right
    have hgroup : (∑ b : Finset (Fin n), w b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
         then (1/q) ^ ((b ∩ a).card) else 0))
        = ∑ Z ∈ a.powerset, ∑ b ∈ univ.filter (fun b => b ∩ a = Z),
            w b * (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
                   then (1/q) ^ ((b ∩ a).card) else 0) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    -- (ii)+(iii) per-trace bound via spreadness
    have hZbound : ∀ Z ∈ a.powerset,
        (∑ b ∈ univ.filter (fun b => b ∩ a = Z),
          w b * (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
                 then (1/q) ^ ((b ∩ a).card) else 0))
        ≤ (if (a.card : ℚ) * c < (Z.card : ℚ)
           then (1/(q*R)) ^ Z.card else 0) := by
      intro Z _
      have hfib : ∀ b ∈ univ.filter (fun b => b ∩ a = Z),
          w b * (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
                 then (1/q) ^ ((b ∩ a).card) else 0)
          = w b * (if (a.card : ℚ) * c < (Z.card : ℚ)
                   then (1/q) ^ Z.card else 0) := by
        intro b hb
        rw [(Finset.mem_filter.mp hb).2]
      rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul]
      by_cases hcut : (a.card : ℚ) * c < (Z.card : ℚ)
      · rw [if_pos hcut, if_pos hcut]
        -- the cut forces `Z` nonempty
        have hZne : Z.Nonempty := by
          rw [← Finset.card_pos]
          by_contra hzero
          push Not at hzero
          interval_cases h : Z.card
          · simp only [Nat.cast_zero] at hcut
            have : (0 : ℚ) ≤ (a.card : ℚ) * c := by positivity
            linarith
        -- fiber mass ≤ superset mass ≤ R^{-|Z|}
        have hsupmass : (∑ b ∈ univ.filter (fun b => b ∩ a = Z), w b)
            ≤ ∑ b : Finset (Fin n), if Z ⊆ b then w b else 0 := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro b hb
            have hb' := (Finset.mem_filter.mp hb).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ b,
              hb' ▸ inter_subset_left⟩
          · exact fun b _ _ => hw.1 b
        have hRpow : (0 : ℚ) < R ^ Z.card := pow_pos hR _
        have hspr : (∑ b : Finset (Fin n), if Z ⊆ b then w b else 0)
            ≤ (R ^ Z.card)⁻¹ := by
          have h := hsp Z hZne
          calc (∑ b : Finset (Fin n), if Z ⊆ b then w b else 0)
              = (∑ b : Finset (Fin n), if Z ⊆ b then w b else 0)
                  * R ^ Z.card * (R ^ Z.card)⁻¹ := by
                field_simp
            _ ≤ 1 * (R ^ Z.card)⁻¹ :=
                mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hRpow.le)
            _ = (R ^ Z.card)⁻¹ := one_mul _
        have hmass : (∑ b ∈ univ.filter (fun b => b ∩ a = Z), w b)
            ≤ (R ^ Z.card)⁻¹ := le_trans hsupmass hspr
        have hq' : (0 : ℚ) < (1/q) ^ Z.card := by positivity
        calc (∑ b ∈ univ.filter (fun b => b ∩ a = Z), w b) * (1/q) ^ Z.card
            ≤ (R ^ Z.card)⁻¹ * (1/q) ^ Z.card :=
              mul_le_mul_of_nonneg_right hmass hq'.le
          _ = (1/(q*R)) ^ Z.card := by
              have hqk : q ^ Z.card ≠ 0 := by positivity
              have hRk : R ^ Z.card ≠ 0 := by positivity
              rw [div_pow, div_pow, one_pow, mul_pow]
              field_simp
      · rw [if_neg hcut, if_neg hcut, mul_zero]
    -- (iv) group traces by cardinality: `choose` many at each level
    have hcardgroup : (∑ Z ∈ a.powerset,
        (if (a.card : ℚ) * c < (Z.card : ℚ) then (1/(q*R)) ^ Z.card else 0))
        = ∑ ℓ ∈ Finset.range (a.card + 1), (a.card.choose ℓ : ℚ) *
            (if (a.card : ℚ) * c < (ℓ : ℚ) then (1/(q*R)) ^ ℓ else 0) := by
      have hmaps2 : ∀ Z ∈ a.powerset, Z.card ∈ Finset.range (a.card + 1) :=
        fun Z hZ => Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.card_le_card (mem_powerset.mp hZ)))
      have hfib2 := Finset.sum_fiberwise_of_maps_to' hmaps2
        (fun ℓ : ℕ => if (a.card : ℚ) * c < (ℓ : ℚ) then (1/(q*R)) ^ ℓ else 0)
      rw [← hfib2]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← Finset.card_powersetCard, powersetCard_eq_filter]
    -- (v) each level term is at most the geometric term `(3c²)^ℓ`
    have hterm : ∀ ℓ ∈ Finset.range (a.card + 1),
        (a.card.choose ℓ : ℚ) *
          (if (a.card : ℚ) * c < (ℓ : ℚ) then (1/(q*R)) ^ ℓ else 0)
        ≤ (if 1 ≤ ℓ then (3 * c ^ 2) ^ ℓ else 0) := by
      intro ℓ _
      by_cases hcut : (a.card : ℚ) * c < (ℓ : ℚ)
      · have hℓ1 : 1 ≤ ℓ := by
          by_contra h
          push Not at h
          interval_cases ℓ
          simp only [Nat.cast_zero] at hcut
          have : (0 : ℚ) ≤ (a.card : ℚ) * c := by positivity
          linarith
        rw [if_pos hcut, if_pos hℓ1]
        have hℓQ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ1
        -- choose ≤ N^ℓ/ℓ! ≤ (3N/ℓ)^ℓ
        have h1 : (a.card.choose ℓ : ℚ) ≤ (a.card : ℚ) ^ ℓ / (ℓ.factorial : ℚ) := by
          exact_mod_cast Nat.choose_le_pow_div ℓ a.card
        have hfacpos : (0 : ℚ) < (ℓ.factorial : ℚ) := by
          exact_mod_cast ℓ.factorial_pos
        have h2 : (a.card : ℚ) ^ ℓ / (ℓ.factorial : ℚ)
            ≤ (3 * (a.card : ℚ)) ^ ℓ / (ℓ : ℚ) ^ ℓ := by
          rw [div_le_div_iff₀ hfacpos (by positivity)]
          calc (a.card : ℚ) ^ ℓ * (ℓ : ℚ) ^ ℓ
              ≤ (a.card : ℚ) ^ ℓ * (3 ^ ℓ * (ℓ.factorial : ℚ)) :=
                mul_le_mul_of_nonneg_left
                  (pow_self_le_three_pow_mul_factorial ℓ) (by positivity)
            _ = (3 * (a.card : ℚ)) ^ ℓ * (ℓ.factorial : ℚ) := by
                rw [mul_pow]; ring
        -- (3N/ℓ)^ℓ · (1/(qR))^ℓ = (3N/(ℓqR))^ℓ ≤ (3c²)^ℓ
        have h3 : (3 * (a.card : ℚ)) / (ℓ : ℚ) * (1/(q*R)) ≤ 3 * c ^ 2 := by
          rw [div_mul_div_comm, mul_one, div_le_iff₀ (by positivity)]
          -- 3N ≤ 3c²·(ℓqR): from N < ℓ/c and c³qR ≥ 1
          have hNc : (a.card : ℚ) * c < (ℓ : ℚ) := hcut
          have hcqR' : 1/c ≤ c ^ 2 * (q * R) := by
            rw [div_le_iff₀ hc]
            calc (1 : ℚ) ≤ c ^ 3 * (q * R) := hcqR
              _ = c ^ 2 * (q * R) * c := by ring
          calc 3 * (a.card : ℚ) ≤ 3 * ((ℓ : ℚ) / c) := by
                have : (a.card : ℚ) ≤ (ℓ : ℚ) / c := by
                  rw [le_div_iff₀ hc]; linarith
                linarith
            _ = 3 * (ℓ : ℚ) * (1/c) := by ring
            _ ≤ 3 * (ℓ : ℚ) * (c ^ 2 * (q * R)) := by
                have h3ℓ : (0 : ℚ) ≤ 3 * (ℓ : ℚ) := by positivity
                exact mul_le_mul_of_nonneg_left hcqR' h3ℓ
            _ = 3 * c ^ 2 * ((ℓ : ℚ) * (q * R)) := by ring
        calc (a.card.choose ℓ : ℚ) * (1/(q*R)) ^ ℓ
            ≤ ((3 * (a.card : ℚ)) ^ ℓ / (ℓ : ℚ) ^ ℓ) * (1/(q*R)) ^ ℓ := by
              apply mul_le_mul_of_nonneg_right (le_trans h1 h2) (by positivity)
          _ = ((3 * (a.card : ℚ)) / (ℓ : ℚ) * (1/(q*R))) ^ ℓ := by
              rw [← div_pow, ← mul_pow]
          _ ≤ (3 * c ^ 2) ^ ℓ := by
              apply pow_le_pow_left₀ (by positivity) h3
      · rw [if_neg hcut, mul_zero]
        by_cases h1 : 1 ≤ ℓ
        · rw [if_pos h1]; positivity
        · rw [if_neg h1]
    -- (vi) the geometric series over levels `ℓ ≥ 1` sums below `6c²`
    have hgeom : (∑ ℓ ∈ Finset.range (a.card + 1),
        (if 1 ≤ ℓ then (3 * c ^ 2) ^ ℓ else 0)) ≤ 6 * c ^ 2 := by
      have hIco : (∑ ℓ ∈ Finset.range (a.card + 1),
          (if 1 ≤ ℓ then (3 * c ^ 2) ^ ℓ else 0))
          = ∑ ℓ ∈ Finset.Ico 1 (a.card + 1), (3 * c ^ 2) ^ ℓ := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hIco]
      have hx0 : (0 : ℚ) ≤ 3 * c ^ 2 := by positivity
      have hx1 : 3 * c ^ 2 < 1 := by linarith
      calc ∑ ℓ ∈ Finset.Ico 1 (a.card + 1), (3 * c ^ 2) ^ ℓ
          ≤ (3 * c ^ 2) ^ 1 / (1 - 3 * c ^ 2) :=
            geom_sum_Ico_le_of_lt_one hx0 hx1
        _ ≤ 6 * c ^ 2 := by
            rw [pow_one, div_le_iff₀ (by linarith)]
            nlinarith
    calc (∑ b : Finset (Fin n), w b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
         then (1/q) ^ ((b ∩ a).card) else 0))
        = ∑ Z ∈ a.powerset, ∑ b ∈ univ.filter (fun b => b ∩ a = Z),
            w b * (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
                   then (1/q) ^ ((b ∩ a).card) else 0) := hgroup
      _ ≤ ∑ Z ∈ a.powerset,
            (if (a.card : ℚ) * c < (Z.card : ℚ)
             then (1/(q*R)) ^ Z.card else 0) := Finset.sum_le_sum hZbound
      _ = ∑ ℓ ∈ Finset.range (a.card + 1), (a.card.choose ℓ : ℚ) *
            (if (a.card : ℚ) * c < (ℓ : ℚ) then (1/(q*R)) ^ ℓ else 0) := hcardgroup
      _ ≤ ∑ ℓ ∈ Finset.range (a.card + 1),
            (if 1 ≤ ℓ then (3 * c ^ 2) ^ ℓ else 0) := Finset.sum_le_sum hterm
      _ ≤ 6 * c ^ 2 := hgeom
  -- assemble over the signal
  calc ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
      w a * w b * (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
                   then (1/q) ^ ((b ∩ a).card) else 0)
      = ∑ a : Finset (Fin n), w a * (∑ b : Finset (Fin n), w b *
          (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
           then (1/q) ^ ((b ∩ a).card) else 0)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ∑ a : Finset (Fin n), w a * (6 * c ^ 2) :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (inner a) (hw.1 a)
    _ = 6 * c ^ 2 := by rw [← Finset.sum_mul, hw.2, one_mul]

/-- Observation grouping: planted expectations of functions of the
    observation `Y = A ∪ V` reduce to the null model reweighted by the
    partition function (the planting trick's change of measure). -/
theorem sum_obs_fun (hq0 : 0 < q) (g : Finset (Fin n) → ℚ) :
    ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * g (a ∪ v)
    = ∑ y : Finset (Fin n), biasedW q y * partZ w q y * g y := by
  have hswap : ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * g (a ∪ v)
      = ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ y : Finset (Fin n),
          (if a ∪ v = y then w a * biasedW q v else 0) * g y := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (a ∪ v)]
    · rw [if_pos rfl]
    · intro y _ hy
      rw [if_neg (fun h : a ∪ v = y => hy h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hswap]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← sum_cplW_obs hq0 y, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm

/-- MNSZ Lemma 2.3 (the planting trick) + assembly: the cut probability is
    at most `5c`, via the ε-cut at `ε := (5/2)·c` against the planted
    marginal `P_p(Y) = Q_p(Y)·Z_Y`. -/
theorem cut_prob_le (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R)) :
    (∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
      cplW w q a v b *
        (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0))
    ≤ 5 * c := by
  have hεpos : (0 : ℚ) < (5/2) * c := by positivity
  rw [cut_prob_eq]
  -- pointwise split at the ε-cut of the partition function
  have hsplit : ∀ a v : Finset (Fin n),
      w a * biasedW q v * (partZcut w q c a (a ∪ v) / partZ w q (a ∪ v))
      ≤ w a * biasedW q v *
          (if partZ w q (a ∪ v) ≤ (5/2) * c then 1 else 0)
        + w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c) := by
    intro a v
    have hW : 0 ≤ w a * biasedW q v :=
      mul_nonneg (hw.1 a) (biasedW_nonneg hq0.le hq1 v)
    by_cases ha : w a = 0
    · rw [ha]
      simp
    · have hZ : 0 < partZ w q (a ∪ v) :=
        partZ_pos hw.1 hq0 ha Finset.subset_union_left
      have hZcut0 : 0 ≤ partZcut w q c a (a ∪ v) := by
        apply Finset.sum_nonneg
        intro b _
        by_cases h : b ⊆ a ∪ v ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
        · rw [if_pos h]
          have := hw.1 b
          positivity
        · rw [if_neg h]
      have hZcutZ : partZcut w q c a (a ∪ v) ≤ partZ w q (a ∪ v) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases h : b ⊆ a ∪ v ∧ (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
        · rw [if_pos h, if_pos h.1]
        · rw [if_neg h]
          by_cases h' : b ⊆ a ∪ v
          · rw [if_pos h']
            have := hw.1 b
            positivity
          · rw [if_neg h']
      by_cases hev : partZ w q (a ∪ v) ≤ (5/2) * c
      · -- small-Z event: the ratio is at most 1
        rw [if_pos hev]
        have hratio : partZcut w q c a (a ∪ v) / partZ w q (a ∪ v) ≤ 1 := by
          rw [div_le_one hZ]
          exact hZcutZ
        have hsecond : 0 ≤ w a * biasedW q v * partZcut w q c a (a ∪ v)
            / ((5/2) * c) := by positivity
        calc w a * biasedW q v * (partZcut w q c a (a ∪ v) / partZ w q (a ∪ v))
            ≤ w a * biasedW q v * 1 := mul_le_mul_of_nonneg_left hratio hW
          _ ≤ w a * biasedW q v * 1
              + w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c) := by
              linarith
      · -- large-Z event: replace the denominator by ε
        rw [if_neg hev]
        push Not at hev
        have hratio : partZcut w q c a (a ∪ v) / partZ w q (a ∪ v)
            ≤ partZcut w q c a (a ∪ v) / ((5/2) * c) :=
          div_le_div_of_nonneg_left hZcut0 hεpos hev.le
        calc w a * biasedW q v * (partZcut w q c a (a ∪ v) / partZ w q (a ∪ v))
            ≤ w a * biasedW q v * (partZcut w q c a (a ∪ v) / ((5/2) * c)) :=
              mul_le_mul_of_nonneg_left hratio hW
          _ = w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c) := by
              ring
          _ ≤ w a * biasedW q v * 0
              + w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c) := by
              linarith
  -- the small-Z event has planted probability at most ε
  have hfirst : ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * (if partZ w q (a ∪ v) ≤ (5/2) * c then 1 else 0)
      ≤ (5/2) * c := by
    have heq := sum_obs_fun (w := w) hq0
      (fun y => if partZ w q y ≤ (5/2) * c then 1 else 0)
    simp only at heq
    rw [heq]
    calc ∑ y : Finset (Fin n), biasedW q y * partZ w q y *
          (if partZ w q y ≤ (5/2) * c then 1 else 0)
        ≤ ∑ y : Finset (Fin n), biasedW q y * ((5/2) * c) := by
          apply Finset.sum_le_sum
          intro y _
          have hb := biasedW_nonneg hq0.le hq1 y
          by_cases hev : partZ w q y ≤ (5/2) * c
          · rw [if_pos hev, mul_one]
            exact mul_le_mul_of_nonneg_left hev hb
          · rw [if_neg hev, mul_zero]
            positivity
      _ = (5/2) * c := by rw [← Finset.sum_mul, sum_biasedW, one_mul]
  -- the truncated mass is at most 6c² (the second moment bound)
  have hsecond : ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c)
      ≤ 6 * c ^ 2 / ((5/2) * c) := by
    have h := (sum_cplW_cut_eq (w := w) (c := c) hq0).trans_le
      (second_moment_bound hw hsp hq0 hc hc' hR hcqR)
    calc ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
        w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c)
        = (∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
            w a * biasedW q v * partZcut w q c a (a ∪ v)) / ((5/2) * c) := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_div _ _ _).symm
      _ ≤ 6 * c ^ 2 / ((5/2) * c) :=
          div_le_div_of_nonneg_right h hεpos.le
  calc ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
      w a * biasedW q v * (partZcut w q c a (a ∪ v) / partZ w q (a ∪ v))
      ≤ ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
          (w a * biasedW q v *
            (if partZ w q (a ∪ v) ≤ (5/2) * c then 1 else 0)
          + w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun v _ => hsplit a v
    _ = (∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
          w a * biasedW q v *
            (if partZ w q (a ∪ v) ≤ (5/2) * c then 1 else 0))
        + ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
            w a * biasedW q v * partZcut w q c a (a ∪ v) / ((5/2) * c) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ ≤ (5/2) * c + 6 * c ^ 2 / ((5/2) * c) := add_le_add hfirst hsecond
    _ = (5/2) * c + (12/5) * c := by
        congr 1
        rw [div_eq_iff hεpos.ne']
        ring
    _ ≤ 5 * c := by linarith

/-- **M1, the one-step contraction (MNSZ Theorem 2.1)**: under the planted
    coupling of an `R`-spread probability weight with `q`-biased noise,
    the expected contraction ratio `|A'\V|/|A|` is at most `6c` whenever
    `1 ≤ c³·(qR)`. -/
theorem one_step (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R)) :
    ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
      cplW w q a v b * ratioX a v b ≤ 6 * c := by
  -- pointwise: on the coupling support, the ratio is at most
  -- `c + 1{cut}` — below the cut it is at most `c`, always at most `1`
  have hpoint : ∀ a v b : Finset (Fin n),
      cplW w q a v b * ratioX a v b
      ≤ cplW w q a v b * c + cplW w q a v b *
          (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0) := by
    intro a v b
    by_cases hz : cplW w q a v b = 0
    · rw [hz, zero_mul, zero_mul, zero_mul, add_zero]
    · have hpos : 0 ≤ cplW w q a v b := cplW_nonneg hw.1 hq0 hq1 a v b
      obtain ⟨ha, hb, hby⟩ := cplW_support hz
      have hratio : ratioX a v b
          ≤ c + (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0) := by
        unfold ratioX
        by_cases hae : a = ∅
        · rw [if_pos hae]
          by_cases hcut : (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
          · rw [if_pos hcut]
            linarith
          · rw [if_neg hcut]
            linarith
        · rw [if_neg hae]
          have hacard : (0 : ℚ) < (a.card : ℚ) := by
            exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hae)
          have hsub : b \ v ⊆ b ∩ a := by
            intro x hx
            obtain ⟨hxb, hxv⟩ := Finset.mem_sdiff.mp hx
            rcases Finset.mem_union.mp (hby hxb) with h | h
            · exact Finset.mem_inter.mpr ⟨hxb, h⟩
            · exact absurd h hxv
          have hle : (((b \ v).card : ℚ)) ≤ ((b ∩ a).card : ℚ) := by
            exact_mod_cast Finset.card_le_card hsub
          by_cases hcut : (a.card : ℚ) * c < ((b ∩ a).card : ℚ)
          · rw [if_pos hcut]
            have h1 : ((b \ v).card : ℚ) / (a.card : ℚ) ≤ 1 := by
              rw [div_le_one hacard]
              calc ((b \ v).card : ℚ) ≤ ((b ∩ a).card : ℚ) := hle
                _ ≤ (a.card : ℚ) := by
                    exact_mod_cast Finset.card_le_card inter_subset_right
            linarith
          · rw [if_neg hcut]
            push Not at hcut
            rw [add_zero, div_le_iff₀ hacard]
            calc ((b \ v).card : ℚ) ≤ ((b ∩ a).card : ℚ) := hle
              _ ≤ (a.card : ℚ) * c := hcut
              _ = c * (a.card : ℚ) := mul_comm _ _
      calc cplW w q a v b * ratioX a v b
          ≤ cplW w q a v b *
              (c + (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hratio hpos
        _ = cplW w q a v b * c + cplW w q a v b *
              (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0) := by
            ring
  calc ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
      cplW w q a v b * ratioX a v b
      ≤ ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
          (cplW w q a v b * c + cplW w q a v b *
            (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun v _ =>
          Finset.sum_le_sum fun b _ => hpoint a v b
    _ = (∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
          cplW w q a v b * c)
        + ∑ a : Finset (Fin n), ∑ v : Finset (Fin n), ∑ b : Finset (Fin n),
            cplW w q a v b *
              (if (a.card : ℚ) * c < ((b ∩ a).card : ℚ) then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib
    _ ≤ 1 * c + 5 * c := by
        apply add_le_add
        · have heq : ∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
              ∑ b : Finset (Fin n), cplW w q a v b * c
              = (∑ a : Finset (Fin n), ∑ v : Finset (Fin n),
                  ∑ b : Finset (Fin n), cplW w q a v b) * c := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun v _ => (Finset.sum_mul _ _ _).symm
          rw [heq, sum_cplW hw hq0]
        · exact cut_prob_le hw hsp hq0 hq1 hc hc' hR hcqR
    _ = 6 * c := by ring

end OneStep

-- ════════════════════════════════════════════════════════════════════
-- §4 M2 — THE ITERATION CHAIN (MNSZ Theorem 1.2, Hölder-free)
--    Conditional measures by recursion, the trajectory space, per-round
--    marginal bounds, support chase, bad-round count, Markov.
-- ════════════════════════════════════════════════════════════════════

/-- The conditional law of the next fragment `A' \ v` given this round's
    noise `v` (MNSZ's `π_{ℓ+1}` given `V_ℓ = v`). -/
def nextW (w : Finset (Fin n) → ℚ) (q : ℚ) (v t : Finset (Fin n)) : ℚ :=
  ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
    w a * postW w q (a ∪ v) b * (if b \ v = t then 1 else 0)

section Chain

variable {w : Finset (Fin n) → ℚ} {q c R : ℚ}

theorem nextW_nonneg (hw : ∀ a, 0 ≤ w a) (hq : 0 < q)
    (v t : Finset (Fin n)) : 0 ≤ nextW w q v t := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  have h1 := hw a
  have h2 := postW_nonneg hw hq (a ∪ v) b
  by_cases h : b \ v = t
  · rw [if_pos h]
    positivity
  · rw [if_neg h]
    rw [mul_zero]

/-- The posterior total mass is at most 1 (equal to 1 on the support,
    0 off the planted support where the partition function vanishes). -/
theorem sum_postW_le_one (hw : ∀ a, 0 ≤ w a) (hq : 0 < q)
    (y : Finset (Fin n)) :
    ∑ b : Finset (Fin n), postW w q y b ≤ 1 := by
  rcases lt_or_eq_of_le (partZ_nonneg hw hq y) with hZ | hZ
  · rw [sum_postW hZ]
  · unfold postW
    rw [← Finset.sum_div, ← hZ, div_zero]
    norm_num

theorem nextW_isProbW (hw : IsProbW w) (hq0 : 0 < q)
    (v : Finset (Fin n)) : IsProbW (nextW w q v) := by
  refine ⟨nextW_nonneg hw.1 hq0 v, ?_⟩
  have hswap : ∑ t : Finset (Fin n), nextW w q v t
      = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
          w a * postW w q (a ∪ v) b *
            (∑ t : Finset (Fin n), if b \ v = t then 1 else 0) := by
    unfold nextW
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have hone : ∀ b : Finset (Fin n),
      (∑ t : Finset (Fin n), if b \ v = t then (1:ℚ) else 0) = 1 := by
    intro b
    rw [Finset.sum_ite_eq (univ : Finset (Finset (Fin n))) (b \ v)
      (fun _ => (1:ℚ))]
    rw [if_pos (Finset.mem_univ _)]
  have hkey : ∀ a : Finset (Fin n),
      ∑ b : Finset (Fin n), w a * postW w q (a ∪ v) b *
        (∑ t : Finset (Fin n), if b \ v = t then (1:ℚ) else 0) = w a := by
    intro a
    by_cases ha : w a = 0
    · rw [ha]
      simp
    · rw [Finset.sum_congr rfl fun b _ => by rw [hone b, mul_one]]
      rw [← Finset.mul_sum,
        sum_postW (partZ_pos hw.1 hq0 ha Finset.subset_union_left),
        mul_one]
  rw [Finset.sum_congr rfl fun a _ => hkey a, hw.2]

/-- Spreadness is preserved by the chain step (MNSZ §2.4, the induction
    claim): `S ⊆ B\v ⊆ A ∪ v` and `S ∩ v = ∅` force `S ⊆ A`. -/
theorem nextW_isSpreadW (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hR : 0 < R) (hq0 : 0 < q) (v : Finset (Fin n)) :
    IsSpreadW R (nextW w q v) := by
  intro Z hZ
  have hkey : (∑ t : Finset (Fin n), if Z ⊆ t then nextW w q v t else 0)
      ≤ ∑ a : Finset (Fin n), if Z ⊆ a then w a else 0 := by
    have hcollapse : (∑ t : Finset (Fin n), if Z ⊆ t then nextW w q v t else 0)
        = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
            w a * postW w q (a ∪ v) b * (if Z ⊆ b \ v then 1 else 0) := by
      have h1 : ∀ t : Finset (Fin n), (if Z ⊆ t then nextW w q v t else 0)
          = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
              w a * postW w q (a ∪ v) b *
                ((if b \ v = t then 1 else 0) * (if Z ⊆ t then 1 else 0)) := by
        intro t
        by_cases hZt : Z ⊆ t
        · rw [if_pos hZt]
          unfold nextW
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [if_pos hZt, mul_one]
        · rw [if_neg hZt]
          symm
          apply Finset.sum_eq_zero
          intro a _
          apply Finset.sum_eq_zero
          intro b _
          rw [if_neg hZt, mul_zero, mul_zero]
      rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      by_cases hZbv : Z ⊆ b \ v
      · rw [if_pos hZbv]
        rw [Finset.sum_eq_single (b \ v)]
        · rw [if_pos rfl, if_pos hZbv, one_mul]
        · intro t _ ht
          rw [if_neg (fun h : b \ v = t => ht h.symm), zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [if_neg hZbv]
        apply Finset.sum_eq_zero
        intro t _
        by_cases hbt : b \ v = t
        · rw [if_pos hbt, if_neg (hbt ▸ hZbv), mul_zero]
        · rw [if_neg hbt, zero_mul]
    rw [hcollapse]
    have hterm : ∀ a : Finset (Fin n),
        (∑ b : Finset (Fin n), w a * postW w q (a ∪ v) b *
          (if Z ⊆ b \ v then 1 else 0))
        ≤ (if Z ⊆ a then w a else 0) := by
      intro a
      by_cases hZa : Z ⊆ a
      · rw [if_pos hZa]
        calc ∑ b : Finset (Fin n), w a * postW w q (a ∪ v) b *
              (if Z ⊆ b \ v then 1 else 0)
            ≤ ∑ b : Finset (Fin n), w a * postW w q (a ∪ v) b := by
              apply Finset.sum_le_sum
              intro b _
              have h1 := hw.1 a
              have h2 := postW_nonneg hw.1 hq0 (a ∪ v) b
              by_cases h : Z ⊆ b \ v
              · rw [if_pos h, mul_one]
              · rw [if_neg h, mul_zero]
                positivity
          _ = w a * ∑ b : Finset (Fin n), postW w q (a ∪ v) b := by
              rw [Finset.mul_sum]
          _ ≤ w a * 1 :=
              mul_le_mul_of_nonneg_left
                (sum_postW_le_one hw.1 hq0 (a ∪ v)) (hw.1 a)
          _ = w a := mul_one _
      · rw [if_neg hZa]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro b _
        by_cases hZbv : Z ⊆ b \ v
        · -- a support term with `Z ⊆ b\v` would force `Z ⊆ a`
          by_cases hpost : postW w q (a ∪ v) b = 0
          · rw [hpost, mul_zero, zero_mul]
          · exfalso
            obtain ⟨-, hbav⟩ := postW_support hpost
            apply hZa
            intro x hx
            have hxbv : x ∈ b \ v := hZbv hx
            obtain ⟨hxb, hxv⟩ := Finset.mem_sdiff.mp hxbv
            rcases Finset.mem_union.mp (hbav hxb) with h | h
            · exact h
            · exact absurd h hxv
        · rw [if_neg hZbv, mul_zero]
    exact Finset.sum_le_sum fun a _ => hterm a
  calc (∑ t : Finset (Fin n), if Z ⊆ t then nextW w q v t else 0) * R ^ Z.card
      ≤ (∑ a : Finset (Fin n), if Z ⊆ a then w a else 0) * R ^ Z.card :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ ≤ 1 := hsp Z hZ

theorem nextW_support {v t : Finset (Fin n)}
    (h : nextW w q v t ≠ 0) : ∃ b, w b ≠ 0 ∧ t = b \ v := by
  unfold nextW at h
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have hpost : postW w q (a ∪ v) b ≠ 0 := by
    intro h0
    rw [h0] at hb
    simp at hb
  have hite : (if b \ v = t then (1:ℚ) else 0) ≠ 0 := by
    intro h0
    rw [h0] at hb
    simp at hb
  by_cases hbt : b \ v = t
  · exact ⟨b, (postW_support hpost).1, hbt.symm⟩
  · rw [if_neg hbt] at hite
    exact absurd rfl hite

end Chain

/-- The trajectory space of `m` rounds: each round records the noise `v`
    and the posterior resample `b`. -/
def Traj (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | m + 1 => (Finset (Fin n) × Finset (Fin n)) × Traj n m

instance : ∀ m, Fintype (Traj n m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    letI := instFintypeTraj m
    inferInstanceAs (Fintype ((Finset (Fin n) × Finset (Fin n)) × Traj n m))

instance : ∀ m, DecidableEq (Traj n m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m + 1 =>
    letI := instDecidableEqTraj m
    inferInstanceAs (DecidableEq ((Finset (Fin n) × Finset (Fin n)) × Traj n m))

/-- Continuation weight of a trajectory from current fragment `a` and
    current conditional measure `w` (the kernel `K_m` of the chain). -/
def trajW (q : ℚ) : (m : ℕ) → (Finset (Fin n) → ℚ) → Finset (Fin n) →
    Traj n m → ℚ
  | 0, _, _, _ => 1
  | m + 1, w, a, ((v, b), rest) =>
      biasedW q v * postW w q (a ∪ v) b * trajW q m (nextW w q v) (b \ v) rest

/-- Full trajectory weight: sample the initial signal from `w`. -/
def fullW (q : ℚ) (m : ℕ) (w : Finset (Fin n) → ℚ)
    (a : Finset (Fin n)) (t : Traj n m) : ℚ :=
  w a * trajW q m w a t

/-- The final fragment after all rounds. -/
def lastA : (m : ℕ) → Finset (Fin n) → Traj n m → Finset (Fin n)
  | 0, a, _ => a
  | m + 1, _, ((v, b), rest) => lastA m (b \ v) rest

/-- The union of all noise sets along a trajectory. -/
def vUnion : (m : ℕ) → Traj n m → Finset (Fin n)
  | 0, _ => ∅
  | m + 1, ((v, _), rest) => v ∪ vUnion m rest

/-- The round-`ℓ` contraction ratio along a trajectory. -/
def xRatio : (m : ℕ) → Finset (Fin n) → Traj n m → Fin m → ℚ
  | 0, _, _ => fun ℓ => ℓ.elim0
  | m + 1, a, ((v, b), rest) =>
      Fin.cases (ratioX a v b) (xRatio m (b \ v) rest)

section TrajLemmas

variable {w : Finset (Fin n) → ℚ} {q c R : ℚ}

theorem trajW_nonneg (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, 0 ≤ trajW (n := n) q m w a t := by
  intro m
  induction m with
  | zero =>
    intro w hw a t
    norm_num [trajW]
  | succ m ih =>
    intro w hw a t
    obtain ⟨⟨v, b⟩, rest⟩ := t
    show 0 ≤ biasedW q v * postW w q (a ∪ v) b *
      trajW q m (nextW w q v) (b \ v) rest
    exact mul_nonneg
      (mul_nonneg (biasedW_nonneg hq0.le hq1 v) (postW_nonneg hw hq0 _ b))
      (ih (nextW w q v) (nextW_nonneg hw hq0 v) (b \ v) rest)

/-- A support pair `(a, b)` of the coupling pushes positive mass onto the
    fragment `b \ v` of the next conditional measure. -/
theorem nextW_pos {w : Finset (Fin n) → ℚ} {q : ℚ} (hw : IsProbW w)
    (hq0 : 0 < q) {a v b : Finset (Fin n)}
    (ha : w a ≠ 0) (hpost : postW w q (a ∪ v) b ≠ 0) :
    0 < nextW w q v (b \ v) := by
  have hwa : 0 < w a := lt_of_le_of_ne (hw.1 a) (Ne.symm ha)
  have hpb : 0 < postW w q (a ∪ v) b :=
    lt_of_le_of_ne (postW_nonneg hw.1 hq0 _ _) (Ne.symm hpost)
  have hterm : ∀ a' b' : Finset (Fin n),
      0 ≤ w a' * postW w q (a' ∪ v) b' *
        (if b' \ v = b \ v then (1:ℚ) else 0) := by
    intro a' b'
    have h1 := hw.1 a'
    have h2 := postW_nonneg hw.1 hq0 (a' ∪ v) b'
    by_cases h : b' \ v = b \ v
    · rw [if_pos h, mul_one]
      positivity
    · rw [if_neg h, mul_zero]
  apply Finset.sum_pos'
  · intro a' _
    exact Finset.sum_nonneg fun b' _ => hterm a' b'
  · refine ⟨a, Finset.mem_univ a, Finset.sum_pos' (fun b' _ => hterm a b')
      ⟨b, Finset.mem_univ b, ?_⟩⟩
    rw [if_pos rfl, mul_one]
    positivity

/-- (J1) The continuation kernel is a probability from any support point. -/
theorem sum_trajW (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), IsProbW w →
      ∀ a, w a ≠ 0 → ∑ t : Traj n m, trajW q m w a t = 1 := by
  intro m
  induction m with
  | zero =>
    intro w hw a ha
    show ∑ _t : PUnit, (1 : ℚ) = 1
    simp
  | succ m ih =>
    intro w hw a ha
    show ∑ t : (Finset (Fin n) × Finset (Fin n)) × Traj n m,
      trajW q (m + 1) w a t = 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hbody : ∀ v b : Finset (Fin n), ∀ rest : Traj n m,
        trajW q (m + 1) w a ((v, b), rest)
        = biasedW q v * postW w q (a ∪ v) b *
            trajW q m (nextW w q v) (b \ v) rest := fun _ _ _ => rfl
    have hinner : ∀ v b : Finset (Fin n),
        ∑ rest : Traj n m, trajW q (m + 1) w a ((v, b), rest)
        = biasedW q v * (postW w q (a ∪ v) b * 1) := by
      intro v b
      rw [Finset.sum_congr rfl fun rest _ => hbody v b rest]
      by_cases hpost : postW w q (a ∪ v) b = 0
      · rw [hpost]
        simp
      · rw [← Finset.mul_sum,
          ih (nextW w q v) (nextW_isProbW hw hq0 v)
            (b \ v) (nextW_pos hw hq0 ha hpost).ne', mul_one, mul_one]
    rw [Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun b _ => hinner v b]
    have hpostsum : ∀ v : Finset (Fin n),
        ∑ b : Finset (Fin n), biasedW q v * (postW w q (a ∪ v) b * 1)
        = biasedW q v := by
      intro v
      rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl fun b _ => mul_one (postW w q (a ∪ v) b)]
      rw [sum_postW (partZ_pos hw.1 hq0 ha Finset.subset_union_left),
        mul_one]
    rw [Finset.sum_congr rfl fun v _ => hpostsum v, sum_biasedW]

/-- Splitting a sum over `Traj n (m+1)` into its three coordinates. -/
theorem sum_traj_succ {m : ℕ} (G : Traj n (m + 1) → ℚ) :
    ∑ t : Traj n (m + 1), G t
    = ∑ v : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
        G ((v, b), rest) := by
  show ∑ t : (Finset (Fin n) × Finset (Fin n)) × Traj n m, G t
    = ∑ v : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
        G ((v, b), rest)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

/-- Regrouping an expectation against `nextW` back into the planted pair
    sum (the change of variables `(a, b) ↦ b \ v`). -/
theorem sum_nextW_mul (v : Finset (Fin n)) (F : Finset (Fin n) → ℚ) :
    ∑ t : Finset (Fin n), nextW w q v t * F t
    = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
        w a * postW w q (a ∪ v) b * F (b \ v) := by
  unfold nextW
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_mul _ _ (F t), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_mul _ _ (F t), Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hper : ∀ t : Finset (Fin n),
      (w a * postW w q (a ∪ v) b * if b \ v = t then (1:ℚ) else 0) * F t
      = if b \ v = t then w a * postW w q (a ∪ v) b * F t else 0 := by
    intro t
    by_cases h : b \ v = t
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun t _ => hper t,
    Finset.sum_ite_eq univ (b \ v) (fun t => w a * postW w q (a ∪ v) b * F t),
    if_pos (Finset.mem_univ _)]

/-- Pulling a constant out of the planted triple sum. -/
theorem triple_mul_sum {m : ℕ} (cst : ℚ)
    (Φ : Finset (Fin n) → Finset (Fin n) → Traj n m → ℚ) :
    ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
      cst * Φ a b rest
    = cst * ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
        Φ a b rest := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-- Chain-step collapse: the planted triple sum against any functional of
    the next fragment and the suffix regroups into the next conditional
    measure's full trajectory weight. -/
theorem sum_step_collapse {m : ℕ} (v : Finset (Fin n))
    (h : Finset (Fin n) → Traj n m → ℚ) :
    ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
      w a * postW w q (a ∪ v) b *
        (trajW q m (nextW w q v) (b \ v) rest * h (b \ v) rest)
    = ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
        fullW q m (nextW w q v) t' rest * h t' rest := by
  have hpull : ∀ a b : Finset (Fin n),
      ∑ rest : Traj n m, w a * postW w q (a ∪ v) b *
        (trajW q m (nextW w q v) (b \ v) rest * h (b \ v) rest)
      = w a * postW w q (a ∪ v) b *
          ∑ rest : Traj n m,
            trajW q m (nextW w q v) (b \ v) rest * h (b \ v) rest :=
    fun a b => (Finset.mul_sum _ _ _).symm
  calc ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
      w a * postW w q (a ∪ v) b *
        (trajW q m (nextW w q v) (b \ v) rest * h (b \ v) rest)
      = ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
          w a * postW w q (a ∪ v) b *
            ∑ rest : Traj n m,
              trajW q m (nextW w q v) (b \ v) rest * h (b \ v) rest :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          hpull a b
    _ = ∑ t' : Finset (Fin n), nextW w q v t' *
          ∑ rest : Traj n m,
            trajW q m (nextW w q v) t' rest * h t' rest :=
        (sum_nextW_mul v fun t' => ∑ rest : Traj n m,
          trajW q m (nextW w q v) t' rest * h t' rest).symm
    _ = ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
          fullW q m (nextW w q v) t' rest * h t' rest := by
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun rest _ => ?_
        show nextW w q v t' * (trajW q m (nextW w q v) t' rest * h t' rest)
          = nextW w q v t' * trajW q m (nextW w q v) t' rest * h t' rest
        exact (mul_assoc _ _ _).symm

/-- Splitting a sum over `(m+1)`-tuples of finsets into the head and the
    tail of the tuple. -/
theorem sum_pi_cons {m : ℕ} (f : (Fin (m + 1) → Finset (Fin n)) → ℚ) :
    ∑ V : Fin (m + 1) → Finset (Fin n), f V
    = ∑ v : Finset (Fin n), ∑ V' : Fin m → Finset (Fin n),
        f (Fin.cons v V') := by
  have h1 : ∑ V : Fin (m + 1) → Finset (Fin n), f V
      = ∑ p : Finset (Fin n) × (Fin m → Finset (Fin n)),
          f (Fin.cons p.1 p.2) := by
    refine Finset.sum_nbij' (i := fun V => (V 0, Fin.tail V))
      (j := fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro V _
      exact Finset.mem_univ _
    · intro p _
      exact Finset.mem_univ _
    · intro V _
      exact Fin.cons_self_tail V
    · intro p _
      simp
    · intro V _
      simp [Fin.cons_self_tail]
  rw [h1, Fintype.sum_prod_type]

/-- The pointwise union of a `Fin.cons` tuple of finsets. -/
theorem sup_univ_cons {m : ℕ} (v : Finset (Fin n)) (V : Fin m → Finset (Fin n)) :
    univ.sup (Fin.cons v V : Fin (m + 1) → Finset (Fin n))
      = v ∪ univ.sup V := by
  ext x
  simp only [Finset.mem_sup, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hx⟩
    revert hx
    refine Fin.cases ?_ ?_ i
    · intro hx
      exact Or.inl (by simpa using hx)
    · intro j hx
      exact Or.inr ⟨j, by simpa using hx⟩
  · rintro (hx | ⟨j, hx⟩)
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨j.succ, by simpa using hx⟩

/-- (J2) The noise marginal of the trajectory measure is the product of
    biased weights: trajectory functionals of the noise alone reduce to
    the `m`-fold product space. -/
theorem sum_fullW_vfun (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), IsProbW w →
      ∀ g : Finset (Fin n) → ℚ,
      ∑ a : Finset (Fin n), ∑ t : Traj n m, fullW q m w a t * g (vUnion m t)
      = ∑ V : Fin m → Finset (Fin n),
          (∏ j, biasedW q (V j)) * g (univ.sup V) := by
  intro m
  induction m with
  | zero =>
    intro w hw g
    have hL : ∑ a : Finset (Fin n), ∑ t : Traj n 0,
        fullW q 0 w a t * g (vUnion 0 t) = g ∅ := by
      show ∑ a : Finset (Fin n), ∑ _t : PUnit, w a * 1 * g ∅ = g ∅
      simp [← Finset.sum_mul, hw.2]
    have hR : ∑ V : Fin 0 → Finset (Fin n),
        (∏ j, biasedW q (V j)) * g (univ.sup V) = g ∅ := by
      have hconst : ∀ V : Fin 0 → Finset (Fin n),
          (∏ j, biasedW q (V j)) * g (univ.sup V) = g ∅ := by
        intro V
        rw [Fin.prod_univ_zero, one_mul]
        congr 1
      rw [Finset.sum_congr rfl fun V _ => hconst V, Finset.sum_const,
        Finset.card_univ, Fintype.card_unique, one_smul]
    rw [hL, hR]
  | succ m ih =>
    intro w hw g
    have hsplit : ∀ a : Finset (Fin n),
        ∑ t : Traj n (m + 1), fullW q (m + 1) w a t * g (vUnion (m + 1) t)
        = ∑ v : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
            fullW q (m + 1) w a ((v, b), rest)
              * g (vUnion (m + 1) ((v, b), rest)) :=
      fun a => sum_traj_succ _
    rw [Finset.sum_congr rfl fun a _ => hsplit a]
    have hbody : ∀ a v b : Finset (Fin n), ∀ rest : Traj n m,
        fullW q (m + 1) w a ((v, b), rest) * g (vUnion (m + 1) ((v, b), rest))
        = biasedW q v * (w a * postW w q (a ∪ v) b *
            (trajW q m (nextW w q v) (b \ v) rest * g (v ∪ vUnion m rest))) := by
      intro a v b rest
      show w a * (biasedW q v * postW w q (a ∪ v) b *
          trajW q m (nextW w q v) (b \ v) rest) * g (v ∪ vUnion m rest)
        = biasedW q v * (w a * postW w q (a ∪ v) b *
            (trajW q m (nextW w q v) (b \ v) rest * g (v ∪ vUnion m rest)))
      ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun rest _ =>
        hbody a v b rest, Finset.sum_comm]
    have hv : ∀ v : Finset (Fin n),
        ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
          biasedW q v * (w a * postW w q (a ∪ v) b *
            (trajW q m (nextW w q v) (b \ v) rest * g (v ∪ vUnion m rest)))
        = biasedW q v * ∑ V' : Fin m → Finset (Fin n),
            (∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V') := by
      intro v
      have hstep : ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
          w a * postW w q (a ∪ v) b *
            (trajW q m (nextW w q v) (b \ v) rest * g (v ∪ vUnion m rest))
          = ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
              fullW q m (nextW w q v) t' rest * g (v ∪ vUnion m rest) :=
        sum_step_collapse v (fun _ rest => g (v ∪ vUnion m rest))
      have hIH : ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
          fullW q m (nextW w q v) t' rest * g (v ∪ vUnion m rest)
          = ∑ V' : Fin m → Finset (Fin n),
              (∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V') :=
        ih (nextW w q v) (nextW_isProbW hw hq0 v) (fun W => g (v ∪ W))
      calc ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
          biasedW q v * (w a * postW w q (a ∪ v) b *
            (trajW q m (nextW w q v) (b \ v) rest * g (v ∪ vUnion m rest)))
          = biasedW q v * ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
              ∑ rest : Traj n m, w a * postW w q (a ∪ v) b *
                (trajW q m (nextW w q v) (b \ v) rest
                  * g (v ∪ vUnion m rest)) := triple_mul_sum _ _
        _ = biasedW q v * ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
              fullW q m (nextW w q v) t' rest * g (v ∪ vUnion m rest) := by
            rw [hstep]
        _ = biasedW q v * ∑ V' : Fin m → Finset (Fin n),
              (∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V') := by
            rw [hIH]
    rw [Finset.sum_congr rfl fun v _ => hv v,
      sum_pi_cons (fun V => (∏ j, biasedW q (V j)) * g (univ.sup V))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun V' _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [sup_univ_cons]
    ring

/-- (T3) Per-round marginal contraction: the trajectory expectation of the
    round-`ℓ` ratio obeys the one-step bound, for every round. -/
theorem sum_fullW_xRatio (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R)) {m : ℕ} (ℓ : Fin m) :
    ∑ a : Finset (Fin n), ∑ t : Traj n m, fullW q m w a t * xRatio m a t ℓ
      ≤ 6 * c := by
  suffices H : ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), IsProbW w →
      IsSpreadW R w → ∀ ℓ : Fin m,
      ∑ a : Finset (Fin n), ∑ t : Traj n m, fullW q m w a t * xRatio m a t ℓ
        ≤ 6 * c by exact H m w hw hsp ℓ
  intro m
  induction m with
  | zero =>
    intro w _ _ ℓ
    exact ℓ.elim0
  | succ m ih =>
    intro w hw hsp ℓ
    have hsplit : ∀ a : Finset (Fin n),
        ∑ t : Traj n (m + 1), fullW q (m + 1) w a t * xRatio (m + 1) a t ℓ
        = ∑ v : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
            fullW q (m + 1) w a ((v, b), rest)
              * xRatio (m + 1) a ((v, b), rest) ℓ :=
      fun a => sum_traj_succ _
    rw [Finset.sum_congr rfl fun a _ => hsplit a]
    refine Fin.cases ?_ ?_ ℓ
    · -- round 0: the one-step contraction
      have hbody : ∀ a v b : Finset (Fin n), ∀ rest : Traj n m,
          fullW q (m + 1) w a ((v, b), rest)
            * xRatio (m + 1) a ((v, b), rest) (0 : Fin (m + 1))
          = cplW w q a v b * ratioX a v b
              * trajW q m (nextW w q v) (b \ v) rest := by
        intro a v b rest
        have hx : xRatio (m + 1) a ((v, b), rest) (0 : Fin (m + 1))
            = ratioX a v b := by
          show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest)
              (0 : Fin (m + 1)) = ratioX a v b
          simp
        rw [hx]
        show w a * (biasedW q v * postW w q (a ∪ v) b *
            trajW q m (nextW w q v) (b \ v) rest) * ratioX a v b
          = cplW w q a v b * ratioX a v b
              * trajW q m (nextW w q v) (b \ v) rest
        unfold cplW
        ring
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun rest _ =>
          hbody a v b rest]
      have hinner : ∀ a v b : Finset (Fin n),
          ∑ rest : Traj n m, cplW w q a v b * ratioX a v b
              * trajW q m (nextW w q v) (b \ v) rest
          = cplW w q a v b * ratioX a v b := by
        intro a v b
        rw [← Finset.mul_sum]
        by_cases ha : w a = 0
        · simp [cplW, ha]
        · by_cases hpost : postW w q (a ∪ v) b = 0
          · simp [cplW, hpost]
          · rw [sum_trajW hq0 m (nextW w q v) (nextW_isProbW hw hq0 v)
              (b \ v) (nextW_pos hw hq0 ha hpost).ne', mul_one]
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun b _ => hinner a v b]
      exact one_step hw hsp hq0 hq1 hc hc' hR hcqR
    · -- later rounds: recurse through the chain step
      intro j
      have hbody : ∀ a v b : Finset (Fin n), ∀ rest : Traj n m,
          fullW q (m + 1) w a ((v, b), rest)
            * xRatio (m + 1) a ((v, b), rest) (Fin.succ j)
          = biasedW q v * (w a * postW w q (a ∪ v) b *
              (trajW q m (nextW w q v) (b \ v) rest
                * xRatio m (b \ v) rest j)) := by
        intro a v b rest
        have hx : xRatio (m + 1) a ((v, b), rest) (Fin.succ j)
            = xRatio m (b \ v) rest j := by
          show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest) (Fin.succ j)
            = xRatio m (b \ v) rest j
          simp
        rw [hx]
        show w a * (biasedW q v * postW w q (a ∪ v) b *
            trajW q m (nextW w q v) (b \ v) rest) * xRatio m (b \ v) rest j
          = biasedW q v * (w a * postW w q (a ∪ v) b *
              (trajW q m (nextW w q v) (b \ v) rest
                * xRatio m (b \ v) rest j))
        ring
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun rest _ =>
          hbody a v b rest, Finset.sum_comm]
      have hv : ∀ v : Finset (Fin n),
          ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
            biasedW q v * (w a * postW w q (a ∪ v) b *
              (trajW q m (nextW w q v) (b \ v) rest
                * xRatio m (b \ v) rest j))
          = biasedW q v * ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
              fullW q m (nextW w q v) t' rest * xRatio m t' rest j := by
        intro v
        have hstep : ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
            ∑ rest : Traj n m, w a * postW w q (a ∪ v) b *
              (trajW q m (nextW w q v) (b \ v) rest
                * xRatio m (b \ v) rest j)
            = ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
                fullW q m (nextW w q v) t' rest * xRatio m t' rest j :=
          sum_step_collapse v (fun t' rest => xRatio m t' rest j)
        calc ∑ a : Finset (Fin n), ∑ b : Finset (Fin n), ∑ rest : Traj n m,
            biasedW q v * (w a * postW w q (a ∪ v) b *
              (trajW q m (nextW w q v) (b \ v) rest
                * xRatio m (b \ v) rest j))
            = biasedW q v * ∑ a : Finset (Fin n), ∑ b : Finset (Fin n),
                ∑ rest : Traj n m, w a * postW w q (a ∪ v) b *
                  (trajW q m (nextW w q v) (b \ v) rest
                    * xRatio m (b \ v) rest j) := triple_mul_sum _ _
          _ = biasedW q v * ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
                fullW q m (nextW w q v) t' rest * xRatio m t' rest j := by
              rw [hstep]
      rw [Finset.sum_congr rfl fun v _ => hv v]
      have hinner : ∀ v : Finset (Fin n),
          ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
            fullW q m (nextW w q v) t' rest * xRatio m t' rest j ≤ 6 * c :=
        fun v => ih (nextW w q v) (nextW_isProbW hw hq0 v)
          (nextW_isSpreadW hw hsp hR hq0 v) j
      calc ∑ v : Finset (Fin n), biasedW q v *
          ∑ t' : Finset (Fin n), ∑ rest : Traj n m,
            fullW q m (nextW w q v) t' rest * xRatio m t' rest j
          ≤ ∑ v : Finset (Fin n), biasedW q v * (6 * c) :=
            Finset.sum_le_sum fun v _ =>
              mul_le_mul_of_nonneg_left (hinner v)
                (biasedW_nonneg hq0.le hq1 v)
        _ = 6 * c := by rw [← Finset.sum_mul, sum_biasedW, one_mul]

/-- Factoring a nonzero step weight: both the posterior factor and the
    continuation factor are nonzero. -/
theorem trajW_succ_ne_zero {m : ℕ} {a v b : Finset (Fin n)} {rest : Traj n m}
    (htw : trajW q (m + 1) w a ((v, b), rest) ≠ 0) :
    postW w q (a ∪ v) b ≠ 0 ∧
      trajW q m (nextW w q v) (b \ v) rest ≠ 0 := by
  have htw' : biasedW q v * postW w q (a ∪ v) b *
      trajW q m (nextW w q v) (b \ v) rest ≠ 0 := htw
  obtain ⟨hbp, hrest⟩ := mul_ne_zero_iff.mp htw'
  exact ⟨(mul_ne_zero_iff.mp hbp).2, hrest⟩

/-- On the posterior support, the next fragment sits inside the current
    one: `B ⊆ A ∪ v` forces `B \ v ⊆ A`. -/
theorem sdiff_subset_of_postW {a v b : Finset (Fin n)}
    (hpost : postW w q (a ∪ v) b ≠ 0) : b \ v ⊆ a := by
  obtain ⟨-, hbav⟩ := postW_support hpost
  intro x hx
  obtain ⟨hxb, hxv⟩ := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp (hbav hxb) with h | h
  · exact h
  · exact absurd h hxv

/-- `nextW_pos` from pointwise nonnegativity alone (no total-mass-one
    hypothesis), for use along the support chase. -/
theorem nextW_pos_of_nonneg (hw : ∀ a, 0 ≤ w a) (hq0 : 0 < q)
    {a v b : Finset (Fin n)}
    (ha : w a ≠ 0) (hpost : postW w q (a ∪ v) b ≠ 0) :
    0 < nextW w q v (b \ v) := by
  have hwa : 0 < w a := lt_of_le_of_ne (hw a) (Ne.symm ha)
  have hpb : 0 < postW w q (a ∪ v) b :=
    lt_of_le_of_ne (postW_nonneg hw hq0 _ _) (Ne.symm hpost)
  have hterm : ∀ a' b' : Finset (Fin n),
      0 ≤ w a' * postW w q (a' ∪ v) b' *
        (if b' \ v = b \ v then (1:ℚ) else 0) := by
    intro a' b'
    have h1 := hw a'
    have h2 := postW_nonneg hw hq0 (a' ∪ v) b'
    by_cases h : b' \ v = b \ v
    · rw [if_pos h, mul_one]
      positivity
    · rw [if_neg h, mul_zero]
  apply Finset.sum_pos'
  · intro a' _
    exact Finset.sum_nonneg fun b' _ => hterm a' b'
  · refine ⟨a, Finset.mem_univ a, Finset.sum_pos' (fun b' _ => hterm a b')
      ⟨b, Finset.mem_univ b, ?_⟩⟩
    rw [if_pos rfl, mul_one]
    positivity

/-- The support chase along the continuation kernel: a nonzero-weight
    trajectory with empty final fragment covers a support member. -/
theorem support_chase_aux (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, w a ≠ 0 → trajW q m w a t ≠ 0 → lastA m a t = ∅ →
      ∃ T, w T ≠ 0 ∧ T ⊆ vUnion m t := by
  intro m
  induction m with
  | zero =>
    intro w hw a t ha _ hlast
    refine ⟨a, ha, ?_⟩
    have hae : a = ∅ := hlast
    rw [hae]
    exact Finset.empty_subset _
  | succ m ih =>
    intro w hw a t ha htw hlast
    obtain ⟨⟨v, b⟩, rest⟩ := t
    obtain ⟨hpost, hrest⟩ := trajW_succ_ne_zero htw
    have hnext : nextW w q v (b \ v) ≠ 0 :=
      (nextW_pos_of_nonneg hw hq0 ha hpost).ne'
    have hlast' : lastA m (b \ v) rest = ∅ := hlast
    obtain ⟨T', hT', hT'sub⟩ := ih (nextW w q v) (nextW_nonneg hw hq0 v)
      (b \ v) rest hnext hrest hlast'
    obtain ⟨c₀, hc₀, hTc⟩ := nextW_support hT'
    refine ⟨c₀, hc₀, ?_⟩
    show c₀ ⊆ v ∪ vUnion m rest
    intro x hx
    by_cases hxv : x ∈ v
    · exact Finset.mem_union.mpr (Or.inl hxv)
    · refine Finset.mem_union.mpr (Or.inr (hT'sub ?_))
      rw [hTc]
      exact Finset.mem_sdiff.mpr ⟨hx, hxv⟩

/-- Support chase (MNSZ §2.4 end): on a positive-weight trajectory whose
    final fragment is empty, some support member of `w` is covered by the
    union of the noise sets. -/
theorem support_chase (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, 0 < fullW q m w a t → lastA m a t = ∅ →
      ∃ T, w T ≠ 0 ∧ T ⊆ vUnion m t := by
  intro m w hw a t hpos hlast
  have hne : w a * trajW q m w a t ≠ 0 := ne_of_gt hpos
  obtain ⟨ha, htw⟩ := mul_ne_zero_iff.mp hne
  exact support_chase_aux hq0 m w hw a t ha htw hlast

/-- On the support of the chain, fragments only shrink: the final fragment
    is contained in the initial one. -/
theorem lastA_subset (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, trajW q m w a t ≠ 0 → lastA m a t ⊆ a := by
  intro m
  induction m with
  | zero =>
    intro w _ a t _
    show a ⊆ a
    exact Finset.Subset.refl a
  | succ m ih =>
    intro w hw a t htw
    obtain ⟨⟨v, b⟩, rest⟩ := t
    obtain ⟨hpost, hrest⟩ := trajW_succ_ne_zero htw
    have hbva : b \ v ⊆ a := sdiff_subset_of_postW hpost
    show lastA m (b \ v) rest ⊆ a
    exact (ih (nextW w q v) (nextW_nonneg hw hq0 v) (b \ v) rest hrest).trans
      hbva

/-- On the support of the chain, every round ratio lies in `[0, 1]`. -/
theorem xRatio_mem_Icc (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, trajW q m w a t ≠ 0 → ∀ ℓ : Fin m,
      0 ≤ xRatio m a t ℓ ∧ xRatio m a t ℓ ≤ 1 := by
  intro m
  induction m with
  | zero =>
    intro w _ a t _ ℓ
    exact ℓ.elim0
  | succ m ih =>
    intro w hw a t htw ℓ
    obtain ⟨⟨v, b⟩, rest⟩ := t
    obtain ⟨hpost, hrest⟩ := trajW_succ_ne_zero htw
    have hbva : b \ v ⊆ a := sdiff_subset_of_postW hpost
    refine Fin.cases ?_ ?_ ℓ
    · have hx : xRatio (m + 1) a ((v, b), rest) (0 : Fin (m + 1))
          = ratioX a v b := by
        show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest)
            (0 : Fin (m + 1)) = ratioX a v b
        simp
      rw [hx]
      unfold ratioX
      by_cases hae : a = ∅
      · rw [if_pos hae]
        norm_num
      · rw [if_neg hae]
        have hacard : (0 : ℚ) < (a.card : ℚ) := by
          exact_mod_cast Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hae)
        constructor
        · positivity
        · rw [div_le_one hacard]
          exact_mod_cast Finset.card_le_card hbva
    · intro i
      have hx : xRatio (m + 1) a ((v, b), rest) (Fin.succ i)
          = xRatio m (b \ v) rest i := by
        show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest) (Fin.succ i)
          = xRatio m (b \ v) rest i
        simp
      rw [hx]
      exact ih (nextW w q v) (nextW_nonneg hw hq0 v) (b \ v) rest hrest i

/-- On the support with nonempty final fragment, the round ratios
    telescope to `|A_{m+1}|/|A₁|`. -/
theorem prod_xRatio (hq0 : 0 < q) :
    ∀ (m : ℕ) (w : Finset (Fin n) → ℚ), (∀ a, 0 ≤ w a) →
      ∀ a t, trajW q m w a t ≠ 0 → lastA m a t ≠ ∅ →
      ∏ ℓ : Fin m, xRatio m a t ℓ
        = ((lastA m a t).card : ℚ) / (a.card : ℚ) := by
  intro m
  induction m with
  | zero =>
    intro w _ a t _ hne
    have hane : a ≠ ∅ := hne
    have hacard : ((a.card : ℚ)) ≠ 0 := by
      have h := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hane)
      exact_mod_cast h.ne'
    show ∏ ℓ : Fin 0, xRatio 0 a t ℓ = ((a.card : ℚ)) / (a.card : ℚ)
    rw [Fin.prod_univ_zero, div_self hacard]
  | succ m ih =>
    intro w hw a t htw hne
    obtain ⟨⟨v, b⟩, rest⟩ := t
    obtain ⟨hpost, hrest⟩ := trajW_succ_ne_zero htw
    have hbva : b \ v ⊆ a := sdiff_subset_of_postW hpost
    have hne' : lastA m (b \ v) rest ≠ ∅ := hne
    have hlsub : lastA m (b \ v) rest ⊆ b \ v :=
      lastA_subset hq0 m (nextW w q v) (nextW_nonneg hw hq0 v)
        (b \ v) rest hrest
    have hbvne : b \ v ≠ ∅ := by
      intro h0
      exact hne' (Finset.subset_empty.mp (h0 ▸ hlsub))
    have hane : a ≠ ∅ := by
      intro h0
      exact hbvne (Finset.subset_empty.mp (h0 ▸ hbva))
    have hbvcard : (((b \ v).card : ℚ)) ≠ 0 := by
      have h := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hbvne)
      exact_mod_cast h.ne'
    have hacard : ((a.card : ℚ)) ≠ 0 := by
      have h := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hane)
      exact_mod_cast h.ne'
    have hIH : ∏ ℓ : Fin m, xRatio m (b \ v) rest ℓ
        = ((lastA m (b \ v) rest).card : ℚ) / (((b \ v).card : ℚ)) :=
      ih (nextW w q v) (nextW_nonneg hw hq0 v) (b \ v) rest hrest hne'
    have hx0 : xRatio (m + 1) a ((v, b), rest) (0 : Fin (m + 1))
        = ratioX a v b := by
      show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest)
          (0 : Fin (m + 1)) = ratioX a v b
      simp
    have hxs : ∀ i : Fin m, xRatio (m + 1) a ((v, b), rest) (Fin.succ i)
        = xRatio m (b \ v) rest i := by
      intro i
      show Fin.cases (ratioX a v b) (xRatio m (b \ v) rest) (Fin.succ i)
        = xRatio m (b \ v) rest i
      simp
    show ∏ ℓ : Fin (m + 1), xRatio (m + 1) a ((v, b), rest) ℓ
      = ((lastA m (b \ v) rest).card : ℚ) / (a.card : ℚ)
    rw [Fin.prod_univ_succ, hx0, Finset.prod_congr rfl fun i _ => hxs i, hIH]
    unfold ratioX
    rw [if_neg hane]
    field_simp

/-- Bad-round count (the Hölder-free aggregation): on a positive-weight
    trajectory with nonempty final fragment and `|A₁| ≤ k ≤ 2^L`, the
    contraction ratios sum to at least `(m - L)/2`. -/
theorem sum_xRatio_ge (hq0 : 0 < q) {k L : ℕ} (hkL : k ≤ 2 ^ L)
    (hw : ∀ a₀, 0 ≤ w a₀) (hsupp : ∀ a₀, w a₀ ≠ 0 → a₀.card ≤ k)
    {m : ℕ} {a : Finset (Fin n)} {t : Traj n m}
    (hpos : 0 < fullW q m w a t) (hne : lastA m a t ≠ ∅) :
    ((m : ℚ) - L) / 2 ≤ ∑ ℓ : Fin m, xRatio m a t ℓ := by
  have hfne : w a * trajW q m w a t ≠ 0 := ne_of_gt hpos
  obtain ⟨hwa, htw⟩ := mul_ne_zero_iff.mp hfne
  have hak : a.card ≤ k := hsupp a hwa
  have hlsub : lastA m a t ⊆ a := lastA_subset hq0 m w hw a t htw
  have hlne : (lastA m a t).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hane : a.Nonempty := hlne.mono hlsub
  have hacard : 0 < a.card := Finset.card_pos.mpr hane
  have hkpos : (0:ℚ) < (k : ℚ) := by
    have h := lt_of_lt_of_le hacard hak
    exact_mod_cast h
  have hx01 := xRatio_mem_Icc hq0 m w hw a t htw
  have hprod := prod_xRatio hq0 m w hw a t htw hne
  -- the product over the bad rounds is at least 1/k …
  have hBnonneg : 0 ≤ ∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
      xRatio m a t ℓ :=
    Finset.prod_nonneg fun ℓ _ => (hx01 ℓ).1
  have hprodB : (1 : ℚ) / k
      ≤ ∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2), xRatio m a t ℓ := by
    have h1 : (1 : ℚ) / k ≤ ((lastA m a t).card : ℚ) / (a.card : ℚ) := by
      have hapos : (0:ℚ) < (a.card : ℚ) := by exact_mod_cast hacard
      have hl1 : (1 : ℚ) ≤ ((lastA m a t).card : ℚ) := by
        exact_mod_cast Finset.card_pos.mpr hlne
      have hka : ((a.card : ℚ)) ≤ (k : ℚ) := by exact_mod_cast hak
      rw [div_le_div_iff₀ hkpos hapos, one_mul]
      calc (a.card : ℚ) ≤ (k : ℚ) := hka
        _ = 1 * (k : ℚ) := (one_mul _).symm
        _ ≤ ((lastA m a t).card : ℚ) * (k : ℚ) :=
            mul_le_mul_of_nonneg_right hl1 hkpos.le
    calc (1:ℚ)/k ≤ ((lastA m a t).card : ℚ) / (a.card : ℚ) := h1
      _ = ∏ ℓ : Fin m, xRatio m a t ℓ := hprod.symm
      _ = (∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
            xRatio m a t ℓ)
          * ∏ ℓ ∈ univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2),
              xRatio m a t ℓ :=
          (Finset.prod_filter_mul_prod_filter_not univ _ _).symm
      _ ≤ (∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
            xRatio m a t ℓ) * 1 :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_one (fun ℓ _ => (hx01 ℓ).1)
              (fun ℓ _ => (hx01 ℓ).2)) hBnonneg
      _ = ∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
            xRatio m a t ℓ := mul_one _
  -- … and at most (1/2)^|B|, so |B| ≤ L
  have hBle : (∏ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
      xRatio m a t ℓ)
      ≤ (1/2 : ℚ) ^ (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun ℓ _ => (hx01 ℓ).1)
      (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2.le)
  have hcardB : (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card ≤ L := by
    have hq2 : (1:ℚ)/k
        ≤ (1/2:ℚ) ^ (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card :=
      le_trans hprodB hBle
    rw [div_pow, one_pow] at hq2
    have h2k : (2:ℚ) ^ (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card
        ≤ (k:ℚ) := le_of_one_div_le_one_div hkpos hq2
    have h2kN : (2:ℕ) ^ (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card
        ≤ k := by exact_mod_cast h2k
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (le_trans h2kN hkL)
  -- the good rounds carry at least 1/2 each
  have hgood : ((univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2)).card : ℚ)
      * (1/2)
      ≤ ∑ ℓ ∈ univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2),
          xRatio m a t ℓ := by
    calc ((univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2)).card : ℚ) * (1/2)
        = ∑ _ℓ ∈ univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2), (1/2:ℚ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ℓ ∈ univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2),
            xRatio m a t ℓ :=
          Finset.sum_le_sum fun ℓ hℓ =>
            not_lt.mp (Finset.mem_filter.mp hℓ).2
  have hbad0 : 0 ≤ ∑ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2),
      xRatio m a t ℓ :=
    Finset.sum_nonneg fun ℓ _ => (hx01 ℓ).1
  have hsum_split : ∑ ℓ : Fin m, xRatio m a t ℓ
      = (∑ ℓ ∈ univ.filter (fun ℓ => xRatio m a t ℓ < 1/2), xRatio m a t ℓ)
        + ∑ ℓ ∈ univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2),
            xRatio m a t ℓ :=
    (Finset.sum_filter_add_sum_filter_not univ _ _).symm
  have hcards : (univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card
      + (univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2)).card = m := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hcast : ((univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card : ℚ)
      + ((univ.filter (fun ℓ => ¬ xRatio m a t ℓ < 1/2)).card : ℚ)
      = (m : ℚ) := by exact_mod_cast hcards
  have hLcast : ((univ.filter (fun ℓ => xRatio m a t ℓ < 1/2)).card : ℚ)
      ≤ (L : ℚ) := by exact_mod_cast hcardB
  linarith [hsum_split, hbad0, hgood, hcast, hLcast]

end TrajLemmas

-- ════════════════════════════════════════════════════════════════════
-- §5 THE SPREAD LEMMA ON PRODUCT SPACES
--    Failure indicator, the chain bound, union law, biased transport.
-- ════════════════════════════════════════════════════════════════════

/-- Failure indicator: 1 if no support member of `w` is contained in `W`. -/
def failInd (w : Finset (Fin n) → ℚ) (W : Finset (Fin n)) : ℚ :=
  if ∃ T ∈ (univ : Finset (Finset (Fin n))), w T ≠ 0 ∧ T ⊆ W then 0 else 1

section FailBound

variable {w : Finset (Fin n) → ℚ} {q c R : ℚ}

/-- **The chain bound (MNSZ Theorem 1.2, counting form)**: for an
    `R`-spread probability weight supported on sets of at most `k ≤ 2^L`
    elements, `m = 2(L+1)` rounds of independent `q`-biased noise cover
    some support member except with probability at most `24c`. -/
theorem fail_prob_le (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R))
    {k L : ℕ} (hkL : k ≤ 2 ^ L)
    (hsupp : ∀ a, w a ≠ 0 → a.card ≤ k) {m : ℕ} (hm : m = 2 * (L + 1)) :
    ∑ V : Fin m → Finset (Fin n),
      (∏ j, biasedW q (V j)) * failInd w (univ.sup V) ≤ 24 * c := by
  have hL2 : (0:ℚ) < (L : ℚ) + 2 := by positivity
  rw [← sum_fullW_vfun hq0 m w hw (failInd w)]
  -- pointwise: failure forces ≥ (L+2)/2 worth of ratio mass
  have hpoint : ∀ a : Finset (Fin n), ∀ t : Traj n m,
      fullW q m w a t * failInd w (vUnion m t)
      ≤ fullW q m w a t *
          ((2/((L:ℚ)+2)) * ∑ ℓ : Fin m, xRatio m a t ℓ) := by
    intro a t
    have hfull0 : 0 ≤ fullW q m w a t :=
      mul_nonneg (hw.1 a) (trajW_nonneg hq0 hq1 m w hw.1 a t)
    rcases eq_or_lt_of_le hfull0 with h0 | hfull
    · rw [← h0, zero_mul, zero_mul]
    · have hfne : w a * trajW q m w a t ≠ 0 := ne_of_gt hfull
      obtain ⟨hwa, htw⟩ := mul_ne_zero_iff.mp hfne
      have hx01 := xRatio_mem_Icc hq0 m w hw.1 a t htw
      have hsumx : 0 ≤ ∑ ℓ : Fin m, xRatio m a t ℓ :=
        Finset.sum_nonneg fun ℓ _ => (hx01 ℓ).1
      by_cases hlast : lastA m a t = ∅
      · obtain ⟨T, hT, hTsub⟩ := support_chase hq0 m w hw.1 a t hfull hlast
        have hfI : failInd w (vUnion m t) = 0 := by
          unfold failInd
          rw [if_pos ⟨T, Finset.mem_univ T, hT, hTsub⟩]
        rw [hfI, mul_zero]
        exact mul_nonneg hfull.le (mul_nonneg (by positivity) hsumx)
      · have hge := sum_xRatio_ge hq0 hkL hw.1 hsupp hfull hlast
        have hmL : ((m:ℚ) - L)/2 = ((L:ℚ) + 2)/2 := by
          rw [hm]
          push_cast
          ring
        rw [hmL] at hge
        have h1K : 1 ≤ (2/((L:ℚ)+2)) * ∑ ℓ : Fin m, xRatio m a t ℓ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hL2, one_mul]
          linarith
        have hfI : failInd w (vUnion m t) ≤ 1 := by
          unfold failInd
          split <;> norm_num
        calc fullW q m w a t * failInd w (vUnion m t)
            ≤ fullW q m w a t * 1 :=
              mul_le_mul_of_nonneg_left hfI hfull.le
          _ ≤ fullW q m w a t *
              ((2/((L:ℚ)+2)) * ∑ ℓ : Fin m, xRatio m a t ℓ) :=
              mul_le_mul_of_nonneg_left h1K hfull.le
  -- linearity + the per-round bound T3
  have hswap : ∀ a : Finset (Fin n), ∀ t : Traj n m,
      fullW q m w a t * ((2/((L:ℚ)+2)) * ∑ ℓ : Fin m, xRatio m a t ℓ)
      = (2/((L:ℚ)+2)) * ∑ ℓ : Fin m, fullW q m w a t * xRatio m a t ℓ := by
    intro a t
    rw [← mul_assoc, mul_comm (fullW q m w a t) (2/((L:ℚ)+2)), mul_assoc,
      Finset.mul_sum]
  calc ∑ a : Finset (Fin n), ∑ t : Traj n m,
      fullW q m w a t * failInd w (vUnion m t)
      ≤ ∑ a : Finset (Fin n), ∑ t : Traj n m,
          fullW q m w a t *
            ((2/((L:ℚ)+2)) * ∑ ℓ : Fin m, xRatio m a t ℓ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun t _ => hpoint a t
    _ = ∑ a : Finset (Fin n), ∑ t : Traj n m,
          (2/((L:ℚ)+2)) * ∑ ℓ : Fin m, fullW q m w a t * xRatio m a t ℓ := by
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
          fun t _ => hswap a t
    _ = (2/((L:ℚ)+2)) * ∑ a : Finset (Fin n), ∑ t : Traj n m,
          ∑ ℓ : Fin m, fullW q m w a t * xRatio m a t ℓ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = (2/((L:ℚ)+2)) * ∑ ℓ : Fin m, ∑ a : Finset (Fin n), ∑ t : Traj n m,
          fullW q m w a t * xRatio m a t ℓ := by
        congr 1
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ (2/((L:ℚ)+2)) * ∑ _ℓ : Fin m, 6 * c := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun ℓ _ =>
          sum_fullW_xRatio hw hsp hq0 hq1 hc hc' hR hcqR ℓ
    _ ≤ 24 * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, hm]
        push_cast
        rw [div_mul_eq_mul_div, div_le_iff₀ hL2]
        linarith [hc.le, mul_nonneg hc.le (Nat.cast_nonneg (α := ℚ) L)]

/-- Two-fold convolution: the union of independent `q`- and `σ`-biased
    sets is `(q + σ - qσ)`-biased. -/
theorem convolution_two (q σ : ℚ) (g : Finset (Fin n) → ℚ) :
    ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
      biasedW q v * biasedW σ z * g (v ∪ z)
    = ∑ W : Finset (Fin n), biasedW (q + σ - q * σ) W * g W := by
  -- group the (v,z)-pairs by their union U
  have hswap : ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
      biasedW q v * biasedW σ z * g (v ∪ z)
      = ∑ v : Finset (Fin n), ∑ z : Finset (Fin n), ∑ U : Finset (Fin n),
          (if v ∪ z = U then biasedW q v * biasedW σ z else 0) * g U := by
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_eq_single (v ∪ z)]
    · rw [if_pos rfl]
    · intro U _ hU
      rw [if_neg (fun h : v ∪ z = U => hU h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hswap, Finset.sum_congr rfl fun v _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  -- the union-fiber mass at U is the (q + σ - qσ)-biased weight of U
  have hUn : U.card ≤ n := by
    calc U.card ≤ (univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ U)
      _ = n := Finset.card_fin n
  have hkey : ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
      (if v ∪ z = U then biasedW q v * biasedW σ z else 0)
      = biasedW (q + σ - q * σ) U := by
    -- inner z-sum: the §1 fiber instance at fixed v ⊆ U
    have hstep : ∀ v : Finset (Fin n),
        (∑ z : Finset (Fin n),
          if v ∪ z = U then biasedW q v * biasedW σ z else 0)
        = if v ⊆ U
          then biasedW q v *
            (σ ^ (U.card - v.card) * (1 - σ) ^ (n - U.card)) else 0 := by
      intro v
      by_cases hvU : v ⊆ U
      · rw [if_pos hvU, ← sum_biasedW_union_fiber σ hvU, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by
          by_cases h : v ∪ z = U
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, mul_zero]
      · rw [if_neg hvU]
        apply Finset.sum_eq_zero
        intro z _
        rw [if_neg (fun h : v ∪ z = U => hvU (h ▸ Finset.subset_union_left))]
    rw [Finset.sum_congr rfl fun v _ => hstep v, ← Finset.sum_filter]
    have hfilter : univ.filter (fun v : Finset (Fin n) => v ⊆ U)
        = U.powerset := by
      ext v
      simp [Finset.mem_powerset]
    rw [hfilter]
    -- outer v-sum: split (1-q)^(n-|v|) across the gap and run the engine
    have hterm : ∀ v ∈ U.powerset,
        biasedW q v * (σ ^ (U.card - v.card) * (1 - σ) ^ (n - U.card))
        = (q ^ v.card * ((1 - q) * σ) ^ (U.card - v.card)) *
            ((1 - q) * (1 - σ)) ^ (n - U.card) := by
      intro v hv
      have hvc : v.card ≤ U.card :=
        Finset.card_le_card (Finset.mem_powerset.mp hv)
      unfold biasedW
      have hexp : n - v.card = (U.card - v.card) + (n - U.card) := by omega
      rw [hexp, pow_add, mul_pow, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      sum_pow_mul_pow_powerset]
    unfold biasedW
    have h1 : q + (1 - q) * σ = q + σ - q * σ := by ring
    have h2 : (1 - q) * (1 - σ) = 1 - (q + σ - q * σ) := by ring
    rw [h1, h2]
  calc ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
      (if v ∪ z = U then biasedW q v * biasedW σ z else 0) * g U
      = (∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
          (if v ∪ z = U then biasedW q v * biasedW σ z else 0)) * g U := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun v _ => (Finset.sum_mul _ _ _).symm
    _ = biasedW (q + σ - q * σ) U * g U := by rw [hkey]

/-- `m`-fold union law: the union of `m` independent `q`-biased sets is
    `(1 - (1-q)^m)`-biased. -/
theorem union_law (q : ℚ) (m : ℕ) (g : Finset (Fin n) → ℚ) :
    ∑ V : Fin m → Finset (Fin n), (∏ j, biasedW q (V j)) * g (univ.sup V)
    = ∑ W : Finset (Fin n), biasedW (1 - (1 - q) ^ m) W * g W := by
  induction m generalizing g with
  | zero =>
    -- both sides are g ∅: the empty product/union, and the 0-biased point mass
    have hL : ∑ V : Fin 0 → Finset (Fin n),
        (∏ j, biasedW q (V j)) * g (univ.sup V) = g ∅ := by
      have hconst : ∀ V : Fin 0 → Finset (Fin n),
          (∏ j, biasedW q (V j)) * g (univ.sup V) = g ∅ := by
        intro V
        rw [Fin.prod_univ_zero, one_mul]
        congr 1
      rw [Finset.sum_congr rfl fun V _ => hconst V, Finset.sum_const,
        Finset.card_univ, Fintype.card_unique, one_smul]
    have hR : ∑ W : Finset (Fin n), biasedW (1 - (1 - q) ^ 0) W * g W
        = g ∅ := by
      have h0 : (1 : ℚ) - (1 - q) ^ 0 = 0 := by ring
      rw [h0, Finset.sum_eq_single ∅]
      · unfold biasedW
        simp
      · intro W _ hW
        unfold biasedW
        rw [zero_pow (fun h => hW (Finset.card_eq_zero.mp h)), zero_mul,
          zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hL, hR]
  | succ m ih =>
    rw [sum_pi_cons (fun V => (∏ j, biasedW q (V j)) * g (univ.sup V))]
    -- peel the head coordinate off the product and the union
    have hbody : ∀ v : Finset (Fin n), ∀ V' : Fin m → Finset (Fin n),
        (∏ j, biasedW q ((Fin.cons v V' : Fin (m + 1) → Finset (Fin n)) j))
            * g (univ.sup (Fin.cons v V' : Fin (m + 1) → Finset (Fin n)))
        = biasedW q v *
            ((∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V')) := by
      intro v V'
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [sup_univ_cons]
      ring
    rw [Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun V' _ => hbody v V']
    -- IH at the v-shifted functional, then the two-fold convolution
    have hv : ∀ v : Finset (Fin n),
        ∑ V' : Fin m → Finset (Fin n),
          biasedW q v * ((∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V'))
        = ∑ W : Finset (Fin n),
            biasedW q v * biasedW (1 - (1 - q) ^ m) W * g (v ∪ W) := by
      intro v
      have hIH : ∑ V' : Fin m → Finset (Fin n),
          (∏ j, biasedW q (V' j)) * g (v ∪ univ.sup V')
          = ∑ W : Finset (Fin n), biasedW (1 - (1 - q) ^ m) W * g (v ∪ W) :=
        ih (fun W => g (v ∪ W))
      rw [← Finset.mul_sum, hIH, Finset.mul_sum]
      exact Finset.sum_congr rfl fun W _ => (mul_assoc _ _ _).symm
    rw [Finset.sum_congr rfl fun v _ => hv v,
      convolution_two q (1 - (1 - q) ^ m) g]
    have hparam : q + (1 - (1 - q) ^ m) - q * (1 - (1 - q) ^ m)
        = 1 - (1 - q) ^ (m + 1) := by ring
    rw [hparam]

/-- Transport of the chain bound to a single `δ`-biased set with
    `δ ≥ 1 - (1-q)^m`, by absorbing the slack into one more independent
    biased set (monotonicity of the failure event). -/
theorem fail_prob_le_biased (hw : IsProbW w) (hsp : IsSpreadW R w)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hc : 0 < c) (hc' : 3 * c ^ 2 ≤ 1/2)
    (hR : 0 < R) (hcqR : 1 ≤ c ^ 3 * (q * R))
    {k L : ℕ} (hkL : k ≤ 2 ^ L)
    (hsupp : ∀ a, w a ≠ 0 → a.card ≤ k) {m : ℕ} (hm : m = 2 * (L + 1))
    {δ : ℚ} (hδ1 : δ ≤ 1) (hδq : 1 - (1 - q) ^ m ≤ δ) :
    ∑ W : Finset (Fin n), biasedW δ W * failInd w W ≤ 24 * c := by
  have he0 : (0:ℚ) ≤ (1 - q) ^ m := pow_nonneg (by linarith) m
  have he1 : (1 - q) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hp'0 : (0:ℚ) ≤ 1 - (1 - q) ^ m := by linarith
  have hp'1 : 1 - (1 - q) ^ m ≤ 1 := by linarith
  -- the absorber bias σ solving p' + σ - p'σ = δ for p' = 1 - (1-q)^m;
  -- at the q = 1, m ≥ 1 edge (where (1-q)^m = 0) the hypotheses force
  -- δ = 1 and the junk value 0/0 = 0 satisfies the identity, so no case
  -- split on q is needed and the §6 call site is untouched
  obtain ⟨σ, hσ0, hσ1, hparam⟩ : ∃ σ : ℚ, 0 ≤ σ ∧ σ ≤ 1 ∧
      1 - (1 - q) ^ m + σ - (1 - (1 - q) ^ m) * σ = δ := by
    refine ⟨(δ - 1 + (1 - q) ^ m) / (1 - q) ^ m, ?_, ?_, ?_⟩
    · rcases lt_or_eq_of_le he0 with he | he
      · exact div_nonneg (by linarith) he.le
      · rw [← he]
        simp
    · rcases lt_or_eq_of_le he0 with he | he
      · rw [div_le_one he]
        linarith
      · rw [← he]
        simp
    · rcases lt_or_eq_of_le he0 with he | he
      · have hne : (1 - q) ^ m ≠ 0 := he.ne'
        field_simp
        ring
      · have hδeq : δ = 1 := le_antisymm hδ1 (by linarith)
        rw [hδeq, ← he]
        norm_num
  -- the chain bound, transported through the union law
  have hchain : ∑ W : Finset (Fin n),
      biasedW (1 - (1 - q) ^ m) W * failInd w W ≤ 24 * c := by
    rw [← union_law q m (failInd w)]
    exact fail_prob_le hw hsp hq0 hq1 hc hc' hR hcqR hkL hsupp hm
  -- failure is antitone in the revealed set
  have hmono : ∀ v z : Finset (Fin n), failInd w (v ∪ z) ≤ failInd w v := by
    intro v z
    unfold failInd
    by_cases hv : ∃ T ∈ (univ : Finset (Finset (Fin n))), w T ≠ 0 ∧ T ⊆ v
    · obtain ⟨T, hTu, hTw, hTv⟩ := hv
      have h2 : ∃ T ∈ (univ : Finset (Finset (Fin n))), w T ≠ 0 ∧ T ⊆ v ∪ z :=
        ⟨T, hTu, hTw, hTv.trans Finset.subset_union_left⟩
      exact le_of_eq (by rw [if_pos h2, if_pos ⟨T, hTu, hTw, hTv⟩])
    · rw [if_neg hv]
      split <;> norm_num
  calc ∑ W : Finset (Fin n), biasedW δ W * failInd w W
      = ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
          biasedW (1 - (1 - q) ^ m) v * biasedW σ z * failInd w (v ∪ z) := by
        rw [convolution_two (1 - (1 - q) ^ m) σ (failInd w), hparam]
    _ ≤ ∑ v : Finset (Fin n), ∑ z : Finset (Fin n),
          biasedW (1 - (1 - q) ^ m) v * biasedW σ z * failInd w v :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hmono v z)
            (mul_nonneg (biasedW_nonneg hp'0 hp'1 v)
              (biasedW_nonneg hσ0 hσ1 z))
    _ = ∑ v : Finset (Fin n), biasedW (1 - (1 - q) ^ m) v * failInd w v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        have h1 : ∀ z : Finset (Fin n),
            biasedW (1 - (1 - q) ^ m) v * biasedW σ z * failInd w v
            = biasedW (1 - (1 - q) ^ m) v * failInd w v * biasedW σ z :=
          fun z => by ring
        rw [Finset.sum_congr rfl fun z _ => h1 z, ← Finset.mul_sum,
          sum_biasedW, mul_one]
    _ ≤ 24 * c := hchain

end FailBound

-- ════════════════════════════════════════════════════════════════════
-- §6 M3 — EXTRACTION (BCW): 2s classes, linearity, pigeonhole
-- ════════════════════════════════════════════════════════════════════

section Extraction

/-- Class marginal: for a uniformly random coloring `χ : Fin n → Fin t`,
    the class `χ⁻¹(i)` is `(1/t)`-biased. -/
theorem class_marginal {t : ℕ} (ht : 0 < t) (i : Fin t)
    (g : Finset (Fin n) → ℚ) :
    ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ * g (univ.filter (fun x => χ x = i))
    = ∑ W : Finset (Fin n), biasedW ((t : ℚ)⁻¹) W * g W := by
  have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  -- (i) group colorings by their `i`-class
  have hmaps : ∀ χ ∈ (univ : Finset (Fin n → Fin t)),
      univ.filter (fun x => χ x = i) ∈ (univ : Finset (Finset (Fin n))) :=
    fun χ _ => Finset.mem_univ _
  have hgroup : (∑ χ : Fin n → Fin t,
      ((t : ℚ) ^ n)⁻¹ * g (univ.filter (fun x => χ x = i)))
      = ∑ W : Finset (Fin n),
          ∑ χ ∈ univ.filter (fun χ : Fin n → Fin t =>
            univ.filter (fun x => χ x = i) = W),
            ((t : ℚ) ^ n)⁻¹ * g (univ.filter (fun x => χ x = i)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [hgroup]
  refine Finset.sum_congr rfl fun W _ => ?_
  -- (ii) the summand is constant on the fiber
  have hfib : ∀ χ ∈ univ.filter (fun χ : Fin n → Fin t =>
      univ.filter (fun x => χ x = i) = W),
      ((t : ℚ) ^ n)⁻¹ * g (univ.filter (fun x => χ x = i))
      = ((t : ℚ) ^ n)⁻¹ * g W := by
    intro χ hχ
    rw [(Finset.mem_filter.mp hχ).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  -- (iii) the fiber count is (t-1)^(n-|W|): coordinates in `W` are forced
  -- to `i`, the rest range over the `t-1` non-`i` colors (Fubini)
  have hcount : (((univ.filter (fun χ : Fin n → Fin t =>
      univ.filter (fun x => χ x = i) = W)).card : ℕ) : ℚ)
      = ((t : ℚ) - 1) ^ (n - W.card) := by
    rw [← Finset.sum_boole]
    have hper : ∀ χ : Fin n → Fin t,
        (if univ.filter (fun x => χ x = i) = W then (1:ℚ) else 0)
        = ∏ x : Fin n, (if (χ x = i ↔ x ∈ W) then (1:ℚ) else 0) := by
      intro χ
      by_cases h : univ.filter (fun x => χ x = i) = W
      · rw [if_pos h]
        symm
        apply Finset.prod_eq_one
        intro x _
        rw [if_pos]
        rw [← h]
        simp
      · rw [if_neg h]
        symm
        have hex : ∃ x : Fin n, ¬(χ x = i ↔ x ∈ W) := by
          by_contra hall
          push Not at hall
          exact h (by ext x; simpa using hall x)
        obtain ⟨x₀, hx₀⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ x₀) (if_neg hx₀)
    rw [Finset.sum_congr rfl fun χ _ => hper χ]
    -- Fubini over coordinates
    have hfub := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin t)))
      (fun x c => if (c = i ↔ x ∈ W) then (1:ℚ) else 0)
    rw [Fintype.piFinset_univ] at hfub
    rw [← hfub]
    -- per-coordinate sums
    have hx : ∀ x : Fin n,
        (∑ c : Fin t, if (c = i ↔ x ∈ W) then (1:ℚ) else 0)
        = if x ∈ W then 1 else ((t : ℚ) - 1) := by
      intro x
      by_cases hxW : x ∈ W
      · rw [if_pos hxW]
        have h1 : ∀ c : Fin t, ((c = i ↔ x ∈ W) ↔ (c = i)) :=
          fun c => by simp [hxW]
        rw [Finset.sum_congr rfl fun c _ => if_congr (h1 c) rfl rfl,
          Finset.sum_ite_eq' univ i (fun _ => (1:ℚ)),
          if_pos (Finset.mem_univ i)]
      · rw [if_neg hxW]
        have h1 : ∀ c : Fin t, ((c = i ↔ x ∈ W) ↔ ¬(c = i)) :=
          fun c => by simp [hxW]
        rw [Finset.sum_congr rfl fun c _ => if_congr (h1 c) rfl rfl,
          Finset.sum_boole]
        have h2 : (univ.filter fun c : Fin t => ¬ c = i) = univ.erase i := by
          ext c
          simp [Finset.mem_erase, and_comm]
        rw [h2, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
    rw [Finset.prod_congr rfl fun x _ => hx x,
      Finset.prod_ite (fun _ => (1:ℚ)) (fun _ => ((t : ℚ) - 1)),
      Finset.prod_const_one, one_mul, Finset.prod_const]
    have hcompl : univ.filter (fun x : Fin n => ¬ x ∈ W) = Wᶜ := by
      ext x
      simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin]
  -- (iv) field algebra: (t-1)^(n-|W|)/t^n is the (1/t)-biased weight
  have hWn : W.card ≤ n := by
    simpa [Finset.card_fin] using Finset.card_le_univ W
  have halg : biasedW ((t : ℚ)⁻¹) W
      = ((t : ℚ) - 1) ^ (n - W.card) * ((t : ℚ) ^ n)⁻¹ := by
    have h1 : (1 : ℚ) - (t : ℚ)⁻¹ = ((t : ℚ) - 1) * (t : ℚ)⁻¹ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ htQ.ne']
    have hexp : W.card + (n - W.card) = n := by omega
    unfold biasedW
    calc ((t : ℚ)⁻¹) ^ W.card * (1 - (t : ℚ)⁻¹) ^ (n - W.card)
        = ((t : ℚ)⁻¹) ^ W.card * (((t : ℚ) - 1) * (t : ℚ)⁻¹) ^ (n - W.card) := by
          rw [h1]
      _ = ((t : ℚ) - 1) ^ (n - W.card) *
            (((t : ℚ)⁻¹) ^ W.card * ((t : ℚ)⁻¹) ^ (n - W.card)) := by
          rw [mul_pow]
          ring
      _ = ((t : ℚ) - 1) ^ (n - W.card) * ((t : ℚ)⁻¹) ^ n := by
          rw [← pow_add, hexp]
      _ = ((t : ℚ) - 1) ^ (n - W.card) * ((t : ℚ) ^ n)⁻¹ := by
          rw [inv_pow]
  rw [hcount, halg]
  ring

/-- **The spread lemma, family form**: a `k`-uniform `r`-spread family
    with `r ≥ 884736·s·(log₂ k + 1)` and `|G| > r^k` contains `s`
    pairwise disjoint members — an `s`-sunflower with empty kernel.
    (MNSZ Theorem 1.2 + BCW extraction.) -/
theorem spread_lemma_core {s k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k) {r : ℚ}
    {G : Finset (Finset (Fin n))}
    (hr : ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) ≤ r)
    (hunif : ∀ S ∈ G, S.card = k) (hspread : IsRSpread r G)
    (hcard : r ^ k < (G.card : ℚ)) :
    HasSunflower G s := by
  classical
  -- ── parameters: L with k ≤ 2^L, m rounds, 2s classes of density δ ──
  set L : ℕ := Nat.log 2 k + 1 with hLdef
  set m : ℕ := 2 * (L + 1) with hmdef
  set t : ℕ := 2 * s with htdef
  set δ : ℚ := ((t : ℚ))⁻¹ with hδdef
  set q : ℚ := δ / (m : ℚ) with hqdef
  -- ── numeric groundwork ──
  have hsQ : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
  have hs0 : (0 : ℚ) < (s : ℚ) := lt_of_lt_of_le one_pos hsQ
  have hlg0 : (0 : ℚ) ≤ (Nat.log 2 k : ℚ) := Nat.cast_nonneg _
  have htpos : 0 < t := by omega
  have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast htpos
  have hmpos : 0 < m := by omega
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hmpos
  have hδ0 : 0 < δ := by rw [hδdef]; exact inv_pos.mpr htQ
  have hq0 : 0 < q := div_pos hδ0 hmQ
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, ← one_div, div_le_one htQ]
    exact_mod_cast htpos
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hmQ]
    calc δ ≤ 1 := hδ1
      _ ≤ (m : ℚ) := by exact_mod_cast hmpos
  have hr0 : (0 : ℚ) < r := by
    have h1 : 0 < 884736 * s * (Nat.log 2 k + 1) :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hs) (Nat.succ_pos _)
    have h2 : (0 : ℚ) < ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) := by
      exact_mod_cast h1
    linarith
  -- ── the spread requirement: q·r ≥ 48³ = 110592 ──
  have hq_eq : q = 1 / (4 * (s : ℚ) * ((Nat.log 2 k : ℚ) + 2)) := by
    rw [hqdef, hδdef, htdef, hmdef, hLdef]
    push_cast
    rw [inv_eq_one_div, div_div]
    congr 1
    ring
  have hden : (0 : ℚ) < 4 * (s : ℚ) * ((Nat.log 2 k : ℚ) + 2) :=
    mul_pos (mul_pos (by norm_num) hs0) (by positivity)
  have hqr : (110592 : ℚ) ≤ q * r := by
    have h2 : q * ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) ≤ q * r :=
      mul_le_mul_of_nonneg_left hr hq0.le
    have h3 : (110592 : ℚ)
        ≤ q * ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) := by
      rw [hq_eq]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hden]
      push_cast
      have hslg : 0 ≤ (s : ℚ) * (Nat.log 2 k : ℚ) :=
        mul_nonneg hs0.le hlg0
      nlinarith
    linarith
  have hcqR : 1 ≤ (1/48 : ℚ) ^ 3 * (q * r) := by
    have h48 : ((1:ℚ)/48) ^ 3 = 1 / 110592 := by norm_num
    rw [h48]
    calc (1 : ℚ) = (1 / 110592) * 110592 := by norm_num
      _ ≤ (1 / 110592) * (q * r) :=
          mul_le_mul_of_nonneg_left hqr (by norm_num)
  -- ── the family is nonempty; uniform weight facts ──
  have hGpos : (0 : ℚ) < (G.card : ℚ) := lt_trans (pow_pos hr0 k) hcard
  have hGne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hGpos)
  have hw : IsProbW (uniformW G) := uniformW_isProbW hGne
  have hspw : IsSpreadW r (uniformW G) :=
    uniformW_isSpreadW hGne hspread
  have hsupp : ∀ a, uniformW G a ≠ 0 → a.card ≤ k :=
    fun a ha => le_of_eq (hunif a (uniformW_support ha))
  have hkL : k ≤ 2 ^ L := by
    rw [hLdef]
    exact (Nat.lt_pow_succ_log_self (by norm_num) k).le
  -- ── Bernoulli: m rounds of q-noise stay below one δ-biased set ──
  have hδq : 1 - (1 - q) ^ m ≤ δ := by
    have hber := one_add_mul_le_pow (a := -q) (by linarith : (-2:ℚ) ≤ -q) m
    have hmq : (m : ℚ) * q = δ := by
      rw [hqdef]
      field_simp
    have h1 : (1 : ℚ) + (m : ℚ) * (-q) = 1 - (m : ℚ) * q := by ring
    have h2 : (1 : ℚ) + -q = 1 - q := by ring
    rw [h1, h2] at hber
    linarith
  -- ── the chain bound, transported to one δ-biased set ──
  have hfail : ∑ W : Finset (Fin n), biasedW δ W * failInd (uniformW G) W
      ≤ 24 * (1/48 : ℚ) :=
    fail_prob_le_biased (c := 1/48) hw hspw hq0 hq1 (by norm_num)
      (by norm_num) hr0 hcqR hkL hsupp hmdef hδ1 hδq
  have hfail2 : ∑ W : Finset (Fin n), biasedW δ W * failInd (uniformW G) W
      ≤ 1/2 := le_trans hfail (by norm_num)
  -- ── per-class failure ≤ 1/2, via the class marginal ──
  have hclass : ∀ i : Fin t,
      ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ *
        failInd (uniformW G) (univ.filter (fun x => χ x = i)) ≤ 1/2 := by
    intro i
    rw [class_marginal htpos i (failInd (uniformW G))]
    rw [hδdef] at hfail2
    exact hfail2
  -- ── linearity over the t classes ──
  have htotal : ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ *
      (∑ i : Fin t, failInd (uniformW G) (univ.filter (fun x => χ x = i)))
      ≤ (s : ℚ) := by
    calc ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ *
        (∑ i : Fin t, failInd (uniformW G) (univ.filter (fun x => χ x = i)))
        = ∑ χ : Fin n → Fin t, ∑ i : Fin t, ((t : ℚ) ^ n)⁻¹ *
            failInd (uniformW G) (univ.filter (fun x => χ x = i)) :=
          Finset.sum_congr rfl fun χ _ => Finset.mul_sum _ _ _
      _ = ∑ i : Fin t, ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ *
            failInd (uniformW G) (univ.filter (fun x => χ x = i)) :=
          Finset.sum_comm
      _ ≤ ∑ _i : Fin t, (1/2 : ℚ) :=
          Finset.sum_le_sum fun i _ => hclass i
      _ = (t : ℚ) * (1/2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = (s : ℚ) := by
          rw [htdef]
          push_cast
          ring
  -- ── pigeonhole: some coloring has at most s failed classes ──
  have hone : ∑ _χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (pow_pos htQ n).ne'
  haveI : Nonempty (Fin n → Fin t) := ⟨fun _ => ⟨0, htpos⟩⟩
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : Fin n → Fin t,
      (∑ i : Fin t, failInd (uniformW G)
        (univ.filter (fun x => χ₀ x = i))) ≤ (s : ℚ) := by
    by_contra hno
    push Not at hno
    have hT0 : (0 : ℚ) < ((t : ℚ) ^ n)⁻¹ := inv_pos.mpr (pow_pos htQ n)
    have hstrict : ∑ _χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ * (s : ℚ)
        < ∑ χ : Fin n → Fin t, ((t : ℚ) ^ n)⁻¹ *
            (∑ i : Fin t, failInd (uniformW G)
              (univ.filter (fun x => χ x = i))) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun χ _ => mul_lt_mul_of_pos_left (hno χ) hT0)
    rw [← Finset.sum_mul, hone, one_mul] at hstrict
    linarith
  -- ── the success classes: at least s of them ──
  set Sc : Finset (Fin t) := univ.filter (fun i : Fin t =>
    failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0) with hScdef
  have hfval : ∀ W : Finset (Fin n),
      failInd (uniformW G) W = 0 ∨ failInd (uniformW G) W = 1 := by
    intro W
    unfold failInd
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hsplit : (∑ i : Fin t, failInd (uniformW G)
      (univ.filter (fun x => χ₀ x = i)))
      = ((univ.filter (fun i : Fin t => ¬ failInd (uniformW G)
          (univ.filter (fun x => χ₀ x = i)) = 0)).card : ℚ) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin t =>
      failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0)]
    have h1 : ∑ i ∈ univ.filter (fun i : Fin t =>
        failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0),
        failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0 :=
      Finset.sum_eq_zero fun i hi => (Finset.mem_filter.mp hi).2
    have h2 : ∑ i ∈ univ.filter (fun i : Fin t =>
        ¬ failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0),
        failInd (uniformW G) (univ.filter (fun x => χ₀ x = i))
        = ∑ _i ∈ univ.filter (fun i : Fin t =>
            ¬ failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0),
            (1 : ℚ) :=
      Finset.sum_congr rfl fun i hi => by
        rcases hfval (univ.filter (fun x => χ₀ x = i)) with h | h
        · exact absurd h (Finset.mem_filter.mp hi).2
        · exact h
    rw [h1, h2, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbad : (univ.filter (fun i : Fin t => ¬ failInd (uniformW G)
      (univ.filter (fun x => χ₀ x = i)) = 0)).card ≤ s := by
    have h := hsplit ▸ hχ₀
    exact_mod_cast h
  have hcards : Sc.card + (univ.filter (fun i : Fin t => ¬ failInd (uniformW G)
      (univ.filter (fun x => χ₀ x = i)) = 0)).card = t := by
    rw [hScdef, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hScard : s ≤ Sc.card := by omega
  -- ── extraction: choose one support member inside each success class ──
  have hexT : ∀ i : Fin t, ∃ T : Finset (Fin n), i ∈ Sc →
      (T ∈ G ∧ T ⊆ univ.filter (fun x => χ₀ x = i)) := by
    intro i
    by_cases hi : i ∈ Sc
    · have h0 : failInd (uniformW G) (univ.filter (fun x => χ₀ x = i)) = 0 := by
        rw [hScdef] at hi
        exact (Finset.mem_filter.mp hi).2
      have hC : ∃ T ∈ (univ : Finset (Finset (Fin n))),
          uniformW G T ≠ 0 ∧ T ⊆ univ.filter (fun x => χ₀ x = i) := by
        by_contra hC
        unfold failInd at h0
        rw [if_neg hC] at h0
        norm_num at h0
      obtain ⟨T, -, hTne, hTsub⟩ := hC
      exact ⟨T, fun _ => ⟨uniformW_support hTne, hTsub⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Tf hTf using hexT
  obtain ⟨I, hIS, hIcard⟩ := Finset.exists_subset_card_eq hScard
  -- the chosen petals are pairwise distinct (classes are disjoint)
  have hinj : Set.InjOn Tf ↑I := by
    intro i hi j hj hij
    have hi' : i ∈ Sc := hIS (Finset.mem_coe.mp hi)
    have hj' : j ∈ Sc := hIS (Finset.mem_coe.mp hj)
    have hne : (Tf i).Nonempty := by
      rw [← Finset.card_pos, hunif _ (hTf i hi').1]
      omega
    obtain ⟨x, hx⟩ := hne
    have hxi : χ₀ x = i := (Finset.mem_filter.mp ((hTf i hi').2 hx)).2
    have hxj : χ₀ x = j :=
      (Finset.mem_filter.mp ((hTf j hj').2 (hij ▸ hx))).2
    exact hxi.symm.trans hxj
  -- ── assemble the s-sunflower with empty kernel ──
  refine ⟨I.image Tf, ?_, ?_, ∅, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hS
    exact (hTf i (hIS hiI)).1
  · rw [Finset.card_image_of_injOn hinj, hIcard]
  · intro S _
    exact Finset.empty_subset S
  · intro S hS
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.sdiff_empty]
    have hne : (Tf i).Nonempty := by
      rw [← Finset.card_pos, hunif _ (hTf i (hIS hiI)).1]
      omega
    exact Finset.nonempty_iff_ne_empty.mp hne
  · intro S hS T' hT' hne
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hT'
    have hij : i ≠ j := fun h => hne (by rw [h])
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
    have h1 : χ₀ x = i :=
      (Finset.mem_filter.mp ((hTf i (hIS hiI)).2 hxi)).2
    have h2 : χ₀ x = j :=
      (Finset.mem_filter.mp ((hTf j (hIS hjI)).2 hxj)).2
    exact hij (h1.symm.trans h2)

end Extraction

-- ════════════════════════════════════════════════════════════════════
-- §7 HEADLINES
-- ════════════════════════════════════════════════════════════════════

/-- **The spread lemma** in the task's goal shape (with the `+1` repair at
    `k = 1`; see header). Constant `C = 884736 = 8·48³`, not optimized. -/
theorem spread_lemma {r : ℚ} {s k : ℕ}
    (hr : ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) ≤ r)
    {F : Finset (Finset (Fin n))}
    (hunif : ∀ S ∈ F, S.card = k) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hspread : IsRSpread r F)
    (hcard : r ^ k < (F.card : ℚ)) :
    HasSunflower F s :=
  spread_lemma_core hs hk hr hunif hspread hcard

/-- **Unconditional sunflower bound (ALWZ/Rao/BCW form, machine-checked)**:
    every `k`-uniform family larger than `(C·s·(log₂ k + 1))^k` contains an
    `s`-sunflower, `C = 884736`. Wired through the committed link-local
    reduction `hasSunflower_of_forall_linkAt_isRSpread`: the spread lemma
    is discharged at every link level `k' = k - |Z| ≤ k` by monotonicity
    of `Nat.log`. -/
theorem sunflower_of_large_family {s k : ℕ} (hs : 1 ≤ s)
    {F : Finset (Finset (Fin n))} (hunif : ∀ S ∈ F, S.card = k)
    (hcard : ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) ^ k < (F.card : ℚ)) :
    HasSunflower F s := by
  have hrpos : 0 < 884736 * s * (Nat.log 2 k + 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hs) (Nat.succ_pos _)
  have hr0 : (0 : ℚ) < ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) := by
    exact_mod_cast hrpos
  refine hasSunflower_of_forall_linkAt_isRSpread hr0 ?_ hunif hcard
  intro Z hZk hsp hunif' hne hsize hthresh
  have hk' : 1 ≤ k - Z.card := by omega
  refine spread_lemma_core hs hk' ?_ hunif' hsp hthresh
  have hlog : Nat.log 2 (k - Z.card) ≤ Nat.log 2 k :=
    Nat.log_mono_right (Nat.sub_le k Z.card)
  have hmono : 884736 * s * (Nat.log 2 (k - Z.card) + 1)
      ≤ 884736 * s * (Nat.log 2 k + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)
  exact_mod_cast hmono

end SpreadLemma
