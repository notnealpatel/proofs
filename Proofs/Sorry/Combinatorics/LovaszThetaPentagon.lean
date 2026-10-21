/-
# Lovász: the Shannon capacity of the pentagon is `√5`

## Source

MathOverflow question 214927, "Important formulas in combinatorics" (asked by
Gil Kalai), answer https://mathoverflow.net/a/216114 by Gil Kalai,
2015-09-01.  Verbatim (re-pulled through the StackExchange API, 2026-10-21):

```
$$\Theta (C_5)=\sqrt 5.$$
This is the formula by Lovasz for the Shannon capacity of the cycle of length 5.
The Shannon capacity of a graph $\Theta (G)= \lim_{n \to \infty}(\omega(G^n))^{1/n}$,
where $\omega (G)$ is the largest size of an independent set of vertices in $G$,
and $G^n$ is the $n$-fold strong product of $G$. A key to Lovasz' proof was the
introduction of a new spectral parameter $\theta (G)$, and a proof that
$\Theta (G) \le \theta (G)$.
```

No arXiv paper is involved; the result is L. Lovász, "On the Shannon capacity
of a graph", IEEE Trans. Inform. Theory 25 (1979) 1-7.  The same statement is
a public Lean evaluation problem (Kim Morrison,
https://lean-lang.org/eval/problems/shannon_capacity_pentagon/).

Date of this card: 2026-10-21.

## Status

Proved in the literature (Lovász 1979); stated, not proved, in the thread.
This module proves it completely (no `sorry`):

* `lovasz_pentagon`: every independent set `S` of the strong power `C₅^⊠n`
  satisfies `|S|² ≤ 5ⁿ`;
* `exists_indep_card` / `shannon_pentagon_lower`: an explicit independent set
  of size `5^⌊n/2⌋`, generated coordinatewise by `{(i, 2i)}`;
* `indepNum_two_mul`: `α(C₅^⊠2k) = 5^k`;
* `shannon_capacity_pentagon`: `α(C₅^⊠n)^{1/n} → √5`.

## Proof method

Lovász's umbrella, unnormalised: `u_j = (r cos(2πj/5), r sin(2πj/5), 1) ∈ ℝ³`
with `r² = √5 - 1`, so `⟨u_i, u_j⟩ = 0` for non-adjacent `i ≠ j` and
`‖u_j‖² = √5`.  For a word `s` the tensor vector `V_s(j) = ∏ᵢ u_{sᵢ}(jᵢ)`
satisfies `⟨V_s, V_t⟩ = ∏ᵢ ⟨u_{sᵢ}, u_{tᵢ}⟩`.  With `w = ∑_{s∈S} V_s`, the
coordinate `w(2,…,2) = |S|` and `‖w‖² = |S| · √5ⁿ`, so `|S|² ≤ |S| · √5ⁿ`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.LovaszThetaPentagon

open Real

/-- The `n`-fold strong power `G^⊠n` of a simple graph `G`, on words `Fin n → V`:
two distinct words are adjacent iff in every coordinate they are equal or adjacent
in `G`.  (Mathlib has no strong product; this is the standard definition.) -/
def strongPow {V : Type*} (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) where
  Adj s t := s ≠ t ∧ ∀ i, s i = t i ∨ G.Adj (s i) (t i)
  symm := ⟨fun _ _ h =>
    ⟨h.1.symm, fun i => (h.2 i).elim (fun e => Or.inl e.symm) (fun a => Or.inr a.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The real number `√5`. -/
noncomputable def s5 : ℝ := √5
/-- The umbrella radius `r = √(√5 - 1)`. -/
noncomputable def rr : ℝ := √(s5 - 1)
/-- `cos (2π/5) = (√5 - 1)/4`. -/
noncomputable def c1 : ℝ := (s5 - 1) / 4
/-- `cos (4π/5) = -(√5 + 1)/4`. -/
noncomputable def c2 : ℝ := -(s5 + 1) / 4
/-- `sin (2π/5) = √(1 - cos² (2π/5))`. -/
noncomputable def sn1 : ℝ := √(1 - c1 ^ 2)
/-- `sin (4π/5) = √(1 - cos² (4π/5))`. -/
noncomputable def sn2 : ℝ := √(1 - c2 ^ 2)

/-- Ground truth: `c2` is `cos (4π/5)`. -/
example : c2 = Real.cos (4 * π / 5) := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub, Real.cos_pi_div_five]
  unfold c2 s5; ring

/-- `(√5)² = 5`. -/
lemma s5_sq : s5 ^ 2 = 5 := by
  unfold s5; rw [sq_sqrt (by norm_num)]

/-- `1 ≤ √5`. -/
lemma one_le_s5 : 1 ≤ s5 := by
  unfold s5; rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by norm_num)

/-- `√5 ≤ 3`. -/
lemma s5_le_three : s5 ≤ 3 := by
  unfold s5; rw [show (3:ℝ) = √9 by rw [show (9:ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  exact sqrt_le_sqrt (by norm_num)

/-- `r² = √5 - 1`. -/
lemma rr_sq : rr ^ 2 = s5 - 1 := by
  unfold rr; rw [sq_sqrt (by linarith [one_le_s5])]

/-- `sin² (2π/5) = 1 - cos² (2π/5)`. -/
lemma sn1_sq : sn1 ^ 2 = 1 - c1 ^ 2 := by
  unfold sn1; rw [sq_sqrt]; unfold c1; nlinarith [one_le_s5, s5_le_three]

/-- `sin² (4π/5) = 1 - cos² (4π/5)`. -/
lemma sn2_sq : sn2 ^ 2 = 1 - c2 ^ 2 := by
  unfold sn2; rw [sq_sqrt]; unfold c2; nlinarith [one_le_s5, s5_le_three]

/-- `sin (2π/5) · sin (4π/5) = √5/4`. -/
lemma sn1_mul_sn2 : sn1 * sn2 = s5 / 4 := by
  unfold sn1 sn2
  rw [← sqrt_mul (by unfold c1; nlinarith [one_le_s5, s5_le_three])]
  have h : (1 - c1 ^ 2) * (1 - c2 ^ 2) = (s5 / 4) ^ 2 := by
    unfold c1 c2; linear_combination ((s5 ^ 2 - 45) / 256) * s5_sq
  rw [h, sqrt_sq (by linarith [one_le_s5])]

/-- The (unnormalised) Lovász umbrella: `u_j = (r cos(2πj/5), r sin(2πj/5), 1)`
for `j : Fin 5`, with `r² = √5 - 1`. -/
noncomputable def umbrella : Fin 5 → Fin 3 → ℝ :=
  ![![rr, 0, 1], ![rr * c1, rr * sn1, 1], ![rr * c2, rr * sn2, 1],
    ![rr * c2, -(rr * sn2), 1], ![rr * c1, -(rr * sn1), 1]]

/-- The handle coordinate of every rib is `1`. -/
lemma umbrella_two (a : Fin 5) : umbrella a 2 = 1 := by
  fin_cases a <;> rfl

/-- Every rib has squared length `√5`. -/
lemma umbrella_norm (a : Fin 5) : ∑ k, umbrella a k * umbrella a k = s5 := by
  have h1 := rr_sq; have h2 := sn1_sq; have h3 := sn2_sq
  fin_cases a <;>
    simp only [umbrella, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.sum_univ_three, mul_zero, add_zero, mul_neg, neg_mul, neg_neg,
      mul_one] <;>
    first
    | linear_combination h1
    | linear_combination h1 + rr ^ 2 * h2
    | linear_combination h1 + rr ^ 2 * h3

/-- Ribs of distinct non-adjacent vertices of `C₅` are orthogonal. -/
lemma umbrella_orth (a b : Fin 5) (h : ¬(a = b ∨ (SimpleGraph.cycleGraph 5).Adj a b)) :
    ∑ k, umbrella a k * umbrella b k = 0 := by
  have h1 := rr_sq; have h2 := sn1_sq; have h3 := sn2_sq; have h4 := sn1_mul_sn2
  have h5 := s5_sq
  fin_cases a <;> fin_cases b <;> simp only [SimpleGraph.cycleGraph_adj] at h <;>
    (try exact absurd (by decide) h) <;>
    simp only [umbrella, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.sum_univ_three, mul_zero, zero_mul, add_zero, neg_zero, mul_neg,
      neg_mul, mul_one] <;>
    unfold c1 c2 at * <;>
    first
    | linear_combination (-(s5 + 1) / 4) * h1 - (1 / 4) * h5
    | linear_combination -rr ^ 2 * h4 + ((s5 - 1) / 4 * (-(s5 + 1) / 4) - s5 / 4) * h1
        - (s5 + 3) / 16 * h5
    | linear_combination -rr ^ 2 * h2 + (2 * ((s5 - 1) / 4) ^ 2 - 1) * h1
        + (s5 - 3) / 8 * h5

/-- The tensor product `V_s = u_{s₀} ⊗ ⋯ ⊗ u_{s_{n-1}}`, as a function on `Fin n → Fin 3`. -/
noncomputable def tensorVec {n : ℕ} (s : Fin n → Fin 5) : (Fin n → Fin 3) → ℝ :=
  fun j => ∏ i, umbrella (s i) (j i)

/-- Inner products of tensor vectors factor coordinatewise. -/
lemma tensorVec_inner {n : ℕ} (s t : Fin n → Fin 5) :
    ∑ j, tensorVec s j * tensorVec t j = ∏ i, ∑ k, umbrella (s i) k * umbrella (t i) k := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [tensorVec, Finset.prod_mul_distrib]

/-- The coordinate `(2, …, 2)` of every tensor vector is `1`. -/
lemma tensorVec_two {n : ℕ} (s : Fin n → Fin 5) : tensorVec s (fun _ => 2) = 1 := by
  simp [tensorVec, umbrella_two]

/-- Adjacency in `C₅^⊠n`, unfolded: distinct words whose coordinates pairwise
differ by `0` or `±1` modulo `5`. -/
theorem strongPow_cycleGraph_adj_iff (n : ℕ) (s t : Fin n → Fin 5) :
    (strongPow (SimpleGraph.cycleGraph 5) n).Adj s t ↔
      s ≠ t ∧ ∀ i, s i = t i ∨ s i - t i = 1 ∨ t i - s i = 1 :=
  Iff.rfl

/-- Ground truth: `(0,0) ~ (1,4)` in `C₅^⊠2`. -/
example : (strongPow (SimpleGraph.cycleGraph 5) 2).Adj ![0, 0] ![1, 4] := by
  rw [strongPow_cycleGraph_adj_iff]
  decide

/-- Ground truth: `(0,0)` and `(2,0)` are not adjacent in `C₅^⊠2`. -/
example : ¬(strongPow (SimpleGraph.cycleGraph 5) 2).Adj ![0, 0] ![2, 0] := by
  rw [strongPow_cycleGraph_adj_iff]
  decide

/-- **Lovász (1979), pentagon case.**  Every independent set `S` of the strong power
`C₅^⊠n` satisfies `|S|² ≤ 5ⁿ`, i.e. `α(C₅^⊠n) ≤ 5^{n/2}`.
(MathOverflow 214927, answer 216114: `Θ(C₅) = √5`.) -/
theorem lovasz_pentagon (n : ℕ) (S : Finset (Fin n → Fin 5))
    (hS : (strongPow (SimpleGraph.cycleGraph 5) n).IsIndepSet (S : Set (Fin n → Fin 5))) :
    S.card ^ 2 ≤ 5 ^ n := by
  classical
  have hpair : ∀ s ∈ S, ∀ t ∈ S,
      ∑ j, tensorVec s j * tensorVec t j = if s = t then s5 ^ n else 0 := by
    intro s hs t ht
    rw [tensorVec_inner]
    split_ifs with hst
    · subst hst; simp [umbrella_norm]
    · have hna := hS hs ht hst
      simp only [strongPow, not_and, not_forall] at hna
      obtain ⟨i, hi⟩ := hna hst
      exact Finset.prod_eq_zero (Finset.mem_univ i) (umbrella_orth _ _ hi)
  let w : (Fin n → Fin 3) → ℝ := fun j => ∑ s ∈ S, tensorVec s j
  have hsum : ∑ j, w j ^ 2 = S.card * s5 ^ n := by
    calc ∑ j, w j ^ 2 = ∑ j, ∑ s ∈ S, ∑ t ∈ S, tensorVec s j * tensorVec t j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ s ∈ S, ∑ t ∈ S, ∑ j, tensorVec s j * tensorVec t j := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s ∈ S, ∑ t ∈ S, (if s = t then s5 ^ n else 0) :=
          Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => hpair s hs t ht
      _ = S.card * s5 ^ n := by simp
  have hw0 : w (fun _ => 2) = S.card := by simp [w, tensorVec_two]
  have hle : w (fun _ => 2) ^ 2 ≤ ∑ j, w j ^ 2 :=
    Finset.single_le_sum (f := fun j => w j ^ 2) (fun j _ => sq_nonneg (w j)) (Finset.mem_univ _)
  rw [hw0, hsum] at hle
  have hs5 : 0 ≤ s5 := by linarith [one_le_s5]
  have hcard : (S.card : ℝ) ≤ s5 ^ n := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero]; positivity
    · have hpos' : (0 : ℝ) < S.card := by exact_mod_cast hpos
      nlinarith
  have hreal : ((S.card ^ 2 : ℕ) : ℝ) ≤ ((5 ^ n : ℕ) : ℝ) := by
    push_cast
    calc (S.card : ℝ) ^ 2 ≤ (s5 ^ n) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = 5 ^ n := by rw [← pow_mul, mul_comm, pow_mul, s5_sq]
  exact_mod_cast hreal

/-- If `x ≠ y` in `ℤ/5`, then `x, y` or `2x, 2y` are distinct and non-adjacent in `C₅`. -/
lemma fin5_sep (x y : Fin 5) (h : x ≠ y) :
    ¬(x = y ∨ (SimpleGraph.cycleGraph 5).Adj x y) ∨
      ¬(2 * x = 2 * y ∨ (SimpleGraph.cycleGraph 5).Adj (2 * x) (2 * y)) := by
  simp only [SimpleGraph.cycleGraph_adj]
  revert x y; decide

/-- The lower-bound code: a word `a` of length `⌊n/2⌋` is sent to
`(a₀, 2a₀, a₁, 2a₁, …)`, padded with a final `0` when `n` is odd. -/
def pairEmbed (n : ℕ) (a : Fin (n / 2) → Fin 5) : Fin n → Fin 5 := fun i =>
  if h : i.val / 2 < n / 2 then
    (if i.val % 2 = 0 then a ⟨i.val / 2, h⟩ else 2 * a ⟨i.val / 2, h⟩)
  else 0

/-- Coordinate `2p` of `pairEmbed n a` is `a p`. -/
lemma pairEmbed_even (n : ℕ) (a : Fin (n / 2) → Fin 5) (p : Fin (n / 2)) :
    pairEmbed n a ⟨2 * p.val, by omega⟩ = a p := by
  have h1 : (2 * p.val) / 2 = p.val := by omega
  have h2 : (2 * p.val) % 2 = 0 := by omega
  simp [pairEmbed, h1, h2]

/-- Coordinate `2p + 1` of `pairEmbed n a` is `2 a p`. -/
lemma pairEmbed_odd (n : ℕ) (a : Fin (n / 2) → Fin 5) (p : Fin (n / 2)) :
    pairEmbed n a ⟨2 * p.val + 1, by omega⟩ = 2 * a p := by
  have h1 : (2 * p.val + 1) / 2 = p.val := by omega
  have h2 : (2 * p.val + 1) % 2 = 1 := by omega
  simp [pairEmbed, h1, h2]

/-- Ground truth: `pairEmbed 2 (3) = (3, 6 mod 5) = (3, 1)`. -/
example : pairEmbed 2 ![3] = ![3, 1] := by decide

/-- `pairEmbed n` is injective. -/
lemma pairEmbed_injective (n : ℕ) : Function.Injective (pairEmbed n) := by
  intro a b hab
  funext p
  have := congrFun hab ⟨2 * p.val, by omega⟩
  rwa [pairEmbed_even, pairEmbed_even] at this

/-- `C₅^⊠n` has an independent set of size `5^⌊n/2⌋` (the image of `pairEmbed n`). -/
theorem exists_indep_card (n : ℕ) :
    ∃ S : Finset (Fin n → Fin 5),
      (strongPow (SimpleGraph.cycleGraph 5) n).IsIndepSet (S : Set (Fin n → Fin 5)) ∧
      S.card = 5 ^ (n / 2) := by
  classical
  refine ⟨Finset.univ.image (pairEmbed n), ?_, ?_⟩
  · intro s hs t ht hst hadj
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hs ht
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    have hab : a ≠ b := fun e => hst (e ▸ rfl)
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hab
    rcases fin5_sep (a p) (b p) hp with h | h
    · have := hadj.2 ⟨2 * p.val, by omega⟩
      rw [pairEmbed_even, pairEmbed_even] at this
      exact h this
    · have := hadj.2 ⟨2 * p.val + 1, by omega⟩
      rw [pairEmbed_odd, pairEmbed_odd] at this
      exact h this
  · rw [Finset.card_image_of_injective _ (pairEmbed_injective n)]
    simp

/-- The spec's lower bound: `C₅^⊠2k` has an independent set of size `5^k`. -/
theorem shannon_pentagon_lower (k : ℕ) :
    ∃ S : Finset (Fin (2 * k) → Fin 5),
      (strongPow (SimpleGraph.cycleGraph 5) (2 * k)).IsIndepSet (S : Set (Fin (2 * k) → Fin 5)) ∧
      S.card = 5 ^ k := by
  obtain ⟨S, hS, hcard⟩ := exists_indep_card (2 * k)
  exact ⟨S, hS, by rw [hcard, Nat.mul_div_cancel_left k (by norm_num)]⟩

/-- Non-vacuity: the hypotheses of `lovasz_pentagon` hold at `n = 2` for a set of size
`5`, where the bound `|S|² ≤ 5²` is attained. -/
example : ∃ S : Finset (Fin 2 → Fin 5),
    (strongPow (SimpleGraph.cycleGraph 5) 2).IsIndepSet (S : Set (Fin 2 → Fin 5)) ∧
      S.card ^ 2 = 5 ^ 2 := by
  obtain ⟨S, hS, hcard⟩ := shannon_pentagon_lower 1
  exact ⟨S, hS, by rw [hcard]; norm_num⟩

/-- `α(C₅^⊠n)² ≤ 5ⁿ`, for Mathlib's `SimpleGraph.indepNum`. -/
theorem indepNum_sq_le (n : ℕ) :
    (strongPow (SimpleGraph.cycleGraph 5) n).indepNum ^ 2 ≤ 5 ^ n := by
  obtain ⟨S, hS⟩ := (strongPow (SimpleGraph.cycleGraph 5) n).exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  exact lovasz_pentagon n S hS.isIndepSet

/-- `5^⌊n/2⌋ ≤ α(C₅^⊠n)`. -/
theorem pow_half_le_indepNum (n : ℕ) :
    5 ^ (n / 2) ≤ (strongPow (SimpleGraph.cycleGraph 5) n).indepNum := by
  obtain ⟨S, hS, hcard⟩ := exists_indep_card n
  rw [← hcard]
  exact hS.card_le_indepNum

/-- `α(C₅^⊠2k) = 5^k` exactly. -/
theorem indepNum_two_mul (k : ℕ) :
    (strongPow (SimpleGraph.cycleGraph 5) (2 * k)).indepNum = 5 ^ k := by
  apply le_antisymm
  · have h := indepNum_sq_le (2 * k)
    rw [pow_mul'] at h
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h
  · have h := pow_half_le_indepNum (2 * k)
    rwa [Nat.mul_div_cancel_left k (by norm_num)] at h

/-- `α(C₅^⊠n) ≤ √5ⁿ` as real numbers. -/
theorem indepNum_le_sqrt_pow (n : ℕ) :
    ((strongPow (SimpleGraph.cycleGraph 5) n).indepNum : ℝ) ≤ √5 ^ n := by
  have h : (((strongPow (SimpleGraph.cycleGraph 5) n).indepNum ^ 2 : ℕ) : ℝ) ≤ ((5 ^ n : ℕ) : ℝ) :=
    by exact_mod_cast indepNum_sq_le n
  push_cast at h
  have h5 : (5 : ℝ) ^ n = (√5 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, sq_sqrt (by norm_num)]
  rw [h5] at h
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).mp h

/-- **Lovász (1979): `Θ(C₅) = √5`.**  The Shannon capacity of the pentagon,
`lim_{n→∞} α(C₅^⊠n)^{1/n}`, exists and equals `√5`.
(MathOverflow 214927, answer 216114 by Gil Kalai.) -/
theorem shannon_capacity_pentagon :
    Filter.Tendsto
      (fun n : ℕ => ((strongPow (SimpleGraph.cycleGraph 5) n).indepNum : ℝ) ^ ((n : ℝ)⁻¹))
      Filter.atTop (nhds √5) := by
  set α : ℕ → ℝ := fun n => ((strongPow (SimpleGraph.cycleGraph 5) n).indepNum : ℝ)
  have hupper : ∀ n : ℕ, 1 ≤ n → α n ^ ((n : ℝ)⁻¹) ≤ √5 := by
    intro n hn
    calc α n ^ ((n : ℝ)⁻¹) ≤ (√5 ^ n) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (indepNum_le_sqrt_pow n) (by positivity)
      _ = √5 := Real.pow_rpow_inv_natCast (by positivity) (by omega)
  have hlower : ∀ n : ℕ, 1 ≤ n →
      (5 : ℝ) ^ ((1 / 2 : ℝ) - (1 / 2) * (n : ℝ)⁻¹) ≤ α n ^ ((n : ℝ)⁻¹) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have : n - 1 ≤ 2 * (n / 2) := by omega
      have h2 : ((n - 1 : ℕ) : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast [Nat.cast_sub hn] at h2
      linarith
    have hα : (5 : ℝ) ^ (((n : ℝ) - 1) / 2) ≤ α n := by
      calc (5 : ℝ) ^ (((n : ℝ) - 1) / 2) ≤ (5 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = ((5 ^ (n / 2) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
        _ ≤ α n := by simp only [α]; exact_mod_cast pow_half_le_indepNum n
    calc (5 : ℝ) ^ ((1 / 2 : ℝ) - (1 / 2) * (n : ℝ)⁻¹)
        = ((5 : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ ((n : ℝ)⁻¹) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          field_simp
      _ ≤ α n ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hα (by positivity)
  have hlim : Filter.Tendsto (fun n : ℕ => (5 : ℝ) ^ ((1 / 2 : ℝ) - (1 / 2) * (n : ℝ)⁻¹))
      Filter.atTop (nhds √5) := by
    have he : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2) * (n : ℝ)⁻¹)
        Filter.atTop (nhds (1 / 2)) := by
      have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
    rw [Real.sqrt_eq_rpow]
    exact ((Real.continuous_const_rpow (by norm_num : (5 : ℝ) ≠ 0)).tendsto _).comp he
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hlower n hn
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hupper n hn

end Candidates.LovaszThetaPentagon
