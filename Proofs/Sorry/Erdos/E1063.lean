/-
  Erdős Problem #1063 — near-uniform divisibility of C(n,k) by n − i.
  Status: open.  Tier UA attack target.

  Verbatim statement (`goof erdos fetch 1063`, pulled 2026-08-05):

    "Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$
    such that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$.
    Estimate $n_k$."

  DB remarks (Erdős–Selfridge, AMM Problem 6447; proof in Monier
  [Mo85]): for n ≥ 2k at least one 0 ≤ i < k has (n−i) ∤ C(n,k), so
  "all but one" is optimal.  Known values n₂ = 4, n₃ = 6, n₄ = 9,
  n₅ = 12 (OEIS A389360: 4, 6, 9, 12, 75, 30, 70, 56, 2403, 280, …).
  Monier: n_k ≤ k! for k ≥ 3 (C(k!, k) is divisible by k! − i for
  1 ≤ i < k).  Cambie (comments): n_k ≤ k·lcm(2,…,k−1) ≤ e^{(1+o(1))k}.
  rickyc + GPT (comments, Jun–Jul 2026, comment-sourced, unrefereed):
  n_k ≥ max(2k, ∏_{p^a ∥ k} p^{a + ⌊log_p (k−1)⌋}).

  Mathlib inventory (leandoc 2026-08-05): `Nat.choose`, `Finset.lcm`,
  `Nat.factorization` / `padicValNat` for the valuation argument;
  repo adjacency: `Proofs/Erdos/Erdos440/LcmCount.lean` (lcm layer).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1063

/-- `divisorDefect n k`: the number of indices `0 ≤ i < k` such that
    `n − i` does NOT divide `C(n,k)`.  (For `n ≥ 2k` the subtraction
    `n − i` never truncates since `i < k ≤ n`.) -/
def divisorDefect (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => ¬ (n - i) ∣ n.choose k)).card

/-- Ground truth: `C(4,2) = 6` is divisible by `4` — no wait, `4 ∤ 6`;
    but `3 ∣ 6`.  Defect of `(4,2)` is exactly 1 (index i = 0 fails).
    -- PROVABLE (decide). -/
example : divisorDefect 4 2 = 1 := by decide

/-- Ground truth: `(6,2)`: `C(6,2) = 15`; `6 ∤ 15`, `5 ∣ 15` — defect 1.
    But n₂ = 4 is the least.  `(5,2)`: `C(5,2) = 10`; `5 ∣ 10`,
    `4 ∤ 10` — defect 1 as well?  A389360 says n₂ = 4, and indeed 4 is
    the least n ≥ 2k = 4.  -- PROVABLE (decide). -/
example : divisorDefect 5 2 = 1 ∧ divisorDefect 4 2 = 1 := by decide

/-- `nk k`: the least `n ≥ 2k` with divisor defect at most one — the
    quantity `n_k` of the problem.  By `erdos_selfridge_defect_pos`
    below the defect is never 0 in range, so "at most one" = "exactly
    one" = "n − i divides C(n,k) for all but one i".  `sInf` is
    justified nonempty by Monier's `k!` witness (`nk_le_factorial`). -/
noncomputable def nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k ≤ 1}

/-- A window of `k` consecutive integers `n - k + 1, …, n` contains a multiple of
    `q` whenever `q ≤ k` or `q` is at most the carry sum `k % q + (n - k) % q`. -/
private theorem exists_dvd_sub_of_carry (n k q : ℕ) (hq : 0 < q) (hkn : k ≤ n)
    (hcarry : q ≤ k ∨ q ≤ k % q + (n - k) % q) :
    ∃ i, i < k ∧ q ∣ n - i := by
  have hkmod : k % q ≤ k := Nat.mod_le k q
  have hr : (n - k) % q < q := Nat.mod_lt _ hq
  have hdiv : q * ((n - k) / q) + (n - k) % q = n - k := Nat.div_add_mod (n - k) q
  have hle : q ≤ k + (n - k) % q := by omega
  refine ⟨k + (n - k) % q - q, by omega, ?_⟩
  have heq : n - (k + (n - k) % q - q) = q * ((n - k) / q + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [heq]
  exact Dvd.intro _ rfl

/-- Kummer bound at a prime divisor `p ∣ k`: there is a level `T ≥ 1` with
    `p ^ T ≤ k` or a carry at level `T`, and `v_p(C(n,k)) < T`. -/
private theorem exists_level_of_prime_dvd (n k p : ℕ) [hp : Fact p.Prime] (hpk : p ∣ k)
    (hk : k ≠ 0) (hkn : k ≤ n) :
    ∃ T, (p ^ T ≤ k ∨ p ^ T ≤ k % p ^ T + (n - k) % p ^ T) ∧
      padicValNat p (n.choose k) < T := by
  set S := (Finset.Ico 1 (Nat.log p n + 1)).filter
    (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) with hS
  have hval : padicValNat p (n.choose k) = S.card :=
    padicValNat_choose hkn (Nat.lt_succ_self _)
  set T := S.sup id ⊔ 1 with hT
  have hsub : S ⊆ Finset.Ico 2 (T + 1) := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    have ht1 : 1 ≤ t := (Finset.mem_Ico.mp ht'.1).1
    have htT : t ≤ T := le_sup_of_le_left (Finset.le_sup (f := id) ht)
    have ht2 : t ≠ 1 := by
      rintro rfl
      have hkp : k % p = 0 := Nat.mod_eq_zero_of_dvd hpk
      have := ht'.2
      simp only [pow_one, hkp, zero_add] at this
      exact absurd (Nat.mod_lt (n - k) hp.out.pos) (not_lt.mpr this)
    rw [Finset.mem_Ico]; omega
  have hcard : S.card < T := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    have h1 : 1 ≤ T := le_sup_right
    omega
  refine ⟨T, ?_, hval ▸ hcard⟩
  rcases Nat.eq_zero_or_pos (S.sup id) with h0 | hpos
  · left
    have hT1 : T = 1 := by rw [hT, h0]; rfl
    rw [hT1, pow_one]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hpk
  · right
    obtain ⟨t, htS, htsup⟩ := Finset.exists_mem_eq_sup S
      (Finset.nonempty_of_ne_empty (by rintro hE; rw [hE] at hpos; simp at hpos)) id
    have hT' : T = t := by
      rw [hT, htsup]
      have : 1 ≤ t := (Finset.mem_Ico.mp (Finset.mem_filter.mp htS).1).1
      simpa using this
    rw [hT']
    exact (Finset.mem_filter.mp htS).2

/-- **Erdős–Selfridge non-divisibility lemma** (ErSe83; proof Monier
    Mo85): for `n ≥ 2k`, `k ≥ 2`, at least one `0 ≤ i < k` has
    `(n − i) ∤ C(n,k)` — i.e. the defect is positive, so "all but one"
    in the problem is optimal.

    Proof sketch (attack plan, from the rickyc comment thread's
    valuation identity): fix a prime power `p^a ∥ k`.  With
    `M = max_{i<k} v_p(n−i)` and `S = v_p(C(n,k))`, the factorization
    `S = Σ v_p(n−i) − v_p(k!)` cancels levels `p, …, p^a` exactly
    between the `k` consecutive integers and `k!`, giving `S ≤ M − a`;
    hence any `i` attaining `v_p(n−i) = M` has `(n−i) ∤ C(n,k)`.
    Self-contained: `padicValNat`, `Nat.factorization_choose`
    (Legendre/Kummer in Mathlib).  The natural first sorry-free target
    of this file.  -/
theorem erdos_selfridge_defect_pos (n k : ℕ) (hk : 2 ≤ k)
    (hn : 2 * k ≤ n) :
    1 ≤ divisorDefect n k := by
  have hkn : k ≤ n := by omega
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hcarry, hlt⟩ := exists_level_of_prime_dvd n k p hpk (by omega) hkn
  obtain ⟨i, hik, hdvd⟩ := exists_dvd_sub_of_carry n k (p ^ T) (pow_pos hp.pos T) hkn hcarry
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hnot : ¬ (n - i) ∣ n.choose k := by
    intro hdiv
    have hpT : p ^ T ∣ n.choose k := hdvd.trans hdiv
    rw [padicValNat_dvd_iff_le hC] at hpT
    omega
  unfold divisorDefect
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hik, hnot⟩⟩

/-- A candidate is the least admissible natural if every smaller natural is inadmissible. -/
private theorem nk_eq_of_least (k w : ℕ)
    (hw : 2 * k ≤ w ∧ divisorDefect w k ≤ 1)
    (hsmall : ∀ n : ℕ, n < w → ¬ (2 * k ≤ n ∧ divisorDefect n k ≤ 1)) :
    nk k = w := by
  unfold nk
  apply Nat.le_antisymm
  · exact Nat.sInf_le hw
  · apply Nat.le_of_not_lt
    intro hlt
    exact hsmall _ hlt
      (Nat.sInf_mem (s := {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k ≤ 1}) ⟨w, hw⟩)

/-- Small values against OEIS A389360 (pulled 2026-08-05:
    4, 6, 9, 12, 75, 30, 70, 56, …): `n₂ = 4`, `n₃ = 6`, `n₄ = 9`,
    `n₅ = 12`.  -- PROVABLE (decide after an sInf-characterization
    lemma; each requires checking finitely many n). -/
theorem nk_two : nk 2 = 4 := by
  apply nk_eq_of_least
  · decide
  · have hsmall : ∀ n : Fin 4, ¬ (2 * 2 ≤ n.val ∧ divisorDefect n.val 2 ≤ 1) :=
      by decide
    intro n hn
    exact hsmall ⟨n, hn⟩

/-- The least admissible value for `k = 3` is `6`. -/
theorem nk_three : nk 3 = 6 := by
  apply nk_eq_of_least
  · decide
  · have hsmall : ∀ n : Fin 6, ¬ (2 * 3 ≤ n.val ∧ divisorDefect n.val 3 ≤ 1) :=
      by decide
    intro n hn
    exact hsmall ⟨n, hn⟩

/-- The least admissible value for `k = 4` is `9`. -/
theorem nk_four : nk 4 = 9 := by
  apply nk_eq_of_least
  · decide
  · have hsmall : ∀ n : Fin 9, ¬ (2 * 4 ≤ n.val ∧ divisorDefect n.val 4 ≤ 1) :=
      by decide
    intro n hn
    exact hsmall ⟨n, hn⟩

/-- The least admissible value for `k = 5` is `12`. -/
theorem nk_five : nk 5 = 12 := by
  apply nk_eq_of_least
  · decide
  · have hsmall : ∀ n : Fin 12, ¬ (2 * 5 ≤ n.val ∧ divisorDefect n.val 5 ≤ 1) :=
      by decide
    intro n hn
    exact hsmall ⟨n, hn⟩

/-- Monier's identity: `C(k!, k) = ∏_{1 ≤ i < k} (k! − i)`, written with `k = k' + 1`. -/
private theorem choose_factorial_eq_prod (k' : ℕ) :
    (k' + 1).factorial.choose (k' + 1) =
      ∏ i ∈ Finset.range k', ((k' + 1).factorial - (i + 1)) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k' + 1).factorial (k' + 1)
  rw [Nat.descFactorial_eq_prod_range, Finset.prod_range_succ', Nat.sub_zero, mul_comm] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) h).symm

/-- The divisor defect of `(k!, k)` is at most one: every `k! − i` with `1 ≤ i < k`
    divides `C(k!, k)`. -/
private theorem divisorDefect_factorial_le_one (k : ℕ) :
    divisorDefect k.factorial k ≤ 1 := by
  rcases k with _ | k'
  · simp [divisorDefect]
  · unfold divisorDefect
    have hsub : (Finset.range (k' + 1)).filter
        (fun i => ¬ ((k' + 1).factorial - i) ∣ (k' + 1).factorial.choose (k' + 1)) ⊆ {0} := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_singleton]
      by_contra hi0
      apply hi.2
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [choose_factorial_eq_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
    simpa using Finset.card_le_card hsub

/-- If every `1 ≤ j ≤ k'` divides `n`, then
    `(k'+1)! · C(n, k'+1) = n · (k'! · ∏_{i < k'} (n/(i+1) − 1))`. -/
private theorem factorial_mul_choose_of_dvd (n k' : ℕ)
    (hdiv : ∀ j, 1 ≤ j → j ≤ k' → j ∣ n) :
    (k' + 1).factorial * n.choose (k' + 1) =
      n * (k'.factorial * ∏ i ∈ Finset.range k', (n / (i + 1) - 1)) := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    Finset.prod_range_succ', Nat.sub_zero, mul_comm, ← Finset.prod_range_add_one_eq_factorial,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  obtain ⟨m, hm⟩ := hdiv (i + 1) (by omega) (by omega)
  have hm' : n / (i + 1) = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
  rw [hm', hm, Nat.mul_sub_one]

/-- With `L = lcm(2, …, k−1)` and `n = k·L`, every `n − i` with `1 ≤ i < k` divides
    `C(n, k)`; hence the divisor defect is at most one. -/
private theorem divisorDefect_mul_lcm_le_one (k : ℕ) (hk : 3 ≤ k) :
    divisorDefect (k * (Finset.Icc 2 (k - 1)).lcm id) k ≤ 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set L := (Finset.Icc 2 (k' + 1 - 1)).lcm id with hL
  have hjL : ∀ j, 1 ≤ j → j ≤ k' → j ∣ L := by
    intro j hj1 hjk
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
    · exact one_dvd _
    · exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hj2, by omega⟩)
  have hL0 : L ≠ 0 := by
    rw [hL, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id] at hx0
    omega
  set n := (k' + 1) * L with hn
  have hdiv : ∀ j, 1 ≤ j → j ≤ k' → j ∣ n := fun j h1 h2 =>
    (hjL j h1 h2).trans (Dvd.intro_left _ rfl)
  set Q := ∏ i ∈ Finset.range k', (n / (i + 1) - 1) with hQ
  have hC : n.choose (k' + 1) = L * Q := by
    have h := factorial_mul_choose_of_dvd n k' hdiv
    rw [Nat.factorial_succ] at h
    have h' : ((k' + 1) * k'.factorial) * n.choose (k' + 1) =
        ((k' + 1) * k'.factorial) * (L * Q) := by
      rw [h, hn]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)) h'
  unfold divisorDefect
  have hsub : (Finset.range (k' + 1)).filter
      (fun i => ¬ (n - i) ∣ n.choose (k' + 1)) ⊆ {0} := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_singleton]
    by_contra hi0
    apply hi.2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨m, hm⟩ := hdiv (j + 1) (by omega) (by omega)
    have hm' : n / (j + 1) = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
    have hsplit : n - (j + 1) = (j + 1) * (n / (j + 1) - 1) := by
      rw [hm', Nat.mul_sub_one, ← hm]
    rw [hsplit, hC]
    exact mul_dvd_mul (hjL (j + 1) (by omega) (by omega))
      (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega)))
  simpa using Finset.card_le_card hsub

/-- **Monier's upper bound**: `n_k ≤ k!` for `3 ≤ k`, witnessed by
    `n = k!`: for `1 ≤ i < k`, `(k! − i) ∣ C(k!, k)`.
    Proof sketch: `C(k!, k) = k!(k!−1)⋯(k!−k+1)/k!`; for `1 ≤ i < k`
    write the product so that `k! − i` survives division — elementary
    manipulation of factorials; the divisor-defect at `n = k!`
    concentrates at `i = 0`.  -/
theorem nk_le_factorial (k : ℕ) (hk : 3 ≤ k) : nk k ≤ k.factorial := by
  apply Nat.sInf_le
  refine ⟨?_, divisorDefect_factorial_le_one k⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : k' ≤ k'.factorial := Nat.self_le_factorial k'
  rw [Nat.factorial_succ]
  nlinarith


/-- **Cambie's improvement** (DB comments): `n_k ≤ k · lcm(2, …, k−1)`,
    giving `n_k ≤ e^{(1+o(1))k}`.  Sits on the repo's Erdos440 lcm
    layer.  Comment-sourced; re-derive the witness before proving. -/
theorem nk_le_mul_lcm (k : ℕ) (hk : 3 ≤ k) :
    nk k ≤ k * (Finset.Icc 2 (k - 1)).lcm id := by
  apply Nat.sInf_le
  refine ⟨?_, divisorDefect_mul_lcm_le_one k hk⟩
  have h2 : 2 ∣ (Finset.Icc 2 (k - 1)).lcm id :=
    Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩)
  have hL0 : (Finset.Icc 2 (k - 1)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    rw [Finset.mem_Icc] at hx
    simp only [id] at hx0
    omega
  have hL2 : 2 ≤ (Finset.Icc 2 (k - 1)).lcm id := Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) h2
  rw [mul_comm 2 k]
  exact Nat.mul_le_mul_left k hL2

/-- Window index: if `m * q ≤ k + (n - k) % q` with `1 ≤ m`, then
    `i = k + (n - k) % q - m * q` satisfies `i < k` and `q ∣ n - i`. -/
private theorem window_index (n k q m : ℕ) (hq : 0 < q) (hkn : k ≤ n) (hm : 1 ≤ m)
    (hmq : m * q ≤ k + (n - k) % q) :
    k + (n - k) % q - m * q < k ∧ q ∣ n - (k + (n - k) % q - m * q) := by
  have hr : (n - k) % q < q := Nat.mod_lt _ hq
  have hdiv : q * ((n - k) / q) + (n - k) % q = n - k := Nat.div_add_mod (n - k) q
  have hqm : q ≤ m * q := Nat.le_mul_of_pos_left q hm
  refine ⟨by omega, ?_⟩
  have heq : n - (k + (n - k) % q - m * q) = q * ((n - k) / q + m) := by
    rw [Nat.mul_add, Nat.mul_comm q m]; omega
  rw [heq]
  exact Dvd.intro _ rfl

/-- If `q ≤ k` and there is a carry at modulus `q`, then `2 q ≤ k + (n - k) % q`. -/
private theorem two_mul_le_of_carry (n k q : ℕ) (hqk : q ≤ k)
    (hcarry : q ≤ k % q + (n - k) % q) : 2 * q ≤ k + (n - k) % q := by
  have hdm : q * (k / q) + k % q = k := Nat.div_add_mod k q
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0; omega
  have h1 : 1 ≤ k / q := (Nat.one_le_div_iff hq0).mpr hqk
  have h2 : q ≤ q * (k / q) := Nat.le_mul_of_pos_right q h1
  omega

/-- Two window indices: if `2 q ≤ k + (n - k) % q` then two distinct `i < k` have `q ∣ n - i`. -/
private theorem two_window_indices (n k q : ℕ) (hq : 0 < q) (hkn : k ≤ n)
    (h2 : 2 * q ≤ k + (n - k) % q) :
    ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ q ∣ n - i ∧ q ∣ n - j := by
  obtain ⟨hi1, hd1⟩ := window_index n k q 1 hq hkn le_rfl (by omega)
  obtain ⟨hi2, hd2⟩ := window_index n k q 2 hq hkn (by norm_num) h2
  exact ⟨_, _, hi1, hi2, by omega, hd1, hd2⟩

/-- Per-prime core of the rickyc–GPT bound: if any two failing indices coincide, then for
    `p ∣ k` some failing index `i < k` has `p ^ (v_p(k) + ⌊log_p (k−1)⌋) ∣ n − i`. -/
private theorem exists_failing_index_pow_dvd (n k p : ℕ) [hp : Fact p.Prime] (hk : 2 ≤ k)
    (hkn : k ≤ n) (hpk : p ∣ k)
    (huniq : ∀ i j, i < k → j < k → ¬ (n - i) ∣ n.choose k → ¬ (n - j) ∣ n.choose k → i = j) :
    ∃ i, i < k ∧ ¬ (n - i) ∣ n.choose k ∧
      p ^ (k.factorization p + Nat.log p (k - 1)) ∣ n - i := by
  have hp1 : 1 < p := hp.out.one_lt
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  set S := padicValNat p (n.choose k) with hSdef
  have hfail : ∀ i, p ^ (S + 1) ∣ n - i → ¬ (n - i) ∣ n.choose k := by
    intro i hd hdiv
    have hpS := hd.trans hdiv
    rw [padicValNat_dvd_iff_le hC] at hpS
    omega
  have huniq' : ∀ i j, i < k → j < k → p ^ (S + 1) ∣ n - i → p ^ (S + 1) ∣ n - j → i = j :=
    fun i j hi hj hdi hdj => huniq i j hi hj (hfail i hdi) (hfail j hdj)
  obtain ⟨T, hcarryT, hST⟩ := exists_level_of_prime_dvd n k p hpk (by omega) hkn
  obtain ⟨i0, hi0, hdT⟩ :=
    exists_dvd_sub_of_carry n k (p ^ T) (pow_pos hp.out.pos T) hkn hcarryT
  have h0 : p ^ (S + 1) ∣ n - i0 := (pow_dvd_pow p (by omega)).trans hdT
  have hni0 : n - i0 ≠ 0 := by omega
  set M := padicValNat p (n - i0) with hMdef
  have hSM : S + 1 ≤ M := (padicValNat_dvd_iff_le hni0).mp h0
  -- above level `S`, the only multiple in the window is `n - i0`
  have hlevel : ∀ j i, S < j → i < k → p ^ j ∣ n - i → j ≤ M := by
    intro j i hSj hik hdj
    have hdS : p ^ (S + 1) ∣ n - i := (pow_dvd_pow p (by omega)).trans hdj
    have hii : i = i0 := huniq' i i0 hik hi0 hdS h0
    subst hii
    exact (padicValNat_dvd_iff_le hni0).mp hdj
  have hA : ∀ j, S < j → ¬ 2 * p ^ j ≤ k + (n - k) % p ^ j := by
    intro j hSj h2
    obtain ⟨i, i', hi, hi', hne, hdi, hdi'⟩ :=
      two_window_indices n k (p ^ j) (pow_pos hp.out.pos j) hkn h2
    exact hne (huniq' i i' hi hi' ((pow_dvd_pow p (by omega)).trans hdi)
      ((pow_dvd_pow p (by omega)).trans hdi'))
  have hB : ∀ j, S < j → p ^ j ≤ k + (n - k) % p ^ j → j ≤ M := by
    intro j hSj h1
    obtain ⟨hi, hdi⟩ := window_index n k (p ^ j) 1 (pow_pos hp.out.pos j) hkn le_rfl
      (by rw [one_mul]; exact h1)
    exact hlevel j _ hSj hi hdi
  set a := k.factorization p with hadef
  set L := Nat.log p k with hLdef
  set e := Nat.log p (k - 1) with hedef
  have ha1 : 1 ≤ a := hp.out.factorization_pos_of_dvd (by omega) hpk
  have hpa : p ^ a ∣ k := Nat.ordProj_dvd k p
  have hpL : p ^ L ≤ k := Nat.pow_log_le_self p (by omega)
  have heL : e ≤ L := Nat.log_mono_right (by omega)
  have hval := padicValNat_choose (p := p) hkn (Nat.lt_succ_self (Nat.log p n))
  rw [← hSdef] at hval
  have hsub : (Finset.Ico 1 (Nat.log p n).succ).filter
      (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) ⊆
      Finset.Ioc a S ∪ Finset.Ioc (max S L) M := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hcarry := hj.2
    have hr : (n - k) % p ^ j < p ^ j := Nat.mod_lt _ (pow_pos hp.out.pos j)
    have hkmod : k % p ^ j ≤ k := Nat.mod_le k _
    have haj : a < j := by
      by_contra haj
      have hdk : p ^ j ∣ k := (pow_dvd_pow p (by omega)).trans hpa
      rw [Nat.mod_eq_zero_of_dvd hdk] at hcarry
      omega
    rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc]
    by_cases hjS : j ≤ S
    · exact Or.inl ⟨haj, hjS⟩
    · right
      have hSj : S < j := by omega
      have hLj : L < j := by
        by_contra hLj
        have hpj : p ^ j ≤ k := (Nat.pow_le_pow_right hp.out.pos (by omega)).trans hpL
        exact hA j hSj (two_mul_le_of_carry n k (p ^ j) hpj hcarry)
      exact ⟨max_lt hSj hLj, hB j hSj (by omega)⟩
  have hcard : S ≤ (S - a) + (M - max S L) := by
    calc S = _ := hval
      _ ≤ (Finset.Ioc a S ∪ Finset.Ioc (max S L) M).card := Finset.card_le_card hsub
      _ ≤ (Finset.Ioc a S).card + (Finset.Ioc (max S L) M).card := Finset.card_union_le _ _
      _ = (S - a) + (M - max S L) := by rw [Nat.card_Ioc, Nat.card_Ioc]
  have hfinal : a + e ≤ M := by
    rcases le_or_gt a S with haS | hSa
    · omega
    · -- the window length is exactly `p ^ (S + 1)`
      have hdk : p ^ (S + 1) ∣ k := (pow_dvd_pow p (by omega)).trans hpa
      have hk2 : k < 2 * p ^ (S + 1) := by
        by_contra hk2
        exact hA (S + 1) (by omega) ((not_lt.mp hk2).trans (Nat.le_add_right _ _))
      obtain ⟨c, hc⟩ := hdk
      have hc1 : c = 1 := by
        have hcpos : c ≠ 0 := by rintro rfl; omega
        have hc2 : c < 2 := by
          rw [hc] at hk2
          rw [mul_comm 2] at hk2
          exact Nat.lt_of_mul_lt_mul_left hk2
        omega
      rw [hc1, mul_one] at hc
      have hLS : L = S + 1 := by rw [hLdef, hc, Nat.log_pow hp1]
      have heS : e < S + 1 := by
        rw [hedef, Nat.log_lt_iff_lt_pow hp1 (by omega)]
        omega
      have haS : a ≤ S + 1 := by
        have hpak : p ^ a ≤ p ^ (S + 1) := hc ▸ Nat.le_of_dvd (by omega) hpa
        exact (Nat.pow_le_pow_iff_right hp1).mp hpak
      omega
  exact ⟨i0, hi0, hfail i0 h0, (pow_dvd_pow p hfinal).trans pow_padicValNat_dvd⟩

/-- Assembly over the primes of `k`: if `n ≥ 2k` has divisor defect at most one, then
    `∏_{p^a ∥ k} p^{a + ⌊log_p (k−1)⌋} ≤ n`.  All primes share the unique failing index
    `i0`, so the pairwise coprime prime powers all divide `n − i0 ≤ n`. -/
private theorem prod_le_of_divisorDefect_le_one (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (hd : divisorDefect n k ≤ 1) :
    k.factorization.prod (fun p a => p ^ (a + Nat.log p (k - 1))) ≤ n := by
  have hkn : k ≤ n := by omega
  have huniq : ∀ i j, i < k → j < k → ¬ (n - i) ∣ n.choose k → ¬ (n - j) ∣ n.choose k →
      i = j := by
    intro i j hi hj hfi hfj
    exact Finset.card_le_one.mp hd i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hfi⟩)
      j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hfj⟩)
  obtain ⟨p0, hp0, hp0k⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  haveI : Fact p0.Prime := ⟨hp0⟩
  obtain ⟨i0, hi0, hf0, -⟩ := exists_failing_index_pow_dvd n k p0 hk hkn hp0k huniq
  have hdvd : k.factorization.prod (fun p a => p ^ (a + Nat.log p (k - 1))) ∣ n - i0 := by
    rw [Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp (Nat.Coprime.pow _ _
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq)).mpr hpq))
    · intro p hp
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      obtain ⟨i, hi, hf, hdi⟩ :=
        exists_failing_index_pow_dvd n k p hk hkn (Nat.dvd_of_mem_primeFactors hp) huniq
      rw [huniq i i0 hi hi0 hf hf0] at hdi
      exact hdi
  exact (Nat.le_of_dvd (by omega) hdvd).trans (Nat.sub_le n i0)

/-- **rickyc–GPT lower bound** (comments, Jul 2026; comment-sourced,
    unrefereed — verify the valuation argument independently before
    building on it): `∏_{p^a ∥ k} p^{a + ⌊log_p (k−1)⌋} ≤ n_k`.
    Stated via `Nat.factorization`; `Nat.log p (k−1)` is Mathlib's
    floor-log. -/
theorem nk_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    k.factorization.prod (fun p a => p ^ (a + Nat.log p (k - 1))) ≤ nk k := by
  have hne : {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k ≤ 1}.Nonempty := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk3
    · exact ⟨4, by decide⟩
    · refine ⟨k.factorial, ?_, divisorDefect_factorial_le_one k⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : k' ≤ k'.factorial := Nat.self_le_factorial k'
      rw [Nat.factorial_succ]
      nlinarith
  have hmem := Nat.sInf_mem hne
  exact prod_le_of_divisorDefect_le_one (nk k) k hk hmem.1 hmem.2

-- The problem "Estimate n_k" itself remains OPEN: it is not even known
-- whether `(n_k)^{1/k}` converges (StijnC, comments: non-monotone;
-- min/max of `n_k^{1/k}` for k ≤ 37 at k = 10 and k = 31).  No formal
-- statement beyond the bounds above is attempted.

end ErdosCandidates.E1063

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB pull exactly.
   - divisorDefect definition correctly counts i with (n-i) not dividing C(n,k).
   - nk uses sInf with {n | 2*k <= n /\ divisorDefect n k <= 1}: faithful to "least
     n >= 2k ... all but one".
   - OEIS A389360 prefix 4,6,9,12,75,30,70,56,2403,280 matches DB pull exactly.
   - nk values n_2=4, n_3=6, n_4=9, n_5=12 independently verified by computation.
   - defect(4,2)=1 verified (i=0 fails: 4 does not divide 6; i=1 passes: 3|6).
   - Monier bound nk <= k! for k >= 3: matches DB body "Monier observed n_k <= k!
     for k >= 3".
   - Cambie bound uses Finset.Icc 2 (k-1) for lcm(2,...,k-1): matches DB
     "k[2,3,...,k-1]". Comment-sourced: correctly flagged.
   - rickyc-GPT lower bound uses Nat.log p (k-1): matches the IMPROVED bound from
     post-7439 (Jul 2026), not the earlier k/2. File header correctly says "Jun-Jul
     2026". Correctly flagged comment-sourced, unrefereed.
   - Types: all ℕ, ℕ-subtraction in divisorDefect guarded by i < k <= n (noted in
     docstring). No junk.
-/
