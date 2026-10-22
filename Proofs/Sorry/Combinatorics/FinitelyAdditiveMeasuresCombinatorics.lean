/-
# Finitely additive measures on ℤ — sharpness of the `sIP_n` threshold (Question 7.1(3))

## Source

Zeinab Ashtab and David Fernández-Bretón, "Finitely additive measures on ℤ and additive
combinatorics", arXiv 2607.26522 (July 2026). Definition of `sIP_n` in Section 6 (just before
Example `ex:sipnotip`); Theorem 6.5 (label `translationinvariant`); Section 7 "Discussion",
first `question` environment, item 3. Recorded 2026-10-21.

Verbatim (Theorem 6.5): "Let $\mu$ be a translation-invariant, positive finitely additive
measure belonging to the unit ball of $\ba(\mathbb Z)$. Then, for every
$A\subseteq\mathbb Z$, if $\mu(A)>1-\frac{1}{2^{n-1}}$ then $A$ is an $\sip_{n}$-set."

Verbatim (Question 7.1(3)): "Is there a translation-invariant measure $\mu\in\ba(\mathbb Z)$,
and a set $A\subseteq\mathbb Z$ that is not a $\sip_n$-set, such that
$\mu(A)=1-\frac{1}{2^{n-1}}$?"

The printed definition reads "$A$ is $\sip_{n+1}$ if, for every $a\in A$, the set
$A\cap(A-n)$ is $\sip_n$"; `A - n` is a typo for `A - a`, as the proof of Theorem 6.5 shows.

## Status

Open in the paper (posed as a question). This module answers it **yes** for every `n ≥ 1`:
`A = ℤ ∖ 2^(n-1) ℤ` is not `sIP_n`, and every translation-invariant mean gives it measure
exactly `1 - 1/2^(n-1)`; invariant means on `ℤ` exist (Følner windows `[0, N)` via Mathlib's
`IsAddFoelner.amenable`). Theorem 6.5 is also reproved (`thm_6_5`).

Computational check (bounded Python, periodic sets): `ℤ ∖ 2^(n-1) ℤ` is not `sIP_n` but is
`sIP_{n-1}` for `n ≤ 6`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FinitelyAdditiveMeasuresCombinatorics

open Set MeasureTheory Filter
open scoped Pointwise Topology ENNReal symmDiff

/-! ## Strongly `IP_n` sets -/

/-- `IsSIP n A` is the paper's "`A` is strongly `IP_n`" (`sIP_n`), Section 6:
`A` is `sIP_1` if it is nonempty, and `A` is `sIP_{n+1}` if for every `a ∈ A` the set
`A ∩ (A - a)` is `sIP_n`. Here `A - a = {x | x + a ∈ A} = (· + a) ⁻¹' A`.
The paper only defines `sIP_n` for `n ≥ 1`; the value at `n = 0` is the junk value `True`
and every statement below carries `1 ≤ n`. -/
def IsSIP : ℕ → Set ℤ → Prop
  | 0, _ => True
  | 1, A => A.Nonempty
  | n + 2, A => ∀ a ∈ A, IsSIP (n + 1) (A ∩ (· + a) ⁻¹' A)

/-- `sIP_1` means nonempty. -/
theorem isSIP_one_iff (A : Set ℤ) : IsSIP 1 A ↔ A.Nonempty := Iff.rfl

/-- The recursive clause of `sIP_{n+1}`. -/
theorem isSIP_add_two_iff (n : ℕ) (A : Set ℤ) :
    IsSIP (n + 2) A ↔ ∀ a ∈ A, IsSIP (n + 1) (A ∩ (· + a) ⁻¹' A) := Iff.rfl

/-- `ℤ` itself is `sIP_n` for every `n`. -/
theorem isSIP_univ : ∀ n : ℕ, IsSIP n (univ : Set ℤ)
  | 0 => trivial
  | 1 => univ_nonempty
  | n + 2 => fun _ _ => by simpa using isSIP_univ (n + 1)

/-- Paper's remark after the definition: `{1, 2, 3}` is not `sIP_2`. -/
example : ¬ IsSIP 2 ({1, 2, 3} : Set ℤ) := by
  intro h
  obtain ⟨x, hx1, hx2⟩ := h 3 (by simp)
  simp only [mem_insert_iff, mem_singleton_iff, mem_preimage] at hx1 hx2
  omega

example : IsSIP 1 ({0} : Set ℤ) := ⟨0, rfl⟩

example : ¬ IsSIP 1 (∅ : Set ℤ) := fun h => not_nonempty_empty h

/-- `2ℤ + 1` is `sIP_1` but not `sIP_2` (odd + odd is even). -/
example : ¬ IsSIP 2 {x : ℤ | ¬ (2 : ℤ) ∣ x} := by
  intro h
  obtain ⟨x, hx1, hx2⟩ := h 1 (by simp)
  simp only [mem_preimage, mem_ofPred_eq] at hx1 hx2
  omega

/-! ## `ℤ ∖ 2^m ℤ` is not `sIP_{m+1}` -/

/-- `window m k` is the set of `x` such that none of `x, x + 1, …, x + 2^k - 1` is divisible
by `2^m`. It is the `k`-th iterate of `S ↦ S ∩ (S - 2^(k-1))` started from `ℤ ∖ 2^m ℤ`. -/
def window (m k : ℕ) : Set ℤ := {x | ∀ s : ℕ, s < 2 ^ k → ¬ (2 : ℤ) ^ m ∣ x + s}

/-- The `0`-th window is `ℤ ∖ 2^m ℤ`. -/
theorem window_zero (m : ℕ) : window m 0 = {x | ¬ (2 : ℤ) ^ m ∣ x} := by
  ext x
  simp only [window, mem_ofPred_eq, pow_zero, Nat.lt_one_iff]
  constructor
  · intro h
    simpa using h 0 rfl
  · rintro h s rfl
    simpa using h

/-- The `m`-th window is empty: among `2^m` consecutive integers one is divisible by `2^m`. -/
theorem window_self_eq_empty (m : ℕ) : window m m = ∅ := by
  ext x
  simp only [window, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_not]
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  have h0 : 0 ≤ (-x) % 2 ^ m := Int.emod_nonneg (-x) hpos.ne'
  have h1 : (-x) % 2 ^ m < 2 ^ m := Int.emod_lt_of_pos (-x) hpos
  refine ⟨((-x) % 2 ^ m).toNat, ?_, ?_⟩
  · have hcast : (((-x) % 2 ^ m).toNat : ℤ) < ((2 ^ m : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
      push_cast
      exact h1
    exact_mod_cast hcast
  · rw [Int.toNat_of_nonneg h0]
    exact ⟨-((-x) / 2 ^ m), by rw [Int.emod_def]; ring⟩

/-- One step of the iteration: `window m (k+1) = window m k ∩ (window m k - 2^k)`. -/
theorem window_succ (m k : ℕ) :
    window m (k + 1) = window m k ∩ (· + (2 : ℤ) ^ k) ⁻¹' window m k := by
  ext x
  simp only [window, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun s hs => h s (by rw [pow_succ]; omega), fun s hs => ?_⟩
    have hlt : 2 ^ k + s < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have := h (2 ^ k + s) hlt
    push_cast at this
    rwa [← add_assoc] at this
  · rintro ⟨h1, h2⟩ s hs
    by_cases hsk : s < 2 ^ k
    · exact h1 s hsk
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 ^ k + t := ⟨s - 2 ^ k, by omega⟩
      have ht : t < 2 ^ k := by rw [pow_succ] at hs; omega
      have := h2 t ht
      push_cast
      rwa [← add_assoc]

/-- For `k < m`, the witness `2^k` lies in `window m k`: the integers `2^k, …, 2^(k+1) - 1`
lie strictly between `0` and `2^m`. -/
theorem two_pow_mem_window {m k : ℕ} (hk : k < m) : (2 : ℤ) ^ k ∈ window m k := by
  intro s hs hdvd
  have hpos : (0 : ℤ) < 2 ^ k + s := by positivity
  have hle := Int.le_of_dvd hpos hdvd
  have hkm : (2 : ℤ) ^ (k + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
  have hs' : (s : ℤ) < 2 ^ k := by exact_mod_cast hs
  rw [pow_succ] at hkm
  linarith

/-- `window m k` is not `sIP_{j+1}` when `k + j = m`. -/
theorem not_isSIP_window (m : ℕ) : ∀ j k : ℕ, k + j = m → ¬ IsSIP (j + 1) (window m k) := by
  intro j
  induction j with
  | zero =>
    intro k hk h
    rw [add_zero] at hk
    subst hk
    rw [isSIP_one_iff, window_self_eq_empty] at h
    exact not_nonempty_empty h
  | succ j ih =>
    intro k hk h
    have hmem : (2 : ℤ) ^ k ∈ window m k := two_pow_mem_window (by omega)
    have hstep := (isSIP_add_two_iff j (window m k)).1 h _ hmem
    rw [← window_succ] at hstep
    exact ih (k + 1) (by omega) hstep

/-- **Combinatorial half of the answer to Question 7.1(3).** For `n ≥ 1`, the set
`A = ℤ ∖ 2^(n-1) ℤ` is not `sIP_n`. -/
theorem not_isSIP_compl_two_pow_dvd (n : ℕ) (hn : 1 ≤ n) :
    ¬ IsSIP n {x : ℤ | ¬ (2 : ℤ) ^ (n - 1) ∣ x} := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← window_zero]
  exact not_isSIP_window j j 0 (zero_add j)

/-! ## Translation-invariant means -/

/-- `IsInvariantMean μ`: `μ` is a translation-invariant, positive, finitely additive
probability measure on all subsets of `ℤ` (an invariant mean; a positive element of norm `1`
of `ba(ℤ)` with `μ(A - x) = μ(A)`). Here `A - x = (· + x) ⁻¹' A`. -/
structure IsInvariantMean (μ : Set ℤ → ℝ) : Prop where
  /-- positivity -/
  nonneg : ∀ s, 0 ≤ μ s
  /-- finite additivity -/
  union_eq_add : ∀ s t, Disjoint s t → μ (s ∪ t) = μ s + μ t
  /-- translation invariance `μ (A - c) = μ A` -/
  preimage_add_eq : ∀ (s : Set ℤ) (c : ℤ), μ ((· + c) ⁻¹' s) = μ s
  /-- normalization -/
  univ_eq_one : μ univ = 1

namespace IsInvariantMean

variable {μ : Set ℤ → ℝ}

/-- An invariant mean gives the empty set measure `0`. -/
theorem empty_eq_zero (hμ : IsInvariantMean μ) : μ ∅ = 0 := by
  have h := hμ.union_eq_add ∅ ∅ (disjoint_empty _)
  rw [union_empty] at h
  linarith

/-- An invariant mean is monotone. -/
theorem mono (hμ : IsInvariantMean μ) {s t : Set ℤ} (hst : s ⊆ t) : μ s ≤ μ t := by
  have h := hμ.union_eq_add s (t \ s) disjoint_sdiff_right
  rw [union_sdiff_cancel hst] at h
  linarith [hμ.nonneg (t \ s)]

/-- An invariant mean is bounded by `1`. -/
theorem le_one (hμ : IsInvariantMean μ) (s : Set ℤ) : μ s ≤ 1 :=
  hμ.univ_eq_one ▸ hμ.mono (subset_univ s)

/-- Complement rule `μ sᶜ = 1 - μ s`. -/
theorem compl_eq (hμ : IsInvariantMean μ) (s : Set ℤ) : μ sᶜ = 1 - μ s := by
  have h := hμ.union_eq_add s sᶜ disjoint_compl_right
  rw [union_compl_self, hμ.univ_eq_one] at h
  linarith

/-- Inclusion–exclusion `μ (s ∪ t) + μ (s ∩ t) = μ s + μ t`. -/
theorem union_add_inter (hμ : IsInvariantMean μ) (s t : Set ℤ) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  have h1 := hμ.union_eq_add s (t \ s) disjoint_sdiff_right
  have h2 := hμ.union_eq_add (s ∩ t) (t \ s)
    (disjoint_sdiff_right.mono_left inter_subset_left)
  rw [union_sdiff_self] at h1
  rw [inter_comm, inter_union_sdiff, inter_comm t s] at h2
  linarith

/-- Every invariant mean gives a residue class `{x | M ∣ x + r}` the same measure as
`M ℤ`, and the multiples of `M ≥ 1` have measure `1 / M`. -/
theorem dvd_eq_inv (hμ : IsInvariantMean μ) (M : ℕ) (hM : 0 < M) :
    μ {x : ℤ | (M : ℤ) ∣ x} = 1 / M := by
  set C : Set ℤ := {x : ℤ | (M : ℤ) ∣ x} with hC
  -- `D k` is the union of the first `k` residue classes.
  let D : ℕ → Set ℤ := fun k => {x | ∃ r : ℕ, r < k ∧ (M : ℤ) ∣ x + r}
  have hshift : ∀ r : ℕ, μ {x : ℤ | (M : ℤ) ∣ x + r} = μ C := fun r =>
    hμ.preimage_add_eq C r
  have hD : ∀ k : ℕ, k ≤ M → μ (D k) = k * μ C := by
    intro k
    induction k with
    | zero =>
      intro _
      have hD0 : D 0 = ∅ := by
        ext x
        simp [D]
      rw [hD0, hμ.empty_eq_zero]
      simp
    | succ k ih =>
      intro hk
      have hsplit : D (k + 1) = D k ∪ {x : ℤ | (M : ℤ) ∣ x + k} := by
        ext x
        simp only [D, mem_union, mem_ofPred_eq]
        constructor
        · rintro ⟨r, hr, hdvd⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
          · exact Or.inl ⟨r, hr, hdvd⟩
          · exact Or.inr hdvd
        · rintro (⟨r, hr, hdvd⟩ | hdvd)
          · exact ⟨r, by omega, hdvd⟩
          · exact ⟨k, by omega, hdvd⟩
      have hdisj : Disjoint (D k) {x : ℤ | (M : ℤ) ∣ x + k} := by
        rw [Set.disjoint_left]
        rintro x ⟨r, hr, hr'⟩ hk'
        have hsub : (M : ℤ) ∣ (k : ℤ) - r := by
          have := dvd_sub hk' hr'
          rwa [add_sub_add_left_eq_sub] at this
        have hpos : (0 : ℤ) < (k : ℤ) - r := by omega
        have := Int.le_of_dvd hpos hsub
        omega
      rw [hsplit, hμ.union_eq_add _ _ hdisj, ih (by omega), hshift]
      push_cast
      ring
  have hDM : D M = univ := by
    refine eq_univ_of_forall fun x => ⟨((-x) % M).toNat, ?_, ?_⟩
    · have hpos : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ (-x) % M := Int.emod_nonneg (-x) hpos.ne'
      have h1 : (-x) % M < M := Int.emod_lt_of_pos (-x) hpos
      omega
    · have hpos : (0 : ℤ) < M := by exact_mod_cast hM
      rw [Int.toNat_of_nonneg (Int.emod_nonneg (-x) hpos.ne')]
      exact ⟨-((-x) / M), by rw [Int.emod_def]; ring⟩
  have hfin := hD M le_rfl
  rw [hDM, hμ.univ_eq_one] at hfin
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp
  linarith

end IsInvariantMean

/-- **Measure half of the answer to Question 7.1(3).** Every translation-invariant mean on `ℤ`
gives `ℤ ∖ 2^m ℤ` measure exactly `1 - 1/2^m` (with `m = n - 1` this is `1 - 1/2^(n-1)`). -/
theorem IsInvariantMean.compl_two_pow_dvd_eq {μ : Set ℤ → ℝ} (hμ : IsInvariantMean μ)
    (m : ℕ) : μ {x : ℤ | ¬ (2 : ℤ) ^ m ∣ x} = 1 - 1 / 2 ^ m := by
  have h := hμ.dvd_eq_inv (2 ^ m) (by positivity)
  have hset : {x : ℤ | ¬ (2 : ℤ) ^ m ∣ x} = {x : ℤ | ((2 ^ m : ℕ) : ℤ) ∣ x}ᶜ := by
    ext x
    simp
  rw [hset, hμ.compl_eq, h]
  push_cast
  ring

/-! ## Existence of an invariant mean (Følner sequence `[0, N)`) -/

/-- The counting measure of the window `[0, N)` is `N`. -/
theorem count_Ico_zero (N : ℕ) : Measure.count (Ico (0 : ℤ) N) = N := by
  rw [← Finset.coe_Ico, Measure.count_apply_finset, Int.card_Ico]
  simp

/-- The translate `g + [0, N)` differs from `[0, N)` in at most `2 |g|` points. -/
theorem count_vadd_Ico_symmDiff_le (g : ℤ) (N : ℕ) :
    Measure.count ((g +ᵥ Ico (0 : ℤ) N) ∆ Ico (0 : ℤ) N) ≤ (2 * g.natAbs : ℕ) := by
  let T : Finset ℤ :=
    Finset.Ico (min 0 g) (max 0 g) ∪ Finset.Ico (min (N : ℤ) (g + N)) (max (N : ℤ) (g + N))
  have hsub : (g +ᵥ Ico (0 : ℤ) N) ∆ Ico (0 : ℤ) N ⊆ (T : Set ℤ) := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_vadd_set_iff_neg_vadd_mem, mem_Ico, vadd_eq_add] at hx
    simp only [T, Finset.coe_union, Finset.coe_Ico, mem_union, mem_Ico]
    omega
  have hcard : T.card ≤ 2 * g.natAbs := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [Int.card_Ico, Int.card_Ico]
    omega
  calc Measure.count ((g +ᵥ Ico (0 : ℤ) N) ∆ Ico (0 : ℤ) N)
      ≤ Measure.count (T : Set ℤ) := measure_mono hsub
    _ = T.card := Measure.count_apply_finset T
    _ ≤ (2 * g.natAbs : ℕ) := by exact_mod_cast hcard

/-- The windows `[0, N)` form an additive Følner sequence for `ℤ` acting on itself. -/
theorem isAddFoelner_Ico :
    IsAddFoelner ℤ (Measure.count : Measure ℤ) atTop (fun N : ℕ => Ico (0 : ℤ) N) where
  eventually_measurableSet := Eventually.of_forall fun _ => MeasurableSet.of_discrete
  eventually_meas_ne_zero := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [count_Ico_zero]
    exact_mod_cast (show N ≠ 0 by omega)
  eventually_meas_ne_top := Eventually.of_forall fun N => by
    rw [count_Ico_zero]
    exact ENNReal.natCast_ne_top N
  tendsto_meas_vadd_symmDiff g := by
    have hlim : Tendsto (fun N : ℕ => ((2 * g.natAbs : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.natCast_ne_top (2 * g.natAbs)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) fun N => ?_
    simp only [count_Ico_zero, div_eq_mul_inv]
    gcongr
    exact count_vadd_Ico_symmDiff_le g N

/-- **Existence of an invariant mean on `ℤ`**: there is a translation-invariant, positive,
finitely additive probability measure on all subsets of `ℤ` (the density along an ultrafilter
of the Følner windows `[0, N)`). -/
theorem exists_isInvariantMean : ∃ μ : Set ℤ → ℝ, IsInvariantMean μ := by
  obtain ⟨m, hm1, hadd, hinv⟩ := isAddFoelner_Ico.amenable
  have hle : ∀ s, m s ≤ 1 := by
    intro s
    rw [← hm1, ← union_compl_self s, hadd s sᶜ MeasurableSet.of_discrete disjoint_compl_right]
    exact le_self_add
  have hne : ∀ s, m s ≠ ⊤ := fun s => ne_top_of_le_ne_top ENNReal.one_ne_top (hle s)
  refine ⟨fun s => (m s).toReal, ?_, ?_, ?_, ?_⟩
  · exact fun s => ENNReal.toReal_nonneg
  · intro s t hst
    rw [hadd s t MeasurableSet.of_discrete hst, ENNReal.toReal_add (hne s) (hne t)]
  · intro s c
    have hpre : (· + c) ⁻¹' s = (-c) +ᵥ s := by
      ext x
      simp only [mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
      rw [add_comm]
    rw [hpre, hinv]
  · rw [hm1, ENNReal.toReal_one]

/-! ## Theorem 6.5 and the answer to Question 7.1(3) -/

/-- **Theorem 6.5** (`translationinvariant`) of the paper: if `μ` is a translation-invariant
mean on `ℤ`, `n ≥ 1`, and `1 - 1/2^(n-1) < μ A`, then `A` is `sIP_n`. -/
theorem thm_6_5 {μ : Set ℤ → ℝ} (hμ : IsInvariantMean μ) (n : ℕ) (hn : 1 ≤ n) (A : Set ℤ)
    (hA : 1 - 1 / 2 ^ (n - 1) < μ A) : IsSIP n A := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hA
  induction j generalizing A with
  | zero =>
    rw [isSIP_one_iff, nonempty_iff_ne_empty]
    rintro rfl
    rw [hμ.empty_eq_zero] at hA
    norm_num at hA
  | succ j ih =>
    rw [isSIP_add_two_iff]
    intro a _
    refine ih _ (by omega) ?_
    have hB : μ ((· + a) ⁻¹' A) = μ A := hμ.preimage_add_eq A a
    have hie := hμ.union_add_inter A ((· + a) ⁻¹' A)
    have hU := hμ.le_one (A ∪ (· + a) ⁻¹' A)
    have hpow : (1 : ℝ) / 2 ^ (j + 1) = (1 / 2 ^ j) / 2 := by
      rw [pow_succ]
      field_simp
    rw [hpow] at hA
    linarith

/-- **Answer to Question 7.1(3) of arXiv 2607.26522: yes.** For every `n ≥ 1` there is a
translation-invariant mean `μ` on `ℤ` and a set `A ⊆ ℤ` that is not `sIP_n` with
`μ A = 1 - 1/2^(n-1)`; one may take `A = ℤ ∖ 2^(n-1) ℤ` and any invariant mean.
So the threshold of Theorem 6.5 is sharp for every `n`. -/
theorem question_7_1_3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ μ : Set ℤ → ℝ, IsInvariantMean μ ∧
      ∃ A : Set ℤ, ¬ IsSIP n A ∧ μ A = 1 - 1 / 2 ^ (n - 1) := by
  obtain ⟨μ, hμ⟩ := exists_isInvariantMean
  exact ⟨μ, hμ, {x : ℤ | ¬ (2 : ℤ) ^ (n - 1) ∣ x}, not_isSIP_compl_two_pow_dvd n hn,
    hμ.compl_two_pow_dvd_eq (n - 1)⟩

/-- Strengthened form: the set `ℤ ∖ 2^(n-1) ℤ` witnesses sharpness for *every*
translation-invariant mean simultaneously. -/
theorem sharpness_for_every_invariant_mean {μ : Set ℤ → ℝ} (hμ : IsInvariantMean μ)
    (n : ℕ) (hn : 1 ≤ n) :
    ¬ IsSIP n {x : ℤ | ¬ (2 : ℤ) ^ (n - 1) ∣ x} ∧
      μ {x : ℤ | ¬ (2 : ℤ) ^ (n - 1) ∣ x} = 1 - 1 / 2 ^ (n - 1) :=
  ⟨not_isSIP_compl_two_pow_dvd n hn, hμ.compl_two_pow_dvd_eq (n - 1)⟩

/-- Non-vacuity at `n = 3`: some invariant mean and some non-`sIP_3` set of measure `3/4`. -/
example : ∃ μ : Set ℤ → ℝ, IsInvariantMean μ ∧ ∃ A : Set ℤ, ¬ IsSIP 3 A ∧ μ A = 3 / 4 := by
  obtain ⟨μ, hμ, A, hA, hμA⟩ := question_7_1_3 3 (by norm_num)
  exact ⟨μ, hμ, A, hA, by rw [hμA]; norm_num⟩

end Candidates.FinitelyAdditiveMeasuresCombinatorics
