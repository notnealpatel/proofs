/-
# Consecutive-divisor ratios: Erdős problem 673

For the sorted positive divisors `1=d₁<⋯<d_τ=n`, let
`G(n)=Σ_{i<τ} d_i/d_{i+1}`. The source asks whether `G(n)` tends to infinity
for almost all integers and asks for an asymptotic formula for its partial sums.
References: Erdős [Er82e] and the Erdős–Tenenbaum distribution result cited
in the Erdős problem 673 archive.

For every rational `M`, the proportion of `1 ≤ n ≤ X` with `G(n) ≤ M`
tends to zero. The partial sums satisfy two-sided bounds of order `X log X`,
with constants `1/16` and `2` for `X ≥ 256`; these are weaker than a precise
asymptotic equivalent. For positive `n`, the imported pointwise bound
`τ(n/m)/m ≤ G(n)` also requires `m ∣ n` and `2 ≤ m`: the unguarded version
fails at `m=1`, `n=7`.
-/
import Enumerative.E673

set_option autoImplicit false

namespace ErdosCandidates.E673

section Density

open Finset

/-- `2^ω(m) ≤ τ(m)` for `m ≠ 0`. -/
private theorem two_pow_card_primeFactors_le (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm]
  apply Finset.pow_card_le_prod
  intro p hp
  have hpos : 0 < m.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- Removing one prime factor drops `ω` by at most one. -/
private theorem card_primeFactors_le_div (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    n.primeFactors.card ≤ (n / p).primeFactors.card + 1 := by
  have hq : n / p ≠ 0 := by
    intro h
    rcases Nat.div_eq_zero_iff.mp h with h | h
    · exact hp.ne_zero h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) (not_le.mpr h)
  have hmul : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
  have hpf : n.primeFactors = {p} ∪ (n / p).primeFactors := by
    conv_lhs => rw [hmul]
    rw [Nat.primeFactors_mul hp.ne_zero hq, hp.primeFactors]
  rw [hpf]
  calc ({p} ∪ (n / p).primeFactors).card ≤ ({p} : Finset ℕ).card + (n / p).primeFactors.card :=
        card_union_le _ _
    _ = (n / p).primeFactors.card + 1 := by rw [card_singleton]; ring

/-- Counting integers in `[1, X]` coprime to `Q`. -/
private theorem card_coprime_Icc_le (Q X : ℕ) (hQ : Q ≠ 0) :
    (((Icc 1 X).filter (fun n => Q.Coprime n)).card : ℝ) ≤
      (Q.totient : ℝ) / Q * X + Q := by
  have hI : Icc 1 X = Ico 1 (1 + X) := by
    ext n; simp only [mem_Icc, mem_Ico]; omega
  have h := Nat.Ico_filter_coprime_le 1 X hQ
  rw [← hI] at h
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hdiv : ((X / Q : ℕ) : ℝ) ≤ (X : ℝ) / Q := Nat.cast_div_le
  have htot : (Q.totient : ℝ) ≤ Q := by exact_mod_cast Nat.totient_le Q
  calc (((Icc 1 X).filter (fun n => Q.Coprime n)).card : ℝ)
      ≤ ((Q.totient * (X / Q + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (Q.totient : ℝ) * ((X / Q : ℕ) : ℝ) + Q.totient := by push_cast; ring
    _ ≤ (Q.totient : ℝ) * ((X : ℝ) / Q) + Q :=
        add_le_add (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)) htot
    _ = (Q.totient : ℝ) / Q * X + Q := by ring

/-- `φ(Q)/Q ≤ exp(-∑_{p∈W} 1/p)` for `Q = ∏ W`, `W` a finite set of primes. -/
private theorem totient_prod_div_le_exp (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) :
    ((∏ p ∈ W, p).totient : ℝ) / (∏ p ∈ W, p : ℕ) ≤ Real.exp (-∑ p ∈ W, (1 : ℝ) / p) := by
  set Q : ℕ := ∏ p ∈ W, p with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hW p hp).ne_zero)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ0
  have hpf : Q.primeFactors = W := Nat.primeFactors_prod hW
  have htotQ : (Q.totient : ℚ) = Q * ∏ p ∈ W, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors, hpf]
  have htotR : (Q.totient : ℝ) = Q * ∏ p ∈ W, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) htotQ
    push_cast at h
    exact h
  rw [htotR, mul_div_cancel_left₀ _ hQpos.ne', ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hW p hp).one_lt.le
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
    linarith
  · intro p _
    have h := Real.add_one_le_exp (-(1 : ℝ) / p)
    rw [neg_div] at h
    rw [one_div] at h ⊢
    linarith

/-- Window lemma: for every `δ > 0` and `L`, some finite set `W` of primes above `L`
    has the property that eventually at most `δ X` integers in `[1, X]` avoid all of `W`. -/
private theorem exists_prime_window (δ : ℝ) (hδ : 0 < δ) (L : ℕ) :
    ∃ W : Finset ℕ, (∀ p ∈ W, p.Prime ∧ L < p) ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Icc 1 X).filter (fun n => ∀ p ∈ W, ¬ p ∣ n)).card : ℝ) ≤ δ * X := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun k _ => by positivity) n
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  obtain ⟨N, hN, hNL⟩ := ((htend.eventually_ge_atTop
    (∑ i ∈ range (L + 1), f i + Real.log (2 / δ))).and (Filter.eventually_ge_atTop (L + 1))).exists
  classical
  set W : Finset ℕ := (range N \ range (L + 1)).filter Nat.Prime with hWdef
  have hWp : ∀ p ∈ W, p.Prime ∧ L < p := by
    intro p hp
    simp only [hWdef, mem_filter, mem_sdiff, mem_range] at hp
    exact ⟨hp.2, by omega⟩
  have hsumW : Real.log (2 / δ) ≤ ∑ p ∈ W, (1 : ℝ) / p := by
    have hsplit := Finset.sum_sdiff (f := f) (range_subset_range.mpr hNL)
    have hWsum : ∑ p ∈ W, (1 : ℝ) / p = ∑ x ∈ range N \ range (L + 1), f x := by
      rw [hWdef, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      simp only [hf, Set.indicator_apply, Set.mem_ofPred_eq]
    linarith
  set Q : ℕ := ∏ p ∈ W, p with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hWp p hp).1.ne_zero)
  have hratio : (Q.totient : ℝ) / Q ≤ δ / 2 := by
    calc (Q.totient : ℝ) / Q ≤ Real.exp (-∑ p ∈ W, (1 : ℝ) / p) :=
          totient_prod_div_le_exp W (fun p hp => (hWp p hp).1)
      _ ≤ Real.exp (-Real.log (2 / δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = δ / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  have hfilt : ∀ X : ℕ, (Icc 1 X).filter (fun n => ∀ p ∈ W, ¬ p ∣ n) =
      (Icc 1 X).filter (fun n => Q.Coprime n) := by
    intro X
    apply Finset.filter_congr
    intro n _
    rw [hQdef, Nat.coprime_prod_left_iff]
    exact forall₂_congr (fun p hp => ((hWp p hp).1.coprime_iff_not_dvd).symm)
  refine ⟨W, hWp, ⌈2 * Q / δ⌉₊, fun X hX => ?_⟩
  have hXQ : 2 * (Q : ℝ) / δ ≤ X := (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hQX : (Q : ℝ) ≤ δ / 2 * X := by
    rw [div_le_iff₀ hδ] at hXQ
    linarith
  rw [hfilt X]
  calc (((Icc 1 X).filter (fun n => Q.Coprime n)).card : ℝ)
      ≤ (Q.totient : ℝ) / Q * X + Q := card_coprime_Icc_le Q X hQ0
    _ ≤ δ / 2 * X + δ / 2 * X :=
        add_le_add (mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)) hQX
    _ = δ * X := by ring

/-- Union bound for eventual density estimates. -/
private theorem card_filter_or_le (P R : ℕ → Prop) [DecidablePred P] [DecidablePred R] (X : ℕ) :
    (((Icc 1 X).filter (fun n => P n ∨ R n)).card : ℝ) ≤
      ((Icc 1 X).filter P).card + ((Icc 1 X).filter R).card := by
  rw [Finset.filter_or]
  exact_mod_cast card_union_le _ _

/-- For every `K` and `δ > 0` there is a finite set `S` of primes such that eventually
    at most `δ X` integers in `[1, X]` have fewer than `K` prime factors in `S`. -/
private theorem exists_primes_many_factors (K : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Icc 1 X).filter (fun n => (S ∩ n.primeFactors).card < K)).card : ℝ) ≤ δ * X := by
  induction K with
  | zero =>
    intro δ hδ
    refine ⟨∅, by simp, 0, fun X _ => ?_⟩
    have hempty : (Icc 1 X).filter (fun n => ((∅ : Finset ℕ) ∩ n.primeFactors).card < 0) = ∅ :=
      Finset.filter_false_of_mem (fun n _ => Nat.not_lt_zero _)
    rw [hempty, card_empty, Nat.cast_zero]
    positivity
  | succ K ih =>
    intro δ hδ
    obtain ⟨S', hS'p, X₁, hX₁⟩ := ih (δ / 2) (by positivity)
    obtain ⟨W, hWp, X₂, hX₂⟩ := exists_prime_window (δ / 2) (by positivity) (S'.sup id)
    classical
    refine ⟨W ∪ S', fun p hp => ?_, max X₁ X₂, fun X hX => ?_⟩
    · rcases mem_union.mp hp with h | h
      · exact (hWp p h).1
      · exact hS'p p h
    have hsub : (Icc 1 X).filter (fun n => ((W ∪ S') ∩ n.primeFactors).card < K + 1) ⊆
        (Icc 1 X).filter (fun n => (∀ p ∈ W, ¬ p ∣ n) ∨ (S' ∩ n.primeFactors).card < K) := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨p, hpW, hpn⟩, hK⟩ := hcon
      have hn0 : n ≠ 0 := by omega
      have hpS' : p ∉ S' := by
        intro hp
        have hle : p ≤ S'.sup id := Finset.le_sup (f := id) hp
        have := (hWp p hpW).2
        omega
      have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨(hWp p hpW).1, hpn, hn0⟩
      have hins : insert p (S' ∩ n.primeFactors) ⊆ (W ∪ S') ∩ n.primeFactors := by
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact mem_inter.mpr ⟨mem_union_left _ hpW, hpf⟩
        · obtain ⟨h1, h2⟩ := mem_inter.mp hq
          exact mem_inter.mpr ⟨mem_union_right _ h1, h2⟩
      have hcard := card_le_card hins
      rw [card_insert_of_notMem (fun h => hpS' (mem_inter.mp h).1)] at hcard
      omega
    calc (((Icc 1 X).filter (fun n => ((W ∪ S') ∩ n.primeFactors).card < K + 1)).card : ℝ)
        ≤ (((Icc 1 X).filter
            (fun n => (∀ p ∈ W, ¬ p ∣ n) ∨ (S' ∩ n.primeFactors).card < K)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ (((Icc 1 X).filter (fun n => ∀ p ∈ W, ¬ p ∣ n)).card : ℝ) +
            ((Icc 1 X).filter (fun n => (S' ∩ n.primeFactors).card < K)).card :=
          card_filter_or_le _ _ X
      _ ≤ δ / 2 * X + δ / 2 * X :=
          add_le_add (hX₂ X (le_of_max_le_right hX)) (hX₁ X (le_of_max_le_left hX))
      _ = δ * X := by ring

end Density

/-- For every rational bound `M`, the integers `1 ≤ n ≤ X` with `G(n) ≤ M`
have proportion tending to zero: the natural-density form of question 1
of Erdős problem 673. -/
theorem G_tendsto_ae (M : ℚ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  have hmain : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ) ≤ ε * X := by
    intro ε hε
    obtain ⟨W, hWp, X₁, hX₁⟩ := exists_prime_window (ε / 2) (by positivity) 0
    set P : ℕ := ∏ p ∈ W, p with hPdef
    have hP0 : 0 < P := Finset.prod_pos (fun p hp => (hWp p hp).1.pos)
    obtain ⟨K, hK⟩ : ∃ K : ℕ, max M 0 * P < 2 ^ K :=
      pow_unbounded_of_one_lt (max M 0 * P) (by norm_num : (1 : ℚ) < 2)
    obtain ⟨S, -, X₂, hX₂⟩ := exists_primes_many_factors (K + 1) (ε / 2) (by positivity)
    refine ⟨max X₁ X₂, fun X hX => ?_⟩
    have hsub : (Finset.Icc 1 X).filter (fun n => G n ≤ M) ⊆
        (Finset.Icc 1 X).filter
          (fun n => (∀ p ∈ W, ¬ p ∣ n) ∨ (S ∩ n.primeFactors).card < K + 1) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      refine ⟨hn.1, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨p, hpW, hpn⟩, hKle⟩ := hcon
      have hn0 : n ≠ 0 := by omega
      have hp : p.Prime := (hWp p hpW).1
      have hω : K ≤ (n / p).primeFactors.card := by
        have h1 := Finset.card_le_card
          (Finset.inter_subset_right : S ∩ n.primeFactors ⊆ n.primeFactors)
        have h2 := card_primeFactors_le_div n p hn0 hp hpn
        omega
      have hq0 : n / p ≠ 0 := by
        have hpn' : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
        exact (Nat.div_pos hpn' hp.pos).ne'
      have hτ : (2 : ℚ) ^ K ≤ (n / p).divisors.card := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hω).trans
          (two_pow_card_primeFactors_le _ hq0)
      have hG := tau_div_le_G n p hn.1.1 hpn hp.two_le
      have hpP : p ≤ P := Nat.le_of_dvd hP0 (Finset.dvd_prod_of_mem _ hpW)
      have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
      have hMp : M * p < 2 ^ K :=
        calc M * p ≤ max M 0 * p := mul_le_mul_of_nonneg_right (le_max_left _ _) hppos.le
          _ ≤ max M 0 * P := mul_le_mul_of_nonneg_left (by exact_mod_cast hpP) (le_max_right _ _)
          _ < 2 ^ K := hK
      have hlt : M < 2 ^ K / p := (lt_div_iff₀ hppos).mpr hMp
      have hdiv : (2 : ℚ) ^ K / p ≤ ((n / p).divisors.card : ℚ) / p :=
        div_le_div_of_nonneg_right hτ hppos.le
      linarith [hn.2]
    calc (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ)
        ≤ (((Finset.Icc 1 X).filter
            (fun n => (∀ p ∈ W, ¬ p ∣ n) ∨ (S ∩ n.primeFactors).card < K + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ W, ¬ p ∣ n)).card : ℝ) +
            ((Finset.Icc 1 X).filter (fun n => (S ∩ n.primeFactors).card < K + 1)).card :=
          card_filter_or_le _ _ X
      _ ≤ ε / 2 * X + ε / 2 * X :=
          add_le_add (hX₁ X (le_of_max_le_left hX)) (hX₂ X (le_of_max_le_right hX))
      _ = ε * X := by ring
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun X => lt_of_lt_of_le ha (by positivity))
  · intro b hb
    obtain ⟨X₀, hX₀⟩ := hmain (b / 2) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop (max X₀ 1)] with X hX
    have hXpos : (0 : ℝ) < X := by
      have : 1 ≤ X := le_of_max_le_right hX
      exact_mod_cast this
    rw [div_lt_iff₀ hXpos]
    calc (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ)
        ≤ b / 2 * X := hX₀ X (le_of_max_le_left hX)
      _ < b * X := by nlinarith

section MeanOrder

open Finset

/-- Dirichlet's hyperbola identity in its simplest form:
    `∑_{n ≤ Y} τ(n) = ∑_{d ≤ Y} ⌊Y/d⌋`. -/
private theorem sum_card_divisors_eq (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, n.divisors.card = ∑ d ∈ Icc 1 Y, Y / d := by
  have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div Y
  simp only [ArithmeticFunction.sigma_zero_apply] at h
  have hI : Icc 1 Y = Ioc 0 Y := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hI]
  exact h

/-- Real upper bound `∑_{n ≤ Y} τ(n) ≤ Y (1 + log Y)`. -/
private theorem sum_card_divisors_le (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) ≤ Y * (1 + Real.log Y) := by
  have hcast : (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) =
      ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := by
    exact_mod_cast sum_card_divisors_eq Y
  have hterm : ∀ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) * (d : ℝ)⁻¹ := by
    intro d _
    rw [← div_eq_mul_inv]
    exact Nat.cast_div_le
  have hharm : ((harmonic Y : ℚ) : ℝ) = ∑ d ∈ Icc 1 Y, (d : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  calc (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ))
      = ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := hcast
    _ ≤ ∑ d ∈ Icc 1 Y, (Y : ℝ) * (d : ℝ)⁻¹ := sum_le_sum hterm
    _ = Y * ((harmonic Y : ℚ) : ℝ) := by rw [← mul_sum, hharm]
    _ ≤ Y * (1 + Real.log Y) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Y) (Nat.cast_nonneg Y)

/-- Real lower bound `Y log Y - Y ≤ ∑_{n ≤ Y} τ(n)`. -/
private theorem sum_card_divisors_ge (Y : ℕ) :
    Y * Real.log Y - Y ≤ (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) := by
  have hcast : (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) =
      ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := by
    exact_mod_cast sum_card_divisors_eq Y
  have hterm : ∀ d ∈ Icc 1 Y, (Y : ℝ) * (d : ℝ)⁻¹ - 1 ≤ ((Y / d : ℕ) : ℝ) := by
    intro d _
    rw [← div_eq_mul_inv, ← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have hharm : ((harmonic Y : ℚ) : ℝ) = ∑ d ∈ Icc 1 Y, (d : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hlog : Real.log Y ≤ ((harmonic Y : ℚ) : ℝ) := by
    have h1 := log_add_one_le_harmonic Y
    by_cases hY : Y = 0
    · subst hY; simp
    · have : Real.log Y ≤ Real.log ((Y + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by positivity)
        push_cast; linarith
      linarith
  calc (Y : ℝ) * Real.log Y - Y
      ≤ Y * ((harmonic Y : ℚ) : ℝ) - Y := by
        have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) Y)
        linarith
    _ = ∑ d ∈ Icc 1 Y, ((Y : ℝ) * (d : ℝ)⁻¹ - 1) := by
        rw [sum_sub_distrib, ← mul_sum, ← hharm]
        simp
    _ ≤ ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := sum_le_sum hterm
    _ = _ := hcast.symm

/-- The `G`-sum over `[1, X]` dominates half the divisor-count sum over `[1, X/2]`,
    using only the even arguments `n = 2k` and `τ(k)/2 ≤ G(2k)`. -/
private theorem sum_card_divisors_half_le_sum_G (X : ℕ) :
    (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℝ)) / 2 ≤
      (((Icc 1 X).sum G : ℚ) : ℝ) := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (Icc 1 (X / 2) : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  have hsub : (Icc 1 (X / 2)).image (fun k : ℕ => 2 * k) ⊆ Icc 1 X := by
    intro n hn
    simp only [mem_image, mem_Icc] at hn ⊢
    omega
  have hterm : ∀ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ) / 2 ≤ G (2 * k) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have h := tau_div_le_G (2 * k) 2 (by omega) (dvd_mul_right 2 k) le_rfl
    rwa [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)] at h
  have hQ : (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ)) / 2 ≤ (Icc 1 X).sum G := by
    calc (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ)) / 2
        = ∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ) / 2 := by rw [sum_div]
      _ ≤ ∑ k ∈ Icc 1 (X / 2), G (2 * k) := sum_le_sum hterm
      _ = ∑ n ∈ (Icc 1 (X / 2)).image (fun k : ℕ => 2 * k), G n :=
          (sum_image (fun a ha b hb h => hinj ha hb h)).symm
      _ ≤ (Icc 1 X).sum G :=
          sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => G_nonneg n)
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  rw [Rat.cast_div, Rat.cast_sum] at hR
  push_cast at hR
  rw [Rat.cast_sum]
  exact hR

/-- The partial sum of consecutive-divisor ratios has order `X log X`,
with positive two-sided constants. This is weaker than the precise
asymptotic equivalent requested in question 2 of Erdős problem 673. -/
theorem G_mean_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c₁ * X * Real.log X ≤ (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ∧
        (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ≤ c₂ * X * Real.log X := by
  refine ⟨1 / 16, 2, by norm_num, by norm_num, 256, fun X hX => ?_⟩
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hXpos : (0 : ℝ) < X := by
    have : (256 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hlogX : 8 * Real.log 2 ≤ Real.log X := by
    have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [← h256]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  constructor
  · -- lower bound through the even terms
    set Y : ℕ := X / 2 with hYdef
    have hY1 : 1 ≤ Y := by omega
    have hYX : (X : ℝ) / 4 ≤ Y := by
      have h2 : X ≤ 2 * Y + 1 := by omega
      have h2' : (X : ℝ) ≤ 2 * Y + 1 := by exact_mod_cast h2
      have hY1' : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
      linarith
    have hlogY : Real.log X - 2 * Real.log 2 ≤ Real.log Y := by
      have hX4 : (0 : ℝ) < X / 4 := by positivity
      have h := Real.log_le_log hX4 hYX
      rw [Real.log_div hXpos.ne' (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
      push_cast at h
      linarith
    have hkey : Real.log X / 2 ≤ Real.log Y - 1 := by linarith
    have hlogXnn : 0 ≤ Real.log X := by linarith
    have hprod : (X : ℝ) / 4 * (Real.log X / 2) ≤ Y * (Real.log Y - 1) :=
      mul_le_mul hYX hkey (by positivity) (by positivity)
    have hT := sum_card_divisors_ge Y
    have hG := sum_card_divisors_half_le_sum_G X
    rw [← hYdef] at hG
    calc 1 / 16 * (X : ℝ) * Real.log X = (X / 4 * (Real.log X / 2)) / 2 := by ring
      _ ≤ (Y * (Real.log Y - 1)) / 2 := by linarith
      _ = (Y * Real.log Y - Y) / 2 := by ring
      _ ≤ (∑ k ∈ Icc 1 Y, (k.divisors.card : ℝ)) / 2 := by linarith
      _ ≤ _ := hG
  · -- upper bound through `G ≤ τ`
    have hterm : ∀ n ∈ Icc 1 X, ((G n : ℚ) : ℝ) ≤ (n.divisors.card : ℝ) := by
      intro n hn
      exact_mod_cast G_le_tau n (mem_Icc.mp hn).1
    have hsum : (((Icc 1 X).sum G : ℚ) : ℝ) ≤ ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) := by
      push_cast
      exact sum_le_sum hterm
    have hU := sum_card_divisors_le X
    have hone : 1 ≤ Real.log X := by linarith
    have hXX : (X : ℝ) * 1 ≤ X * Real.log X :=
      mul_le_mul_of_nonneg_left hone hXpos.le
    calc (((Icc 1 X).sum G : ℚ) : ℝ) ≤ ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) := hsum
      _ ≤ X * (1 + Real.log X) := hU
      _ ≤ 2 * X * Real.log X := by linarith

end MeanOrder

end ErdosCandidates.E673


