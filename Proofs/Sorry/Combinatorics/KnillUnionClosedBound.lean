/-
# Union-closed sets: Knill's logarithmic frequency bound

## Source

* MathOverflow question 219638, "Proposals for polymath projects" (Gil Kalai),
  answer 227478 by Dominic van der Zypen (2016-01-02):
  https://mathoverflow.net/a/227478 . Verbatim:
  "A conjecture that can be stated in so simple terms that it is hard to classify,
  is Frankl's Union-Closed Sets Conjecture. It would be fantastic to see this solved."
* Frankl's conjecture (open): every finite union-closed family containing a nonempty
  set has an element lying in at least half of its members. Gilmer (arXiv 2211.09055)
  and follow-ups give a constant fraction (about 0.38).
* Target (known result): E. Knill, "Graph generated union-closed families of sets",
  arXiv math/9409215 (1994): every union-closed family `F` of `m` sets with a nonempty
  member has an element lying in at least `(m - 1) / log₂ m` members.
  Warm-up (Sarvate–Renaud): if `F` contains a set of size one or two, one of its elements
  lies in at least half of the members.
* Date recorded: 2026-10-21. Status: proved in the literature (Knill 1994;
  Sarvate–Renaud 1989); Frankl's conjecture itself remains open and is NOT stated here.

## Proof outline (formalized below, sorry-free)

Choose a transversal `S` (meeting every nonempty member) of minimum size; each `x ∈ S` has a
private witness `A_x ∈ F` with `A_x ∩ S = {x}`. Unions of witnesses inject the `2 ^ |S| - 1`
nonempty subsets of `S` into nonempty members, and double counting through `S` gives
`m' ≤ |S| · max freq`. The `|F|` form uses `(n - 1) log (n + 1) ≤ n log n` when `∅ ∉ F`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.KnillUnionClosedBound

variable {α : Type*} [DecidableEq α]

/-- A finite family `F` of finite sets is *union-closed* if `A ∪ B ∈ F` whenever
`A, B ∈ F`. -/
def IsUnionClosed (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- The frequency of `x` in `F`: the number of members of `F` containing `x`. -/
def freq (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter (x ∈ ·)).card

/-- The number of nonempty members of `F`. -/
def numNonempty (F : Finset (Finset α)) : ℕ :=
  (F.filter (·.Nonempty)).card

/-- Union-closedness of a finite family is decidable (bounded quantifiers over `F`). -/
instance (F : Finset (Finset α)) : Decidable (IsUnionClosed F) := by
  unfold IsUnionClosed; infer_instance

example : IsUnionClosed ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) := by decide
example : ¬ IsUnionClosed ({{0}, {1}} : Finset (Finset ℕ)) := by decide
example : freq ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) 0 = 2 := by decide
example : freq ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) 2 = 0 := by decide
example : numNonempty ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) = 3 := by decide
example : numNonempty ({{0}, {1}, {0, 1}} : Finset (Finset ℕ)) = 3 := by decide

/-! Non-vacuity: the hypotheses of `knill`, `knill_nat` and the Sarvate–Renaud lemmas hold
jointly on concrete families (with and without the empty set). -/
example : IsUnionClosed ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) ∧
    (∃ A ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)), A.Nonempty) ∧
    ({0, 1} : Finset ℕ) ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) :=
  ⟨by decide, ⟨{0}, by decide, ⟨0, by decide⟩⟩, by decide⟩
example : IsUnionClosed ({{0}, {1}, {0, 1}} : Finset (Finset ℕ)) ∧
    (∃ A ∈ ({{0}, {1}, {0, 1}} : Finset (Finset ℕ)), A.Nonempty) ∧
    ({0} : Finset ℕ) ∈ ({{0}, {1}, {0, 1}} : Finset (Finset ℕ)) :=
  ⟨by decide, ⟨{0}, by decide, ⟨0, by decide⟩⟩, by decide⟩

/-- A union-closed family is closed under finite nonempty unions. -/
theorem IsUnionClosed.sup_mem {F : Finset (Finset α)} (hU : IsUnionClosed F) {ι : Type*}
    {T : Finset ι} (hT : T.Nonempty) {g : ι → Finset α} (hg : ∀ i ∈ T, g i ∈ F) :
    T.sup g ∈ F := by
  have hsc : SupClosed (F : Set (Finset α)) := fun A hA B hB => hU A hA B hB
  exact hsc.finsetSup_mem hT hg

/-- Minimal transversal: there is `S` meeting every nonempty member of `F` such that every
`x ∈ S` has a *private witness* `A ∈ F` with `A ∩ S = {x}`. -/
theorem exists_transversal_private (F : Finset (Finset α)) :
    ∃ S : Finset α, (∀ A ∈ F, A.Nonempty → (A ∩ S).Nonempty) ∧
      ∀ x ∈ S, ∃ A ∈ F, x ∈ A ∧ ∀ y ∈ S, y ∈ A → y = x := by
  classical
  let U : Finset α := F.sup id
  let C : Finset (Finset α) :=
    U.powerset.filter (fun T => ∀ A ∈ F, A.Nonempty → (A ∩ T).Nonempty)
  have hUC : U ∈ C := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset_self U, ?_⟩
    rintro A hA ⟨a, ha⟩
    exact ⟨a, Finset.mem_inter.2 ⟨ha, Finset.mem_sup.2 ⟨A, hA, ha⟩⟩⟩
  obtain ⟨S, hSC, hmin⟩ := Finset.exists_min_image C Finset.card ⟨U, hUC⟩
  obtain ⟨hSU, hStr⟩ := Finset.mem_filter.1 hSC
  refine ⟨S, hStr, fun x hx => ?_⟩
  have hnot : S.erase x ∉ C := by
    intro hmem
    have hle := hmin _ hmem
    have hlt := Finset.card_erase_lt_of_mem hx
    omega
  have hsub : S.erase x ∈ U.powerset :=
    Finset.mem_powerset.2 ((Finset.erase_subset x S).trans (Finset.mem_powerset.1 hSU))
  have hnot' : ¬ ∀ A ∈ F, A.Nonempty → (A ∩ S.erase x).Nonempty := fun h =>
    hnot (Finset.mem_filter.2 ⟨hsub, h⟩)
  push Not at hnot'
  obtain ⟨A, hA, hAne, hAe⟩ := hnot'
  have hpriv : ∀ y ∈ S, y ∈ A → y = x := by
    intro y hy hyA
    by_contra hyx
    have : y ∈ A ∩ S.erase x := Finset.mem_inter.2 ⟨hyA, Finset.mem_erase.2 ⟨hyx, hy⟩⟩
    rw [hAe] at this
    simp at this
  obtain ⟨y, hy⟩ := hStr A hA hAne
  obtain ⟨hyA, hyS⟩ := Finset.mem_inter.1 hy
  have hyx : y = x := hpriv y hyS hyA
  exact ⟨A, hA, hyx ▸ hyA, hpriv⟩

/-- **Knill's bound, natural-number form** (Knill 1994, arXiv math/9409215).
If `F` is union-closed and has a nonempty member, then with `m'` the number of nonempty
members there are an element `x` and a natural number `s` (the size of a minimal transversal)
with `2 ^ s ≤ m' + 1` and `m' ≤ s * freq F x`; i.e. some element lies in at least
`m' / log₂ (m' + 1)` members. -/
theorem knill_nat (F : Finset (Finset α)) (hU : IsUnionClosed F)
    (hne : ∃ A ∈ F, A.Nonempty) :
    ∃ (x : α) (s : ℕ), 2 ^ s ≤ numNonempty F + 1 ∧ numNonempty F ≤ s * freq F x := by
  classical
  obtain ⟨S, hStr, hwit⟩ := exists_transversal_private F
  choose! g hgF hgx hgu using hwit
  -- the union of the private witnesses of `T ⊆ S` meets `S` exactly in `T`
  have htrace : ∀ T ⊆ S, ∀ y ∈ S, y ∈ T.sup g ↔ y ∈ T := by
    intro T hTS y hy
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨v, hv, hyv⟩
      rw [hgu v (hTS hv) y hy hyv]
      exact hv
    · intro hyT
      exact ⟨y, hyT, hgx y hy⟩
  -- injection of nonempty subsets of `S` into nonempty members of `F`
  have hinj : (S.powerset.filter (·.Nonempty)).card ≤ numNonempty F := by
    refine Finset.card_le_card_of_injOn (fun T => T.sup g) ?_ ?_
    · intro T hT
      obtain ⟨hTS, hTne⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hT)
      have hTS' := Finset.mem_powerset.1 hTS
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hU.sup_mem hTne fun i hi => hgF i (hTS' hi), ?_⟩)
      obtain ⟨t, ht⟩ := hTne
      exact ⟨t, (htrace T hTS' t (hTS' ht)).2 ht⟩
    · intro T₁ hT₁ T₂ hT₂ heq
      have heq' : T₁.sup g = T₂.sup g := heq
      have h₁ := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hT₁)).1
      have h₂ := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hT₂)).1
      ext y
      constructor
      · intro hy
        have hyS := h₁ hy
        rw [← htrace T₂ h₂ y hyS, ← heq', htrace T₁ h₁ y hyS]
        exact hy
      · intro hy
        have hyS := h₂ hy
        rw [← htrace T₁ h₁ y hyS, heq', htrace T₂ h₂ y hyS]
        exact hy
  have hpow : (S.powerset.filter (·.Nonempty)).card = 2 ^ S.card - 1 := by
    have hfe : S.powerset.filter (·.Nonempty) = S.powerset.erase ∅ := by
      ext T
      simp [Finset.nonempty_iff_ne_empty, and_comm]
    rw [hfe, Finset.card_erase_of_mem (Finset.empty_mem_powerset S), Finset.card_powerset]
  have h2s : 2 ^ S.card ≤ numNonempty F + 1 := by
    have h1 : 1 ≤ 2 ^ S.card := Nat.one_le_two_pow
    omega
  -- double counting through the transversal
  have hcount : numNonempty F ≤ ∑ x ∈ S, freq F x := by
    have hsub : F.filter (·.Nonempty) ⊆ S.biUnion (fun x => F.filter (x ∈ ·)) := by
      intro A hA
      obtain ⟨hAF, hAne⟩ := Finset.mem_filter.1 hA
      obtain ⟨x, hx⟩ := hStr A hAF hAne
      obtain ⟨hxA, hxS⟩ := Finset.mem_inter.1 hx
      exact Finset.mem_biUnion.2 ⟨x, hxS, Finset.mem_filter.2 ⟨hAF, hxA⟩⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hSne : S.Nonempty := by
    obtain ⟨A, hAF, hAne⟩ := hne
    obtain ⟨x, hx⟩ := hStr A hAF hAne
    exact ⟨x, (Finset.mem_inter.1 hx).2⟩
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_max_image S (freq F) hSne
  refine ⟨x₀, S.card, h2s, hcount.trans ?_⟩
  simpa using Finset.sum_le_card_nsmul S (freq F) (freq F x₀) hx₀

/-- **Sarvate–Renaud, two-element case.** If a union-closed family `F` contains `{x, y}`, then
`|F| ≤ freq F x + freq F y`: the map `A ↦ A ∪ {x, y}` injects the members avoiding both `x`
and `y` into the members containing both. -/
theorem card_le_freq_add_freq_of_pair_mem (F : Finset (Finset α)) (hU : IsUnionClosed F)
    {x y : α} (hxy : {x, y} ∈ F) : F.card ≤ freq F x + freq F y := by
  classical
  let Fx : Finset (Finset α) := F.filter (x ∈ ·)
  let Fy : Finset (Finset α) := F.filter (y ∈ ·)
  have hsplit : (F.filter (fun A => x ∈ A ∨ y ∈ A)).card
      + (F.filter (fun A => ¬ (x ∈ A ∨ y ∈ A))).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  have hunion : F.filter (fun A => x ∈ A ∨ y ∈ A) = Fx ∪ Fy := Finset.filter_or _ _ _
  have hinter : Fx ∩ Fy = F.filter (fun A => x ∈ A ∧ y ∈ A) := (Finset.filter_and _ _ _).symm
  have hN : (F.filter (fun A => ¬ (x ∈ A ∨ y ∈ A))).card ≤ (Fx ∩ Fy).card := by
    rw [hinter]
    refine Finset.card_le_card_of_injOn (fun A => A ∪ {x, y}) ?_ ?_
    · intro A hA
      obtain ⟨hAF, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hA)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hU A hAF _ hxy, ?_, ?_⟩) <;> simp
    · intro A hA B hB hAB
      have hdisj : ∀ C ∈ (F.filter (fun A => ¬ (x ∈ A ∨ y ∈ A)) : Set (Finset α)),
          Disjoint C {x, y} := by
        intro C hC
        obtain ⟨-, hC⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hC)
        rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
        tauto
      have hAB' : A ∪ {x, y} = B ∪ {x, y} := hAB
      rw [← Finset.union_sdiff_cancel_right (hdisj A hA),
        ← Finset.union_sdiff_cancel_right (hdisj B hB), hAB']
  have hui := Finset.card_union_add_card_inter Fx Fy
  have hfx : freq F x = Fx.card := rfl
  have hfy : freq F y = Fy.card := rfl
  rw [hunion] at hsplit
  omega

/-- **Sarvate–Renaud.** If a union-closed family contains a set `{x, y}` of size one or two,
then one of its elements lies in at least half of the members of `F`. -/
theorem exists_mem_pair_card_le_two_mul_freq (F : Finset (Finset α)) (hU : IsUnionClosed F)
    {x y : α} (hxy : {x, y} ∈ F) :
    ∃ z ∈ ({x, y} : Finset α), F.card ≤ 2 * freq F z := by
  have h := card_le_freq_add_freq_of_pair_mem F hU hxy
  rcases le_total (freq F x) (freq F y) with hle | hle
  · exact ⟨y, by simp, by omega⟩
  · exact ⟨x, by simp, by omega⟩

/-- **Sarvate–Renaud, singleton case.** If a union-closed family contains `{x}`, then `x` lies
in at least half of the members of `F`. -/
theorem card_le_two_mul_freq_of_singleton_mem (F : Finset (Finset α)) (hU : IsUnionClosed F)
    {x : α} (hx : {x} ∈ F) : F.card ≤ 2 * freq F x := by
  have hpair : ({x, x} : Finset α) ∈ F := by simpa using hx
  have h := card_le_freq_add_freq_of_pair_mem F hU hpair
  omega

/-- Elementary inequality behind the passage from `log₂ (|F| + 1)` to `log₂ |F|`:
for `1 ≤ n`, `(n - 1) log (n + 1) ≤ n log n`. -/
theorem sub_one_mul_log_succ_le (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 1) * Real.log (n + 1) ≤ n * Real.log n := by
  rcases Nat.eq_or_lt_of_le hn with h1 | h2
  · subst h1; norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  -- `n (log (n + 1) - log n) ≤ 1`
  have hdiff : (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 := by
    have hq : (0 : ℝ) < (n + 1) / n := by positivity
    have hlog := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div (by positivity) hn0.ne'] at hlog
    have hfrac : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    rw [hfrac] at hlog
    calc (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ n * (1 / n) :=
          mul_le_mul_of_nonneg_left hlog hn0.le
      _ = 1 := by field_simp
  -- `1 ≤ log (n + 1)` since `e < 3 ≤ n + 1`
  have hone : 1 ≤ Real.log (n + 1) := by
    have he : Real.exp 1 < (n : ℝ) + 1 := by
      linarith [Real.exp_one_lt_d9]
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2 he).le
  nlinarith [hdiff, hone]

/-- `log₂` form of `sub_one_mul_log_succ_le`. -/
theorem sub_one_mul_logb_succ_le (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 1) * Real.logb 2 (n + 1) ≤ n * Real.logb 2 n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold Real.logb
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (sub_one_mul_log_succ_le n hn) hl2.le

/-- From `2 ^ s ≤ y` get `s ≤ log₂ y`. -/
theorem natCast_le_logb_two_of_two_pow_le {s y : ℕ} (h : 2 ^ s ≤ y) :
    (s : ℝ) ≤ Real.logb 2 y := by
  have hy : (0 : ℝ) < y := by exact_mod_cast (Nat.one_le_two_pow.trans h)
  rw [Real.le_logb_iff_rpow_le one_lt_two hy, Real.rpow_natCast]
  exact_mod_cast h

/-- **Knill's bound, nonempty-member form.** If `F` is union-closed with `m' ≥ 1` nonempty
members, some element lies in at least `m' / log₂ (m' + 1)` members. -/
theorem knill_real_numNonempty (F : Finset (Finset α)) (hU : IsUnionClosed F)
    (hne : ∃ A ∈ F, A.Nonempty) :
    ∃ x : α, (numNonempty F : ℝ) / Real.logb 2 (numNonempty F + 1) ≤ freq F x := by
  obtain ⟨x, s, h2s, hms⟩ := knill_nat F hU hne
  refine ⟨x, ?_⟩
  have hm1 : 1 ≤ numNonempty F := by
    obtain ⟨A, hAF, hAne⟩ := hne
    exact Finset.card_pos.2 ⟨A, Finset.mem_filter.2 ⟨hAF, hAne⟩⟩
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, zero_mul] at hms; omega
    · exact hpos
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hsL : (s : ℝ) ≤ Real.logb 2 ((numNonempty F : ℝ) + 1) := by
    simpa using natCast_le_logb_two_of_two_pow_le h2s
  have hmsR : (numNonempty F : ℝ) ≤ s * freq F x := by exact_mod_cast hms
  calc (numNonempty F : ℝ) / Real.logb 2 (numNonempty F + 1)
      ≤ (numNonempty F : ℝ) / s := div_le_div_of_nonneg_left (by positivity) hs0 hsL
    _ ≤ freq F x := by rw [div_le_iff₀ hs0]; linarith

/-- **Knill's bound** (Knill 1994, arXiv math/9409215; cited in MathOverflow 219638).
Every union-closed family `F` with a nonempty member has an element lying in at least
`(|F| - 1) / log₂ |F|` members. -/
theorem knill (F : Finset (Finset α)) (hU : IsUnionClosed F) (hne : ∃ A ∈ F, A.Nonempty) :
    ∃ x : α, ((F.card : ℝ) - 1) / Real.logb 2 F.card ≤ freq F x := by
  obtain ⟨x, s, h2s, hms⟩ := knill_nat F hU hne
  refine ⟨x, ?_⟩
  have hmN : numNonempty F ≤ F.card := Finset.card_filter_le _ _
  have hNm : F.card ≤ numNonempty F + 1 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun A : Finset α => A.Nonempty)
    have hle : (F.filter fun A : Finset α => ¬ A.Nonempty).card ≤ 1 := by
      refine Finset.card_le_one.2 fun A hA B hB => ?_
      rw [Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hA).2,
        Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hB).2]
    unfold numNonempty
    omega
  have hm1 : 1 ≤ numNonempty F := by
    obtain ⟨A, hAF, hAne⟩ := hne
    exact Finset.card_pos.2 ⟨A, Finset.mem_filter.2 ⟨hAF, hAne⟩⟩
  have hf0 : (0 : ℝ) ≤ freq F x := Nat.cast_nonneg _
  rcases (show F.card = 1 ∨ 2 ≤ F.card by omega) with hN | hN
  · simp [hN]
  have hN2 : (2 : ℝ) ≤ F.card := by exact_mod_cast hN
  have hL : 0 < Real.logb 2 (F.card : ℝ) := Real.logb_pos one_lt_two (by linarith)
  rw [div_le_iff₀ hL]
  have hmsR : (numNonempty F : ℝ) ≤ s * freq F x := by exact_mod_cast hms
  by_cases hcase : numNonempty F + 1 ≤ F.card
  · -- `∅ ∈ F`: then `|F| = m' + 1` and `s ≤ log₂ |F|`
    have hsL : (s : ℝ) ≤ Real.logb 2 (F.card : ℝ) :=
      natCast_le_logb_two_of_two_pow_le (h2s.trans hcase)
    have hNm' : (F.card : ℝ) - 1 ≤ numNonempty F := by
      have hc : (F.card : ℝ) ≤ numNonempty F + 1 := by exact_mod_cast hNm
      linarith
    calc (F.card : ℝ) - 1 ≤ s * freq F x := hNm'.trans hmsR
      _ ≤ Real.logb 2 (F.card : ℝ) * freq F x := mul_le_mul_of_nonneg_right hsL hf0
      _ = freq F x * Real.logb 2 (F.card : ℝ) := mul_comm _ _
  · -- `∅ ∉ F`: then `|F| = m'`, `s ≤ log₂ (|F| + 1)`, and the elementary inequality closes
    have hmeq : numNonempty F = F.card := by omega
    have hsL' : (s : ℝ) ≤ Real.logb 2 ((F.card : ℝ) + 1) := by
      simpa using natCast_le_logb_two_of_two_pow_le (hmeq ▸ h2s : 2 ^ s ≤ F.card + 1)
    have hNf : (F.card : ℝ) ≤ s * freq F x := by rw [← hmeq]; exact hmsR
    have hN1 : (0 : ℝ) ≤ (F.card : ℝ) - 1 := by linarith
    have hN0 : (0 : ℝ) < F.card := by linarith
    have hkey := sub_one_mul_logb_succ_le F.card (by omega)
    have hprod : (F.card : ℝ) * ((F.card : ℝ) - 1)
        ≤ (F.card : ℝ) * (freq F x * Real.logb 2 (F.card : ℝ)) := by
      calc (F.card : ℝ) * ((F.card : ℝ) - 1) = ((F.card : ℝ) - 1) * F.card := mul_comm _ _
        _ ≤ ((F.card : ℝ) - 1) * (s * freq F x) := mul_le_mul_of_nonneg_left hNf hN1
        _ = (((F.card : ℝ) - 1) * s) * freq F x := by ring
        _ ≤ (((F.card : ℝ) - 1) * Real.logb 2 ((F.card : ℝ) + 1)) * freq F x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsL' hN1) hf0
        _ ≤ ((F.card : ℝ) * Real.logb 2 (F.card : ℝ)) * freq F x :=
          mul_le_mul_of_nonneg_right hkey hf0
        _ = (F.card : ℝ) * (freq F x * Real.logb 2 (F.card : ℝ)) := by ring
    exact le_of_mul_le_mul_left hprod hN0

end Candidates.KnillUnionClosedBound
