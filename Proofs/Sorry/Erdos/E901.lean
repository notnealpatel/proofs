/-
  Erdős Problem #901 — Property B and m(n).
  Status: open.  Tier UC lemma mine (m(2) = 3, m(3) = 7 finite
  theorems; union-bound lower bound).

  Verbatim statement (`goof erdos fetch 901`, pulled 2026-08-05):

    "Let $m(n)$ be minimal such that there is an $n$-uniform
    hypergraph with $m(n)$ edges which is $3$-chromatic. Estimate
    $m(n)$."

  DB remarks: 3-chromatic = does not have Property B (no set meets
  every edge without containing one; equivalently not 2-colorable).
  Known: m(2) = 3, m(3) = 7, m(4) = 23.  Erdős: 2ⁿ ≪ m(n) ≪ n²2ⁿ
  ([Er63b], [Er64e]).  Beck [Be77], [Be78]: m(n) ≫ n^{1/3−o(1)}2ⁿ.
  Radhakrishnan–Srinivasan [RaSr00]: m(n) ≫ √(n/log n)·2ⁿ.  Pluhár
  [Pl09]: short proof of m(n) ≫ n^{1/4}2ⁿ.  Erdős–Lovász [ErLo75]
  speculate m(n) ≍ n·2ⁿ.

  Repo adjacency: shares the ProperColoring vocabulary with #836 and
  #834 sketches; `Proofs/Erdos/ErdosLovasz.lean` is the same paper.

  Mathlib inventory: no hypergraph 2-colorability; fresh defs
  (consistent with E836/E834 files).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E901

variable {V : Type*} [DecidableEq V]

/-- `TwoColorable H`: some 2-coloring leaves no edge monochromatic
    (= Property B). -/
def TwoColorable (H : Finset (Finset V)) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H, (∃ x ∈ e, c x = true) ∧ (∃ x ∈ e, c x = false)

/-- `mProperty n m`: there is an `n`-uniform hypergraph with `m`
    edges (on some finite vertex set, wlog `Fin (n*m)`) that is NOT
    2-colorable. -/
def mProperty (n m : ℕ) : Prop :=
  ∃ H : Finset (Finset (Fin (n * m))),
    H.card = m ∧ (∀ e ∈ H, e.card = n) ∧ ¬ TwoColorable H

/-- `mB n`: the minimal number of edges of a non-2-colorable
    `n`-uniform hypergraph — the `m(n)` of the problem.  `sInf` is
    honest for `n ≥ 1`: the complete `n`-uniform hypergraph on `2n−1`
    vertices is not 2-colorable (any 2-coloring has a color class of
    size ≥ n).  Support `Fin (n*m)` loses no generality: `m` edges of
    size `n` touch ≤ n·m vertices. -/
noncomputable def mB (n : ℕ) : ℕ := sInf {m : ℕ | mProperty n m}

section Helpers

open Finset

/-- The triangle `{{0,1},{1,2},{0,2}}` on `Fin 6` is not 2-colorable. -/
private lemma triangle_not_twoColorable :
    ¬ TwoColorable ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 6))) := by
  rintro ⟨c, h⟩
  have h01 := h {0, 1} (by simp)
  have h12 := h {1, 2} (by simp)
  have h02 := h {0, 2} (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
    at h01 h12 h02
  cases hc0 : c 0 <;> cases hc1 : c 1 <;> cases hc2 : c 2 <;> simp_all

/-- Membership in `mProperty n m` places the witness among the `m`-subsets of
    the `n`-subsets of `Fin (n * m)`. -/
private lemma mem_powersetCard_of_mProperty_witness {n m : ℕ}
    {H : Finset (Finset (Fin (n * m)))} (hcard : H.card = m) (hedge : ∀ e ∈ H, e.card = n) :
    H ∈ Finset.powersetCard m (Finset.powersetCard n (Finset.univ : Finset (Fin (n * m)))) := by
  rw [Finset.mem_powersetCard]
  refine ⟨fun e he => ?_, hcard⟩
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ e, hedge e he⟩

/-- Every `2`-uniform hypergraph with `m ≤ 2` edges on `Fin (2 * m)` is
    2-colorable (finite check). -/
private lemma not_mProperty_two_of_lt_three {m : ℕ} (hm : m < 3) : ¬ mProperty 2 m := by
  rintro ⟨H, hcard, hedge, hnot⟩
  apply hnot
  have hmem := mem_powersetCard_of_mProperty_witness hcard hedge
  unfold TwoColorable
  interval_cases m
  all_goals
    clear hnot hcard hedge
    revert H
    decide

/-- On a finite type, exactly `2 ^ (|V| - |e|)` colorings are constantly `b` on `e`. -/
private lemma card_filter_const_on [Fintype V] (e : Finset V) (b : Bool) :
    (univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = b)).card =
      2 ^ (Fintype.card V - e.card) := by
  have hset : univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = b) =
      Fintype.piFinset (fun x => if x ∈ e then ({b} : Finset Bool) else univ) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      by_cases hx : x ∈ e
      · simp [hx, h x hx]
      · simp [hx]
    · intro h x hx
      simpa [hx] using h x
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton, card_univ, Fintype.card_bool]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  rw [filter_not, card_sdiff, filter_mem_eq_inter, univ_inter, card_univ, inter_univ]

/-- Union bound: an `n`-uniform hypergraph (`2 ≤ n`) with at most `2 ^ (n - 1)` edges on a
    finite vertex type is 2-colorable. -/
private lemma twoColorable_of_card_le [Fintype V] {n : ℕ} (hn : 2 ≤ n)
    (H : Finset (Finset V)) (hedge : ∀ e ∈ H, e.card = n) (hm : H.card ≤ 2 ^ (n - 1)) :
    TwoColorable H := by
  rcases H.eq_empty_or_nonempty with hH | ⟨e0, he0⟩
  · exact ⟨fun _ => true, by simp [hH]⟩
  have hN : n ≤ Fintype.card V := by
    rw [← hedge e0 he0]; exact card_le_univ e0
  obtain ⟨v, -⟩ : e0.Nonempty := by rw [← card_pos, hedge e0 he0]; omega
  have hpow : 2 ^ Fintype.card V = 2 ^ (n - 1) * (2 * 2 ^ (Fintype.card V - n)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  let K := 2 ^ (Fintype.card V - n)
  let t : V → Bool := fun _ => true
  let f : V → Bool := fun _ => false
  have htf : t ≠ f := fun h => by simpa [t, f] using congrFun h v
  have hpair : ({t, f} : Finset (V → Bool)).card = 2 := card_pair htf
  let S : Finset V → Finset (V → Bool) := fun e =>
    univ.filter (fun c => (∀ x ∈ e, c x = true) ∨ (∀ x ∈ e, c x = false))
  have hS_card : ∀ e ∈ H, (S e \ {t, f}).card + 2 ≤ 2 * K := by
    intro e he
    have hsub : ({t, f} : Finset (V → Bool)) ⊆ S e := by
      intro c hc
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [S, t, f]
    have hSe : (S e).card ≤ 2 * K := by
      have hsplit : S e = univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = true) ∪
          univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = false) := by
        rw [← filter_or]
      rw [hsplit]
      calc _ ≤ _ := card_union_le _ _
        _ = K + K := by rw [card_filter_const_on, card_filter_const_on, hedge e he]
        _ = 2 * K := by ring
    have hsd := card_sdiff_add_card_eq_card hsub
    omega
  by_contra hnot
  have hcover : (univ : Finset (V → Bool)) ⊆ {t, f} ∪ H.biUnion (fun e => S e \ {t, f}) := by
    intro c _
    by_cases hc : c ∈ ({t, f} : Finset (V → Bool))
    · exact mem_union_left _ hc
    apply mem_union_right
    have hbad : ∃ e ∈ H, ¬((∃ x ∈ e, c x = true) ∧ (∃ x ∈ e, c x = false)) := by
      by_contra hall
      exact hnot ⟨c, fun e he => by_contra fun h => hall ⟨e, he, h⟩⟩
    obtain ⟨e, he, hmono⟩ := hbad
    rw [mem_biUnion]
    refine ⟨e, he, mem_sdiff.mpr ⟨?_, hc⟩⟩
    simp only [S, mem_filter, mem_univ, true_and]
    by_cases hA : ∃ x ∈ e, c x = true
    · left
      intro x hx
      by_contra hx'
      exact hmono ⟨hA, x, hx, by simpa using hx'⟩
    · right
      intro x hx
      by_contra hx'
      exact hA ⟨x, hx, by simpa using hx'⟩
  have hcard_univ : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool]
  have hle : 2 ^ Fintype.card V ≤ 2 + H.card * (2 * K - 2) := by
    rw [← hcard_univ]
    calc _ ≤ _ := card_le_card hcover
      _ ≤ ({t, f} : Finset (V → Bool)).card + (H.biUnion (fun e => S e \ {t, f})).card :=
          card_union_le _ _
      _ ≤ 2 + ∑ e ∈ H, (S e \ {t, f}).card := by
          rw [hpair]; gcongr; exact card_biUnion_le
      _ ≤ 2 + H.card • (2 * K - 2) := by
          gcongr
          exact sum_le_card_nsmul _ _ _ (fun e he => by have := hS_card e he; omega)
      _ = 2 + H.card * (2 * K - 2) := by rw [smul_eq_mul]
  have hK : 1 ≤ K := Nat.one_le_two_pow
  have hP : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨B, hB⟩ : ∃ B, 2 * K = B + 2 := ⟨2 * K - 2, by omega⟩
  rw [hB, Nat.add_sub_cancel] at hle
  rw [hB] at hpow
  have hmB : H.card * B ≤ 2 ^ (n - 1) * B := Nat.mul_le_mul_right B hm
  nlinarith

/-- For `2 ≤ n`, the complete `n`-uniform hypergraph on `2n - 1` vertices (embedded in
    `Fin (n * choose (2n-1) n)`) is not 2-colorable, witnessing
    `mProperty n (choose (2n-1) n)`. -/
private lemma mProperty_complete {n : ℕ} (hn : 2 ≤ n) :
    mProperty n ((2 * n - 1).choose n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h2n : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  rw [h2n]
  have hfit : 2 * k + 3 ≤ (k + 2) * (2 * k + 3).choose (k + 2) := by
    have h := Nat.add_one_mul_choose_eq (2 * k + 2) (k + 1)
    have hpos : 0 < (2 * k + 2).choose (k + 1) := Nat.choose_pos (by omega)
    calc 2 * k + 3 ≤ (2 * k + 2 + 1) * (2 * k + 2).choose (k + 1) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = (k + 2) * (2 * k + 3).choose (k + 2) := by rw [h, mul_comm]
  let S : Finset (Fin ((k + 2) * (2 * k + 3).choose (k + 2))) :=
    (univ : Finset (Fin (2 * k + 3))).map (Fin.castLEEmb hfit)
  have hS : S.card = 2 * k + 3 := by simp [S]
  refine ⟨S.powersetCard (k + 2), by rw [card_powersetCard, hS],
    fun e he => (mem_powersetCard.mp he).2, ?_⟩
  rintro ⟨c, hc⟩
  have hsplit := card_filter_add_card_filter_not (s := S) (fun x => c x = true)
  rw [hS] at hsplit
  by_cases hT : k + 2 ≤ (S.filter (fun x => c x = true)).card
  · obtain ⟨e, heS, hecard⟩ := exists_subset_card_eq hT
    have he : e ∈ S.powersetCard (k + 2) :=
      mem_powersetCard.mpr ⟨heS.trans (filter_subset _ _), hecard⟩
    obtain ⟨x, hx, hxf⟩ := (hc e he).2
    have hxt : c x = true := (mem_filter.mp (heS hx)).2
    rw [hxt] at hxf
    exact Bool.noConfusion hxf
  · have hF : k + 2 ≤ (S.filter (fun x => ¬ c x = true)).card := by omega
    obtain ⟨e, heS, hecard⟩ := exists_subset_card_eq hF
    have he : e ∈ S.powersetCard (k + 2) :=
      mem_powersetCard.mpr ⟨heS.trans (filter_subset _ _), hecard⟩
    obtain ⟨x, hx, hxt⟩ := (hc e he).1
    exact (mem_filter.mp (heS hx)).2 hxt

end Helpers

/-- `m(2) = 3`: the triangle {{a,b},{b,c},{a,c}} is not 2-colorable
    (some pair repeats a color), and any 2 edges are 2-colorable.
    -- PROVABLE (decide-scale; the encoding bookkeeping on
    `Fin (2*3)` is the only friction).  The quick first landing. -/
theorem mB_two : mB 2 = 3 := by
  have h3 : mProperty 2 3 := by
    refine ⟨{{0, 1}, {1, 2}, {0, 2}}, by decide, by decide, triangle_not_twoColorable⟩
  have hne : ({m : ℕ | mProperty 2 m} : Set ℕ).Nonempty := ⟨3, h3⟩
  refine le_antisymm (Nat.sInf_le h3) (not_lt.mp fun hlt => ?_)
  exact not_mProperty_two_of_lt_three hlt (Nat.sInf_mem hne)

/-- `m(3) = 7`: the Fano plane is the witness (7 edges, 3-uniform,
    not 2-colorable — cf. the E836 sketch's `fano`); minimality is a
    bounded but genuine finite theorem (every 3-uniform hypergraph
    with ≤ 6 edges is 2-colorable).
    -- PROVABLE (witness by decide; minimality via a bounded search /
    union-bound argument — Effort M, flagged as nontrivial). -/
theorem mB_three : mB 3 = 7 := by
  sorry

/-- `m(4) = 23` (Östergård's computation, reported in the DB): the
    heavy certified-search boundary; archived. -/
theorem mB_four : mB 4 = 23 := by
  sorry

/-- **Union-bound lower bound (the entry-point target)**:
    `2^{n-1} < m(n)` — a hypergraph with `m ≤ 2^{n-1}` edges is
    2-colorable.  Finite probabilistic argument: a uniformly random
    2-coloring makes each edge monochromatic with probability
    `2^{1-n}`; with `m ≤ 2^{n-1}` edges the expected number of
    monochromatic edges is ≤ 1, and strict inequality analysis (or
    the weighted counting over all 2^V colorings) yields a proper
    coloring.  Fully finite: count colorings, no measure theory.
    This is Erdős's [Er63b] bound; next door to the repo's
    ErdosLovasz counting style.  Effort M. -/
theorem union_bound_lower (n : ℕ) (hn : 2 ≤ n) : 2 ^ (n - 1) < mB n := by
  have hne : ({m : ℕ | mProperty n m} : Set ℕ).Nonempty := ⟨_, mProperty_complete hn⟩
  obtain ⟨H, hcard, hedge, hnot⟩ : mProperty n (mB n) := Nat.sInf_mem hne
  by_contra hle
  exact hnot (twoColorable_of_card_le hn H hedge (by omega))

/-- **Erdős's upper bound** ([Er64e]), archived: `m(n) ≪ n²·2ⁿ` —
    random construction.  Stated with explicit constant. -/
theorem erdos_upper :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → mB n ≤ C * n ^ 2 * 2 ^ n := by
  sorry

/-- **Radhakrishnan–Srinivasan** ([RaSr00]), archived:
    `m(n) ≫ √(n/log n)·2ⁿ`. -/
theorem radhakrishnan_srinivasan :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.sqrt (n / Real.log n) * 2 ^ n ≤ (mB n : ℝ) := by
  sorry

/-- Satisfiability sanity: the triangle (as 2-uniform hypergraph on 3
    vertices, embedded in `Fin 6`) is not 2-colorable.
    -- PROVABLE (decide). -/
example : ¬ TwoColorable
    ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 6))) :=
  triangle_not_twoColorable

end ErdosCandidates.E901

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB: "m(n) minimal ... n-uniform ... 3-chromatic."
   - DB values m(2)=3, m(3)=7, m(4)=23 match file theorems.
   - Bounds: 2^n << m(n) << n^2*2^n (Erdos), sqrt(n/log n)*2^n (R-S) match DB.
   - Erdos-Lovasz n*2^n speculation recorded in file header, matches DB.
   - Triangle non-2-colorability: triangle is odd cycle on 3 vertices, not
     2-colorable as a 2-uniform hypergraph (each edge needs both colors). Correct.
   - TwoColorable def correctly captures Property B; mProperty/mB correctly
     capture the negation. Lean types faithful.
   - union_bound_lower states 2^(n-1) < mB n, consistent with the standard
     first-moment bound from [Er63b].
-/
