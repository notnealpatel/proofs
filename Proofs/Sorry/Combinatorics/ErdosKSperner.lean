/-
# Erdős's k-Sperner theorem

## Source

* P. Erdős, "On a lemma of Littlewood and Offord", Bull. Amer. Math. Soc. 51 (1945),
  898–902 (the theorem is stated and proved there as the combinatorial core of the sharp
  Littlewood–Offord bound).
* K. Engel, *Sperner Theory*, Cambridge Univ. Press (1997), Chapter 1 (LYM form).

## Informal statement (verbatim from the target spec)

"If 𝒜 ⊆ 2^[n] contains no chain of k+1 distinct sets, then |𝒜| is at most the sum of the
k largest binomial coefficients C(n,i). Moreover Σ_{A∈𝒜} 1/C(n,|A|) ≤ k."

## Formalization notes (2026-10-21)

* "No chain of `k + 1` distinct sets" is stated as: every subfamily `𝒞 ⊆ 𝒜` that is a chain
  for `⊆` has `#𝒞 ≤ k`.
* "The sum of the `k` largest binomial coefficients `C(n, i)`" is `sumLargestChoose n k`,
  the maximum of `∑ i ∈ S, C(n, i)` over index sets `S ⊆ {0, …, n}` with `#S ≤ k`. This is
  the sum of the `k` largest entries of the row `C(n, 0), …, C(n, n)` (all of them when
  `n + 1 ≤ k`). Ground-truth checks follow the definition.
* Mathlib (checked with `leandoc`) has only the case `k = 1`:
  `IsAntichain.sperner` and `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`.
* Proof: peel off the maximal members (an antichain, LYM ≤ 1) and induct on `k` for the
  LYM form; then a fractional-knapsack threshold argument against the top `k` layers.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.ErdosKSperner

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Peeling step: the maximal members of a family form an antichain. -/
theorem isAntichain_maximals (𝒜 : Finset (Finset α)) :
    IsAntichain (· ⊆ ·)
      ((𝒜.filter fun A => ∀ B ∈ 𝒜, A ⊆ B → B = A : Finset (Finset α)) : Set (Finset α)) := by
  intro A hA B hB hAB hsub
  simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
  exact hAB (hA.2 B hB.1 hsub).symm

/-- Peeling step: removing the maximal members of `𝒜` shortens every chain. If every chain
in `𝒜` has at most `k + 1` members, every chain among the non-maximal members has at most
`k`. -/
theorem chain_card_le_of_not_maximal (𝒜 : Finset (Finset α)) (k : ℕ)
    (h : ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ k + 1) :
    ∀ 𝒞 ⊆ 𝒜.filter (fun A => ¬ ∀ B ∈ 𝒜, A ⊆ B → B = A),
      IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ k := by
  intro 𝒞 h𝒞 hchain
  rcases 𝒞.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  obtain ⟨c, hc, hcmax⟩ := 𝒞.exists_max_image card hne
  -- every member of the chain lies below `c`
  have hbelow : ∀ x ∈ 𝒞, x ⊆ c := by
    intro x hx
    by_cases hxc : x = c
    · exact hxc ▸ subset_rfl
    rcases hchain (mem_coe.2 hx) (mem_coe.2 hc) hxc with hxc' | hcx
    · exact hxc'
    · exact (eq_of_subset_of_card_le hcx (hcmax x hx)).symm ▸ subset_rfl
  have hcR := h𝒞 hc
  simp only [mem_filter, not_forall] at hcR
  obtain ⟨hc𝒜, B, hB, hcB, hBc⟩ := hcR
  have hBnot : B ∉ 𝒞 := fun hB𝒞 => hBc (subset_antisymm (hbelow B hB𝒞) hcB)
  have hins : insert B 𝒞 ⊆ 𝒜 := by
    refine insert_subset hB fun x hx => ?_
    exact (mem_filter.1 (h𝒞 hx)).1
  have hchain' : IsChain (· ⊆ ·) ((insert B 𝒞 : Finset (Finset α)) : Set (Finset α)) := by
    rw [coe_insert]
    refine hchain.insert fun x hx _ => Or.inr ((hbelow x hx).trans hcB)
  have hlong := h _ hins hchain'
  rw [card_insert_of_notMem hBnot] at hlong
  omega

/-- **LYM inequality for `k`-Sperner families.** If `𝒜 ⊆ 2^α` contains no chain of `k + 1`
distinct sets, then `∑_{A ∈ 𝒜} 1 / C(|α|, |A|) ≤ k`. -/
theorem sum_inv_choose_le_of_chain_card_le (k : ℕ) (𝒜 : Finset (Finset α))
    (h : ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ k) :
    ∑ A ∈ 𝒜, ((Fintype.card α).choose #A : ℚ)⁻¹ ≤ k := by
  induction k generalizing 𝒜 with
  | zero =>
    have hemp : 𝒜 = ∅ := by
      refine eq_empty_of_forall_notMem fun A hA => ?_
      have hone := h {A} (singleton_subset_iff.2 hA) (by simp [IsChain])
      simp at hone
    simp [hemp]
  | succ k ih =>
    rw [← sum_filter_add_sum_filter_not 𝒜 (fun A => ∀ B ∈ 𝒜, A ⊆ B → B = A)]
    have h1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ)
      (isAntichain_maximals 𝒜)
    have h2 := ih _ (chain_card_le_of_not_maximal 𝒜 k h)
    push_cast
    linarith

/-! ## The sum of the `k` largest binomial coefficients -/

/-- The sum of the `k` largest binomial coefficients in the row `C(n, 0), …, C(n, n)`:
the maximum of `∑ i ∈ S, C(n, i)` over index sets `S ⊆ {0, …, n}` with `#S ≤ k`
(when `n + 1 ≤ k` this is the whole row sum `2 ^ n`). -/
def sumLargestChoose (n k : ℕ) : ℕ :=
  ((range (n + 1)).powerset.filter (fun S => #S ≤ k)).sup fun S => ∑ i ∈ S, n.choose i

/-! Ground truth: row `n = 4` is `1, 4, 6, 4, 1`; row `n = 5` is `1, 5, 10, 10, 5, 1`;
row `n = 3` is `1, 3, 3, 1`. -/

example : sumLargestChoose 4 0 = 0 := by decide
example : sumLargestChoose 4 1 = 6 := by decide
example : sumLargestChoose 4 2 = 10 := by decide
example : sumLargestChoose 4 3 = 14 := by decide
example : sumLargestChoose 5 2 = 20 := by decide
example : sumLargestChoose 3 2 = 6 := by decide
example : sumLargestChoose 3 7 = 8 := by decide

/-- Exchange step: for `k ≤ n + 1` there is a set `S` of exactly `k` indices in `{0, …, n}`
such that every binomial coefficient `C(n, j)` with `j ∉ S` is at most every `C(n, i)` with
`i ∈ S` (the "top `k` layers"). -/
theorem exists_top_layers (n k : ℕ) (hk : k ≤ n + 1) :
    ∃ S ⊆ range (n + 1), #S = k ∧
      ∀ i ∈ S, ∀ j ∈ range (n + 1), j ∉ S → n.choose j ≤ n.choose i := by
  have hne : ((range (n + 1)).powersetCard k).Nonempty := by
    rw [powersetCard_nonempty, card_range]
    exact hk
  obtain ⟨S, hS, hmax⟩ := ((range (n + 1)).powersetCard k).exists_max_image
    (fun S => ∑ i ∈ S, n.choose i) hne
  rw [mem_powersetCard] at hS
  refine ⟨S, hS.1, hS.2, fun i hi j hj hjS => ?_⟩
  by_contra hle'
  have hlt : n.choose i < n.choose j := not_le.1 hle'
  have hjE : j ∉ S.erase i := fun h => hjS (mem_of_mem_erase h)
  have hmem : insert j (S.erase i) ∈ (range (n + 1)).powersetCard k := by
    rw [mem_powersetCard, card_insert_of_notMem hjE, card_erase_of_mem hi]
    refine ⟨insert_subset hj ((erase_subset i S).trans hS.1), ?_⟩
    have hSpos : 1 ≤ #S := card_pos.2 ⟨i, hi⟩
    omega
  have hle := hmax _ hmem
  rw [sum_insert hjE] at hle
  have hsplit := add_sum_erase S (fun i => n.choose i) hi
  omega

omit [DecidableEq α] in
/-- Fractional-knapsack step. Let `S ⊆ {0, …, n}` (`n = |α|`) with `#S = k` and a threshold
`t` with `C(n, r) ≤ t` for `r ∉ S` and `t ≤ C(n, r)` for `r ∈ S`. If
`∑_{A ∈ 𝒜} 1 / C(n, |A|) ≤ k` then `#𝒜 ≤ ∑_{r ∈ S} C(n, r)`. -/
theorem card_le_sum_choose_of_threshold (𝒜 : Finset (Finset α)) (S : Finset ℕ) (t k : ℕ)
    (hSrange : S ⊆ range (Fintype.card α + 1)) (hS : #S = k)
    (hlym : ∑ A ∈ 𝒜, ((Fintype.card α).choose #A : ℚ)⁻¹ ≤ k)
    (hout : ∀ r ∈ range (Fintype.card α + 1), r ∉ S → (Fintype.card α).choose r ≤ t)
    (hin : ∀ r ∈ S, t ≤ (Fintype.card α).choose r) :
    #𝒜 ≤ ∑ r ∈ S, (Fintype.card α).choose r := by
  set n := Fintype.card α with hn
  have hpos : ∀ r, r ≤ n → (0 : ℚ) < n.choose r := fun r hr => by
    exact_mod_cast Nat.choose_pos hr
  have hAle : ∀ A : Finset α, #A ≤ n := fun A => card_le_univ A
  -- split `1 = t / C + (1 - t / C)` over `𝒜`
  have hsplit : (#𝒜 : ℚ) = t * ∑ A ∈ 𝒜, ((n.choose #A : ℚ))⁻¹
      + ∑ A ∈ 𝒜, (1 - t * ((n.choose #A : ℚ))⁻¹) := by
    rw [mul_sum, ← sum_add_distrib]
    simp
  -- layers outside `S` contribute nonpositively
  have hdrop : ∑ A ∈ 𝒜, (1 - t * ((n.choose #A : ℚ))⁻¹)
      ≤ ∑ A ∈ 𝒜.filter (fun A => #A ∈ S), (1 - t * ((n.choose #A : ℚ))⁻¹) := by
    rw [← sum_filter_add_sum_filter_not 𝒜 (fun A => #A ∈ S)]
    have hneg : ∑ A ∈ 𝒜.filter (fun A => #A ∉ S), (1 - t * ((n.choose #A : ℚ))⁻¹) ≤ 0 := by
      refine sum_nonpos fun A hA => ?_
      have hAS := (mem_filter.1 hA).2
      have hc := hpos #A (hAle A)
      have hct : (n.choose #A : ℚ) ≤ t := by
        exact_mod_cast hout #A (mem_range.2 (Nat.lt_succ_of_le (hAle A))) hAS
      rw [sub_nonpos, ← div_eq_mul_inv, le_div_iff₀ hc, one_mul]
      exact hct
    linarith
  -- each layer inside `S` contributes at most `C(n, r) - t`
  have hfib : ∑ A ∈ 𝒜.filter (fun A => #A ∈ S), (1 - t * ((n.choose #A : ℚ))⁻¹)
      ≤ ∑ r ∈ S, ((n.choose r : ℚ) - t) := by
    rw [← sum_fiberwise_of_maps_to (s := 𝒜.filter (fun A => #A ∈ S)) (t := S) (g := card)
      (fun A hA => (mem_filter.1 hA).2)]
    refine sum_le_sum fun r hr => ?_
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (mem_range.1 (hSrange hr))
    have hc := hpos r hr'
    have hconst : ∑ A ∈ (𝒜.filter (fun A => #A ∈ S)).filter (fun A => #A = r),
        (1 - t * ((n.choose #A : ℚ))⁻¹)
        = #((𝒜.filter (fun A => #A ∈ S)).filter (fun A => #A = r)) *
          (1 - t * ((n.choose r : ℚ))⁻¹) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl fun A hA => by rw [(mem_filter.1 hA).2]
    have hcard : (#((𝒜.filter (fun A => #A ∈ S)).filter (fun A => #A = r)) : ℚ)
        ≤ n.choose r := by
      exact_mod_cast Set.Sized.card_le fun A hA => (mem_filter.1 (mem_coe.1 hA)).2
    have hfac : 0 ≤ 1 - t * ((n.choose r : ℚ))⁻¹ := by
      have htc : (t : ℚ) ≤ n.choose r := by exact_mod_cast hin r hr
      rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hc, one_mul]
      exact htc
    rw [hconst]
    calc _ ≤ (n.choose r : ℚ) * (1 - t * ((n.choose r : ℚ))⁻¹) :=
          mul_le_mul_of_nonneg_right hcard hfac
      _ = (n.choose r : ℚ) - t := by field_simp
  have hsumS : ∑ r ∈ S, ((n.choose r : ℚ) - t) = ∑ r ∈ S, (n.choose r : ℚ) - k * t := by
    rw [sum_sub_distrib, sum_const, hS, nsmul_eq_mul]
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  have htk : (t : ℚ) * ∑ A ∈ 𝒜, ((n.choose #A : ℚ))⁻¹ ≤ t * k :=
    mul_le_mul_of_nonneg_left hlym ht0
  have hmain : (#𝒜 : ℚ) ≤ ∑ r ∈ S, (n.choose r : ℚ) := by
    rw [hsplit]
    linarith
  exact_mod_cast hmain

/-- **Erdős's k-Sperner theorem** (for an arbitrary finite ground set `α`, `n = |α|`). If
`𝒜 ⊆ 2^α` contains no chain of `k + 1` distinct sets, then `#𝒜` is at most the sum of the
`k` largest binomial coefficients `C(n, i)`. -/
theorem card_le_sumLargestChoose_of_chain_card_le (k : ℕ) (𝒜 : Finset (Finset α))
    (h : ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ k) :
    #𝒜 ≤ sumLargestChoose (Fintype.card α) k := by
  set n := Fintype.card α with hn
  by_cases hk : n + 1 ≤ k
  · -- all layers fit: compare with the whole power set
    have hmem : range (n + 1) ∈ (range (n + 1)).powerset.filter (fun S => #S ≤ k) := by
      rw [mem_filter, card_range]
      exact ⟨mem_powerset_self _, hk⟩
    calc #𝒜 ≤ #(univ : Finset (Finset α)) := card_le_univ 𝒜
      _ = ∑ i ∈ range (n + 1), n.choose i := by
          rw [card_univ, Fintype.card_finset, Nat.sum_range_choose]
      _ ≤ sumLargestChoose n k :=
          le_sup (f := fun S => ∑ i ∈ S, n.choose i) hmem
  · obtain ⟨S, hSrange, hScard, hSexch⟩ := exists_top_layers n k (by omega)
    set t := ((range (n + 1)) \ S).sup (fun j => n.choose j) with ht
    have hout : ∀ r ∈ range (n + 1), r ∉ S → n.choose r ≤ t := fun r hr hrS =>
      le_sup (f := fun j => n.choose j) (mem_sdiff.2 ⟨hr, hrS⟩)
    have hin : ∀ r ∈ S, t ≤ n.choose r := fun r hr =>
      Finset.sup_le fun j hj => hSexch r hr j (mem_sdiff.1 hj).1 (mem_sdiff.1 hj).2
    have hmem : S ∈ (range (n + 1)).powerset.filter (fun S => #S ≤ k) := by
      rw [mem_filter, mem_powerset]
      exact ⟨hSrange, hScard.le⟩
    calc #𝒜 ≤ ∑ r ∈ S, n.choose r :=
          card_le_sum_choose_of_threshold 𝒜 S t k hSrange hScard
            (sum_inv_choose_le_of_chain_card_le k 𝒜 h) hout hin
      _ ≤ sumLargestChoose n k := le_sup (f := fun S => ∑ i ∈ S, n.choose i) hmem

omit [Fintype α] in
/-- A family contained in the union of the layers indexed by `S` has no chain with more than
`#S` members (members of a chain have pairwise distinct sizes). -/
theorem chain_card_le_of_subset_layers (S : Finset ℕ) (𝒜 : Finset (Finset α))
    (h𝒜 : ∀ A ∈ 𝒜, #A ∈ S) :
    ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ #S := by
  intro 𝒞 h𝒞 hchain
  refine card_le_card_of_injOn card (fun A hA => h𝒜 A (h𝒞 (mem_coe.1 hA))) ?_
  intro A hA B hB hAB
  by_contra hne
  rcases hchain hA hB hne with hsub | hsub
  · exact hne (eq_of_subset_of_card_le hsub hAB.ge)
  · exact hne (eq_of_subset_of_card_le hsub hAB.le).symm

/-- **Sharpness of Erdős's k-Sperner bound.** Some family `𝒜 ⊆ 2^α` with no chain of `k + 1`
distinct sets has exactly `sumLargestChoose |α| k` members (the union of the `k` largest
layers). In particular the bound is attained and the hypothesis is satisfiable. -/
theorem exists_card_eq_sumLargestChoose (k : ℕ) :
    ∃ 𝒜 : Finset (Finset α),
      (∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset α)) → #𝒞 ≤ k) ∧
        #𝒜 = sumLargestChoose (Fintype.card α) k := by
  set n := Fintype.card α with hn
  have hne : ((range (n + 1)).powerset.filter (fun S => #S ≤ k)).Nonempty :=
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  obtain ⟨S, hS, hSsup⟩ := exists_mem_eq_sup _ hne fun S => ∑ i ∈ S, n.choose i
  rw [mem_filter, mem_powerset] at hS
  refine ⟨univ.filter (fun A : Finset α => #A ∈ S), fun 𝒞 h𝒞 hchain => ?_, ?_⟩
  · exact (chain_card_le_of_subset_layers S _ (fun A hA => (mem_filter.1 hA).2) 𝒞 h𝒞
      hchain).trans hS.2
  · rw [sumLargestChoose, hSsup,
      card_eq_sum_card_fiberwise (s := univ.filter (fun A : Finset α => #A ∈ S)) (f := card)
        (t := S) (fun A hA => (mem_filter.1 (mem_coe.1 hA)).2)]
    refine sum_congr rfl fun r hr => ?_
    have hlayer : (univ.filter (fun A : Finset α => #A ∈ S)).filter (fun A => #A = r)
        = powersetCard r univ := by
      ext A
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard_univ]
      constructor
      · exact fun hA => hA.2
      · exact fun hA => ⟨hA ▸ hr, hA⟩
    rw [hlayer, card_powersetCard, card_univ]

/-! ## The statements on `2^[n]` -/

/-- **Erdős's k-Sperner theorem (1945).** If `𝒜 ⊆ 2^[n]` contains no chain of `k + 1`
distinct sets, then `|𝒜|` is at most the sum of the `k` largest binomial coefficients
`C(n, i)`. -/
theorem erdos_k_sperner (n k : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h : ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset (Fin n))) → #𝒞 ≤ k) :
    #𝒜 ≤ sumLargestChoose n k := by
  simpa using card_le_sumLargestChoose_of_chain_card_le k 𝒜 h

/-- **LYM inequality for k-Sperner families.** If `𝒜 ⊆ 2^[n]` contains no chain of `k + 1`
distinct sets, then `∑_{A ∈ 𝒜} 1 / C(n, |A|) ≤ k`. -/
theorem erdos_k_sperner_lym (n k : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h : ∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset (Fin n))) → #𝒞 ≤ k) :
    ∑ A ∈ 𝒜, ((n.choose #A : ℚ))⁻¹ ≤ k := by
  simpa using sum_inv_choose_le_of_chain_card_le k 𝒜 h

/-- **Sharpness on `2^[n]`.** The union of the `k` largest layers of `2^[n]` has no chain of
`k + 1` distinct sets and has exactly `sumLargestChoose n k` members. -/
theorem erdos_k_sperner_sharp (n k : ℕ) :
    ∃ 𝒜 : Finset (Finset (Fin n)),
      (∀ 𝒞 ⊆ 𝒜, IsChain (· ⊆ ·) (𝒞 : Set (Finset (Fin n))) → #𝒞 ≤ k) ∧
        #𝒜 = sumLargestChoose n k := by
  simpa using exists_card_eq_sumLargestChoose (α := Fin n) k

end Candidates.ErdosKSperner
