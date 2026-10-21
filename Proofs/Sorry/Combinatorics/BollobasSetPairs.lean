/-
# Bollobás set-pairs inequality (the two-families theorem)

## Classical source

* B. Bollobás, *On generalized graphs*, Acta Math. Acad. Sci. Hungar. 16
  (1965) 447–452 (the original statement).
* S. Jukna, *Extremal Combinatorics*, Chapter 9 ("Bollobás's theorem").
* P. Frankl, N. Tokushige, *Extremal Problems for Finite Sets*.

## Informal statement (verbatim from the target specification)

```
Let (A_i, B_i), i=1..m, be pairs of finite sets with A_i ∩ B_i = ∅ and
A_i ∩ B_j ≠ ∅ for i ≠ j. Then Σ_i 1 / C(|A_i|+|B_i|, |A_i|) ≤ 1. In
particular, if |A_i| = a and |B_i| = b, then m ≤ C(a+b, a).
```

Date: 2026-10-21.

## Mathlib absence check

`leandoc` searches ("Bollobas set pairs", "two families theorem disjoint
pairs", "sum inverse choose card le one", "LYM inequality antichain") and a
`grep Bollob` over Mathlib found only bibliography lines and the
Lubell–Yamamoto–Meshalkin inequality (`Finset.lubell_yamamoto_meshalkin_*`),
not the set-pairs inequality.

## Proof

Induction on the ground set `X` containing all `A_i, B_i` (the proof of
Lovász / Tuza).  If some `B_i = ∅` the cross condition forces the index set to
be `{i}`.  Otherwise, for each `x ∈ X` the pairs `(A_i, B_i \ {x})` with
`x ∉ A_i` satisfy the hypotheses on `X \ {x}`; summing the induction hypothesis
over `x ∈ X` and using `b · C(a+b, a) = (a+b) · C(a+b-1, a)` gives
`|X| · Σ_i 1 / C(a_i+b_i, a_i) ≤ |X|`.

No new definitions are introduced: the statement uses `Finset`, `Disjoint`,
`Finset.card` and `Nat.choose` from Mathlib.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BollobasSetPairs

open Finset

/-- Pascal-type identity `(c+1) · C(a+c+1, a) = (a+c+1) · C(a+c, a)`, i.e.
`b · C(a+b, a) = (a+b) · C(a+b-1, a)` for `b = c + 1 ≥ 1`. -/
theorem succ_mul_choose_add_succ (a c : ℕ) :
    (c + 1) * (a + (c + 1)).choose a = (a + (c + 1)) * (a + c).choose a := by
  have h1 : (a + (c + 1)).choose a = (a + c + 1).choose (c + 1) := by
    rw [Nat.choose_symm_add, ← add_assoc]
  have h2 : (a + c).choose a = (a + c).choose c := Nat.choose_symm_add
  rw [h1, h2, ← add_assoc, Nat.add_one_mul_choose_eq]
  ring

/-- Double-counting weight identity for one pair: if `A, B ⊆ X` are disjoint and
`B` is nonempty, then summing `1 / C(|A| + |B \ {x}|, |A|)` over `x ∈ X \ A`
gives `|X| / C(|A| + |B|, |A|)`. -/
theorem sum_inv_choose_erase_eq {α : Type*} [DecidableEq α] (X A B : Finset α)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hAB : Disjoint A B) (hB : B.Nonempty) :
    ∑ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℕ) : ℚ)⁻¹ =
      (#X : ℚ) * (((#A + #B).choose #A : ℕ) : ℚ)⁻¹ := by
  obtain ⟨c, hc⟩ : ∃ c, #B = c + 1 := ⟨#B - 1, by have := hB.card_pos; omega⟩
  have hsplit : ∀ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℕ) : ℚ)⁻¹ =
      if x ∈ B then (((#A + c).choose #A : ℕ) : ℚ)⁻¹
      else (((#A + (c + 1)).choose #A : ℕ) : ℚ)⁻¹ := by
    intro x _
    split_ifs with hx
    · rw [card_erase_of_mem hx, hc, Nat.add_sub_cancel]
    · rw [erase_eq_of_notMem hx, hc]
  rw [sum_congr rfl hsplit, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hfilt : {x ∈ X \ A | x ∈ B} = B := by
    ext x
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨_, hxB⟩
      exact hxB
    · intro hxB
      exact ⟨⟨hBX hxB, disjoint_right.1 hAB hxB⟩, hxB⟩
  have hcardXA : #(X \ A) + #A = #X := card_sdiff_add_card_eq_card hAX
  have hcardsplit := card_filter_add_card_filter_not (s := X \ A) (fun x => x ∈ B)
  rw [hfilt] at hcardsplit
  have hrest : (#{x ∈ X \ A | x ∉ B} : ℚ) = #X - #A - (c + 1) := by
    have hnat : #{x ∈ X \ A | x ∉ B} + (c + 1) + #A = #X := by omega
    have hq : (#{x ∈ X \ A | x ∉ B} : ℚ) + (c + 1) + #A = #X := by exact_mod_cast hnat
    linarith
  rw [hfilt, hrest, hc]
  have hid : ((c + 1 : ℕ) : ℚ) * ((#A + (c + 1)).choose #A : ℕ) =
      ((#A + (c + 1) : ℕ) : ℚ) * ((#A + c).choose #A : ℕ) := by
    exact_mod_cast succ_mul_choose_add_succ #A c
  have hpos1 : (0 : ℚ) < ((#A + c).choose #A : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hpos2 : (0 : ℚ) < ((#A + (c + 1)).choose #A : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  push_cast at hid ⊢
  field_simp
  linear_combination hid

/-- Bollobás's inequality relative to a ground set `X`: if every `A i`, `B i`
(`i ∈ s`) lies in `X`, `A i ∩ B i = ∅`, and `A i ∩ B j ≠ ∅` for distinct
`i, j ∈ s`, then `Σ_{i ∈ s} 1 / C(|A i| + |B i|, |A i|) ≤ 1`.  Proved by strong
induction on `X`. -/
theorem sum_inv_choose_le_one_of_subset {α ι : Type*} [DecidableEq α]
    (A : ι → Finset α) (X : Finset α) :
    ∀ (s : Finset ι) (B : ι → Finset α), (∀ i ∈ s, A i ⊆ X) → (∀ i ∈ s, B i ⊆ X) →
      (∀ i ∈ s, Disjoint (A i) (B i)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) →
      ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
  induction X using Finset.strongInduction with
  | H X ih =>
  intro s B hAX hBX hdisj hcross
  by_cases hemptyB : ∃ i ∈ s, B i = ∅
  · -- an empty `B i` forces `s = {i}` by the cross condition
    obtain ⟨i, hi, hBi⟩ := hemptyB
    have hs : s = {i} := by
      ext j
      rw [mem_singleton]
      constructor
      · intro hj
        by_contra hji
        exact hcross j hj i hi hji (by rw [hBi]; exact disjoint_empty_right _)
      · rintro rfl
        exact hi
    simp [hs, hBi]
  push Not at hemptyB
  rcases s.eq_empty_or_nonempty with hs | ⟨i0, hi0⟩
  · simp [hs]
  have hXpos : (0 : ℚ) < #X := by
    obtain ⟨y, hy⟩ := hemptyB i0 hi0
    exact_mod_cast card_pos.2 ⟨y, hBX i0 hi0 hy⟩
  -- the induction hypothesis on `X \ {x}` for the pairs `(A i, B i \ {x})`, `x ∉ A i`
  have hIH : ∀ x ∈ X, ∑ i ∈ s with x ∉ A i,
      (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
    intro x hxX
    apply ih (X.erase x) (erase_ssubset hxX)
    · intro i hi y hy
      have hxA : x ∉ A i := (mem_filter.1 hi).2
      exact mem_erase.2 ⟨fun hyx => hxA (hyx ▸ hy), hAX i (mem_filter.1 hi).1 hy⟩
    · intro i hi
      exact erase_subset_erase x (hBX i (mem_filter.1 hi).1)
    · intro i hi
      exact disjoint_of_subset_right (erase_subset _ _) (hdisj i (mem_filter.1 hi).1)
    · intro i hi j hj hij hd
      obtain ⟨y, hyA, hyB⟩ :=
        not_disjoint_iff.1 (hcross i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hij)
      have hxA : x ∉ A i := (mem_filter.1 hi).2
      exact disjoint_left.1 hd hyA (mem_erase.2 ⟨fun hyx => hxA (hyx ▸ hyA), hyB⟩)
  have hkey : (#X : ℚ) * ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤
      (#X : ℚ) * 1 := by
    calc (#X : ℚ) * ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹
        = ∑ i ∈ s, ∑ x ∈ X \ A i,
            (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ := by
          rw [mul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [sum_inv_choose_erase_eq X (A i) (B i) (hAX i hi) (hBX i hi) (hdisj i hi)
            (hemptyB i hi)]
      _ = ∑ x ∈ X, ∑ i ∈ s with x ∉ A i,
            (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ := by
          refine sum_comm' fun i x => ?_
          simp only [mem_sdiff, mem_filter]
          tauto
      _ ≤ ∑ _x ∈ X, (1 : ℚ) := sum_le_sum hIH
      _ = (#X : ℚ) * 1 := by simp
  exact le_of_mul_le_mul_left hkey hXpos

/-- **Bollobás's set-pairs inequality** (two-families theorem, 1965).  Let
`(A i, B i)`, `i ∈ s`, be pairs of finite sets with `A i ∩ B i = ∅` and
`A i ∩ B j ≠ ∅` for `i ≠ j`.  Then `Σ_{i ∈ s} 1 / C(|A i| + |B i|, |A i|) ≤ 1`. -/
theorem bollobas_set_pairs {α ι : Type*} (s : Finset ι) (A B : ι → Finset α)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
  classical
  refine sum_inv_choose_le_one_of_subset A (s.biUnion fun i => A i ∪ B i) s B
    (fun i hi => ?_) (fun i hi => ?_) hdisj hcross
  · exact subset_union_left.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi)
  · exact subset_union_right.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi)

/-- **Uniform Bollobás bound.**  If moreover `|A i| = a` and `|B i| = b` for all
`i ∈ s`, then the number of pairs is at most `C(a + b, a)`. -/
theorem card_le_choose_of_bollobas {α ι : Type*} (s : Finset ι) (A B : ι → Finset α)
    (a b : ℕ) (hA : ∀ i ∈ s, #(A i) = a) (hB : ∀ i ∈ s, #(B i) = b)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    #s ≤ (a + b).choose a := by
  have hsum := bollobas_set_pairs s A B hdisj hcross
  have hconst : ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ =
      (#s : ℚ) * (((a + b).choose a : ℕ) : ℚ)⁻¹ := by
    rw [sum_congr rfl fun i hi => by rw [hA i hi, hB i hi], sum_const, nsmul_eq_mul]
  have hpos : (0 : ℚ) < ((a + b).choose a : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [hconst, mul_inv_le_iff₀ hpos, one_mul] at hsum
  exact_mod_cast hsum

/-- Satisfiability witness: the two pairs `({0}, {1})` and `({1}, {0})` meet
all hypotheses, and attain equality `1/2 + 1/2 = 1` in Bollobás's inequality
(and `2 = C(2, 1)` in the uniform bound). -/
example :
    let A : Fin 2 → Finset (Fin 2) := ![{0}, {1}]
    let B : Fin 2 → Finset (Fin 2) := ![{1}, {0}]
    (∀ i ∈ (univ : Finset (Fin 2)), Disjoint (A i) (B i)) ∧
      (∀ i ∈ (univ : Finset (Fin 2)), ∀ j ∈ (univ : Finset (Fin 2)), i ≠ j →
        ¬ Disjoint (A i) (B j)) ∧
      ∑ i ∈ (univ : Finset (Fin 2)), (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ = 1 ∧
      #(univ : Finset (Fin 2)) = (1 + 1).choose 1 := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  norm_num [Fin.sum_univ_two]

end Candidates.BollobasSetPairs
