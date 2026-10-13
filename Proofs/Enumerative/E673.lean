import Mathlib
import Erdos.Erdos673.DivisorRatios

set_option autoImplicit false

namespace ErdosCandidates.E673

/-- The increasing list of divisors of `n`. -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- `G n`: the sum of ratios of consecutive divisors,
    `∑_{i < τ(n)−1} d_i / d_{i+1} : ℚ`, via `zipWith` on the sorted
    divisor list and its tail. -/
def G (n : ℕ) : ℚ :=
  (List.zipWith (fun a b => (a : ℚ) / b) (divisorList n)
    (divisorList n).tail).sum

private theorem divisors_twelve : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by
  decide

private theorem divisors_seven : (7 : ℕ).divisors = {1, 7} := by
  decide

private theorem divisorList_twelve : divisorList 12 = [1, 2, 3, 4, 6, 12] := by
  rw [divisorList, divisors_twelve]
  change ([1, 2, 3, 4, 6, 12] : List ℕ).toFinset.sort (· ≤ ·) = _
  exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

private theorem divisorList_seven : divisorList 7 = [1, 7] := by
  rw [divisorList, divisors_seven]
  change ([1, 7] : List ℕ).toFinset.sort (· ≤ ·) = _
  exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

/-- Ground truth: the consecutive divisor ratios of 12 sum to 37/12. -/
example : G 12 = 37 / 12 := by
  rw [G, divisorList_twelve]
  norm_num [List.zipWith_cons_cons, List.sum_cons]

/-- Ground truth: the prime 7 has one ratio, and 1 has none. -/
example : G 7 = 1 / 7 ∧ G 1 = 0 := by
  constructor
  · rw [G, divisorList_seven]
    norm_num
  · simp [G, divisorList]

/-- The live entry's literal `m = 1` lower bound fails at `n = 7`. -/
example : ¬(((7 / 1).divisors.card : ℚ) / 1 ≤ G 7) := by
  norm_num [G, divisorList_seven, divisors_seven]

private theorem adjacent_nonneg (l : List ℕ) :
    0 ≤ (List.zipWith (fun a b => (a : ℚ) / b) l l.tail).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.tail_cons] at ih
      exact add_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) ih

private theorem adjacent_le_length (l : List ℕ) (h : l.Pairwise (· ≤ ·)) :
    (List.zipWith (fun a b => (a : ℚ) / b) l l.tail).sum ≤
      ((l.length - 1 : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hab : a ≤ b := h.rel_head (by simp)
      have htail : (b :: l).Pairwise (· ≤ ·) := h.of_cons
      have hratio : (a : ℚ) / b ≤ 1 := by
        by_cases hb : b = 0
        · simp [hb]
        · have hbpos : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
          exact (div_le_one hbpos).2 (by exact_mod_cast hab)
      have hsum := add_le_add hratio (ih htail)
      simpa [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, add_comm] using hsum

/-- Every consecutive divisor ratio is nonnegative, including the empty sum at zero. -/
theorem G_nonneg (n : ℕ) : 0 ≤ G n := adjacent_nonneg (divisorList n)

/-- There are at most `τ(n) - 1` consecutive ratios, each at most one. -/
theorem G_le_tau_sub_one (n : ℕ) : G n ≤ ((n.divisors.card - 1 : ℕ) : ℚ) := by
  have h := adjacent_le_length (divisorList n) (Finset.pairwise_sort _ _)
  simpa [G, divisorList] using h

/-- The sum of consecutive divisor ratios is at most the number of divisors. -/
theorem G_le_tau (n : ℕ) (hn : 1 ≤ n) : G n ≤ n.divisors.card := by
  exact (G_le_tau_sub_one n).trans (by exact_mod_cast Nat.sub_le n.divisors.card 1)

example : 1 ≤ (12 : ℕ) := by decide
example : G 0 = 0 := by simp [G, divisorList]

private theorem next_of_adjacent (n a b : ℕ) (p t : List ℕ)
    (heq : Erdos673.divisorList n = p ++ a :: b :: t) :
    Erdos673.nextDivisor n a = b := by
  have hsorted := Erdos673.divisorList_pairwise n
  have hnodup := Erdos673.divisorList_nodup n
  rw [heq] at hsorted hnodup
  have hab : a < b := by
    have hle : a ≤ b := (List.pairwise_append.mp hsorted).2.1.rel_head (by simp)
    have hne : a ≠ b := by
      have ha := (List.nodup_append.mp hnodup).2.1
      exact fun hab => (List.nodup_cons.mp ha).1 (by simp [hab])
    exact lt_of_le_of_ne hle hne
  have hbmem : b ∈ n.divisors := by
    apply Erdos673.mem_divisorList.mp
    rw [heq]
    simp
  have hnonempty : (n.divisors.filter (a < ·)).Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨hbmem, hab⟩⟩
  rw [Erdos673.nextDivisor, dif_pos hnonempty]
  apply le_antisymm
  · exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hbmem, hab⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨hxmem, hax⟩ := Finset.mem_filter.mp hx
    have hxl : x ∈ p ++ a :: b :: t := by
      rw [← heq]
      exact Erdos673.mem_divisorList.mpr hxmem
    rcases List.mem_append.mp hxl with hxp | hxt
    · have hxa : x ≤ a := (List.pairwise_append.mp hsorted).2.2 x hxp a (by simp)
      omega
    · simp only [List.mem_cons] at hxt
      rcases hxt with rfl | rfl | hxt
      · omega
      · exact le_rfl
      · have hbt : (b :: t).Pairwise (· ≤ ·) :=
          (List.pairwise_append.mp hsorted).2.1.of_cons
        exact hbt.rel_head (by simp [hxt])

private theorem next_of_terminal (n a : ℕ) (p : List ℕ)
    (heq : Erdos673.divisorList n = p ++ [a]) :
    Erdos673.nextDivisor n a = 0 := by
  have hsorted := Erdos673.divisorList_pairwise n
  rw [heq] at hsorted
  have hempty : ¬(n.divisors.filter (a < ·)).Nonempty := by
    rintro ⟨x, hx⟩
    obtain ⟨hxmem, hax⟩ := Finset.mem_filter.mp hx
    have hxl : x ∈ p ++ [a] := by
      rw [← heq]
      exact Erdos673.mem_divisorList.mpr hxmem
    rcases List.mem_append.mp hxl with hxp | hxa
    · have hle : x ≤ a := (List.pairwise_append.mp hsorted).2.2 x hxp a (by simp)
      omega
    · simp only [List.mem_singleton] at hxa
      omega
  simp [Erdos673.nextDivisor, hempty]

private theorem zip_sum_eq_map (l : List ℕ) (f : ℕ → ℚ)
    (hadj : ∀ p a b t, l = p ++ a :: b :: t → f a = (a : ℚ) / b)
    (hlast : ∀ p a, l = p ++ [a] → f a = 0) :
    (List.zipWith (fun a b => (a : ℚ) / b) l l.tail).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simpa using (hlast [] a rfl).symm
    | cons b t =>
      have hfa := hadj [] a b t rfl
      have htail := ih
        (fun p x y s h => hadj (a :: p) x y s (by simp [h]))
        (fun p x h => hlast (a :: p) x (by simp [h]))
      simpa [hfa] using congrArg (fun z : ℚ => (a : ℚ) / b + z) htail

/-- The rational adjacent-list sum agrees with the canonical successor sum for every natural number. -/
theorem G_eq_canonical (n : ℕ) : G n = Erdos673.G n := by
  let f : ℕ → ℚ := fun d => (d : ℚ) / Erdos673.nextDivisor n d
  have hzip : G n = ((Erdos673.divisorList n).map f).sum := by
    apply zip_sum_eq_map
    · intro p a b t heq
      dsimp only [f]
      rw [next_of_adjacent n a b p t heq]
    · intro p a heq
      dsimp only [f]
      rw [next_of_terminal n a p heq, Nat.cast_zero, div_zero]
  have hsum : ((Erdos673.divisorList n).map f).sum = n.divisors.sum f := by
    rw [← List.sum_toFinset f (Erdos673.divisorList_nodup n)]
    simp [Erdos673.divisorList]
  have hnnext : Erdos673.nextDivisor n n = 0 := by
    have hempty : ¬(n.divisors.filter (n < ·)).Nonempty := by
      rintro ⟨d, hd⟩
      obtain ⟨hdmem, hnd⟩ := Finset.mem_filter.mp hd
      exact (not_lt_of_ge (Nat.divisor_le hdmem)) hnd
    simp [Erdos673.nextDivisor, hempty]
  have herase : (n.divisors.erase n).sum f = n.divisors.sum f := by
    apply Finset.sum_subset (Finset.erase_subset n n.divisors)
    intro d hd hnot
    have hdn : d = n := by
      by_contra hne
      exact hnot (Finset.mem_erase.mpr ⟨hne, hd⟩)
    simp [hdn, hnnext]
  exact hzip.trans (hsum.trans herase.symm)

/-- **Corrected lower inequality**: if `m ∣ n` and `2 ≤ m`, then
    `τ(n/m) / m ≤ G(n)`. The bound is transported from the canonical
    successor representation without changing the adjacent-list definition. -/
theorem tau_div_le_G (n m : ℕ) (hn : 1 ≤ n) (hm : m ∣ n) (hm2 : 2 ≤ m) :
    ((n / m).divisors.card : ℚ) / m ≤ G n := by
  rw [G_eq_canonical]
  exact Erdos673.tau_div_le_G n m (by omega) hm hm2

/-- For even `n` at least two, `τ(n)/4 ≤ G(n) ≤ τ(n)`. -/
theorem G_even_bounds (n : ℕ) (hn : 2 ≤ n) (heven : 2 ∣ n) :
    (n.divisors.card : ℚ) / 4 ≤ G n ∧ G n ≤ n.divisors.card := by
  rw [G_eq_canonical]
  exact Erdos673.G_even_bounds n (by omega) heven

example : 1 ≤ (12 : ℕ) ∧ 2 ∣ 12 ∧ 2 ≤ (2 : ℕ) := by decide
example : 2 ≤ (12 : ℕ) ∧ 2 ∣ 12 := by decide
example : ((12 / 2).divisors.card : ℚ) / 2 ≤ G 12 :=
  tau_div_le_G 12 2 (by decide) (by decide) (by decide)
example : ((12 : ℕ).divisors.card : ℚ) / 4 ≤ G 12 ∧
    G 12 ≤ (12 : ℕ).divisors.card :=
  G_even_bounds 12 (by decide) (by decide)
example : G 0 = Erdos673.G 0 ∧ G 0 = 0 := by
  exact ⟨G_eq_canonical 0, by simp [G, divisorList]⟩
example : G 1 = Erdos673.G 1 ∧ G 1 = 0 := by
  exact ⟨G_eq_canonical 1, by simp [G, divisorList]⟩

end ErdosCandidates.E673
