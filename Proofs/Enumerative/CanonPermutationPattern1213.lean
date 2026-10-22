/-
# Lattice words avoiding the S₃-orbit of 1213

Robert Laudone, *Pattern avoidance in canon permutations*, arXiv:2608.21351,
"Further Directions", "Changing the patterns", Conjecture `conj: 1213`.
For every `n ≥ 2` and every `k ≥ 0`, the number of k-regular lattice words
on `Fin n` with no subsequence `x y x z` of pairwise distinct letters is
`catalan k`. The first `n-2` letters form forced constant blocks; the last
two encode a Dyck word.
The paper's orbit is `{1213,1312,2123,2321,3132,3231}`. Its Theorem
`thm: symmetric` converts this lattice-word count to the canon-permutation
count `n! C_k`; that conversion and the equivalence with the six standardized
patterns are not separate formal bridges here. The lattice-word theorem
also includes `k=0,1`, beyond the conjecture's `k ≥ 2`.
-/
import Mathlib

set_option autoImplicit false

namespace CanonPermutationPattern1213

open List

/-- A `k`-regular lattice word on the alphabet `Fin n`: every letter occurs exactly
`k` times, and in every prefix the letter `i` occurs at least as often as the letter
`i + 1`. -/
def IsRegLatticeWord (n k : ℕ) (w : List (Fin n)) : Prop :=
  (∀ i : Fin n, w.count i = k) ∧
    ∀ u : List (Fin n), u <+: w → ∀ i j : Fin n, i.val + 1 = j.val → u.count j ≤ u.count i

/-- A word contains a pattern of the `S₃`-orbit `O(1213)` iff it has a (not necessarily
contiguous) subsequence `x y x z` with `x, y, z` pairwise distinct. -/
def ContainsOrbit1213 {n : ℕ} (w : List (Fin n)) : Prop :=
  ∃ x y z : Fin n, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ [x, y, x, z] <+ w

/-- The relation `b < m → a ≤ b`: a letter below `m` is never preceded by a larger
letter.  Every avoiding regular lattice word is sorted for it (`pairwise_of_avoids`). -/
def SortedBelow (m : ℕ) (a b : Fin (m + 2)) : Prop := b.val < m → a ≤ b

/-- Prefix quantification in `IsRegLatticeWord` ranges over the finite list `w.inits`;
this form is decidable and is used for the examples below. -/
theorem isRegLatticeWord_iff_inits (n k : ℕ) (w : List (Fin n)) :
    IsRegLatticeWord n k w ↔ (∀ i : Fin n, w.count i = k) ∧
      ∀ u ∈ w.inits, ∀ i j : Fin n, i.val + 1 = j.val → u.count j ≤ u.count i := by
  simp only [IsRegLatticeWord, List.mem_inits]

/-! ### Examples -/

/-- `001212` (the paper's `112323`, 0-indexed) is a `2`-regular lattice word on `[3]`. -/
example : IsRegLatticeWord 3 2 [0, 0, 1, 2, 1, 2] := by
  rw [isRegLatticeWord_iff_inits]
  decide

/-- `10` is not a lattice word (its first prefix has a `1` but no `0`). -/
example : ¬ IsRegLatticeWord 2 1 [1, 0] := by
  rw [isRegLatticeWord_iff_inits]
  decide

/-- The paper's lattice word `111122112231122333223333` (`k = 8`, `n = 3`, Theorem
`thm: 12j1-k=2(j-1)`), written 0-indexed, is an `8`-regular lattice word. -/
example : IsRegLatticeWord 3 8
    [0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2] := by
  rw [isRegLatticeWord_iff_inits]
  decide

/-- The paper's word above contains `1213` (positions `1, 5, 7, 11`). -/
example : ContainsOrbit1213
    ([0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2] : List (Fin 3)) := by
  unfold ContainsOrbit1213
  decide

/-- `1213` itself contains a pattern of `O(1213)`. -/
example : ContainsOrbit1213 ([0, 1, 0, 2] : List (Fin 3)) := by
  unfold ContainsOrbit1213
  decide

/-- `001212` avoids `O(1213)`; it lies in the counted set for `n = 3`, `k = 2`. -/
example : ¬ ContainsOrbit1213 ([0, 0, 1, 2, 1, 2] : List (Fin 3)) := by
  unfold ContainsOrbit1213
  decide

/-- `010122` is a `2`-regular lattice word containing `0 1 0 2`. -/
example : IsRegLatticeWord 3 2 [0, 1, 0, 1, 2, 2] ∧
    ContainsOrbit1213 ([0, 1, 0, 1, 2, 2] : List (Fin 3)) := by
  rw [isRegLatticeWord_iff_inits]
  unfold ContainsOrbit1213
  decide

/-! ### Proof -/

/-- In a regular lattice word, every prefix contains letter `i` at least as often as any
letter `j ≥ i` (iterate the defining inequality). -/
theorem count_le_count_of_le {n k : ℕ} {w : List (Fin n)} (hw : IsRegLatticeWord n k w)
    {u : List (Fin n)} (hu : u <+: w) {i j : Fin n} (hij : i ≤ j) :
    u.count j ≤ u.count i := by
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + d := ⟨j.val - i.val, by omega⟩
  induction d generalizing j with
  | zero =>
    have hji : j = i := Fin.ext (by omega)
    rw [hji]
  | succ d ih =>
    have hlt : i.val + d < n := by omega
    have hstep := hw.2 u hu ⟨i.val + d, hlt⟩ j (by simp only; omega)
    exact hstep.trans (ih (j := ⟨i.val + d, hlt⟩) (Fin.mk_le_mk.mpr (by simp)) rfl)

/-- **Key step.** An `O(1213)`-avoiding `k`-regular lattice word on `Fin (m + 2)` has no
subsequence `a b` with `b < m` and `b < a`: otherwise a first `b` before `a`, the given
`b`, and a later letter `z ∈ {b+1, b+2} \ {a}` form `b a b z`. -/
theorem pairwise_of_avoids {m k : ℕ} {w : List (Fin (m + 2))}
    (hw : IsRegLatticeWord (m + 2) k w) (hav : ¬ ContainsOrbit1213 w) :
    w.Pairwise (SortedBelow m) := by
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab hbm
  by_contra hba
  rw [not_le] at hba
  have hab_ne : a ≠ b := ne_of_gt hba
  obtain ⟨r₁, r₂, hw12, ha, hb⟩ := List.cons_sublist_iff.mp hab
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  obtain ⟨s', t', rfl⟩ := List.append_of_mem (List.singleton_sublist.mp hb)
  -- a first copy of `b` precedes `a`
  have hbs : b ∈ s := by
    have hpre : s ++ [a] <+: w := ⟨t ++ (s' ++ b :: t'), by simp [hw12]⟩
    have hle := count_le_count_of_le hw hpre hba.le
    have hca : 1 ≤ (s ++ [a]).count a := by simp
    have hcb : (s ++ [a]).count b = s.count b := by
      simp [List.count_append, hab_ne]
    exact List.count_pos_iff.mp (by omega)
  -- a third letter `z > b`, `z ≠ a`, occurs after the second `b`
  obtain ⟨z, hbz, hza⟩ : ∃ z : Fin (m + 2), b < z ∧ z ≠ a := by
    by_cases hab1 : a.val = b.val + 1
    · exact ⟨⟨b.val + 2, by omega⟩, Fin.mk_lt_mk.mpr (by omega) |>.trans_le' le_rfl,
        fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    · exact ⟨⟨b.val + 1, by omega⟩, by rw [Fin.lt_def]; simp,
        fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
  have hzb : z ≠ b := ne_of_gt hbz
  have hzt : z ∈ t' := by
    set u := s ++ a :: t ++ s' with hu
    have hwu : w = u ++ b :: t' := by simp [hw12, hu]
    have hpre : u <+: w := ⟨b :: t', hwu.symm⟩
    have hpre' : u ++ [b] <+: w := ⟨t', by simp [hwu]⟩
    have hle := count_le_count_of_le hw hpre hbz.le
    have hbk : (u ++ [b]).count b ≤ k := hw.1 b ▸ hpre'.sublist.count_le b
    have hzk : w.count z = k := hw.1 z
    have hzw : w.count z = u.count z + t'.count z := by
      rw [hwu, List.count_append, List.count_cons]
      simp [hzb.symm]
    have hbu : (u ++ [b]).count b = u.count b + 1 := by simp
    exact List.count_pos_iff.mp (by omega)
  apply hav
  refine ⟨b, a, z, hab_ne.symm, hzb.symm, hza.symm, ?_⟩
  have hbz_sub : [b, z] <+ t ++ (s' ++ b :: t') :=
    List.sublist_append_of_sublist_right
      (by simpa using (List.nil_sublist s').append ((List.singleton_sublist.mpr hzt).cons_cons b))
  have hsub := (List.singleton_sublist.mpr hbs).append (hbz_sub.cons_cons a)
  rw [hw12]
  simpa using hsub



/-- The letter `m` of `Fin (m + 2)` (second-largest letter). -/
def midL (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩
/-- The letter `m + 1` of `Fin (m + 2)` (largest letter). -/
def topL (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

/-- Encode a Dyck step as a letter: `U ↦ m`, `D ↦ m + 1`. -/
def stepLetter (m : ℕ) : DyckStep → Fin (m + 2)
  | .U => midL m
  | .D => topL m

/-- Decode a letter `m` or `m + 1` as a Dyck step: `m ↦ U`, anything else `↦ D`. -/
def letterStep (m : ℕ) (a : Fin (m + 2)) : DyckStep := if a.val = m then .U else .D

/-- The block word `0^k 1^k ⋯ (m-1)^k` on `Fin (m + 2)`. -/
def blockWord (m k : ℕ) : List (Fin (m + 2)) :=
  ((List.finRange (m + 2)).filter (fun i => i.val < m)).flatMap (List.replicate k)

/-- The avoiding lattice word attached to a Dyck word `p` of semilength `k`:
`0^k ⋯ (m-1)^k` followed by `p` written in the letters `m` (up) and `m + 1` (down). -/
def ofDyck (m : ℕ) (p : DyckWord) : List (Fin (m + 2)) :=
  blockWord m p.semilength ++ p.toList.map (stepLetter m)

/-- Counting in a concatenation of constant blocks over a duplicate-free list. -/
theorem count_flatMap_replicate {α : Type*} [DecidableEq α] (k : ℕ) (c : α) :
    ∀ l : List α, l.Nodup → (l.flatMap (List.replicate k)).count c = if c ∈ l then k else 0
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.count_append, count_flatMap_replicate k c l hl.2,
      List.count_replicate]
    by_cases hac : a = c
    · subst hac
      simp [hl.1]
    · have hca : c ≠ a := fun h => hac h.symm
      simp [hac, hca]

/-- Every letter `c < m` occurs `k` times in the block word, the others not at all. -/
theorem count_blockWord (m k : ℕ) (c : Fin (m + 2)) :
    (blockWord m k).count c = if c.val < m then k else 0 := by
  rw [blockWord, count_flatMap_replicate k c _ ((List.nodup_finRange _).filter _)]
  simp

/-- Constant blocks over a strictly increasing list form a weakly increasing list. -/
theorem pairwise_flatMap_replicate {α : Type*} [PartialOrder α] (k : ℕ) :
    ∀ l : List α, l.Pairwise (· < ·) → (l.flatMap (List.replicate k)).Pairwise (· ≤ ·)
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.pairwise_cons] at hl
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl),
      pairwise_flatMap_replicate k l hl.2, ?_⟩
    intro x hx y hy
    rw [List.mem_replicate] at hx
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
    rw [List.mem_replicate] at hyb
    rw [hx.2, hyb.2]
    exact (hl.1 b hb).le

/-- The block word is weakly increasing. -/
theorem pairwise_blockWord (m k : ℕ) : (blockWord m k).Pairwise (· ≤ ·) :=
  pairwise_flatMap_replicate k _ ((List.pairwise_lt_finRange _).filter _)

/-- Letter counts of an encoded Dyck step list. -/
theorem count_map_stepLetter (m : ℕ) (c : Fin (m + 2)) :
    ∀ l : List DyckStep, (l.map (stepLetter m)).count c =
      if c.val = m then l.count .U else if c.val = m + 1 then l.count .D else 0
  | [] => by simp
  | s :: l => by
    rw [List.map_cons, List.count_cons, count_map_stepLetter m c l]
    rcases s with _ | _ <;> by_cases h1 : c.val = m <;> by_cases h2 : c.val = m + 1 <;>
      simp [stepLetter, midL, topL, Fin.ext_iff, h1, h2] <;> omega

/-- Encoded Dyck steps are letters `≥ m`. -/
theorem le_val_of_mem_map_stepLetter (m : ℕ) (l : List DyckStep) (x : Fin (m + 2))
    (hx : x ∈ l.map (stepLetter m)) : m ≤ x.val := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
  rcases s with _ | _ <;> simp [stepLetter, midL, topL]

/-- The word `ofDyck m p` satisfies the sortedness relation `SortedBelow m`. -/
theorem pairwise_ofDyck (m : ℕ) (p : DyckWord) : (ofDyck m p).Pairwise (SortedBelow m) := by
  rw [ofDyck, List.pairwise_append]
  refine ⟨(pairwise_blockWord m _).imp (fun {a b} (h : a ≤ b) => (fun _ => h : SortedBelow m a b)),
    ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      (fun _ _ => trivial))
    intro a b _ hb _ hbm
    have := le_val_of_mem_map_stepLetter m _ b hb
    omega
  · intro a _ b hb hbm
    have := le_val_of_mem_map_stepLetter m _ b hb
    omega

/-- A word sorted for `SortedBelow m` avoids `O(1213)`: in `x y x z` all three letters
would have to be `≥ m`, but only two such letters exist. -/
theorem not_contains_of_pairwise {m : ℕ} {w : List (Fin (m + 2))}
    (hw : w.Pairwise (SortedBelow m)) : ¬ ContainsOrbit1213 w := by
  rintro ⟨x, y, z, hxy, hxz, hyz, hsub⟩
  have hR : ∀ {a b : Fin (m + 2)}, [a, b] <+ w → b.val < m → a ≤ b :=
    fun h => List.pairwise_iff_forall_sublist.mp hw h
  have hxy' : [x, y] <+ w := (by simp : [x, y] <+ [x, y, x, z]).trans hsub
  have hyx' : [y, x] <+ w := (by simp : [y, x] <+ [x, y, x, z]).trans hsub
  have hxz' : [x, z] <+ w := (by simp : [x, z] <+ [x, y, x, z]).trans hsub
  have hxm : m ≤ x.val := by
    by_contra hx
    have h1 := hR hyx' (by omega)
    by_cases hy : y.val < m
    · exact hxy (le_antisymm (hR hxy' hy) h1)
    · rw [Fin.le_def] at h1
      omega
  have hym : m ≤ y.val := by
    by_contra hy
    have := hR hxy' (by omega)
    rw [Fin.le_def] at this
    omega
  have hzm : m ≤ z.val := by
    by_contra hz
    have := hR hxz' (by omega)
    rw [Fin.le_def] at this
    omega
  have hx2 := x.isLt
  have hy2 := y.isLt
  have hz2 := z.isLt
  rw [Ne, Fin.ext_iff] at hxy hxz hyz
  omega

/-- A `SortedBelow m`-sorted word with all letter counts `k` is a `k`-regular lattice word
as soon as every prefix has at most as many `m + 1` as `m`. -/
theorem lattice_of_pairwise {m k : ℕ} {w : List (Fin (m + 2))}
    (hw : w.Pairwise (SortedBelow m)) (hc : ∀ i, w.count i = k)
    (htop : ∀ u, u <+: w → u.count (topL m) ≤ u.count (midL m)) :
    IsRegLatticeWord (m + 2) k w := by
  refine ⟨hc, ?_⟩
  intro u hu i j hij
  by_cases hj : j.val = m + 1
  · have hi : i = midL m := Fin.ext (by simp only [midL]; omega)
    have hj' : j = topL m := Fin.ext (by simp only [topL]; omega)
    rw [hi, hj']
    exact htop u hu
  · by_cases hju : j ∈ u
    · obtain ⟨v, rfl⟩ := hu
      have hiv : v.count i = 0 := by
        rw [List.count_eq_zero]
        intro hiv
        have hsub : [j, i] <+ u ++ v :=
          (List.singleton_sublist.mpr hju).append (List.singleton_sublist.mpr hiv)
        have hji := List.pairwise_iff_forall_sublist.mp hw hsub (by omega)
        rw [Fin.le_def] at hji
        omega
      have h1 := hc i
      have h2 := hc j
      rw [List.count_append] at h1 h2
      omega
    · rw [List.count_eq_zero.mpr hju]
      exact Nat.zero_le _

/-- Every letter occurs exactly `semilength p` times in `ofDyck m p`. -/
theorem count_ofDyck (m : ℕ) (p : DyckWord) (c : Fin (m + 2)) :
    (ofDyck m p).count c = p.semilength := by
  rw [ofDyck, List.count_append, count_blockWord, count_map_stepLetter,
    ← DyckWord.semilength_eq_count_D]
  have hU : p.toList.count .U = p.semilength := rfl
  rw [hU]
  have hc := c.isLt
  by_cases h1 : c.val < m
  · simp [h1, show c.val ≠ m by omega, show c.val ≠ m + 1 by omega]
  · by_cases h2 : c.val = m
    · simp [h2]
    · have h3 : c.val = m + 1 := by omega
      simp [h3]

/-- Prefixes of `ofDyck m p` have at most as many letters `m + 1` as `m`. -/
theorem top_le_mid_ofDyck (m : ℕ) (p : DyckWord) (u : List (Fin (m + 2)))
    (hu : u <+: ofDyck m p) : u.count (topL m) ≤ u.count (midL m) := by
  rw [List.prefix_iff_eq_take] at hu
  rw [hu, ofDyck, List.take_append, ← List.map_take, List.count_append, List.count_append]
  have hB : ((blockWord m p.semilength).take u.length).count (topL m) = 0 := by
    have := ((List.take_sublist u.length (blockWord m p.semilength)).count_le (topL m))
    rw [count_blockWord, if_neg (by simp [topL])] at this
    omega
  have ht : (topL m).val = m + 1 := rfl
  have ht' : ¬ (topL m).val = m := by rw [ht]; omega
  have hm : (midL m).val = m := rfl
  rw [hB, count_map_stepLetter, count_map_stepLetter, if_neg ht', if_pos ht, if_pos hm]
  have := p.count_D_le_count_U (u.length - (blockWord m p.semilength).length)
  omega

/-- `ofDyck m p` is a `semilength p`-regular lattice word avoiding `O(1213)`. -/
theorem ofDyck_good (m : ℕ) (p : DyckWord) :
    IsRegLatticeWord (m + 2) p.semilength (ofDyck m p) ∧ ¬ ContainsOrbit1213 (ofDyck m p) :=
  ⟨lattice_of_pairwise (pairwise_ofDyck m p) (count_ofDyck m p) (top_le_mid_ofDyck m p),
    not_contains_of_pairwise (pairwise_ofDyck m p)⟩

/-- The step encoding is injective. -/
theorem stepLetter_injective (m : ℕ) : Function.Injective (stepLetter m) := by
  intro s t hst
  rcases s with _ | _ <;> rcases t with _ | _ <;>
    simp_all [stepLetter, midL, topL, Fin.ext_iff]

/-- Distinct Dyck words give distinct words `ofDyck m p`. -/
theorem ofDyck_injective (m : ℕ) : Function.Injective (ofDyck m) := by
  intro p q hpq
  have hs : p.semilength = q.semilength := by
    rw [← count_ofDyck m p (midL m), ← count_ofDyck m q (midL m), hpq]
  rw [ofDyck, ofDyck, hs, List.append_cancel_left_eq] at hpq
  exact DyckWord.ext (List.map_injective_iff.mpr (stepLetter_injective m) hpq)

/-- The subword of letters `< m`. -/
abbrev lowPart (m : ℕ) (w : List (Fin (m + 2))) : List (Fin (m + 2)) :=
  w.filter (fun a => decide (a.val < m))

/-- The subword of letters `≥ m`. -/
abbrev highPart (m : ℕ) (w : List (Fin (m + 2))) : List (Fin (m + 2)) :=
  w.filter (fun a => !decide (a.val < m))

/-- A `SortedBelow m`-sorted word is its letters `< m` followed by its letters `≥ m`. -/
theorem lowPart_append_highPart {m : ℕ} :
    ∀ w : List (Fin (m + 2)), w.Pairwise (SortedBelow m) → lowPart m w ++ highPart m w = w
  | [], _ => rfl
  | a :: t, hw => by
    rw [List.pairwise_cons] at hw
    by_cases ha : a.val < m
    · simp only [lowPart, highPart, List.filter_cons, ha, decide_true, if_true, Bool.not_true,
        Bool.false_eq_true, if_false, List.cons_append]
      rw [lowPart_append_highPart t hw.2]
    · have hlow : lowPart m t = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hbm
        have hab := hw.1 b hb (by simpa using hbm)
        rw [Fin.le_def] at hab
        simp only [decide_eq_true_eq] at hbm
        omega
      have hhigh : highPart m t = t := by
        rw [List.filter_eq_self]
        intro b hb
        have hbm : ¬ b.val < m := by
          intro hbm
          have hab := hw.1 b hb hbm
          rw [Fin.le_def] at hab
          omega
        simpa using hbm
      simp only [lowPart, highPart, List.filter_cons, ha, decide_false, Bool.not_false,
        Bool.false_eq_true, if_false, if_true]
      simp only [lowPart, highPart] at hlow hhigh
      rw [hlow, hhigh, List.nil_append]

/-- Letter counts of the high part. -/
theorem count_highPart {m : ℕ} (w : List (Fin (m + 2))) (c : Fin (m + 2)) :
    (highPart m w).count c = if c.val < m then 0 else w.count c := by
  by_cases hc : c.val < m
  · rw [if_pos hc, List.count_eq_zero]
    intro hmem
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hmem
    exact hmem.2 hc
  · rw [if_neg hc, List.count_filter (by simpa using hc)]

/-- Letter counts of the low part. -/
theorem count_lowPart {m : ℕ} (w : List (Fin (m + 2))) (c : Fin (m + 2)) :
    (lowPart m w).count c = if c.val < m then w.count c else 0 := by
  by_cases hc : c.val < m
  · rw [if_pos hc, List.count_filter (by simpa using hc)]
  · rw [if_neg hc, List.count_eq_zero]
    intro hmem
    simp only [List.mem_filter, decide_eq_true_eq] at hmem
    exact hc hmem.2

/-- In a sorted word with all counts `k`, the low part is the block word. -/
theorem lowPart_eq_blockWord {m k : ℕ} {w : List (Fin (m + 2))}
    (hc : ∀ i, w.count i = k) (hw : w.Pairwise (SortedBelow m)) :
    lowPart m w = blockWord m k := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ (pairwise_blockWord m k) ?_
  · refine (hw.filter _).imp_of_mem ?_
    intro a b _ hb hab
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hab hb.2
  · rw [List.perm_iff_count]
    intro c
    rw [count_lowPart, count_blockWord, hc]

/-- Decoding then encoding a letter `≥ m` is the identity. -/
theorem stepLetter_letterStep {m : ℕ} (a : Fin (m + 2)) (ha : m ≤ a.val) :
    stepLetter m (letterStep m a) = a := by
  unfold letterStep
  by_cases h : a.val = m
  · simp [h, stepLetter, midL, Fin.ext_iff]
  · have h' : a.val = m + 1 := by have := a.isLt; omega
    simp [stepLetter, topL, Fin.ext_iff, h']

/-- Up steps correspond to letters `m`. -/
theorem count_U_eq_count_midL (m : ℕ) (l : List DyckStep) :
    l.count .U = (l.map (stepLetter m)).count (midL m) := by
  have hm : (midL m).val = m := rfl
  rw [count_map_stepLetter, if_pos hm]

/-- Down steps correspond to letters `m + 1`. -/
theorem count_D_eq_count_topL (m : ℕ) (l : List DyckStep) :
    l.count .D = (l.map (stepLetter m)).count (topL m) := by
  have ht : (topL m).val = m + 1 := rfl
  have ht' : ¬ (topL m).val = m := by rw [ht]; omega
  rw [count_map_stepLetter, if_neg ht', if_pos ht]

/-- Every `O(1213)`-avoiding `k`-regular lattice word on `Fin (m + 2)` is `ofDyck m p` for a
Dyck word `p` of semilength `k`. -/
theorem exists_ofDyck_eq {m k : ℕ} {w : List (Fin (m + 2))}
    (hw : IsRegLatticeWord (m + 2) k w) (hav : ¬ ContainsOrbit1213 w) :
    ∃ p : DyckWord, p.semilength = k ∧ ofDyck m p = w := by
  have hP := pairwise_of_avoids hw hav
  have hsplit := lowPart_append_highPart w hP
  set T := (highPart m w).map (letterStep m) with hT
  have hTT : T.map (stepLetter m) = highPart m w := by
    rw [hT, List.map_map]
    conv_rhs => rw [← List.map_id (highPart m w)]
    refine List.map_congr_left ?_
    intro a ha
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    exact stepLetter_letterStep a (by omega)
  have hmid_ne : ¬ (midL m).val < m := by simp [midL]
  have htop_ne : ¬ (topL m).val < m := by simp [topL]
  have hU : T.count .U = k := by
    rw [count_U_eq_count_midL m, hTT, count_highPart, if_neg hmid_ne, hw.1]
  have hD : T.count .D = k := by
    rw [count_D_eq_count_topL m, hTT, count_highPart, if_neg htop_ne, hw.1]
  have hpre : ∀ i, (T.take i).count .D ≤ (T.take i).count .U := by
    intro i
    have hTi : (T.take i).map (stepLetter m) = (highPart m w).take i := by
      rw [List.map_take, hTT]
    rw [count_U_eq_count_midL m, count_D_eq_count_topL m, hTi]
    have hu : lowPart m w ++ (highPart m w).take i <+: w := by
      conv_rhs => rw [← hsplit]
      exact (List.prefix_append_right_inj _).mpr (List.take_prefix i _)
    have hlat := hw.2 _ hu (midL m) (topL m) rfl
    rw [List.count_append, List.count_append, count_lowPart, count_lowPart, if_neg hmid_ne,
      if_neg htop_ne] at hlat
    omega
  let p : DyckWord := ⟨T, hU.trans hD.symm, hpre⟩
  have hps : p.semilength = k := hU
  refine ⟨p, hps, ?_⟩
  change blockWord m p.semilength ++ T.map (stepLetter m) = w
  rw [hps, hTT, ← lowPart_eq_blockWord hw.1 hP, hsplit]

/-- **Conjecture `conj: 1213` of Laudone (arXiv:2608.21351), lattice-word form.**
For `n ≥ 2` and every `k`, the number of `k`-regular lattice words on `[n]` avoiding
every pattern of `O(1213) = {1213,1312,2123,2321,3132,3231}` is the Catalan number
`C_k`, independently of `n`.  Combined with the paper's Theorem `thm: symmetric`
this gives `c_n^k(O(1213)) = n! C_k`. -/
theorem conj_1213 (n k : ℕ) (hn : 2 ≤ n) :
    {w : List (Fin n) | IsRegLatticeWord n k w ∧ ¬ ContainsOrbit1213 w}.ncard = catalan k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hset : {w : List (Fin (m + 2)) | IsRegLatticeWord (m + 2) k w ∧ ¬ ContainsOrbit1213 w} =
      ofDyck m '' {p : DyckWord | p.semilength = k} := by
    ext w
    constructor
    · rintro ⟨hw, hav⟩
      obtain ⟨p, hp, rfl⟩ := exists_ofDyck_eq hw hav
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hgood := ofDyck_good m p
      rw [hp] at hgood
      exact hgood
  have hcat : Nat.card {p : DyckWord // p.semilength = k} = catalan k := by
    rw [Nat.card_eq_fintype_card, DyckWord.card_dyckWord_semilength_eq_catalan]
  rw [hset, Set.ncard_image_of_injective _ (ofDyck_injective m), ← Nat.card_coe_set_eq]
  exact hcat

end CanonPermutationPattern1213
