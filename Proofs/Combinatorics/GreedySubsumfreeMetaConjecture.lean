/-
# Greedy 3-subsumfree sequences `S_{1,g,g+d}`

W. Bosma, R. Bruin, R. Fokkink, J. Grube, A. Reuijl and T. Tromp,
*Using Walnut to solve problems from the OEIS*, arXiv:2503.04122,
J. Integer Seq. 28 (2025), Art. 25.3.8, §"Subsumfreeness", Conjecture 17
(`conj_d_g`). A greedy 3-subsumfree sequence starts at `x < y < z` and
then takes the least larger integer not expressible as a sum of three
distinct earlier entries.

For `2 ≤ d`, `d+1 ≤ g`, the conjectured set consists of
`{1,g,2g+d-1,2g+d}` together with `z > g+d` whose residue modulo
`5g+2d` lies in `[g+d-2,2g+d-2]`. As printed this omits the start value
`g+d` (`printed_conj_17_false`). The paper's Walnut code for `S_{1,4,8}`
uses `z ≥ 8`; the corrected set `conjSet` uses `z ≥ g+d`.

The argument adapts the interval-sumset proof of the `d = 1` case by
O. Shtrezi, arXiv:2606.17447.

## Results

* `conj_17`: for `d ≥ 2`, `g ≥ d + 1`, every set obeying the greedy rule with start values
  `1, g, g + d` equals the corrected set `T_{g,d}` (`conjSet g d`).
* `conj_17_seq`: the same for the paper's sequence formulation: the range of every greedy
  sequence `a` (`IsGreedySeq`) is `T_{g,d}`; `exists_isGreedySeq` shows such a sequence exists.
* `conj_17_of_le`: the formula also holds at `g = d ≥ 3` (hypotheses `2 ≤ d ≤ g`, `3 ≤ g`); the
  pair `g = d = 2` genuinely fails (simulation), as do all `g < d` tested.
* The "in particular" periodicity remark is an immediate reading of the formula and is not
  separately formalized.
-/
import Mathlib

set_option autoImplicit false

namespace GreedySubsumfree

/-! ## Definitions -/

/-- `IsSum3Distinct S z`: `z` is a sum of three distinct elements of `S`, written `a < b < c`.
Since `a < b` forces `b ≥ 1`, any such summands are automatically smaller than `z`. -/
def IsSum3Distinct (S : Set ℕ) (z : ℕ) : Prop :=
  ∃ a b c, a < b ∧ b < c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a + b + c = z

/-- The greedy 3-subsumfree rule for the set of terms of `S_{x,y,w}`: the members of `S` up to `w`
are exactly the start values `x, y, w`, and an integer `z > w` belongs to `S` iff it is not a sum
of three distinct (necessarily smaller) members of `S`. For `x < y < w` this set is unique
(`IsGreedy3Subsumfree.eq`) and is the range of the greedy sequence
(`IsGreedySeq.isGreedy3Subsumfree`,
`IsGreedy3Subsumfree.isGreedySeq_nth`). -/
def IsGreedy3Subsumfree (x y w : ℕ) (S : Set ℕ) : Prop :=
  (∀ z, z ≤ w → (z ∈ S ↔ z = x ∨ z = y ∨ z = w)) ∧
    ∀ z, w < z → (z ∈ S ↔ ¬ IsSum3Distinct S z)

/-- The paper's greedy 3-subsumfree sequence `S_{x,y,w}`, 0-indexed: `a 0 = x`, `a 1 = y`,
`a 2 = w`, and for every later index `n + 3` the entry `a (n + 3)` is the smallest number exceeding
`a (n + 2)` which is not a sum `a i + a j + a k` of three different previous entries
`i < j < k < n + 3`. -/
def IsGreedySeq (x y w : ℕ) (a : ℕ → ℕ) : Prop :=
  a 0 = x ∧ a 1 = y ∧ a 2 = w ∧ ∀ n,
    a (n + 2) < a (n + 3) ∧
    (¬ ∃ i j k, i < j ∧ j < k ∧ k < n + 3 ∧ a i + a j + a k = a (n + 3)) ∧
    ∀ z, a (n + 2) < z → z < a (n + 3) →
      ∃ i j k, i < j ∧ j < k ∧ k < n + 3 ∧ a i + a j + a k = z

/-- The corrected conjectured set `T_{g,d}` of Conjecture 17: `z ∈ T_{g,d}` iff
`z ∈ {1, g, 2g + d - 1, 2g + d}`, or `z ≥ g + d` and `z mod (5g + 2d) ∈ [g + d - 2, 2g + d - 2]`.
(The paper prints `z > g + d`; see `printedConjSet`.) The truncated subtractions are harmless in
the intended range `d ≥ 2`, `g ≥ 1`. -/
def conjSet (g d : ℕ) : Set ℕ :=
  {z | z = 1 ∨ z = g ∨ z = 2 * g + d - 1 ∨ z = 2 * g + d ∨
    (g + d ≤ z ∧ g + d - 2 ≤ z % (5 * g + 2 * d) ∧ z % (5 * g + 2 * d) ≤ 2 * g + d - 2)}

/-- The set exactly as printed in Conjecture 17 of arXiv:2503.04122, with the strict inequality
`z > g + d`. -/
def printedConjSet (g d : ℕ) : Set ℕ :=
  {z | z = 1 ∨ z = g ∨ z = 2 * g + d - 1 ∨ z = 2 * g + d ∨
    (g + d < z ∧ g + d - 2 ≤ z % (5 * g + 2 * d) ∧ z % (5 * g + 2 * d) ≤ 2 * g + d - 2)}

/-- Membership in `conjSet g d` is decidable (used only for the examples below). -/
instance (g d : ℕ) : DecidablePred (· ∈ conjSet g d) := fun z => by
  unfold conjSet; infer_instance

/-! ## Examples

The greedy prefixes below were computed by direct simulation of the greedy rule;
`S_{1,4,8}` is the paper's Walnut example (`g = d = 4`, modulus `28`, residues `6..10`), and
`S_{1,3,5}` is `g = 3`, `d = 2` (modulus `19`, residues `3..7`). -/

example : ∀ z < 71, (z ∈ conjSet 4 4 ↔
    z ∈ ({1, 4, 8, 9, 10, 11, 12, 34, 35, 36, 37, 38, 62, 63, 64, 65, 66} : Finset ℕ)) := by
  decide

example : ∀ z < 61, (z ∈ conjSet 3 2 ↔
    z ∈ ({1, 3, 5, 6, 7, 8, 22, 23, 24, 25, 41, 42, 43, 44, 60} : Finset ℕ)) := by
  decide

/-- The greedy rule for `S_{1,4,8}` excludes `13 = 1 + 4 + 8`. -/
example (S : Set ℕ) (hS : IsGreedy3Subsumfree 1 4 8 S) : 13 ∉ S := by
  rw [hS.2 13 (by norm_num), not_not]
  exact ⟨1, 4, 8, by norm_num, by norm_num, (hS.1 1 (by norm_num)).2 (Or.inl rfl),
    (hS.1 4 (by norm_num)).2 (Or.inr (Or.inl rfl)),
    (hS.1 8 le_rfl).2 (Or.inr (Or.inr rfl)), rfl⟩

/-- The greedy rule for `S_{1,4,8}` admits `9`: the only members below `9` are `1, 4, 8`. -/
example (S : Set ℕ) (hS : IsGreedy3Subsumfree 1 4 8 S) : 9 ∈ S := by
  rw [hS.2 9 (by norm_num)]
  rintro ⟨a, b, c, hab, hbc, ha, hb, hc, hsum⟩
  have ha' := (hS.1 a (by omega)).1 ha
  have hb' := (hS.1 b (by omega)).1 hb
  have hc' := (hS.1 c (by omega)).1 hc
  omega

/-! ## Greedy sequences versus the greedy rule -/

/-- A greedy sequence with `x < y < w` is strictly increasing. -/
theorem IsGreedySeq.strictMono {x y w : ℕ} {a : ℕ → ℕ} (ha : IsGreedySeq x y w a)
    (hxy : x < y) (hyw : y < w) : StrictMono a := by
  obtain ⟨h0, h1, h2, hrec⟩ := ha
  refine strictMono_nat_of_lt_succ fun n => ?_
  match n with
  | 0 => rw [h0, h1]; exact hxy
  | 1 => rw [h1, h2]; exact hyw
  | n + 2 => exact (hrec n).1

/-- The range of a greedy sequence obeys the greedy rule. -/
theorem IsGreedySeq.isGreedy3Subsumfree {x y w : ℕ} {a : ℕ → ℕ} (ha : IsGreedySeq x y w a)
    (hxy : x < y) (hyw : y < w) : IsGreedy3Subsumfree x y w (Set.range a) := by
  have hmono := ha.strictMono hxy hyw
  obtain ⟨h0, h1, h2, hrec⟩ := ha
  -- every entry of index `≥ 3` exceeds `w`
  have hbig : ∀ n, w < a (n + 3) := fun n => by
    rw [← h2]; exact hmono (by omega)
  refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · rintro ⟨n, rfl⟩
    match n with
    | 0 => exact Or.inl h0
    | 1 => exact Or.inr (Or.inl h1)
    | 2 => exact Or.inr (Or.inr h2)
    | n + 3 => exact absurd hz (not_le.2 (hbig n))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  · rintro ⟨n, rfl⟩ ⟨p, q, r, hpq, hqr, ⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum⟩
    match n with
    | 0 => rw [h0] at hz; omega
    | 1 => rw [h1] at hz; omega
    | 2 => rw [h2] at hz; omega
    | n + 3 =>
      have hij : i < j := hmono.lt_iff_lt.1 hpq
      have hjk : j < k := hmono.lt_iff_lt.1 hqr
      have hkn : k < n + 3 := hmono.lt_iff_lt.1 (by omega)
      exact (hrec n).2.1 ⟨i, j, k, hij, hjk, hkn, hsum⟩
  · intro hns
    by_contra hnot
    have hex : ∃ n, z < a n := ⟨z + 1, lt_of_lt_of_le (Nat.lt_succ_self z) (hmono.id_le _)⟩
    let N := Nat.find hex
    have hN : z < a N := Nat.find_spec hex
    have hN3 : 3 ≤ N := by
      by_contra hlt
      have hle : a N ≤ a 2 := hmono.monotone (by omega)
      omega
    obtain ⟨M, hM⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
    have hprev : ¬ z < a (M + 2) := Nat.find_min hex (by omega)
    have hne : a (M + 2) ≠ z := fun h => hnot ⟨M + 2, h⟩
    rw [hM] at hN
    obtain ⟨i, j, k, hij, hjk, hkn, hsum⟩ := (hrec M).2.2 z (by omega) hN
    exact hns ⟨a i, a j, a k, hmono hij, hmono hjk, ⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum⟩

/-- **Uniqueness.** Two sets obeying the greedy rule with the same start values coincide
(strong induction: membership of `z > w` depends only on smaller members). -/
theorem IsGreedy3Subsumfree.eq {x y w : ℕ} {S S' : Set ℕ} (h : IsGreedy3Subsumfree x y w S)
    (h' : IsGreedy3Subsumfree x y w S') : S = S' := by
  ext z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases le_or_gt z w with hz | hz
    · rw [h.1 z hz, h'.1 z hz]
    · rw [h.2 z hz, h'.2 z hz]
      apply not_congr
      constructor
      · rintro ⟨a, b, c, hab, hbc, ha, hb, hc, hsum⟩
        exact ⟨a, b, c, hab, hbc, (ih a (by omega)).1 ha, (ih b (by omega)).1 hb,
          (ih c (by omega)).1 hc, hsum⟩
      · rintro ⟨a, b, c, hab, hbc, ha, hb, hc, hsum⟩
        exact ⟨a, b, c, hab, hbc, (ih a (by omega)).2 ha, (ih b (by omega)).2 hb,
          (ih c (by omega)).2 hc, hsum⟩

/-- A set obeying the greedy rule is infinite (a large non-member would need to be a sum of
three bounded members). -/
theorem IsGreedy3Subsumfree.infinite {x y w : ℕ} {S : Set ℕ}
    (hS : IsGreedy3Subsumfree x y w S) : S.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hz : 3 * B + w + 1 ∉ S := fun h => by have := hB h; omega
  have hsum : IsSum3Distinct S (3 * B + w + 1) := by
    by_contra hns
    exact hz ((hS.2 _ (by omega)).2 hns)
  obtain ⟨p, q, r, -, -, hp, hq, hr, hpqr⟩ := hsum
  have := hB hp
  have := hB hq
  have := hB hr
  omega

/-- Conversely, enumerating a set obeying the greedy rule (with `x < y < w`) in increasing order
gives a greedy sequence; in particular greedy sequences exist. -/
theorem IsGreedy3Subsumfree.isGreedySeq_nth {x y w : ℕ} {S : Set ℕ}
    (hS : IsGreedy3Subsumfree x y w S) (hxy : x < y) (hyw : y < w) :
    IsGreedySeq x y w (Nat.nth (· ∈ S)) := by
  have hinf : (Set.ofPred (· ∈ S)).Infinite := hS.infinite
  have hmono : StrictMono (Nat.nth (· ∈ S)) := Nat.nth_strictMono hinf
  have hmem : ∀ n, Nat.nth (· ∈ S) n ∈ S := Nat.nth_mem_of_infinite hinf
  have hrange : ∀ s ∈ S, ∃ n, Nat.nth (· ∈ S) n = s := fun s hs => by
    have hs' : s ∈ Set.range (Nat.nth (· ∈ S)) := by
      rw [Nat.range_nth_of_infinite hinf]; exact hs
    exact hs'
  set a := Nat.nth (· ∈ S) with ha_def
  -- small members of `S` are exactly `x, y, w`
  have hsmall : ∀ n, a n ≤ w → a n = x ∨ a n = y ∨ a n = w := fun n hn =>
    (hS.1 _ hn).1 (hmem n)
  have hxS : x ∈ S := (hS.1 x (by omega)).2 (Or.inl rfl)
  have hyS : y ∈ S := (hS.1 y (by omega)).2 (Or.inr (Or.inl rfl))
  have hwS : w ∈ S := (hS.1 w le_rfl).2 (Or.inr (Or.inr rfl))
  obtain ⟨i, hi⟩ := hrange x hxS
  obtain ⟨j, hj⟩ := hrange y hyS
  obtain ⟨k, hk⟩ := hrange w hwS
  have hij : i < j := hmono.lt_iff_lt.1 (by omega)
  have hjk : j < k := hmono.lt_iff_lt.1 (by omega)
  have hi0 : i = 0 := by
    by_contra hne
    have h0 : a 0 < a i := hmono (by omega)
    rcases hsmall 0 (by omega) with h | h | h <;> omega
  have hj1 : j = 1 := by
    by_contra hne
    have h1 : a 1 < a j := hmono (by omega)
    have h1' : a i < a 1 := hmono (by omega)
    rcases hsmall 1 (by omega) with h | h | h <;> omega
  have hk2 : k = 2 := by
    by_contra hne
    have h2 : a 2 < a k := hmono (by omega)
    have h2' : a j < a 2 := hmono (by omega)
    rcases hsmall 2 (by omega) with h | h | h <;> omega
  subst hi0 hj1 hk2
  refine ⟨hi, hj, hk, fun n => ⟨hmono (by omega), ?_, ?_⟩⟩
  · rintro ⟨i', j', k', hij', hjk', hkn', hsum⟩
    have hbig : w < a (n + 3) := by rw [← hk]; exact hmono (by omega)
    exact ((hS.2 _ hbig).1 (hmem (n + 3)))
      ⟨a i', a j', a k', hmono hij', hmono hjk', hmem i', hmem j', hmem k', hsum⟩
  · intro z hz1 hz2
    have hzw : w < z := by
      have : a 2 ≤ a (n + 2) := hmono.monotone (by omega)
      omega
    have hzS : z ∉ S := by
      intro hzS
      obtain ⟨m, rfl⟩ := hrange z hzS
      have h1 : n + 2 < m := hmono.lt_iff_lt.1 hz1
      have h2 : m < n + 3 := hmono.lt_iff_lt.1 hz2
      omega
    have hsum : IsSum3Distinct S z := by
      by_contra hns
      exact hzS ((hS.2 z hzw).2 hns)
    obtain ⟨p, q, r, hpq, hqr, hp, hq, hr, hpqr⟩ := hsum
    obtain ⟨i', rfl⟩ := hrange p hp
    obtain ⟨j', rfl⟩ := hrange q hq
    obtain ⟨k', rfl⟩ := hrange r hr
    exact ⟨i', j', k', hmono.lt_iff_lt.1 hpq, hmono.lt_iff_lt.1 hqr,
      hmono.lt_iff_lt.1 (by omega), hpqr⟩

/-! ## Arithmetic of `T_{g,d}` -/

/-- Three pairwise distinct members of `S` with sum `z` witness `IsSum3Distinct S z`. -/
theorem isSum3Distinct_of_ne {S : Set ℕ} {a b c z : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hsum : a + b + c = z) :
    IsSum3Distinct S z := by
  rcases Nat.lt_or_gt_of_ne hab with hab' | hab' <;>
  rcases Nat.lt_or_gt_of_ne hac with hac' | hac' <;>
  rcases Nat.lt_or_gt_of_ne hbc with hbc' | hbc'
  · exact ⟨a, b, c, hab', hbc', ha, hb, hc, hsum⟩
  · exact ⟨a, c, b, hac', hbc', ha, hc, hb, by omega⟩
  · omega
  · exact ⟨c, a, b, hac', hab', hc, ha, hb, by omega⟩
  · exact ⟨b, a, c, hab', hac', hb, ha, hc, by omega⟩
  · omega
  · exact ⟨b, c, a, hbc', hac', hb, hc, ha, by omega⟩
  · exact ⟨c, b, a, hbc', hab', hc, hb, ha, by omega⟩

variable {g d : ℕ}

/-- Every `(5g + 2d)k + r` with `r ∈ [g + d - 2, 2g + d - 2]` and value `≥ g + d` lies in
`T_{g,d}` (the periodic part). -/
theorem mem_conjSet_of_mod (k r : ℕ) (hr1 : g + d - 2 ≤ r) (hr2 : r ≤ 2 * g + d - 2)
    (hgd : g + d ≤ (5 * g + 2 * d) * k + r) (hg : 1 ≤ g) :
    (5 * g + 2 * d) * k + r ∈ conjSet g d := by
  have hr : r < 5 * g + 2 * d := by omega
  have hmod : ((5 * g + 2 * d) * k + r) % (5 * g + 2 * d) = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  right; right; right; right
  exact ⟨hgd, by rw [hmod]; exact hr1, by rw [hmod]; exact hr2⟩

/-- The whole initial interval `[g + d, 2g + d]` lies in `T_{g,d}`: its members below
`2g + d - 1` are periodic members of block 0, the last two are `2g + d - 1` and `2g + d`. -/
theorem mem_conjSet_of_le (hd : 2 ≤ d) (x : ℕ) (h1 : g + d ≤ x) (h2 : x ≤ 2 * g + d) :
    x ∈ conjSet g d := by
  have hx : x % (5 * g + 2 * d) = x := Nat.mod_eq_of_lt (by omega)
  show x = 1 ∨ x = g ∨ x = 2 * g + d - 1 ∨ x = 2 * g + d ∨ _
  rw [hx]
  omega

/-- Members of `T_{g,d}` are `1`, `g`, or at least `g + d`. -/
theorem lower_bounds_of_mem (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {x : ℕ}
    (hx : x ∈ conjSet g d) :
    1 ≤ x ∧ (x ≠ 1 → g ≤ x) ∧ (x ≠ 1 → x ≠ g → g + d ≤ x) := by
  rcases hx with h | h | h | h | h <;> omega

/-- Residue classification of a member `x` of `T_{g,d}` modulo `m = 5g + 2d`: `x` is one of the
exceptional values `1, g, 2g + d - 1, 2g + d` (each smaller than `m`, so equal to its residue),
or its residue lies in `R = [g + d - 2, 2g + d - 2]`. -/
theorem residue_of_mem (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {x : ℕ}
    (hx : x ∈ conjSet g d) :
    (x = 1 ∧ x % (5 * g + 2 * d) = 1) ∨ (x = g ∧ x % (5 * g + 2 * d) = g) ∨
    (x = 2 * g + d - 1 ∧ x % (5 * g + 2 * d) = 2 * g + d - 1) ∨
    (x = 2 * g + d ∧ x % (5 * g + 2 * d) = 2 * g + d) ∨
    (g + d - 2 ≤ x % (5 * g + 2 * d) ∧ x % (5 * g + 2 * d) ≤ 2 * g + d - 2) := by
  rcases hx with h | h | h | h | h
  · left; exact ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩
  · right; left; exact ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩
  · right; right; left; exact ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩
  · right; right; right; left; exact ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩
  · right; right; right; right; exact ⟨h.2.1, h.2.2⟩

/-- **Residue arithmetic (no member is forced).** If three entries `a < b < c` have residues
`ra, rb, rc` of the shape given by `residue_of_mem` (exceptional entries being pairwise distinct
because `a < b < c`), then `(ra + rb + rc) mod (5g + 2d)` lies outside `[g + d - 2, 2g + d - 2]`.
The proof splits `ra + rb + rc = j(5g + 2d) + r` with `j ∈ {0, 1, 2}`; each branch is linear. -/
theorem residue_sum_not_mem (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {a b c ra rb rc : ℕ}
    (hab : a < b) (hbc : b < c)
    (ha : (a = 1 ∧ ra = 1) ∨ (a = g ∧ ra = g) ∨ (a = 2 * g + d - 1 ∧ ra = 2 * g + d - 1) ∨
      (a = 2 * g + d ∧ ra = 2 * g + d) ∨ (g + d - 2 ≤ ra ∧ ra ≤ 2 * g + d - 2))
    (hb : (b = 1 ∧ rb = 1) ∨ (b = g ∧ rb = g) ∨ (b = 2 * g + d - 1 ∧ rb = 2 * g + d - 1) ∨
      (b = 2 * g + d ∧ rb = 2 * g + d) ∨ (g + d - 2 ≤ rb ∧ rb ≤ 2 * g + d - 2))
    (hc : (c = 1 ∧ rc = 1) ∨ (c = g ∧ rc = g) ∨ (c = 2 * g + d - 1 ∧ rc = 2 * g + d - 1) ∨
      (c = 2 * g + d ∧ rc = 2 * g + d) ∨ (g + d - 2 ≤ rc ∧ rc ≤ 2 * g + d - 2)) :
    ¬ (g + d - 2 ≤ (ra + rb + rc) % (5 * g + 2 * d) ∧
      (ra + rb + rc) % (5 * g + 2 * d) ≤ 2 * g + d - 2) := by
  have hdiv := Nat.div_add_mod (ra + rb + rc) (5 * g + 2 * d)
  have hlt : (ra + rb + rc) / (5 * g + 2 * d) < 3 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  generalize (ra + rb + rc) / (5 * g + 2 * d) = j at hdiv hlt
  generalize (ra + rb + rc) % (5 * g + 2 * d) = r at hdiv ⊢
  interval_cases j <;> omega

/-- **No member above `g + d` is forced.** A member `z > g + d` of `T_{g,d}` is not a sum of
three distinct members of `T_{g,d}`. For `z ∈ {2g + d - 1, 2g + d}` the least such sum is
`1 + g + (g + d) = 2g + d + 1`; for periodic `z` use `residue_sum_not_mem`. -/
theorem not_isSum3Distinct_of_mem (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {z : ℕ}
    (hz : z ∈ conjSet g d) (hzg : g + d < z) : ¬ IsSum3Distinct (conjSet g d) z := by
  rintro ⟨a, b, c, hab, hbc, ha, hb, hc, rfl⟩
  rcases hz with h | h | h | h | ⟨-, hz1, hz2⟩
  · omega
  · omega
  · have la := lower_bounds_of_mem hd hg hg3 ha
    have lb := lower_bounds_of_mem hd hg hg3 hb
    have lc := lower_bounds_of_mem hd hg hg3 hc
    omega
  · have la := lower_bounds_of_mem hd hg hg3 ha
    have lb := lower_bounds_of_mem hd hg hg3 hb
    have lc := lower_bounds_of_mem hd hg hg3 hc
    omega
  · have hmod : (a + b + c) % (5 * g + 2 * d) =
        (a % (5 * g + 2 * d) + b % (5 * g + 2 * d) + c % (5 * g + 2 * d)) %
          (5 * g + 2 * d) := by
      simp [Nat.add_mod]
    rw [hmod] at hz1 hz2
    exact residue_sum_not_mem hd hg hg3 hab hbc (residue_of_mem hd hg hg3 ha)
      (residue_of_mem hd hg hg3 hb) (residue_of_mem hd hg hg3 hc) ⟨hz1, hz2⟩

/-- **Every omitted integer above `g + d` is forced.** If `z > g + d` and `z ∉ T_{g,d}`, then `z`
is a sum of three distinct members of `T_{g,d}`; the witnesses are explicit, split by the block
`k = z / (5g + 2d)` and the residue `w = z % (5g + 2d)`. -/
theorem isSum3Distinct_of_not_mem (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {z : ℕ}
    (hz : z ∉ conjSet g d) (hzg : g + d < z) : IsSum3Distinct (conjSet g d) z := by
  have hdiv := Nat.div_add_mod z (5 * g + 2 * d)
  have hw : z % (5 * g + 2 * d) < 5 * g + 2 * d := Nat.mod_lt _ (by omega)
  generalize z / (5 * g + 2 * d) = k at hdiv
  generalize hwdef : z % (5 * g + 2 * d) = w at hdiv hw
  have hnot : z ≠ 1 ∧ z ≠ g ∧ z ≠ 2 * g + d - 1 ∧ z ≠ 2 * g + d ∧
      (w < g + d - 2 ∨ 2 * g + d - 2 < w) := by
    simp only [conjSet, Set.mem_ofPred_eq, not_or, not_and, not_le] at hz
    refine ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, ?_⟩
    have h5 := hz.2.2.2.2 (by omega)
    rw [hwdef] at h5
    by_contra hcon
    omega
  have hB : ∀ x, g + d ≤ x → x ≤ 2 * g + d → x ∈ conjSet g d :=
    fun x h1 h2 => mem_conjSet_of_le hd x h1 h2
  have h1 : (1 : ℕ) ∈ conjSet g d := Or.inl rfl
  have hgm : g ∈ conjSet g d := Or.inr (Or.inl rfl)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- block 0
    subst hk
    simp only [mul_zero, zero_add] at hdiv
    subst hdiv
    have hz1 : 2 * g + d + 1 ≤ w := by omega
    by_cases hA : w ≤ 3 * g + d + 1
    · exact isSum3Distinct_of_ne h1 hgm (hB (w - 1 - g) (by omega) (by omega))
        (by omega) (by omega) (by omega) (by omega)
    by_cases hB' : w ≤ 3 * g + 2 * d + 1
    · exact isSum3Distinct_of_ne h1 (hB (g + d) le_rfl (by omega))
        (hB (w - 1 - g - d) (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)
    by_cases hC : w ≤ 4 * g + 2 * d
    · exact isSum3Distinct_of_ne h1 (hB (w - 1 - 2 * g - d) (by omega) (by omega))
        (hB (2 * g + d) (by omega) le_rfl) (by omega) (by omega) (by omega) (by omega)
    · exact isSum3Distinct_of_ne hgm (hB (w - 3 * g - d) (by omega) (by omega))
        (hB (2 * g + d) (by omega) le_rfl) (by omega) (by omega) (by omega) (by omega)
  · -- block `k = k' + 1 ≥ 1`
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hQ : (5 * g + 2 * d) * (k' + 1) = (5 * g + 2 * d) * k' + (5 * g + 2 * d) := by ring
    have hblk : ∀ r, g + d - 2 ≤ r → r ≤ 2 * g + d - 2 →
        (5 * g + 2 * d) * (k' + 1) + r ∈ conjSet g d := fun r hr1 hr2 =>
      mem_conjSet_of_mod (k' + 1) r hr1 hr2 (by omega) (by omega)
    have he : 2 * g + d - 1 ∈ conjSet g d := hB _ (by omega) (by omega)
    have hf : 2 * g + d ∈ conjSet g d := hB _ (by omega) le_rfl
    rcases hnot.2.2.2.2 with hlow | hhigh
    · -- wrap-around residues `w ∈ [0, g + d - 3]`
      by_cases hsmall : w ≤ d - 2
      · rcases Nat.eq_zero_or_pos k' with hk' | hk'
        · subst hk'
          by_cases hgw : d < g + w
          · exact isSum3Distinct_of_ne (hB (g + d) le_rfl (by omega)) (hB (2 * g + w) (by omega)
              (by omega)) hf (by omega) (by omega) (by omega) (by omega)
          · -- only `g = d`, `w = 0`: `5g + 2d = (g + d) + (g + d + 1) + (3g - 1)`
            exact isSum3Distinct_of_ne (hB (g + d) le_rfl (by omega))
              (hB (g + d + 1) (by omega) (by omega)) (hB (3 * g - 1) (by omega) (by omega))
              (by omega) (by omega) (by omega) (by omega)
        · have hPm : 5 * g + 2 * d ≤ (5 * g + 2 * d) * k' := Nat.le_mul_of_pos_right _ hk'
          exact isSum3Distinct_of_ne (hB (g + d) le_rfl (by omega))
            (hB (2 * g + 2 + w) (by omega) (by omega))
            (mem_conjSet_of_mod k' (2 * g + d - 2) (by omega) le_rfl (by omega) (by omega))
            (by omega) (by omega) (by omega) (by omega)
      · have hP : (5 * g + 2 * d) * k' = 0 ∨ 5 * g + 2 * d ≤ (5 * g + 2 * d) * k' := by
          rcases Nat.eq_zero_or_pos k' with hk' | hk'
          · left; rw [hk', mul_zero]
          · right; exact Nat.le_mul_of_pos_right _ hk'
        exact isSum3Distinct_of_ne
          (mem_conjSet_of_mod k' (g + w + 1) (by omega) (by omega) (by omega) (by omega)) he hf
          (by omega) (by omega) (by omega) (by omega)
    · -- residues `w ∈ [2g + d - 1, 5g + 2d - 1]`
      by_cases hA : w ≤ 3 * g + d - 1
      · exact isSum3Distinct_of_ne h1 hgm (hblk (w - 1 - g) (by omega) (by omega))
          (by omega) (by omega) (by omega) (by omega)
      by_cases hB' : w ≤ 3 * g + 2 * d - 1
      · exact isSum3Distinct_of_ne h1 (hB (w - g - d + 1) (by omega) (by omega))
          (hblk (g + d - 2) le_rfl (by omega)) (by omega) (by omega) (by omega) (by omega)
      by_cases hC : w ≤ 4 * g + 2 * d - 1
      · exact isSum3Distinct_of_ne h1 hf (hblk (w - 2 * g - d - 1) (by omega) (by omega))
          (by omega) (by omega) (by omega) (by omega)
      by_cases hD : w ≤ 5 * g + 2 * d - 2
      · exact isSum3Distinct_of_ne hgm hf (hblk (w - 3 * g - d) (by omega) (by omega))
          (by omega) (by omega) (by omega) (by omega)
      · exact isSum3Distinct_of_ne (hB (2 * g + 1) (by omega) (by omega)) hf
          (hblk (g + d - 2) le_rfl (by omega)) (by omega) (by omega) (by omega) (by omega)

/-! ## The meta-conjecture -/

/-- `T_{g,d}` obeys the greedy rule with start values `1, g, g + d`, whenever `2 ≤ d ≤ g` and
`3 ≤ g` (this covers the conjectured range `g ≥ d + 1` and the extra diagonal `g = d ≥ 3`). -/
theorem conjSet_isGreedy (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) :
    IsGreedy3Subsumfree 1 g (g + d) (conjSet g d) := by
  refine ⟨fun z hz => ⟨fun hmem => ?_, fun hz' => ?_⟩, fun z hz =>
    ⟨fun hmem => not_isSum3Distinct_of_mem hd hg hg3 hmem hz, fun hns => ?_⟩⟩
  · rcases hmem with h | h | h | h | ⟨h1, -, -⟩ <;> omega
  · rcases hz' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact mem_conjSet_of_le hd z (by omega) (by omega)
  · by_contra hcon
    exact hns (isSum3Distinct_of_not_mem hd hg hg3 hcon hz)

/-- **Conjecture 17 of arXiv:2503.04122, corrected and generalized to `2 ≤ d ≤ g`, `3 ≤ g`.**
The greedy 3-subsumfree set with start values `1, g, g + d` equals `T_{g,d}`. -/
theorem conj_17_of_le (hd : 2 ≤ d) (hg : d ≤ g) (hg3 : 3 ≤ g) {S : Set ℕ}
    (hS : IsGreedy3Subsumfree 1 g (g + d) S) : S = conjSet g d :=
  hS.eq (conjSet_isGreedy hd hg hg3)

/-- **Conjecture 17 of arXiv:2503.04122 (Bosma–Bruin–Fokkink–Grube–Reuijl–Tromp), corrected.**
Let `d ≥ 2` and `g ≥ d + 1`. Then the greedy 3-subsumfree set `S_{1,g,g+d}` is characterized by
`z ∈ S_{1,g,g+d} ⟺ z ∈ {1, g, 2g + d - 1, 2g + d}` or (`z ≥ g + d` and
`z mod (5g + 2d) ∈ [g + d - 2, 2g + d - 2]`). -/
theorem conj_17 (hd : 2 ≤ d) (hg : d + 1 ≤ g) {S : Set ℕ}
    (hS : IsGreedy3Subsumfree 1 g (g + d) S) : S = conjSet g d :=
  conj_17_of_le hd (by omega) (by omega) hS

/-- **Conjecture 17, sequence form.** For `d ≥ 2`, `g ≥ d + 1`, the set of entries of the greedy
3-subsumfree sequence `S_{1,g,g+d}` (any `a` satisfying `IsGreedySeq 1 g (g + d) a`) is
`T_{g,d}`. -/
theorem conj_17_seq (hd : 2 ≤ d) (hg : d + 1 ≤ g) {a : ℕ → ℕ}
    (ha : IsGreedySeq 1 g (g + d) a) : Set.range a = conjSet g d :=
  conj_17 hd hg (ha.isGreedy3Subsumfree (by omega) (by omega))

/-- Non-vacuity: for `d ≥ 2`, `g ≥ d + 1` the greedy sequence `S_{1,g,g+d}` exists (it is the
increasing enumeration of `T_{g,d}`). -/
theorem exists_isGreedySeq (hd : 2 ≤ d) (hg : d + 1 ≤ g) :
    ∃ a : ℕ → ℕ, IsGreedySeq 1 g (g + d) a :=
  ⟨_, (conjSet_isGreedy hd (by omega) (by omega)).isGreedySeq_nth (by omega) (by omega)⟩

/-- **The printed statement is false.** For `d ≥ 1`, `g ≥ 2`, the start value `g + d` belongs to
every greedy set `S_{1,g,g+d}` but not to the printed set (which demands `z > g + d`), so the
characterization as printed in arXiv:2503.04122 fails at `z = g + d`. -/
theorem printed_conj_17_false (hd : 1 ≤ d) (hg : 2 ≤ g) {S : Set ℕ}
    (hS : IsGreedy3Subsumfree 1 g (g + d) S) : g + d ∈ S ∧ g + d ∉ printedConjSet g d := by
  refine ⟨(hS.1 (g + d) le_rfl).2 (Or.inr (Or.inr rfl)), ?_⟩
  rintro (h | h | h | h | ⟨h, -, -⟩) <;> omega

/-- Satisfiability of the hypotheses of `conj_17` at `g = 3`, `d = 2` (the set `S_{1,3,5}`). -/
example : IsGreedy3Subsumfree 1 3 (3 + 2) (conjSet 3 2) :=
  conjSet_isGreedy (by norm_num) (by norm_num) (by norm_num)

end GreedySubsumfree
