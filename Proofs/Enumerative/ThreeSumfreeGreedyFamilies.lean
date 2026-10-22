/-
Strict greedy 3-sumfree families S_{f,g,g+1}.

Source: Daan van Berkel and Wieb Bosma, On t-sumfree sequences,
arXiv:2609.16843, §6, Theorems thm:k=1d=1 and thm:d=1.
A strict greedy sequence excludes sums of three distinct previous terms.
For 1≤f<g, the unique support with seeds f,g,g+1 is
 {f,2g+f,6g+3f-2} ∪ {z : z mod M ∈ [g,2g+f-1] ∪ [6g+3f-1,7g+4f-3]},
where M=10g+6f-3.

The support is periodic with shift M from 6g+3f-1; the preceding point
6g+3f-2 breaks that shift. This is the set form of the paper's difference
pattern, not a theorem about the difference-sequence object or its lengths.
The f=1 specialization gives thm:k=1d=1, and g=2 gives OEIS A026471,
attributed in the source to Akeran (2004). No general all-seeds theorem is claimed.
-/
import Mathlib

set_option autoImplicit false

namespace ThreeSumfreeGreedyFamilies

/-- `z` is a sum of three distinct elements of `S`, all smaller than `z`. -/
def IsThreeSum (S : Set ℕ) (z : ℕ) : Prop :=
  ∃ a b c, a < b ∧ b < c ∧ c < z ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a + b + c = z

/-- The greedy strict 3-sumfree set started at `f < g < h`. -/
def IsGreedy3SumFree (f g h : ℕ) (S : Set ℕ) : Prop :=
  (∀ z, z ≤ h → (z ∈ S ↔ z = f ∨ z = g ∨ z = h)) ∧
    ∀ z, h < z → (z ∈ S ↔ ¬ IsThreeSum S z)

/-- The explicit set for `S_{f,g,g+1}`. -/
def familySet (f g : ℕ) : Set ℕ :=
  {z | z = f ∨ z = 2 * g + f ∨ z = 6 * g + 3 * f - 2 ∨
    (g ≤ z % (10 * g + 6 * f - 3) ∧ z % (10 * g + 6 * f - 3) ≤ 2 * g + f - 1) ∨
    (6 * g + 3 * f - 1 ≤ z % (10 * g + 6 * f - 3) ∧
      z % (10 * g + 6 * f - 3) ≤ 7 * g + 4 * f - 3)}

/-! ### Examples on the paper's examples -/

/-- `6 = 1 + 2 + 3` is a 3-sum of distinct members of `{1, 2, 3}`. -/
example : IsThreeSum {1, 2, 3} 6 := ⟨1, 2, 3, by decide, by decide, by decide,
  by simp, by simp, by simp, rfl⟩

/-- The first 22 terms of `S_{1,2,3}` listed in the paper agree with `familySet 1 2`
below `84`. -/
example : ∀ z < 84, z ∈ familySet 1 2 ↔
    z ∈ ({1, 2, 3, 4, 5, 13, 14, 15, 25, 26, 27, 37, 38, 48, 49, 50, 60, 61, 71, 72, 73,
      83} : Finset ℕ) := by
  unfold familySet
  simp only [Set.mem_ofPred_eq]
  decide

/-- The paper's example `S_{4,7,8} = (4, 7⋯18, 52⋯62, 98⋯108, 144⋯153, 189⋯199, ⋯)`
agrees with `familySet 4 7` below `200`. -/
example : ∀ z < 200, z ∈ familySet 4 7 ↔
    (z = 4 ∨ (7 ≤ z ∧ z ≤ 18) ∨ (52 ≤ z ∧ z ≤ 62) ∨ (98 ≤ z ∧ z ≤ 108) ∨
      (144 ≤ z ∧ z ≤ 153) ∨ (189 ≤ z ∧ z ≤ 199)) := by
  unfold familySet
  simp only [Set.mem_ofPred_eq]
  set_option maxRecDepth 4000 in decide

/-- Three residues below `m` sum to `r` modulo `m` up to at most two wraps. -/
lemma sum_mod_cases (a b c z m : ℕ) (hm : 0 < m) (h : a + b + c = z) :
    a % m + b % m + c % m = z % m ∨ a % m + b % m + c % m = z % m + m ∨
      a % m + b % m + c % m = z % m + 2 * m := by
  have hmod : (a % m + b % m + c % m) % m = z % m := by
    rw [← h]; simp [Nat.add_mod]
  set s := a % m + b % m + c % m with hs
  have ha := Nat.mod_lt a hm
  have hb := Nat.mod_lt b hm
  have hc := Nat.mod_lt c hm
  have hdiv := Nat.div_add_mod s m
  have hq : s / m < 3 := by
    rw [Nat.div_lt_iff_lt_mul hm]; omega
  rw [hmod] at hdiv
  interval_cases hq' : s / m <;> omega

/-- Membership in the family set, unfolded with an abstract modulus `m`. -/
lemma mem_familySet_iff (f g m z : ℕ) (hm : m = 10 * g + 6 * f - 3) :
    z ∈ familySet f g ↔ z = f ∨ z = 2 * g + f ∨ z = 6 * g + 3 * f - 2 ∨
      (g ≤ z % m ∧ z % m ≤ 2 * g + f - 1) ∨
      (6 * g + 3 * f - 1 ≤ z % m ∧ z % m ≤ 7 * g + 4 * f - 3) := by
  subst hm; rfl

/-- Residue-level description of a member: a special value (equal to its own
residue) or a residue in one of the two periodic windows. -/
lemma mem_familySet_residue (f g m z : ℕ) (hf : 1 ≤ f) (hfg : f < g)
    (hm : m = 10 * g + 6 * f - 3) (hz : z ∈ familySet f g) :
    (z = f ∧ z % m = f) ∨ (z = 2 * g + f ∧ z % m = 2 * g + f) ∨
      (z = 6 * g + 3 * f - 2 ∧ z % m = 6 * g + 3 * f - 2) ∨
      (g ≤ z % m ∧ z % m ≤ 2 * g + f - 1) ∨
      (6 * g + 3 * f - 1 ≤ z % m ∧ z % m ≤ 7 * g + 4 * f - 3) := by
  rw [mem_familySet_iff f g m z hm] at hz
  rcases hz with h | h | h | h | h
  · exact Or.inl ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩
  · exact Or.inr (Or.inl ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, by rw [h]; exact Nat.mod_eq_of_lt (by omega)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Below the modulus, membership is a condition on the value itself. -/
lemma mem_familySet_of_lt (f g m z : ℕ) (hm : m = 10 * g + 6 * f - 3) (hzm : z < m) :
    z ∈ familySet f g ↔ z = f ∨ z = 2 * g + f ∨ z = 6 * g + 3 * f - 2 ∨
      (g ≤ z ∧ z ≤ 2 * g + f - 1) ∨ (6 * g + 3 * f - 1 ≤ z ∧ z ≤ 7 * g + 4 * f - 3) := by
  rw [mem_familySet_iff f g m z hm, Nat.mod_eq_of_lt hzm]

/-- The residue computation behind closure: three distinct members whose residues
are in the allowed classes never sum to a window residue modulo `m`. -/
lemma residue_contra (f g m a b c ra rb rc rz : ℕ) (hf : 1 ≤ f) (hfg : f < g)
    (hm : m = 10 * g + 6 * f - 3) (hab : a < b) (hbc : b < c)
    (hra : (a = f ∧ ra = f) ∨ (a = 2 * g + f ∧ ra = 2 * g + f) ∨
      (a = 6 * g + 3 * f - 2 ∧ ra = 6 * g + 3 * f - 2) ∨
      (g ≤ ra ∧ ra ≤ 2 * g + f - 1) ∨ (6 * g + 3 * f - 1 ≤ ra ∧ ra ≤ 7 * g + 4 * f - 3))
    (hrb : (b = f ∧ rb = f) ∨ (b = 2 * g + f ∧ rb = 2 * g + f) ∨
      (b = 6 * g + 3 * f - 2 ∧ rb = 6 * g + 3 * f - 2) ∨
      (g ≤ rb ∧ rb ≤ 2 * g + f - 1) ∨ (6 * g + 3 * f - 1 ≤ rb ∧ rb ≤ 7 * g + 4 * f - 3))
    (hrc : (c = f ∧ rc = f) ∨ (c = 2 * g + f ∧ rc = 2 * g + f) ∨
      (c = 6 * g + 3 * f - 2 ∧ rc = 6 * g + 3 * f - 2) ∨
      (g ≤ rc ∧ rc ≤ 2 * g + f - 1) ∨ (6 * g + 3 * f - 1 ≤ rc ∧ rc ≤ 7 * g + 4 * f - 3))
    (hzr : (g ≤ rz ∧ rz ≤ 2 * g + f - 1) ∨
      (6 * g + 3 * f - 1 ≤ rz ∧ rz ≤ 7 * g + 4 * f - 3))
    (hcases : ra + rb + rc = rz ∨ ra + rb + rc = rz + m ∨ ra + rb + rc = rz + 2 * m) :
    False := by
  subst hm
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have h1 : 10 * g + 6 * (e + 1) - 3 = 10 * g + 6 * e + 3 := by omega
  have h2 : 2 * g + (e + 1) - 1 = 2 * g + e := by omega
  have h3 : 6 * g + 3 * (e + 1) - 2 = 6 * g + 3 * e + 1 := by omega
  have h4 : 6 * g + 3 * (e + 1) - 1 = 6 * g + 3 * e + 2 := by omega
  have h5 : 7 * g + 4 * (e + 1) - 3 = 7 * g + 4 * e + 1 := by omega
  rw [h1] at hcases
  rw [h2, h3, h4, h5] at hra hrb hrc
  rw [h2, h4, h5] at hzr
  clear h1 h2 h3 h4 h5
  rcases hzr with hz | hz <;> rcases hcases with hs | hs | hs <;>
  rcases hra with ha | ha | ha | ha | ha <;> rcases hrb with hb | hb | hb | hb | hb <;>
    rcases hrc with hc | hc | hc | hc | hc <;> omega

/-- Closure: no element of the family set above `g + 1` is a 3-sum. -/
lemma not_isThreeSum_of_mem (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) (z : ℕ)
    (hz : z ∈ familySet f g) (hzh : g + 1 < z) : ¬ IsThreeSum (familySet f g) z := by
  rintro ⟨a, b, c, hab, hbc, hcz, ha, hb, hc, hsum⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 10 * g + 6 * f - 3 := ⟨_, rfl⟩
  by_cases hzm : z < m
  · -- Every summand is below the modulus: a value-level contradiction
    rw [mem_familySet_of_lt f g m a hm (by omega)] at ha
    rw [mem_familySet_of_lt f g m b hm (by omega)] at hb
    rw [mem_familySet_of_lt f g m c hm (by omega)] at hc
    rw [mem_familySet_of_lt f g m z hm hzm] at hz
    rcases ha with ha | ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb | hb <;>
      rcases hc with hc | hc | hc | hc | hc <;> omega
  · -- `z` is not special, so its residue lies in a window
    have hzr : (g ≤ z % m ∧ z % m ≤ 2 * g + f - 1) ∨
        (6 * g + 3 * f - 1 ≤ z % m ∧ z % m ≤ 7 * g + 4 * f - 3) := by
      rw [mem_familySet_iff f g m z hm] at hz; omega
    have hcases := sum_mod_cases a b c z m (by omega) hsum
    have hra := mem_familySet_residue f g m a hf hfg hm ha
    have hrb := mem_familySet_residue f g m b hf hfg hm hb
    have hrc := mem_familySet_residue f g m c hf hfg hm hc
    generalize a % m = ra at hra hcases
    generalize b % m = rb at hrb hcases
    generalize c % m = rc at hrc hcases
    generalize z % m = rz at hzr hcases
    exact residue_contra f g m a b c ra rb rc rz hf hfg hm hab hbc hra hrb hrc hzr hcases

/-- Two distinct integers in `[L, U]` realize every sum in `[2L+1, 2U-1]`. -/
lemma pair_interval (L U s : ℕ) (h1 : 2 * L + 1 ≤ s) (h2 : s + 1 ≤ 2 * U) :
    ∃ x y, L ≤ x ∧ x < y ∧ y ≤ U ∧ x + y = s := by
  by_cases hs : s ≤ L + U
  · exact ⟨L, s - L, le_rfl, by omega, by omega, by omega⟩
  · exact ⟨s - U, U, by omega, by omega, le_rfl, by omega⟩

/-- Three distinct integers in `[L, U]` realize every sum in `[3L+3, 3U-3]`. -/
lemma triple_interval (L U s : ℕ) (h1 : 3 * L + 3 ≤ s) (h2 : s + 3 ≤ 3 * U) :
    ∃ x y w, L ≤ x ∧ x < y ∧ y < w ∧ w ≤ U ∧ x + y + w = s := by
  by_cases hs : s + 1 ≤ 2 * U + L
  · obtain ⟨y, w, hy, hyw, hw, hsum⟩ := pair_interval (L + 1) U (s - L) (by omega) (by omega)
    exact ⟨L, y, w, le_rfl, by omega, hyw, hw, by omega⟩
  · obtain ⟨x, y, hx, hxy, hy, hsum⟩ := pair_interval L (U - 1) (s - U) (by omega) (by omega)
    exact ⟨x, y, U, hx, hxy, by omega, le_rfl, by omega⟩

/-- An element of `[L₁, U₁]` plus an element of `[L₂, U₂]` realizes every sum in
`[L₁ + L₂, U₁ + U₂]`. -/
lemma pair_two (L₁ U₁ L₂ U₂ s : ℕ) (h₁ : L₁ ≤ U₁) (h₂ : L₂ ≤ U₂) (hs₁ : L₁ + L₂ ≤ s)
    (hs₂ : s ≤ U₁ + U₂) : ∃ x y, L₁ ≤ x ∧ x ≤ U₁ ∧ L₂ ≤ y ∧ y ≤ U₂ ∧ x + y = s := by
  by_cases hs : s ≤ L₁ + U₂
  · exact ⟨L₁, s - L₁, le_rfl, h₁, by omega, by omega, by omega⟩
  · exact ⟨s - U₂, U₂, by omega, by omega, h₂, le_rfl, by omega⟩

/-- `f` belongs to the family set. -/
lemma f_mem_familySet (f g : ℕ) : f ∈ familySet f g := Or.inl rfl

/-- The initial block `[g, 2g+f]` lies in the family set. -/
lemma mem_familySet_of_low (f g x : ℕ) (hf : 1 ≤ f) (h1 : g ≤ x) (h2 : x ≤ 2 * g + f) :
    x ∈ familySet f g := by
  rw [mem_familySet_of_lt f g _ x rfl (by omega)]; omega

/-- The block `[6g+3f-2, 7g+4f-3]` lies in the family set. -/
lemma mem_familySet_of_high (f g x : ℕ) (hf : 1 ≤ f) (h1 : 6 * g + 3 * f - 2 ≤ x)
    (h2 : x ≤ 7 * g + 4 * f - 3) : x ∈ familySet f g := by
  rw [mem_familySet_of_lt f g _ x rfl (by omega)]; omega

/-- A shift by a multiple of the modulus of a window residue is in the family set. -/
lemma mem_familySet_of_shift (f g m k r : ℕ) (hf : 1 ≤ f) (hm : m = 10 * g + 6 * f - 3)
    (hr : (g ≤ r ∧ r ≤ 2 * g + f - 1) ∨ (6 * g + 3 * f - 1 ≤ r ∧ r ≤ 7 * g + 4 * f - 3)) :
    m * k + r ∈ familySet f g := by
  have hrm : r < m := by omega
  have hmod : (m * k + r) % m = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrm]
  rw [mem_familySet_iff f g m _ hm, hmod]; omega

/-- Two distinct members up to `2g+f` realize every sum in `[f+g, 4g+2f-1]`. -/
lemma pair_small (f g s : ℕ) (hf : 1 ≤ f) (hfg : f < g) (h1 : f + g ≤ s)
    (h2 : s ≤ 4 * g + 2 * f - 1) :
    ∃ x y, x < y ∧ y ≤ 2 * g + f ∧ x ∈ familySet f g ∧ y ∈ familySet f g ∧ x + y = s := by
  by_cases hs : s ≤ 2 * g + 2 * f
  · exact ⟨f, s - f, by omega, by omega, f_mem_familySet f g,
      mem_familySet_of_low f g _ hf (by omega) (by omega), by omega⟩
  · obtain ⟨x, y, hx, hxy, hy, hsum⟩ := pair_interval g (2 * g + f) s (by omega) (by omega)
    exact ⟨x, y, hxy, hy, mem_familySet_of_low f g x hf hx (by omega),
      mem_familySet_of_low f g y hf (by omega) hy, hsum⟩

/-- Two distinct members up to `7g+4f-3` realize every sum in `[6g+4f-2, 9g+5f-3]`. -/
lemma pair_big (f g s : ℕ) (hf : 1 ≤ f) (hfg : f < g) (h1 : 6 * g + 4 * f - 2 ≤ s)
    (h2 : s ≤ 9 * g + 5 * f - 3) :
    ∃ x y, x < y ∧ y ≤ 7 * g + 4 * f - 3 ∧ x ∈ familySet f g ∧ y ∈ familySet f g ∧
      x + y = s := by
  by_cases hs : s ≤ 7 * g + 5 * f - 3
  · exact ⟨f, s - f, by omega, by omega, f_mem_familySet f g,
      mem_familySet_of_high f g _ hf (by omega) (by omega), by omega⟩
  · obtain ⟨x, y, hx, hx', hy, hy', hsum⟩ :=
      pair_two g (2 * g + f) (6 * g + 3 * f - 2) (7 * g + 4 * f - 3) s
        (by omega) (by omega) (by omega) (by omega)
    exact ⟨x, y, by omega, hy', mem_familySet_of_low f g x hf hx hx',
      mem_familySet_of_high f g y hf hy hy', hsum⟩

/-- Completeness: every non-member above `g + 1` is a sum of three distinct smaller
members of the family set. -/
lemma isThreeSum_of_not_mem (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) (z : ℕ)
    (hz : z ∉ familySet f g) (hzh : g + 1 < z) : IsThreeSum (familySet f g) z := by
  obtain ⟨m, hm⟩ : ∃ m, m = 10 * g + 6 * f - 3 := ⟨_, rfl⟩
  have hdiv := Nat.div_add_mod z m
  have hrm : z % m < m := Nat.mod_lt z (by omega)
  rw [mem_familySet_iff f g m z hm] at hz
  generalize z % m = r at hdiv hrm hz
  generalize z / m = q at hdiv
  rcases q with _ | k
  · -- Below the modulus: three summands from the initial blocks
    simp only [Nat.mul_zero, Nat.zero_add] at hdiv
    subst hdiv
    by_cases hA : r ≤ 4 * g + 3 * f - 1
    · obtain ⟨x, y, hx, hxy, hy, hsum⟩ := pair_interval g (2 * g + f) (r - f) (by omega) (by omega)
      exact ⟨f, x, y, by omega, hxy, by omega, f_mem_familySet f g,
        mem_familySet_of_low f g x hf hx (by omega), mem_familySet_of_low f g y hf (by omega) hy,
        by omega⟩
    by_cases hB : r ≤ 6 * g + 3 * f - 3
    · obtain ⟨x, y, w, hx, hxy, hyw, hw, hsum⟩ :=
        triple_interval g (2 * g + f) r (by omega) (by omega)
      exact ⟨x, y, w, hxy, hyw, by omega, mem_familySet_of_low f g x hf hx (by omega),
        mem_familySet_of_low f g y hf (by omega) (by omega),
        mem_familySet_of_low f g w hf (by omega) hw, hsum⟩
    by_cases hC : r ≤ 9 * g + 6 * f - 3
    · obtain ⟨x, y, hx, hx', hy, hy', hsum⟩ :=
        pair_two g (2 * g + f) (6 * g + 3 * f - 2) (7 * g + 4 * f - 3) (r - f)
          (by omega) (by omega) (by omega) (by omega)
      exact ⟨f, x, y, by omega, by omega, by omega, f_mem_familySet f g,
        mem_familySet_of_low f g x hf hx hx', mem_familySet_of_high f g y hf hy hy', by omega⟩
    · obtain ⟨x, y, hx, hxy, hy, hsum⟩ :=
        pair_interval g (2 * g + f) (r - (7 * g + 4 * f - 3)) (by omega) (by omega)
      exact ⟨x, y, 7 * g + 4 * f - 3, hxy, by omega, by omega,
        mem_familySet_of_low f g x hf hx (by omega), mem_familySet_of_low f g y hf (by omega) hy,
        mem_familySet_of_high f g _ hf (by omega) le_rfl, by omega⟩
  · -- At or above the modulus: a shifted window element plus a small pair
    have hmk : m * (k + 1) = m * k + m := by ring
    rw [hmk] at hdiv
    have hz' : ¬ ((g ≤ r ∧ r ≤ 2 * g + f - 1) ∨
        (6 * g + 3 * f - 1 ≤ r ∧ r ≤ 7 * g + 4 * f - 3)) := by
      intro h; exact hz (Or.inr (Or.inr (Or.inr h)))
    by_cases h0 : r < g
    · have hc := mem_familySet_of_shift f g m k (7 * g + 4 * f - 3) hf hm (by omega)
      obtain ⟨x, y, hxy, hy, hx, hy', hsum⟩ :=
        pair_small f g (m + r - (7 * g + 4 * f - 3)) hf hfg (by omega) (by omega)
      exact ⟨x, y, _, hxy, by omega, by omega, hx, hy', hc, by omega⟩
    by_cases h1 : r ≤ 3 * g + 2 * f - 1
    · have hc := mem_familySet_of_shift f g m (k + 1) g hf hm (by omega)
      rw [hmk] at hc
      obtain ⟨x, y, hxy, hy, hx, hy', hsum⟩ := pair_small f g (r - g) hf hfg (by omega) (by omega)
      exact ⟨x, y, _, hxy, by omega, by omega, hx, hy', hc, by omega⟩
    by_cases h2 : r ≤ 6 * g + 3 * f - 2
    · have hc := mem_familySet_of_shift f g m (k + 1) (2 * g + f - 1) hf hm (by omega)
      rw [hmk] at hc
      obtain ⟨x, y, hxy, hy, hx, hy', hsum⟩ :=
        pair_small f g (r - (2 * g + f - 1)) hf hfg (by omega) (by omega)
      exact ⟨x, y, _, hxy, by omega, by omega, hx, hy', hc, by omega⟩
    by_cases h3 : r ≤ 10 * g + 5 * f - 3
    · have hc := mem_familySet_of_shift f g m (k + 1) g hf hm (by omega)
      rw [hmk] at hc
      obtain ⟨x, y, hxy, hy, hx, hy', hsum⟩ := pair_big f g (r - g) hf hfg (by omega) (by omega)
      exact ⟨x, y, _, hxy, by omega, by omega, hx, hy', hc, by omega⟩
    · have hc := mem_familySet_of_shift f g m (k + 1) (2 * g + f - 1) hf hm (by omega)
      rw [hmk] at hc
      obtain ⟨x, y, hxy, hy, hx, hy', hsum⟩ :=
        pair_big f g (r - (2 * g + f - 1)) hf hfg (by omega) (by omega)
      exact ⟨x, y, _, hxy, by omega, by omega, hx, hy', hc, by omega⟩

/-- The greedy strict 3-sumfree set with given initial terms is unique: membership of
each `z` is determined by membership of the integers below `z`. -/
theorem IsGreedy3SumFree.unique {f g h : ℕ} {S S' : Set ℕ} (hS : IsGreedy3SumFree f g h S)
    (hS' : IsGreedy3SumFree f g h S') : S = S' := by
  ext z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    by_cases hz : z ≤ h
    · rw [hS.1 z hz, hS'.1 z hz]
    · have hz' : h < z := by omega
      have hsum : IsThreeSum S z ↔ IsThreeSum S' z := by
        constructor
        · rintro ⟨a, b, c, hab, hbc, hcz, ha, hb, hc, hs⟩
          exact ⟨a, b, c, hab, hbc, hcz, (ih a (by omega)).1 ha, (ih b (by omega)).1 hb,
            (ih c hcz).1 hc, hs⟩
        · rintro ⟨a, b, c, hab, hbc, hcz, ha, hb, hc, hs⟩
          exact ⟨a, b, c, hab, hbc, hcz, (ih a (by omega)).2 ha, (ih b (by omega)).2 hb,
            (ih c hcz).2 hc, hs⟩
      rw [hS.2 z hz', hS'.2 z hz', hsum]

/-- The explicit family set satisfies the greedy strict 3-sumfree recursion started at
`f, g, g + 1`, for every `1 ≤ f < g`. -/
theorem isGreedy3SumFree_familySet (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) :
    IsGreedy3SumFree f g (g + 1) (familySet f g) := by
  refine ⟨fun z hz => ?_, fun z hz => ⟨fun hmem => ?_, fun hns => ?_⟩⟩
  · rw [mem_familySet_of_lt f g _ z rfl (by omega)]; omega
  · exact not_isThreeSum_of_mem f g hf hfg z hmem hz
  · by_contra hmem
    exact hns (isThreeSum_of_not_mem f g hf hfg z hmem hz)

/-- **van Berkel–Bosma, Theorem `thm:d=1` (set form).**  For `1 ≤ f < g`, a set is the
greedy strict 3-sumfree sequence `S_{f,g,g+1}` iff it equals `familySet f g`, i.e.
`z ∈ S_{f,g,g+1}` iff `z ∈ {f, 2g+f, 6g+3f-2}` or `z mod (10g+6f-3)` lies in
`[g, 2g+f-1] ∪ [6g+3f-1, 7g+4f-3]`. -/
theorem isGreedy3SumFree_iff_eq_familySet (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) (S : Set ℕ) :
    IsGreedy3SumFree f g (g + 1) S ↔ S = familySet f g := by
  constructor
  · intro hS; exact hS.unique (isGreedy3SumFree_familySet f g hf hfg)
  · rintro rfl; exact isGreedy3SumFree_familySet f g hf hfg

/-- Ultimate periodicity of `S_{f,g,g+1}` modulo `10g+6f-3` from `6g+3f-1` on. -/
theorem familySet_add_modulus_iff (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) (z : ℕ)
    (hz : 6 * g + 3 * f - 1 ≤ z) :
    z + (10 * g + 6 * f - 3) ∈ familySet f g ↔ z ∈ familySet f g := by
  rw [mem_familySet_iff f g _ _ rfl, mem_familySet_iff f g _ _ rfl, Nat.add_mod_right]
  omega

/-- The preperiod is sharp: `6g+3f-2` is in `S_{f,g,g+1}` but `6g+3f-2 + (10g+6f-3)`
is not. -/
theorem familySet_not_periodic_before (f g : ℕ) (hf : 1 ≤ f) (hfg : f < g) :
    6 * g + 3 * f - 2 ∈ familySet f g ∧
      6 * g + 3 * f - 2 + (10 * g + 6 * f - 3) ∉ familySet f g := by
  refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩
  rw [mem_familySet_iff f g _ _ rfl, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show 6 * g + 3 * f - 2 < 10 * g + 6 * f - 3 by omega)]
  omega

/-- **van Berkel–Bosma, Theorem `thm:k=1d=1`.**  For every `g ≥ 2`, a set is the greedy
strict 3-sumfree sequence `S_{1,g,g+1}` iff it consists of `1, 2g+1, 6g+1` and all
`z` with `z mod (10g+3)` in `{g, …, 2g} ∪ {6g+2, …, 7g+1}`. -/
theorem thm_k1_d1 (g : ℕ) (hg : 2 ≤ g) (S : Set ℕ) :
    IsGreedy3SumFree 1 g (g + 1) S ↔
      S = {z | z = 1 ∨ z = 2 * g + 1 ∨ z = 6 * g + 1 ∨
        (g ≤ z % (10 * g + 3) ∧ z % (10 * g + 3) ≤ 2 * g) ∨
        (6 * g + 2 ≤ z % (10 * g + 3) ∧ z % (10 * g + 3) ≤ 7 * g + 1)} := by
  have hset : familySet 1 g = {z | z = 1 ∨ z = 2 * g + 1 ∨ z = 6 * g + 1 ∨
      (g ≤ z % (10 * g + 3) ∧ z % (10 * g + 3) ≤ 2 * g) ∨
      (6 * g + 2 ≤ z % (10 * g + 3) ∧ z % (10 * g + 3) ≤ 7 * g + 1)} := by
    ext z
    rw [mem_familySet_iff 1 g (10 * g + 3) z (by omega), Set.mem_ofPred_eq]
    omega
  rw [isGreedy3SumFree_iff_eq_familySet 1 g le_rfl (by omega), hset]

/-- **A026471** (Akeran 2004; the case `g = 2`): `S_{1,2,3}` consists of `1, 5, 13` and
all integers congruent to `2, 3, 4, 14, 15` modulo `23`. -/
theorem a026471 (S : Set ℕ) :
    IsGreedy3SumFree 1 2 3 S ↔
      S = {z | z = 1 ∨ z = 5 ∨ z = 13 ∨ z % 23 ∈ ({2, 3, 4, 14, 15} : Finset ℕ)} := by
  rw [thm_k1_d1 2 le_rfl S]
  have hset : {z : ℕ | z = 1 ∨ z = 2 * 2 + 1 ∨ z = 6 * 2 + 1 ∨
      (2 ≤ z % (10 * 2 + 3) ∧ z % (10 * 2 + 3) ≤ 2 * 2) ∨
      (6 * 2 + 2 ≤ z % (10 * 2 + 3) ∧ z % (10 * 2 + 3) ≤ 7 * 2 + 1)} =
      {z | z = 1 ∨ z = 5 ∨ z = 13 ∨ z % 23 ∈ ({2, 3, 4, 14, 15} : Finset ℕ)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hset]

/-- The hypotheses `1 ≤ f < g` hold for `S_{4,7,8}`, and the greedy
predicate is realized there. -/
example : IsGreedy3SumFree 4 7 8 (familySet 4 7) :=
  isGreedy3SumFree_familySet 4 7 (by norm_num) (by norm_num)

end ThreeSumfreeGreedyFamilies
