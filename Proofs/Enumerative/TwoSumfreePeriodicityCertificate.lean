/-
A finite periodicity certificate for strict greedy 2-sumfree sequences.

Source: Daan van Berkel and Wieb Bosma, Periodicity conjectures for all
2-sumfree sequences, arXiv:2609.18522, §5, Theorems 5.1–5.3
(5.1 from [BeBo, Theorem 13]; 5.3 from [BeBo, Lemma 6], t=2).
For positive seeds f<g, the greedy rule excludes sums of two distinct
previous terms. The finite scan charSet defines the unique support sumfreeSeq.

If the five initial characteristic blocks of positive length M are identical
and nonnull except possibly for the first, the support is M-periodic from
index M. Strong induction proves the certificate.
Explicit support formulas are proved for 0<f<g<2f (thm_5_1) and
f≥3,g=2f (thm_5_2). The trailing source clauses about minimal period and
preperiod lengths of the difference sequence are not formalized.
The scan includes index zero, absent under the positive-seed hypotheses;
the certificate permits the exceptional first block.
-/
import Mathlib

set_option autoImplicit false

namespace TwoSumfree

/-! ## Definitions -/

/-- The fixpoint characterization of the strict greedy 2-sumfree set with
initial terms `f < g`: `z` belongs to `S` iff `z = f`, or `z = g`, or `z > g`
and `z` is not the sum of two distinct elements of `S`. -/
def IsGS (f g : ℕ) (S : Set ℕ) : Prop :=
  ∀ z, z ∈ S ↔ (z = f ∨ z = g ∨ (g < z ∧ ¬ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = z))

/-- `charSet f g n` is the set of elements below `n` of the greedy
2-sumfree sequence `S_{f,g}`, computed by scanning `0, 1, …, n-1`: the
integer `n` is admitted iff it is `f`, `g`, or exceeds `g` and is not a
sum of two distinct elements already admitted. -/
def charSet (f g : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
    if n = f ∨ n = g ∨ (g < n ∧ ¬ ∃ a ∈ charSet f g n, ∃ b ∈ charSet f g n, a < b ∧ a + b = n)
    then insert n (charSet f g n) else charSet f g n

/-- The strict greedy 2-sumfree sequence `S_{f,g}` of van Berkel–Bosma,
as a subset of `ℕ` (equivalently, its characteristic sequence `C_{f,g}`). -/
def sumfreeSeq (f g : ℕ) : Set ℕ := {z | z ∈ charSet f g (z + 1)}

/-! ### Examples from the paper -/

/-- The first 26 terms of `S_{3,7}` listed in the Introduction. -/
example : charSet 3 7 79 = {3, 7, 8, 9, 13, 14, 18, 19, 24, 29, 30, 34, 35, 40, 45, 46, 50, 51,
    56, 61, 62, 66, 67, 72, 77, 78} := by decide +kernel

/-- The terms of `S_{3,6}` listed in Example 5 (before Theorem 5.2). -/
example : charSet 3 6 55 = {3, 6, 7, 8, 12, 16, 17, 21, 26, 30, 31, 35, 40, 44, 45, 49, 54} := by
  decide +kernel

/-- The terms of `S_{1,2}` and `S_{2,4}` listed in Example 5. -/
example : charSet 1 2 23 = {1, 2, 4, 7, 10, 13, 16, 19, 22} ∧
    charSet 2 4 24 = {2, 4, 5, 8, 11, 14, 17, 20, 23} := by decide +kernel

/-! ## Basic API -/

/-- Membership in the finite scan `charSet f g n` is membership in
`S_{f,g}` below `n`. -/
theorem mem_charSet_iff (f g n z : ℕ) : z ∈ charSet f g n ↔ z < n ∧ z ∈ sumfreeSeq f g := by
  induction n with
  | zero => simp [charSet]
  | succ n ih =>
    by_cases hzn : z = n
    · subst hzn
      simp [sumfreeSeq]
    · have hstep : z ∈ charSet f g (n + 1) ↔ z ∈ charSet f g n := by
        simp only [charSet]
        split_ifs <;> simp [hzn]
      rw [hstep, ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩

/-- The one-step greedy rule for `S_{f,g}`. -/
theorem mem_sumfreeSeq_iff (f g z : ℕ) : z ∈ sumfreeSeq f g ↔
    (z = f ∨ z = g ∨
      (g < z ∧ ¬ ∃ a ∈ charSet f g z, ∃ b ∈ charSet f g z, a < b ∧ a + b = z)) := by
  show z ∈ charSet f g (z + 1) ↔ _
  simp only [charSet]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Finset.mem_insert_self _ _⟩
  · refine ⟨fun hz => absurd ((mem_charSet_iff f g z z).1 hz).1 (lt_irrefl z), fun hz => ?_⟩
    exact absurd hz h

/-- Every element of a set satisfying the fixpoint is at least `f`. -/
theorem IsGS.le_of_mem {f g : ℕ} {S : Set ℕ} (hS : IsGS f g S) (hfg : f < g) {a : ℕ}
    (ha : a ∈ S) : f ≤ a := by
  rcases (hS a).1 ha with h | h | ⟨h, _⟩ <;> omega

/-- Above `g`, membership is exactly "not a sum of two distinct members". -/
theorem IsGS.mem_iff_of_lt {f g : ℕ} {S : Set ℕ} (hS : IsGS f g S) (hfg : f < g) {z : ℕ}
    (hz : g < z) : z ∈ S ↔ ¬ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = z := by
  rw [hS z]
  constructor
  · rintro (h | h | ⟨_, h⟩)
    · omega
    · omega
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨hz, h⟩)

/-- `S_{f,g}` satisfies the fixpoint characterization (for `0 < f < g`). -/
theorem isGS_sumfreeSeq {f g : ℕ} (hf : 0 < f) (hfg : f < g) : IsGS f g (sumfreeSeq f g) := by
  intro z
  have hle : ∀ a ∈ sumfreeSeq f g, f ≤ a := by
    intro a ha
    rcases (mem_sumfreeSeq_iff f g a).1 ha with h | h | ⟨h, _⟩ <;> omega
  have hsum : (∃ a ∈ charSet f g z, ∃ b ∈ charSet f g z, a < b ∧ a + b = z) ↔
      (∃ a ∈ sumfreeSeq f g, ∃ b ∈ sumfreeSeq f g, a < b ∧ a + b = z) := by
    constructor
    · rintro ⟨a, ha, b, hb, hab, rfl⟩
      exact ⟨a, ((mem_charSet_iff f g _ a).1 ha).2, b, ((mem_charSet_iff f g _ b).1 hb).2,
        hab, rfl⟩
    · rintro ⟨a, ha, b, hb, hab, rfl⟩
      have hfa := hle a ha
      exact ⟨a, (mem_charSet_iff f g _ a).2 ⟨by omega, ha⟩, b,
        (mem_charSet_iff f g _ b).2 ⟨by omega, hb⟩, hab, rfl⟩
  rw [mem_sumfreeSeq_iff, hsum]

/-- The fixpoint characterization determines the set uniquely. -/
theorem IsGS.unique {f g : ℕ} {S T : Set ℕ} (hS : IsGS f g S) (hT : IsGS f g T)
    (hf : 0 < f) (hfg : f < g) : S = T := by
  ext z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rw [hS z, hT z]
    have hsum : (∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = z) ↔ (∃ a ∈ T, ∃ b ∈ T, a < b ∧ a + b = z) := by
      constructor
      · rintro ⟨a, ha, b, hb, hab, rfl⟩
        have hfa := hS.le_of_mem hfg ha
        exact ⟨a, (ih a (by omega)).1 ha, b, (ih b (by omega)).1 hb, hab, rfl⟩
      · rintro ⟨a, ha, b, hb, hab, rfl⟩
        have hfa := hT.le_of_mem hfg ha
        exact ⟨a, (ih a (by omega)).2 ha, b, (ih b (by omega)).2 hb, hab, rfl⟩
    rw [hsum]

/-- Any set satisfying the fixpoint characterization is `S_{f,g}`. -/
theorem IsGS.eq_sumfreeSeq {f g : ℕ} {S : Set ℕ} (hS : IsGS f g S) (hf : 0 < f)
    (hfg : f < g) : S = sumfreeSeq f g :=
  hS.unique (isGS_sumfreeSeq hf hfg) hf hfg

/-! ## Theorem 5.3: a finite periodicity certificate -/

/-- If the first block `[M, 2M)` meets `S` and blocks `1,…,4` agree, then
`g < 3M` (the two members `x`, `x + M` force `g ≤ x + M`). -/
theorem IsGS.lt_of_blocks {f g M : ℕ} {S : Set ℕ} (hS : IsGS f g S) (hfg : f < g)
    (hne : ∃ x ∈ S, M ≤ x ∧ x < 2 * M)
    (hrep : ∀ x, M ≤ x → x < 4 * M → (x ∈ S ↔ x + M ∈ S)) : g < 3 * M := by
  obtain ⟨x, hx, hMx, hx2⟩ := hne
  have hxM : x + M ∈ S := (hrep x hMx (by omega)).1 hx
  have hfx := hS.le_of_mem hfg hx
  rcases (hS (x + M)).1 hxM with h | h | ⟨h, _⟩ <;> omega

/-- **Theorem 5.3** (van Berkel–Bosma, arXiv:2609.18522, Thm 5.3 = [BeBo, Lemma 6]
for `t = 2`), in the sharp form given by its proof.  Let `S = S_{f,g}`
(`0 < f < g`, characterized by `IsGS`).  If the characteristic sequence
has blocks `[jM, (j+1)M)`, `j = 1,…,4`, which are identical (`x ∈ S ↔
x + M ∈ S` for `M ≤ x < 4M`) and non-null (`S` meets `[M, 2M)`), then
`x ∈ S ↔ x + M ∈ S` for every `x ≥ M`. -/
theorem IsGS.mem_iff_add_of_blocks {f g M : ℕ} {S : Set ℕ} (hS : IsGS f g S) (hf : 0 < f)
    (hfg : f < g) (hne : ∃ x ∈ S, M ≤ x ∧ x < 2 * M)
    (hrep : ∀ x, M ≤ x → x < 4 * M → (x ∈ S ↔ x + M ∈ S)) :
    ∀ x, M ≤ x → (x ∈ S ↔ x + M ∈ S) := by
  have hg3 : g < 3 * M := hS.lt_of_blocks hfg hne hrep
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hMx
    by_cases hx4 : x < 4 * M
    · exact hrep x hMx hx4
    have hxg : g < x := by omega
    have hvg : g < x + M := by omega
    rw [hS.mem_iff_of_lt hfg hxg, hS.mem_iff_of_lt hfg hvg]
    constructor
    · -- `x ∉ sums` ⟹ `x + M ∉ sums`
      rintro hx ⟨r₁, hr₁, r₂, hr₂, hr, hsum⟩
      have hfr₁ := hS.le_of_mem hfg hr₁
      -- `y = r₂ - M` lies in `[M, x)`, so `y ∈ S` by the induction hypothesis
      obtain ⟨y, rfl⟩ : ∃ y, r₂ = y + M := ⟨r₂ - M, by omega⟩
      have hy : y ∈ S := (ih y (by omega) (by omega)).2 hr₂
      rcases lt_trichotomy r₁ y with h | h | h
      · exact hx ⟨r₁, hr₁, y, hy, h, by omega⟩
      · -- `r₁ = r₂ - M`; then `r₁ - M ∈ S` and `x = (r₁ - M) + r₂`
        subst h
        obtain ⟨z, rfl⟩ : ∃ z, r₁ = z + M := ⟨r₁ - M, by omega⟩
        have hz : z ∈ S := (ih z (by omega) (by omega)).2 hr₁
        exact hx ⟨z, hz, z + M + M, hr₂, by omega, by omega⟩
      · exact hx ⟨y, hy, r₁, hr₁, h, by omega⟩
    · -- `x + M ∉ sums` ⟹ `x ∉ sums`
      rintro hv ⟨q₁, hq₁, q₂, hq₂, hq, hsum⟩
      have hfq₁ := hS.le_of_mem hfg hq₁
      have hq₂M : q₂ + M ∈ S := (ih q₂ (by omega) (by omega)).1 hq₂
      exact hv ⟨q₁, hq₁, q₂ + M, hq₂M, by omega, by omega⟩

/-- **Theorem 5.3**, as stated in the paper: under the block hypotheses the
characteristic sequence of `S_{f,g}` is ultimately periodic. -/
theorem thm_5_3 {f g M : ℕ} (hf : 0 < f) (hfg : f < g)
    (hne : ∃ x ∈ sumfreeSeq f g, M ≤ x ∧ x < 2 * M)
    (hrep : ∀ x, M ≤ x → x < 4 * M → (x ∈ sumfreeSeq f g ↔ x + M ∈ sumfreeSeq f g)) :
    ∃ N p : ℕ, 0 < p ∧ ∀ x, N ≤ x → (x ∈ sumfreeSeq f g ↔ x + p ∈ sumfreeSeq f g) := by
  have hM : 0 < M := by
    obtain ⟨x, _, h1, h2⟩ := hne
    omega
  exact ⟨M, M, hM, (isGS_sumfreeSeq hf hfg).mem_iff_add_of_blocks hf hfg hne hrep⟩

/-- The certificate is a finite check: the block hypotheses of Theorem 5.3
for `S_{f,g}` reduce to membership in the single finite scan
`charSet f g (5M)`. -/
theorem thm_5_3_of_charSet {f g M : ℕ} (hf : 0 < f) (hfg : f < g)
    (hne : ∃ x ∈ Finset.Ico M (2 * M), x ∈ charSet f g (5 * M))
    (hrep : ∀ x ∈ Finset.Ico M (4 * M), (x ∈ charSet f g (5 * M) ↔ x + M ∈ charSet f g (5 * M))) :
    ∀ x, M ≤ x → (x ∈ sumfreeSeq f g ↔ x + M ∈ sumfreeSeq f g) := by
  refine (isGS_sumfreeSeq hf hfg).mem_iff_add_of_blocks hf hfg ?_ ?_
  · obtain ⟨x, hxI, hx⟩ := hne
    rw [Finset.mem_Ico] at hxI
    exact ⟨x, ((mem_charSet_iff f g _ x).1 hx).2, hxI⟩
  · intro x hMx hx4
    have h := hrep x (Finset.mem_Ico.2 ⟨hMx, hx4⟩)
    rw [mem_charSet_iff, mem_charSet_iff] at h
    constructor
    · intro hx
      exact (h.1 ⟨by omega, hx⟩).2
    · intro hx
      exact (h.2 ⟨by omega, hx⟩).2

/-- Worked certificate: `S_{3,7}` is periodic with period `16` from `16` on
(the paper's Introduction finds preperiod length 9 and period length 16). -/
theorem sumfreeSeq_3_7_periodic :
    ∀ x, 16 ≤ x → (x ∈ sumfreeSeq 3 7 ↔ x + 16 ∈ sumfreeSeq 3 7) :=
  thm_5_3_of_charSet (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-! ## Arithmetic helpers for the explicit families -/

/-- Division with remainder above a base point `c`. -/
theorem exists_offset_decomp {c m z : ℕ} (hm : 0 < m) (hcz : c ≤ z) :
    ∃ r k : ℕ, r < m ∧ z = c + r + k * m :=
  ⟨(z - c) % m, (z - c) / m, Nat.mod_lt _ hm, by
    have h := Nat.div_add_mod' (z - c) m
    omega⟩

/-- If `X + K·m ≡ s` with `s < m` and `X < 3m`, then `X ∈ {s, s+m, s+2m}`. -/
theorem eq_of_add_mul_eq {m X s K k : ℕ} (hs : s < m) (hX : X < 3 * m)
    (h : X + K * m = s + k * m) : X = s ∨ X = s + m ∨ X = s + 2 * m := by
  have hmod : X % m = s := by
    have h' := congrArg (· % m) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs] at h'
    exact h'
  have hdiv : X / m < 3 := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hX)
  have hdm := Nat.div_add_mod X m
  interval_cases hq : X / m <;> omega

/-- A multiple `k * m` is either `0` or at least `m`. -/
theorem mul_eq_zero_or_le (k m : ℕ) : k * m = 0 ∨ m ≤ k * m := by
  rcases k with _ | k
  · exact Or.inl (zero_mul m)
  · exact Or.inr (Nat.le_mul_of_pos_left m (Nat.succ_pos k))

/-! ## Theorem 5.1: the family `f < g ≤ 2f - 1` -/

/-- The explicit set of Theorem 5.1: `z = f`, `z = g`, `g+1 ≤ z ≤ f+g-1`, or
`z = w + k(2f+g-1)` with `2f+2g-2 ≤ w ≤ 3f+2g-3`, `k ≥ 0`. (The truncated
subtractions are exact under the theorem's hypothesis `1 ≤ f < g`.) -/
def upperSet (f g : ℕ) : Set ℕ :=
  {z | z = f ∨ z = g ∨ (g + 1 ≤ z ∧ z ≤ f + g - 1) ∨
    ∃ k w : ℕ, (2 * f + 2 * g - 2 ≤ w ∧ w ≤ 3 * f + 2 * g - 3) ∧ z = w + k * (2 * f + g - 1)}

/-- Normal form of membership in `upperSet`: an initial element or
`c + s + k m` with `s < f`, where `c = 2f+2g-2`, `m = 2f+g-1`. -/
theorem mem_upperSet_iff {f g z : ℕ} (hf : 0 < f) :
    z ∈ upperSet f g ↔ (z = f ∨ (g ≤ z ∧ z ≤ f + g - 1)) ∨
      ∃ s k : ℕ, s < f ∧ z = (2 * f + 2 * g - 2) + s + k * (2 * f + g - 1) := by
  constructor
  · rintro (h | h | h | ⟨k, w, ⟨hw1, hw2⟩, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr ⟨w - (2 * f + 2 * g - 2), k, by omega, by omega⟩
  · rintro ((h | ⟨h1, h2⟩) | ⟨s, k, hs, rfl⟩)
    · exact Or.inl h
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, 2 * f + 2 * g - 2 + s, ⟨by omega, by omega⟩, rfl⟩))

/-- No sum of two distinct elements of `upperSet f g` lies in it. -/
theorem upperSet_add_not_mem {f g a b : ℕ} (hf : 0 < f) (hfg : f < g) (hg : g < 2 * f)
    (ha : a ∈ upperSet f g) (hb : b ∈ upperSet f g) (hab : a < b) :
    a + b ∉ upperSet f g := by
  intro hz
  rw [mem_upperSet_iff hf] at ha hb hz
  set m := 2 * f + g - 1 with hm
  set c := 2 * f + 2 * g - 2 with hc
  rcases hz with hz | ⟨s₃, k₃, hs₃, hz⟩ <;>
    rcases ha with ha | ⟨s₁, k₁, hs₁, ha⟩ <;> rcases hb with hb | ⟨s₂, k₂, hs₂, hb⟩
  all_goals first
    | omega
    | have h := eq_of_add_mul_eq (m := m) (X := a + s₂) (s := s₃) (K := k₂) (k := k₃)
        (by omega) (by omega) (by omega)
      omega
    | have hk : (k₁ + k₂) * m = k₁ * m + k₂ * m := add_mul _ _ _
      have h := eq_of_add_mul_eq (m := m) (X := c + s₁ + s₂) (s := s₃) (K := k₁ + k₂)
        (k := k₃) (by omega) (by omega) (by omega)
      omega

/-- Every `z > g` outside `upperSet f g` is a sum of two distinct elements. -/
theorem exists_add_eq_of_not_mem_upperSet {f g z : ℕ} (hf : 0 < f) (hfg : f < g)
    (hg : g < 2 * f) (hgz : g < z) (hz : z ∉ upperSet f g) :
    ∃ a ∈ upperSet f g, ∃ b ∈ upperSet f g, a < b ∧ a + b = z := by
  have hinit : ∀ x, g ≤ x → x ≤ f + g - 1 → x ∈ upperSet f g := fun x h1 h2 =>
    (mem_upperSet_iff hf).2 (Or.inl (Or.inr ⟨h1, h2⟩))
  have hper : ∀ s k, s < f →
      (2 * f + 2 * g - 2) + s + k * (2 * f + g - 1) ∈ upperSet f g := fun s k hs =>
    (mem_upperSet_iff hf).2 (Or.inr ⟨s, k, hs, rfl⟩)
  have hfmem : f ∈ upperSet f g := (mem_upperSet_iff hf).2 (Or.inl (Or.inl rfl))
  rw [mem_upperSet_iff hf] at hz
  by_cases hzc : z < 2 * f + 2 * g - 2
  · -- A sum of two initial elements
    by_cases h1 : z ≤ 2 * f + g - 1
    · exact ⟨f, hfmem, z - f, hinit _ (by omega) (by omega), by omega, by omega⟩
    by_cases h2 : z ≤ f + 2 * g - 1
    · exact ⟨g, hinit g le_rfl (by omega), z - g, hinit _ (by omega) (by omega), by omega,
        by omega⟩
    · exact ⟨z - (f + g - 1), hinit _ (by omega) (by omega), f + g - 1,
        hinit _ (by omega) le_rfl, by omega, by omega⟩
  · obtain ⟨r, k, hr, rfl⟩ := exists_offset_decomp (c := 2 * f + 2 * g - 2)
      (m := 2 * f + g - 1) (z := z) (by omega) (by omega)
    have hrf : f ≤ r := by
      by_contra hrf
      exact hz (Or.inr ⟨r, k, by omega, rfl⟩)
    by_cases h1 : r < 2 * f
    · exact ⟨f, hfmem, _, hper (r - f) k (by omega), by omega, by omega⟩
    by_cases h2 : r ≤ f + g - 1
    · exact ⟨g, hinit g le_rfl (by omega), _, hper (r - g) k (by omega), by omega, by omega⟩
    · exact ⟨r - (f - 1), hinit _ (by omega) (by omega), _, hper (f - 1) k (by omega),
        by omega, by omega⟩

/-- `upperSet f g` satisfies the greedy fixpoint for `0 < f < g < 2f`. -/
theorem isGS_upperSet {f g : ℕ} (hf : 0 < f) (hfg : f < g) (hg : g < 2 * f) :
    IsGS f g (upperSet f g) := by
  intro z
  constructor
  · intro hz
    by_cases hzf : z = f
    · exact Or.inl hzf
    by_cases hzg : z = g
    · exact Or.inr (Or.inl hzg)
    have hgz : g < z := by
      rcases (mem_upperSet_iff hf).1 hz with (h | h) | ⟨s, k, _, h⟩ <;> omega
    refine Or.inr (Or.inr ⟨hgz, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact upperSet_add_not_mem hf hfg hg ha hb hab hz
  · rintro (rfl | rfl | ⟨hgz, hns⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · by_contra hz
      exact hns (exists_add_eq_of_not_mem_upperSet hf hfg hg hgz hz)

/-- **Theorem 5.1** (van Berkel–Bosma, arXiv:2609.18522, Thm 5.1 = [BeBo, Thm 13]).
For `1 ≤ f < g ≤ 2f - 1`, `z ∈ S_{f,g}` iff `z = f`, `z = g`,
`g + 1 ≤ z ≤ f + g - 1`, or `z = w + k(2f+g-1)` for some `k ≥ 0` and
`2f+2g-2 ≤ w ≤ 3f+2g-3`. -/
theorem thm_5_1 {f g : ℕ} (hf : 0 < f) (hfg : f < g) (hg : g < 2 * f) :
    sumfreeSeq f g = upperSet f g :=
  ((isGS_upperSet hf hfg hg).eq_sumfreeSeq hf hfg).symm

/-! ## Theorem 5.2: the diagonal family `g = 2f`, `f ≥ 3` -/

/-- The explicit set of Theorem 5.2: `z = f`, `z = 2f`, `2f+1 ≤ z ≤ 3f-1`, or
`z = w + k(5f-1)` with `w ∈ {4f, 6f-2, 6f-1} ∪ [7f, 8f-3]`, `k ≥ 0`. (The
truncated subtractions are exact under the theorem's hypothesis `3 ≤ f`.) -/
def diagSet (f : ℕ) : Set ℕ :=
  {z | z = f ∨ z = 2 * f ∨ (2 * f + 1 ≤ z ∧ z ≤ 3 * f - 1) ∨
    ∃ k w : ℕ, (w = 4 * f ∨ w = 6 * f - 2 ∨ w = 6 * f - 1 ∨ (7 * f ≤ w ∧ w ≤ 8 * f - 3)) ∧
      z = w + k * (5 * f - 1)}

/-- Normal form of membership in `diagSet`: an initial element or
`4f + s + k(5f-1)` with offset `s ∈ {0, 2f-2, 2f-1} ∪ [3f, 4f-3]`. -/
theorem mem_diagSet_iff {f z : ℕ} (hf : 3 ≤ f) :
    z ∈ diagSet f ↔ (z = f ∨ (2 * f ≤ z ∧ z ≤ 3 * f - 1)) ∨
      ∃ s k : ℕ, (s = 0 ∨ s = 2 * f - 2 ∨ s = 2 * f - 1 ∨ (3 * f ≤ s ∧ s ≤ 4 * f - 3)) ∧
        z = 4 * f + s + k * (5 * f - 1) := by
  constructor
  · rintro (h | h | h | ⟨k, w, hw, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr ⟨w - 4 * f, k, by omega, by omega⟩
  · rintro ((h | ⟨h1, h2⟩) | ⟨s, k, hs, rfl⟩)
    · exact Or.inl h
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, 4 * f + s, by omega, rfl⟩))

/-- No sum of two distinct elements of `diagSet f` lies in it (`f ≥ 3`). -/
theorem diagSet_add_not_mem {f a b : ℕ} (hf : 3 ≤ f) (ha : a ∈ diagSet f)
    (hb : b ∈ diagSet f) (hab : a < b) : a + b ∉ diagSet f := by
  intro hz
  rw [mem_diagSet_iff hf] at ha hb hz
  set m := 5 * f - 1 with hm
  rcases hz with hz | ⟨s₃, k₃, hs₃, hz⟩ <;>
    rcases ha with ha | ⟨s₁, k₁, hs₁, ha⟩ <;> rcases hb with hb | ⟨s₂, k₂, hs₂, hb⟩
  all_goals first
    | omega
    | have h := mul_eq_zero_or_le k₃ m
      omega
    | have h := eq_of_add_mul_eq (m := m) (X := a + s₂) (s := s₃) (K := k₂) (k := k₃)
        (by omega) (by omega) (by omega)
      omega
    | have hk : (k₁ + k₂) * m = k₁ * m + k₂ * m := add_mul _ _ _
      have h := eq_of_add_mul_eq (m := m) (X := 4 * f + s₁ + s₂) (s := s₃) (K := k₁ + k₂)
        (k := k₃) (by omega) (by omega) (by omega)
      omega

/-- Every `z > 2f` outside `diagSet f` is a sum of two distinct elements. -/
theorem exists_add_eq_of_not_mem_diagSet {f z : ℕ} (hf : 3 ≤ f) (hgz : 2 * f < z)
    (hz : z ∉ diagSet f) : ∃ a ∈ diagSet f, ∃ b ∈ diagSet f, a < b ∧ a + b = z := by
  have hinit : ∀ x, 2 * f ≤ x → x ≤ 3 * f - 1 → x ∈ diagSet f := fun x h1 h2 =>
    (mem_diagSet_iff hf).2 (Or.inl (Or.inr ⟨h1, h2⟩))
  have hper : ∀ s k, (s = 0 ∨ s = 2 * f - 2 ∨ s = 2 * f - 1 ∨ (3 * f ≤ s ∧ s ≤ 4 * f - 3)) →
      4 * f + s + k * (5 * f - 1) ∈ diagSet f := fun s k hs =>
    (mem_diagSet_iff hf).2 (Or.inr ⟨s, k, hs, rfl⟩)
  have hfmem : f ∈ diagSet f := (mem_diagSet_iff hf).2 (Or.inl (Or.inl rfl))
  rw [mem_diagSet_iff hf] at hz
  by_cases hzc : z < 4 * f
  · exact ⟨f, hfmem, z - f, hinit _ (by omega) (by omega), by omega, by omega⟩
  obtain ⟨r, k, hr, rfl⟩ := exists_offset_decomp (c := 4 * f) (m := 5 * f - 1) (z := z)
    (by omega) (by omega)
  have hrO : ¬ (r = 0 ∨ r = 2 * f - 2 ∨ r = 2 * f - 1 ∨ (3 * f ≤ r ∧ r ≤ 4 * f - 3)) :=
    fun h => hz (Or.inr ⟨r, k, h, rfl⟩)
  by_cases h1 : 2 * f ≤ r ∧ r ≤ 3 * f - 1
  · -- `z = r + (4f + k m)`
    exact ⟨r, hinit r h1.1 h1.2, _, hper 0 k (Or.inl rfl), by omega, by omega⟩
  by_cases h2 : r = 4 * f - 2
  · exact ⟨2 * f, hinit _ le_rfl (by omega), _, hper (2 * f - 2) k (by omega), by omega,
      by omega⟩
  by_cases h3 : 4 * f - 1 ≤ r
  · exact ⟨r - (2 * f - 1), hinit _ (by omega) (by omega), _, hper (2 * f - 1) k (by omega),
      by omega, by omega⟩
  -- Remaining offsets: `1 ≤ r ≤ 2f - 3`
  have hr1 : 1 ≤ r ∧ r ≤ 2 * f - 3 := by omega
  rcases k with _ | k
  · -- `z = 4f + r ∈ [4f+1, 6f-3]`, a sum of two initial elements
    by_cases h4 : 4 * f + r + 0 * (5 * f - 1) ≤ 5 * f - 1
    · exact ⟨2 * f, hinit _ le_rfl (by omega), _, hinit (2 * f + r) (by omega) (by omega),
        by omega, by omega⟩
    · exact ⟨r + f + 1, hinit _ (by omega) (by omega), 3 * f - 1, hinit _ (by omega) le_rfl,
        by omega, by omega⟩
  · have hk : (k + 1) * (5 * f - 1) = k * (5 * f - 1) + (5 * f - 1) := by ring
    by_cases h5 : r ≤ f
    · exact ⟨r + 2 * f - 1, hinit _ (by omega) (by omega), _, hper (3 * f) k (by omega),
        by omega, by omega⟩
    · exact ⟨3 * f - 1, hinit _ (by omega) le_rfl, _, hper (r + 2 * f) k (by omega),
        by omega, by omega⟩

/-- `diagSet f` satisfies the greedy fixpoint with initial terms `f`, `2f`
for `f ≥ 3`. -/
theorem isGS_diagSet {f : ℕ} (hf : 3 ≤ f) : IsGS f (2 * f) (diagSet f) := by
  intro z
  constructor
  · intro hz
    by_cases hzf : z = f
    · exact Or.inl hzf
    by_cases hzg : z = 2 * f
    · exact Or.inr (Or.inl hzg)
    have hgz : 2 * f < z := by
      rcases (mem_diagSet_iff hf).1 hz with (h | h) | ⟨s, k, _, h⟩ <;> omega
    refine Or.inr (Or.inr ⟨hgz, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact diagSet_add_not_mem hf ha hb hab hz
  · rintro (rfl | rfl | ⟨hgz, hns⟩)
    · exact (mem_diagSet_iff hf).2 (Or.inl (Or.inl rfl))
    · exact (mem_diagSet_iff hf).2 (Or.inl (Or.inr ⟨le_rfl, by omega⟩))
    · by_contra hz
      exact hns (exists_add_eq_of_not_mem_diagSet hf hgz hz)

/-- **Theorem 5.2** (van Berkel–Bosma, arXiv:2609.18522, Thm 5.2, new in that
paper).  For `f ≥ 3`, `z ∈ S_{f,2f}` iff `z = f`, `z = 2f`, `2f+1 ≤ z ≤ 3f-1`,
or `z = w + k(5f-1)` for some `k ≥ 0` and
`w ∈ {4f, 6f-2, 6f-1, 7f, 7f+1, …, 8f-3}`. -/
theorem thm_5_2 {f : ℕ} (hf : 3 ≤ f) : sumfreeSeq f (2 * f) = diagSet f :=
  ((isGS_diagSet hf).eq_sumfreeSeq (by omega) (by omega)).symm

/-! ## The hypotheses of the family theorems are satisfiable -/

/-- Theorem 5.1 applies at `(f, g) = (3, 5)`. -/
example : sumfreeSeq 3 5 = upperSet 3 5 := thm_5_1 (by norm_num) (by norm_num) (by norm_num)

/-- Theorem 5.2 applies at `f = 3`. -/
example : sumfreeSeq 3 6 = diagSet 3 := thm_5_2 le_rfl

end TwoSumfree
