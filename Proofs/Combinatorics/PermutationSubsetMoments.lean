import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Tactic

set_option autoImplicit false

namespace PermutationSubsetMoments

/-- Actual six-element subsets of the finite ordinal. -/
abbrev SixSubset (n : ℕ) := {s : Finset (Fin n) // s.card = 6}

/-- The increasing enumeration of an actual six-element subset, with zero-based ranks. -/
noncomputable def sorted6 {n : ℕ} (s : SixSubset n) : Fin 6 ↪o Fin n :=
  s.val.orderEmbOfFin s.property

example : Nonempty (SixSubset 6) := ⟨⟨Finset.univ, by simp⟩⟩

example {n : ℕ} (s : SixSubset n) :
    sorted6 s = s.val.orderEmbOfFin s.property := rfl

/-- Every enumerated value belongs to the underlying subset. -/
theorem sorted6_mem {n : ℕ} (s : SixSubset n) (i : Fin 6) : sorted6 s i ∈ s.val :=
  Finset.orderEmbOfFin_mem _ _ _

/-- The increasing enumeration covers the underlying subset exactly. -/
theorem image_sorted6 {n : ℕ} (s : SixSubset n) :
    Finset.univ.image (sorted6 s) = s.val :=
  Finset.image_orderEmbOfFin_univ _ _

/-- A genuine six-element subset requires at least six ambient points. -/
theorem six_le {n : ℕ} (s : SixSubset n) : 6 ≤ n := by
  have hc := Finset.card_le_card (Finset.subset_univ s.val)
  simpa [s.property] using hc

/-- The seven nonnegative gaps before, between, and after the six sorted points. -/
noncomputable def gaps6 {n : ℕ} (s : SixSubset n) : Fin 7 → ℕ :=
  let z := fun i => (sorted6 s i).val
  fun j => if j.val = 0 then z 0 else if j.val = 1 then z 1 - z 0 - 1
    else if j.val = 2 then z 2 - z 1 - 1 else if j.val = 3 then z 3 - z 2 - 1
    else if j.val = 4 then z 4 - z 3 - 1 else if j.val = 5 then z 5 - z 4 - 1
    else n - z 5 - 1

example {n : ℕ} (s : SixSubset n) : gaps6 s 0 = (sorted6 s 0).val := rfl

private theorem sorted6_bounds {n : ℕ} (s : SixSubset n) :
    (sorted6 s 0).val < (sorted6 s 1).val ∧
    (sorted6 s 1).val < (sorted6 s 2).val ∧
    (sorted6 s 2).val < (sorted6 s 3).val ∧
    (sorted6 s 3).val < (sorted6 s 4).val ∧
    (sorted6 s 4).val < (sorted6 s 5).val ∧ (sorted6 s 5).val < n := by
  exact ⟨(sorted6 s).strictMono (by decide), (sorted6 s).strictMono (by decide),
    (sorted6 s).strictMono (by decide), (sorted6 s).strictMono (by decide),
    (sorted6 s).strictMono (by decide), (sorted6 s 5).isLt⟩

/-- The actual subset gaps are a weak composition of the unused ambient points. -/
theorem sum_gaps6 {n : ℕ} (s : SixSubset n) : ∑ i, gaps6 s i = n - 6 := by
  have hb := sorted6_bounds s
  norm_num [gaps6, Fin.sum_univ_succ] 
  omega

/-- Actual subset gaps belong to Mathlib's finite weak-composition enumeration. -/
theorem gaps6_mem_antidiagonal {n : ℕ} (s : SixSubset n) :
    gaps6 s ∈ Finset.Nat.antidiagonalTuple 7 (n - 6) :=
  Finset.Nat.mem_antidiagonalTuple.mpr (sum_gaps6 s)

/-- Seven nonnegative integers with the specified total. -/
abbrev SevenGaps (N : ℕ) := {g : Fin 7 → ℕ // ∑ i, g i = N}

example : Nonempty (SevenGaps 0) := ⟨⟨0, by simp⟩⟩

/-- The six positions reconstructed from seven gaps, before imposing an ambient bound. -/
def positions6 (g : Fin 7 → ℕ) : Fin 6 → ℕ :=
  fun i => if i.val = 0 then g 0 else if i.val = 1 then g 0 + g 1 + 1
    else if i.val = 2 then g 0 + g 1 + g 2 + 2
    else if i.val = 3 then g 0 + g 1 + g 2 + g 3 + 3
    else if i.val = 4 then g 0 + g 1 + g 2 + g 3 + g 4 + 4
    else g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + 5

example (g : Fin 7 → ℕ) : positions6 g 0 = g 0 := rfl

/-- Nonnegative gaps give strictly increasing reconstructed positions. -/
theorem positions6_strictMono (g : Fin 7 → ℕ) : StrictMono (positions6 g) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [positions6] <;> omega

/-- Every reconstructed point is within the ambient finite ordinal. -/
theorem positions6_lt {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) (i : Fin 6) :
    positions6 g.val i < n := by
  have hs := g.property
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change g.val 0 + (g.val 1 + (g.val 2 + (g.val 3 + (g.val 4 + (g.val 5 + g.val 6))))) = n - 6 at hs
  have hi : i ≤ (5 : Fin 6) := by omega
  have hm := (positions6_strictMono g.val).monotone hi
  change positions6 g.val i ≤ g.val 0 + g.val 1 + g.val 2 + g.val 3 + g.val 4 + g.val 5 + 5 at hm
  omega

/-- The increasing embedding reconstructed from seven gaps. -/
def embedding6 {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) : Fin 6 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨positions6 g.val i, positions6_lt hn g i⟩)
    (fun _ _ hij => positions6_strictMono g.val hij)

example {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) (i : Fin 6) :
    (embedding6 hn g i).val = positions6 g.val i := rfl

/-- The actual six-element subset reconstructed from seven gaps. -/
def subset6OfGaps {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) : SixSubset n :=
  ⟨Finset.univ.map (embedding6 hn g).toEmbedding, by simp⟩

example {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) :
    (subset6OfGaps hn g).val = Finset.univ.map (embedding6 hn g).toEmbedding := rfl

/-- Sorting the subset reconstructed from gaps recovers the reconstructed embedding. -/
theorem sorted6_subset6OfGaps {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) :
    sorted6 (subset6OfGaps hn g) = embedding6 hn g := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Taking gaps after reconstructing an actual subset recovers all seven gaps. -/
theorem gaps6_subset6OfGaps {n : ℕ} (hn : 6 ≤ n) (g : SevenGaps (n - 6)) :
    gaps6 (subset6OfGaps hn g) = g.val := by
  let a := g.val 0
  let b := g.val 1
  let c := g.val 2
  let d := g.val 3
  let e := g.val 4
  let f := g.val 5
  let h := g.val 6
  have hs := g.property
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change a + (b + (c + (d + (e + (f + h))))) = n - 6 at hs
  simp only [gaps6, sorted6_subset6OfGaps]
  funext i
  fin_cases i
  · change a = a
    rfl
  · change a + b + 1 - a - 1 = b
    omega
  · change a + b + c + 2 - (a + b + 1) - 1 = c
    omega
  · change a + b + c + d + 3 - (a + b + c + 2) - 1 = d
    omega
  · change a + b + c + d + e + 4 - (a + b + c + d + 3) - 1 = e
    omega
  · change a + b + c + d + e + f + 5 - (a + b + c + d + e + 4) - 1 = f
    omega
  · change n - (a + b + c + d + e + f + 5) - 1 = h
    omega

/-- Reconstructing the actual subset gaps recovers every sorted position. -/
theorem positions6_gaps6 {n : ℕ} (s : SixSubset n) (i : Fin 6) :
    positions6 (gaps6 s) i = (sorted6 s i).val := by
  let a := (sorted6 s 0).val
  let b := (sorted6 s 1).val
  let c := (sorted6 s 2).val
  let d := (sorted6 s 3).val
  let e := (sorted6 s 4).val
  let f := (sorted6 s 5).val
  have hb := sorted6_bounds s
  change a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < n at hb
  fin_cases i
  · change a = a
    rfl
  · change a + (b - a - 1) + 1 = b
    omega
  · change a + (b - a - 1) + (c - b - 1) + 2 = c
    omega
  · change a + (b - a - 1) + (c - b - 1) + (d - c - 1) + 3 = d
    omega
  · change a + (b - a - 1) + (c - b - 1) + (d - c - 1) + (e - d - 1) + 4 = e
    omega
  · change a + (b - a - 1) + (c - b - 1) + (d - c - 1) + (e - d - 1) + (f - e - 1) + 5 = f
    omega

/-- Actual six-subsets are in bijection with their seven nonnegative gaps. -/
noncomputable def subset6EquivGaps {n : ℕ} (hn : 6 ≤ n) :
    SixSubset n ≃ SevenGaps (n - 6) where
  toFun s := ⟨gaps6 s, sum_gaps6 s⟩
  invFun := subset6OfGaps hn
  left_inv s := by
    apply Subtype.ext
    have he : embedding6 hn ⟨gaps6 s, sum_gaps6 s⟩ = sorted6 s := by
      ext i
      exact positions6_gaps6 s i
    change Finset.univ.map (embedding6 hn ⟨gaps6 s, sum_gaps6 s⟩).toEmbedding = s.val
    rw [he, Finset.map_eq_image]
    exact image_sorted6 s
  right_inv g := Subtype.ext (gaps6_subset6OfGaps hn g)

example {n : ℕ} (hn : 6 ≤ n) (s : SixSubset n) :
    (subset6EquivGaps hn s).val = gaps6 s := rfl

noncomputable instance sevenGapsFintype (N : ℕ) : Fintype (SevenGaps N) :=
  Fintype.ofEquiv (↥(Finset.Nat.antidiagonalTuple 7 N))
    { toFun := fun g => ⟨g.val, Finset.Nat.mem_antidiagonalTuple.mp g.property⟩
      invFun := fun g => ⟨g.val, Finset.Nat.mem_antidiagonalTuple.mpr g.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Relabelling the seven gaps preserves the finite weak-composition sample space. -/
def permuteGaps (N : ℕ) (e : Equiv.Perm (Fin 7)) : SevenGaps N ≃ SevenGaps N where
  toFun g := ⟨g.val ∘ e, (Equiv.sum_comp e g.val).trans g.property⟩
  invFun g := ⟨g.val ∘ e.symm, (Equiv.sum_comp e.symm g.val).trans g.property⟩
  left_inv g := by ext i; simp
  right_inv g := by ext i; simp

example (N : ℕ) (e : Equiv.Perm (Fin 7)) (g : SevenGaps N) (i : Fin 7) :
    (permuteGaps N e g).val i = g.val (e i) := rfl

/-- Every gap has the same unnormalized first moment under actual uniform compositions. -/
theorem sum_gap_eq (N : ℕ) (i j : Fin 7) :
    (∑ g : SevenGaps N, g.val i) = ∑ g : SevenGaps N, g.val j := by
  have he := (permuteGaps N (Equiv.swap i j)).sum_comp (fun g => g.val i)
  simpa [permuteGaps] using he.symm

/-- Fixed total and coordinate symmetry determine each unnormalized gap mean. -/
theorem seven_mul_sum_gap (N : ℕ) (i : Fin 7) :
    7 * (∑ g : SevenGaps N, g.val i) = Fintype.card (SevenGaps N) * N := by
  calc
    7 * (∑ g : SevenGaps N, g.val i) = ∑ j : Fin 7, ∑ g : SevenGaps N, g.val j := by
      simp_rw [← sum_gap_eq N i]
      simp
    _ = ∑ g : SevenGaps N, ∑ j : Fin 7, g.val j := Finset.sum_comm
    _ = Fintype.card (SevenGaps N) * N := by
      have htotal (g : SevenGaps N) : ∑ j, g.val j = N := g.property
      simp_rw [htotal]
      simp

/-- The actual subset gap sums obey the same uniform first-moment identity. -/
theorem seven_mul_sum_subset_gap {n : ℕ} (hn : 6 ≤ n) (i : Fin 7) :
    7 * (∑ s : SixSubset n, gaps6 s i) = Fintype.card (SixSubset n) * (n - 6) := by
  have he := Equiv.sum_comp (subset6EquivGaps hn) (fun g => g.val i)
  have hc := Fintype.card_congr (subset6EquivGaps hn)
  calc
    7 * (∑ s : SixSubset n, gaps6 s i) = 7 * (∑ g : SevenGaps (n - 6), g.val i) := congrArg (7 * ·) he
    _ = Fintype.card (SevenGaps (n - 6)) * (n - 6) := seven_mul_sum_gap (n - 6) i
    _ = Fintype.card (SixSubset n) * (n - 6) := by rw [hc]

/-- Each sorted position is its zero-based rank plus the preceding gaps. -/
theorem sorted6_eq_sum_gaps {n : ℕ} (s : SixSubset n) (i : Fin 6) :
    (sorted6 s i).val = i.val + ∑ j : Fin (i.val + 1), gaps6 s ⟨j.val, by omega⟩ := by
  have hp := positions6_gaps6 s i
  fin_cases i
  · change (sorted6 s 0).val = 0 + (gaps6 s 0 + 0)
    change gaps6 s 0 = (sorted6 s 0).val at hp
    omega
  · change (sorted6 s 1).val = 1 + (gaps6 s 0 + gaps6 s 1)
    change gaps6 s 0 + gaps6 s 1 + 1 = (sorted6 s 1).val at hp
    omega
  · change (sorted6 s 2).val = 2 + (gaps6 s 0 + (gaps6 s 1 + gaps6 s 2))
    change gaps6 s 0 + gaps6 s 1 + gaps6 s 2 + 2 = (sorted6 s 2).val at hp
    omega
  · change (sorted6 s 3).val = 3 + (gaps6 s 0 + (gaps6 s 1 + (gaps6 s 2 + gaps6 s 3)))
    change gaps6 s 0 + gaps6 s 1 + gaps6 s 2 + gaps6 s 3 + 3 = (sorted6 s 3).val at hp
    omega
  · change (sorted6 s 4).val = 4 + (gaps6 s 0 + (gaps6 s 1 + (gaps6 s 2 + (gaps6 s 3 + gaps6 s 4))))
    change gaps6 s 0 + gaps6 s 1 + gaps6 s 2 + gaps6 s 3 + gaps6 s 4 + 4 = (sorted6 s 4).val at hp
    omega
  · change (sorted6 s 5).val = 5 + (gaps6 s 0 + (gaps6 s 1 + (gaps6 s 2 + (gaps6 s 3 + (gaps6 s 4 + gaps6 s 5)))))
    change gaps6 s 0 + gaps6 s 1 + gaps6 s 2 + gaps6 s 3 + gaps6 s 4 + gaps6 s 5 + 5 = (sorted6 s 5).val at hp
    omega

/-- The exact unnormalized mean of every sorted position in actual uniform six-subsets. -/
theorem seven_mul_sum_sorted6 {n : ℕ} (hn : 6 ≤ n) (i : Fin 6) :
    7 * (∑ s : SixSubset n, (sorted6 s i).val) =
      Fintype.card (SixSubset n) * (7 * i.val + (i.val + 1) * (n - 6)) := by
  simp_rw [sorted6_eq_sum_gaps]
  rw [Finset.sum_add_distrib, Nat.mul_add]
  have hsum : 7 * (∑ s : SixSubset n,
      ∑ j : Fin (i.val + 1), gaps6 s ⟨j.val, by omega⟩) =
      (i.val + 1) * (Fintype.card (SixSubset n) * (n - 6)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm (j : Fin (i.val + 1)) := seven_mul_sum_subset_gap hn (⟨j.val, by omega⟩ : Fin 7)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hterm j)
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

private theorem sum_range_cast (t : ℕ) :
    (∑ a ∈ Finset.range (t + 1), (a : ℚ)) = (t : ℚ) * (t + 1) / 2 := by
  induction t with
  | zero => norm_num
  | succ t ht =>
    rw [Finset.sum_range_succ, ht]
    push_cast
    ring

private theorem sum_range_cast_sq (t : ℕ) :
    (∑ a ∈ Finset.range (t + 1), (a : ℚ)^2) = (t : ℚ) * (t + 1) * (2 * t + 1) / 6 := by
  induction t with
  | zero => norm_num
  | succ t ht =>
    rw [Finset.sum_range_succ, ht]
    push_cast
    ring

/-- For a uniformly split fixed pair total, the diagonal falling moment is twice the mixed moment. -/
theorem pair_split_falling_eq_twice_mixed (t : ℕ) :
    (∑ a ∈ Finset.range (t + 1), (a : ℚ) * (a - 1)) =
      2 * ∑ a ∈ Finset.range (t + 1), (a : ℚ) * ((t : ℚ) - a) := by
  have hf : ∀ a : ℕ, (a : ℚ) * (a - 1) = (a : ℚ)^2 - a := fun a => by ring
  have hm : ∀ a : ℕ, (a : ℚ) * ((t : ℚ) - a) = (t : ℚ) * a - (a : ℚ)^2 := fun a => by ring
  simp_rw [hf, hm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_range_cast, sum_range_cast_sq]
  ring

/-- The representative of a two-coordinate fiber has its first gap zero. -/
abbrev PairBase (N : ℕ) := {g : SevenGaps N // g.val 0 = 0}

example : Nonempty (PairBase 0) := ⟨⟨⟨0, by simp⟩, rfl⟩⟩

/-- Collapse the first two gaps to their total, keeping all five other gaps. -/
def collapsePair (N : ℕ) (g : SevenGaps N) : PairBase N :=
  ⟨⟨fun i => if i.val = 0 then 0 else if i.val = 1 then g.val 0 + g.val 1 else g.val i, by
    have hs := g.property
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs ⊢
    change 0 + ((g.val 0 + g.val 1) + (g.val 2 + (g.val 3 + (g.val 4 + (g.val 5 + g.val 6))))) = N
    change g.val 0 + (g.val 1 + (g.val 2 + (g.val 3 + (g.val 4 + (g.val 5 + g.val 6))))) = N at hs
    omega⟩, rfl⟩

example (N : ℕ) (g : SevenGaps N) : (collapsePair N g).val.val 1 = g.val 0 + g.val 1 := rfl

/-- Split the total in the first two coordinates at any allowed integer cut. -/
def splitPair (N : ℕ) (b : PairBase N) (a : Fin (b.val.val 1 + 1)) : SevenGaps N :=
  ⟨fun i => if i.val = 0 then a.val else if i.val = 1 then b.val.val 1 - a.val else b.val.val i, by
    have hs := b.val.property
    have hz := b.property
    have ha := a.isLt
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs ⊢
    change a.val + ((b.val.val 1 - a.val) + (b.val.val 2 + (b.val.val 3 + (b.val.val 4 + (b.val.val 5 + b.val.val 6))))) = N
    change b.val.val 0 + (b.val.val 1 + (b.val.val 2 + (b.val.val 3 + (b.val.val 4 + (b.val.val 5 + b.val.val 6))))) = N at hs
    omega⟩

example (N : ℕ) (b : PairBase N) (a : Fin (b.val.val 1 + 1)) :
    (splitPair N b a).val 0 = a.val := rfl

private theorem fin_heq_of_val_eq {m n : ℕ} (a : Fin m) (b : Fin n)
    (hmn : m = n) (hab : a.val = b.val) : HEq a b := by
  subst n
  exact heq_of_eq (Fin.ext hab)

/-- The weak-composition space decomposes into uniform splits of each fixed pair total. -/
def pairSplitEquiv (N : ℕ) : SevenGaps N ≃ (Σ b : PairBase N, Fin (b.val.val 1 + 1)) where
  toFun g := ⟨collapsePair N g, ⟨g.val 0, by change g.val 0 < g.val 0 + g.val 1 + 1; omega⟩⟩
  invFun p := splitPair N p.1 p.2
  left_inv g := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · change g.val 0 + g.val 1 - g.val 0 = g.val 1
      omega
    all_goals rfl
  right_inv p := by
    rcases p with ⟨b, a⟩
    have hb : collapsePair N (splitPair N b a) = b := by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      have hz := b.property
      have ha := a.isLt
      fin_cases i
      · exact hz.symm
      · change a.val + (b.val.val 1 - a.val) = b.val.val 1
        omega
      all_goals rfl
    apply Sigma.ext hb
    apply fin_heq_of_val_eq
    · exact congrArg (fun b : PairBase N => b.val.val 1 + 1) hb
    · rfl

example (N : ℕ) (g : SevenGaps N) : (pairSplitEquiv N g).1 = collapsePair N g := rfl

/-- Uniform weak compositions have diagonal falling moment twice the mixed moment. -/
theorem sum_gap_falling_eq_twice_mixed (N : ℕ) :
    (∑ g : SevenGaps N, (g.val 0 : ℚ) * (g.val 0 - 1)) =
      2 * ∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 1 := by
  classical
  rw [← Equiv.sum_comp (pairSplitEquiv N).symm (fun g => (g.val 0 : ℚ) * (g.val 0 - 1)),
    ← Equiv.sum_comp (pairSplitEquiv N).symm (fun g => (g.val 0 : ℚ) * g.val 1),
    Fintype.sum_sigma, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ a : Fin (b.val.val 1 + 1), (a.val : ℚ) * (a.val - 1)) =
    2 * ∑ a : Fin (b.val.val 1 + 1), (a.val : ℚ) * (b.val.val 1 - a.val : ℕ)
  have hcast (a : Fin (b.val.val 1 + 1)) :
      ((b.val.val 1 - a.val : ℕ) : ℚ) = (b.val.val 1 : ℚ) - a.val := by
    exact Nat.cast_sub (by have ha := a.isLt; omega)
  simp_rw [hcast]
  rw [Fin.sum_univ_eq_sum_range (fun a => (a : ℚ) * (a - 1)),
    Fin.sum_univ_eq_sum_range (fun a => (a : ℚ) * ((b.val.val 1 : ℚ) - a))]
  exact pair_split_falling_eq_twice_mixed (b.val.val 1)

/-- Coordinate permutations preserve every unnormalized second product moment. -/
theorem sum_gap_product_perm (N : ℕ) (e : Equiv.Perm (Fin 7)) (i j : Fin 7) :
    (∑ g : SevenGaps N, (g.val (e i) : ℚ) * g.val (e j)) =
      ∑ g : SevenGaps N, (g.val i : ℚ) * g.val j := by
  exact Equiv.sum_comp (permuteGaps N e) (fun g => (g.val i : ℚ) * g.val j)

/-- A prescribed ordered pair of distinct coordinates is the image of coordinates zero and one. -/
theorem exists_perm_zero_one (i j : Fin 7) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 7), e 0 = i ∧ e 1 = j := by
  let a := Equiv.swap (0 : Fin 7) i
  let k := a j
  have hk : k ≠ 0 := by
    intro h
    have hh := congrArg a h
    simp only [k, a, Equiv.swap_apply_self, Equiv.swap_apply_left] at hh
    exact hij hh.symm
  let e := (Equiv.swap (1 : Fin 7) k).trans a
  refine ⟨e, ?_, ?_⟩
  · change a (Equiv.swap (1 : Fin 7) k 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk)]
    exact Equiv.swap_apply_left _ _
  · change a (Equiv.swap (1 : Fin 7) k 1) = j
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_self _ _ _

/-- All off-diagonal gap product sums equal the zero-one product sum. -/
theorem sum_gap_product_ne (N : ℕ) (i j : Fin 7) (hij : i ≠ j) :
    (∑ g : SevenGaps N, (g.val i : ℚ) * g.val j) =
      ∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 1 := by
  obtain ⟨e, hi, hj⟩ := exists_perm_zero_one i j hij
  simpa only [hi, hj] using sum_gap_product_perm N e 0 1

/-- All diagonal gap product sums equal the zero-coordinate square sum. -/
theorem sum_gap_square_eq (N : ℕ) (i : Fin 7) :
    (∑ g : SevenGaps N, (g.val i : ℚ) * g.val i) =
      ∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 0 := by
  simpa only [Equiv.swap_apply_left] using sum_gap_product_perm N (Equiv.swap 0 i) 0 0

/-- The actual finite product sum depends only on whether the two coordinates coincide. -/
theorem sum_gap_product_ite (N : ℕ) (i j : Fin 7) :
    (∑ g : SevenGaps N, (g.val i : ℚ) * g.val j) =
      if i = j then (∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 0)
      else (∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 1) := by
  split_ifs with h
  · subst j; exact sum_gap_square_eq N i
  · exact sum_gap_product_ne N i j h

/-- The exact unnormalized off-diagonal product moment of actual uniform compositions. -/
theorem sum_gap_product_zero_one (N : ℕ) :
    56 * (∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 1) =
      (Fintype.card (SevenGaps N) : ℚ) * N * ((N : ℚ) - 1) := by
  let D : ℚ := ∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 0
  let M : ℚ := ∑ g : SevenGaps N, (g.val 0 : ℚ) * g.val 1
  let S : ℚ := ∑ g : SevenGaps N, (g.val 0 : ℚ)
  let C : ℚ := Fintype.card (SevenGaps N)
  have hf : D - S = 2 * M := by
    simpa only [mul_sub, mul_one, Finset.sum_sub_distrib] using sum_gap_falling_eq_twice_mixed N
  have hmean : 7 * S = C * N := by
    dsimp [S, C]
    exact_mod_cast seven_mul_sum_gap N 0
  have htotal (g : SevenGaps N) : (∑ i, (g.val i : ℚ)) = N := by
    exact_mod_cast g.property
  have hsquare : (∑ i : Fin 7, ∑ j : Fin 7,
      ∑ g : SevenGaps N, (g.val i : ℚ) * g.val j) = C * (N : ℚ)^2 := by
    calc
      _ = ∑ g : SevenGaps N, ∑ i : Fin 7, ∑ j : Fin 7, (g.val i : ℚ) * g.val j := by
        calc
          _ = ∑ i : Fin 7, ∑ g : SevenGaps N, ∑ j : Fin 7, (g.val i : ℚ) * g.val j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      _ = C * (N : ℚ)^2 := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul, htotal]
        simp [C, pow_two]
  have hrow (i : Fin 7) : (∑ j : Fin 7, if i = j then D else M) = D + 6 * M := by
    have he (j : Fin 7) : (if i = j then D else M) = M + if i = j then D - M else 0 := by
      split_ifs <;> ring
    simp_rw [he]
    have hs : (∑ x : Fin 7, if i = x then D - M else 0) = D - M := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi
        simp [Ne.symm hbi]
      · simp
    rw [Finset.sum_add_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hproducts (i j : Fin 7) := sum_gap_product_ite N i j
  have hdouble : (∑ i : Fin 7, ∑ j : Fin 7, ∑ g : SevenGaps N, (g.val i : ℚ) * g.val j) =
      ∑ i : Fin 7, ∑ j : Fin 7, if i = j then D else M := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hproducts i j
  rw [hdouble] at hsquare
  change (∑ i : Fin 7, ∑ j : Fin 7, if i = j then D else M) = C * (N : ℚ)^2 at hsquare
  simp_rw [hrow] at hsquare
  norm_num at hsquare
  change 56 * M = C * N * ((N : ℚ) - 1)
  nlinarith [hsquare]

/-- Exact rational product moments of actual weak compositions, including the diagonal correction. -/
theorem sum_gap_product (N : ℕ) (i j : Fin 7) :
    (∑ g : SevenGaps N, (g.val i : ℚ) * g.val j) =
      (Fintype.card (SevenGaps N) : ℚ) *
        ((N : ℚ) * (N - 1) / 56 + if i = j then (N : ℚ) * (N + 7) / 56 else 0) := by
  have hm := sum_gap_product_zero_one N
  have hf := sum_gap_falling_eq_twice_mixed N
  have hs : 7 * (∑ g : SevenGaps N, (g.val 0 : ℚ)) =
      (Fintype.card (SevenGaps N) : ℚ) * N := by
    exact_mod_cast seven_mul_sum_gap N 0
  rw [sum_gap_product_ite]
  split_ifs <;> simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hf <;> nlinarith

/-- Actual uniform six-subsets have the exact rational gap product moments. -/
theorem sum_subset_gap_product {n : ℕ} (hn : 6 ≤ n) (i j : Fin 7) :
    (∑ s : SixSubset n, (gaps6 s i : ℚ) * gaps6 s j) =
      (Fintype.card (SixSubset n) : ℚ) *
        (((n : ℚ) - 6) * (n - 7) / 56 +
          if i = j then ((n : ℚ) - 6) * (n + 1) / 56 else 0) := by
  have he := Equiv.sum_comp (subset6EquivGaps hn)
    (fun g => (g.val i : ℚ) * g.val j)
  have hc := Fintype.card_congr (subset6EquivGaps hn)
  have hcast : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by
    exact_mod_cast Nat.cast_sub hn (R := ℚ)
  change (∑ s : SixSubset n, (gaps6 s i : ℚ) * gaps6 s j) = _ at he
  rw [he, sum_gap_product, ← hc, hcast]
  split_ifs <;> ring

/-- Actual uniform six-subsets have the exact rational first gap moments. -/
theorem sum_subset_gap {n : ℕ} (hn : 6 ≤ n) (i : Fin 7) :
    (∑ s : SixSubset n, (gaps6 s i : ℚ)) =
      (Fintype.card (SixSubset n) : ℚ) * ((n : ℚ) - 6) / 7 := by
  have h : 7 * (∑ s : SixSubset n, (gaps6 s i : ℚ)) =
      (Fintype.card (SixSubset n) : ℚ) * ((n - 6 : ℕ) : ℚ) := by
    exact_mod_cast seven_mul_sum_subset_gap hn i
  rw [Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem sum_product_sums {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → ℚ) (g : α → γ → ℚ) :
    (∑ s, (∑ a, f s a) * (∑ b, g s b)) = ∑ a, ∑ b, ∑ s, f s a * g s b := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- The actual sorted-position cross moment, before simplifying the finite prefix intersection. -/
theorem sum_sorted6_product_prefix {n : ℕ} (hn : 6 ≤ n) (i j : Fin 6) :
    (∑ s : SixSubset n, ((sorted6 s i).val : ℚ) * (sorted6 s j).val) =
      (Fintype.card (SixSubset n) : ℚ) * (i.val : ℚ) * j.val +
      (i.val : ℚ) * (j.val + 1) * ((Fintype.card (SixSubset n) : ℚ) * ((n : ℚ) - 6) / 7) +
      (j.val : ℚ) * (i.val + 1) * ((Fintype.card (SixSubset n) : ℚ) * ((n : ℚ) - 6) / 7) +
      ∑ a : Fin (i.val + 1), ∑ b : Fin (j.val + 1),
        (Fintype.card (SixSubset n) : ℚ) *
          (((n : ℚ) - 6) * (n - 7) / 56 +
            if a.val = b.val then ((n : ℚ) - 6) * (n + 1) / 56 else 0) := by
  have hexp (s : SixSubset n) :
      ((sorted6 s i).val : ℚ) * (sorted6 s j).val =
      (i.val : ℚ) * j.val +
      (i.val : ℚ) * (∑ b : Fin (j.val + 1), (gaps6 s ⟨b.val, by omega⟩ : ℚ)) +
      (j.val : ℚ) * (∑ a : Fin (i.val + 1), (gaps6 s ⟨a.val, by omega⟩ : ℚ)) +
      (∑ a : Fin (i.val + 1), (gaps6 s ⟨a.val, by omega⟩ : ℚ)) *
        (∑ b : Fin (j.val + 1), (gaps6 s ⟨b.val, by omega⟩ : ℚ)) := by
    rw [sorted6_eq_sum_gaps s i, sorted6_eq_sum_gaps s j]
    push_cast
    ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_product_sums]
  have hprefix (k : Fin 6) :
      (∑ s : SixSubset n, ∑ a : Fin (k.val + 1), (gaps6 s ⟨a.val, by omega⟩ : ℚ)) =
      (k.val + 1) * ((Fintype.card (SixSubset n) : ℚ) * ((n : ℚ) - 6) / 7) := by
    calc
      _ = ∑ a : Fin (k.val + 1), ∑ s : SixSubset n, (gaps6 s ⟨a.val, by omega⟩ : ℚ) :=
        Finset.sum_comm
      _ = ∑ _a : Fin (k.val + 1), (Fintype.card (SixSubset n) : ℚ) * ((n : ℚ) - 6) / 7 := by
        apply Finset.sum_congr rfl
        intro a _
        exact sum_subset_gap hn ⟨a.val, by omega⟩
      _ = _ := by simp
  rw [hprefix, hprefix]
  have hcross : (∑ a : Fin (i.val + 1), ∑ b : Fin (j.val + 1),
      ∑ s : SixSubset n, (gaps6 s ⟨a.val, by omega⟩ : ℚ) * gaps6 s ⟨b.val, by omega⟩) =
      ∑ a : Fin (i.val + 1), ∑ b : Fin (j.val + 1),
        (Fintype.card (SixSubset n) : ℚ) * (((n : ℚ) - 6) * (n - 7) / 56 +
          if a.val = b.val then ((n : ℚ) - 6) * (n + 1) / 56 else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simpa only [Fin.ext_iff] using sum_subset_gap_product hn
      (⟨a.val, by omega⟩ : Fin 7) (⟨b.val, by omega⟩ : Fin 7)
  rw [hcross]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [Finset.mul_sum]
  ring

/-- The exact raw cross moment of two sorted positions in actual uniform six-subsets. -/
theorem sum_sorted6_product {n : ℕ} (hn : 6 ≤ n) (i j : Fin 6) :
    (∑ s : SixSubset n, ((sorted6 s i).val : ℚ) * (sorted6 s j).val) =
      (Fintype.card (SixSubset n) : ℚ) *
        ((i.val : ℚ) * j.val +
          ((i.val : ℚ) * (j.val + 1) + (j.val : ℚ) * (i.val + 1)) * ((n : ℚ) - 6) / 7 +
          (i.val + 1) * (j.val + 1) * ((n : ℚ) - 6) * (n - 7) / 56 +
          (min i.val j.val + 1) * ((n : ℚ) - 6) * (n + 1) / 56) := by
  rw [sum_sorted6_product_prefix hn]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Fin.val_succ, Fin.val_zero] <;> ring

/-- Exact rational first moment of every actual sorted position. -/
theorem sum_sorted6 {n : ℕ} (hn : 6 ≤ n) (i : Fin 6) :
    (∑ s : SixSubset n, ((sorted6 s i).val : ℚ)) =
      (Fintype.card (SixSubset n) : ℚ) * ((i.val + 1) * ((n : ℚ) + 1) / 7 - 1) := by
  have h : 7 * (∑ s : SixSubset n, ((sorted6 s i).val : ℚ)) =
      (Fintype.card (SixSubset n) : ℚ) *
        (7 * (i.val : ℚ) + (i.val + 1) * ((n - 6 : ℕ) : ℚ)) := by
    exact_mod_cast seven_mul_sum_sorted6 hn i
  rw [Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

private theorem sum_centered_product {α : Type*} [Fintype α] (f g : α → ℚ)
    (d : ℚ) (hd : d ≠ 0) :
    (∑ s, (f s / d - 1 / 2) * (g s / d - 1 / 2)) =
      (∑ s, f s * g s) / d ^ 2 - (∑ s, f s) / (2 * d) -
        (∑ s, g s) / (2 * d) + (Fintype.card α : ℚ) / 4 := by
  have hp (s : α) : (f s / d - 1 / 2) * (g s / d - 1 / 2) =
      f s * g s / d ^ 2 - f s / (2 * d) - g s / (2 * d) + 1 / 4 := by
    field_simp [hd]
    <;> ring
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp

/-- The exact centered endpoint-scaled cross-moment sum over actual six-subsets. -/
theorem sum_sorted6_scaled_centered {n : ℕ} (hn : 6 ≤ n) (i j : Fin 6) :
    (∑ s : SixSubset n,
      (((sorted6 s i).val : ℚ) / ((n : ℚ) - 1) - 1 / 2) *
      (((sorted6 s j).val : ℚ) / ((n : ℚ) - 1) - 1 / 2)) =
      (Fintype.card (SixSubset n) : ℚ) *
        (((n : ℚ) + 1)^2 * (2 * (i.val + 1) - 7) * (2 * (j.val + 1) - 7) /
            (196 * ((n : ℚ) - 1)^2) +
          (min i.val j.val + 1) * (7 - ((max i.val j.val : ℕ) + 1 : ℚ)) *
            ((n : ℚ) + 1) * (n - 6) / (392 * ((n : ℚ) - 1)^2)) := by
  have hd : (n : ℚ) - 1 ≠ 0 := by
    have h6 : (6 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [sum_centered_product _ _ _ hd, sum_sorted6_product hn, sum_sorted6 hn, sum_sorted6 hn]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.val_succ, Fin.val_zero, min_def, max_def] <;>
      field_simp [hd] <;> ring

end PermutationSubsetMoments
