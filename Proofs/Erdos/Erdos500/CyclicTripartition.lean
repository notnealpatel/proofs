import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

set_option autoImplicit false

/-!
The classical cyclic tripartition construction for the tetrahedron problem.
Only ABC, AAB, BBC and CCA are edges. No optimality or priority claim is made.
-/
namespace Erdos500.CyclicTripartition

/-- The first canonical interval, of length `n / 3`. -/
def partA (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n / 3)

/-- The second canonical interval, of length `n / 3`. -/
def partB (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => n / 3 ≤ i.val ∧ i.val < 2 * (n / 3))

/-- The third canonical interval, of length `n / 3`. -/
def partC (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2 * (n / 3) ≤ i.val ∧ i.val < 3 * (n / 3))

/-- The four permitted intersection-count vectors, in their cyclic orientation. -/
def allowed (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) ∨
  (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2)

instance (a b c : ℕ) : Decidable (allowed a b c) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The actual finite family of unordered triples with precisely the four permitted vectors. -/
def edges (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun s =>
    allowed (s ∩ partA n).card (s ∩ partB n).card (s ∩ partC n).card)

/-- Membership retains both actual three-uniformity and the exact four-vector predicate. -/
theorem mem_edges (n : ℕ) (s : Finset (Fin n)) :
    s ∈ edges n ↔ s.card = 3 ∧
      allowed (s ∩ partA n).card (s ∩ partB n).card (s ∩ partC n).card := by
  simp [edges]

example : partA 3 = {0} := by decide
example : partB 3 = {1} := by decide
example : partC 3 = {2} := by decide
example : allowed 2 1 0 ∧ ¬ allowed 1 2 0 := by decide
example : (edges 3).card = 1 := by decide

private theorem interval_card (n l k : ℕ) (h : l + k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => l ≤ i.val ∧ i.val < l + k)).card = k := by
  classical
  symm
  calc
    k = (Finset.range k).card := (Finset.card_range k).symm
    _ = _ := by
      apply Finset.card_bij (fun i hi => (⟨l + i, by have := Finset.mem_range.mp hi; omega⟩ : Fin n))
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := Finset.mem_range.mp hi
        omega
      · intro i hi j hj he
        have hv := congrArg Fin.val he
        dsimp at hv
        omega
      · intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        refine ⟨x.val - l, Finset.mem_range.mpr (by omega), ?_⟩
        apply Fin.ext
        dsimp
        omega

/-- The three canonical parts are pairwise disjoint. -/
theorem parts_disjoint (n : ℕ) :
    Disjoint (partA n) (partB n) ∧ Disjoint (partA n) (partC n) ∧
      Disjoint (partB n) (partC n) := by
  simp only [Finset.disjoint_left, partA, partB, partC, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro x ha hb
    omega
  constructor
  · intro x ha hc
    omega
  · intro x hb hc
    omega

/-- Each canonical interval has exactly `n / 3` vertices, including at zero. -/
theorem parts_card (n : ℕ) :
    (partA n).card = n / 3 ∧ (partB n).card = n / 3 ∧ (partC n).card = n / 3 := by
  have hq : 3 * (n / 3) ≤ n := by omega
  constructor
  · simpa [partA] using interval_card n 0 (n / 3) (by omega)
  constructor
  · simpa [partB, two_mul] using interval_card n (n / 3) (n / 3) (by omega)
  · have he : 2 * (n / 3) + n / 3 = 3 * (n / 3) := by omega
    simpa [partC, he] using interval_card n (2 * (n / 3)) (n / 3) (by omega)

private theorem recover {α : Type*} [DecidableEq α]
    (A B C u v w : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hu : u ⊆ A) (hv : v ⊆ B) (hw : w ⊆ C) :
    (u ∪ v ∪ w) ∩ A = u ∧ (u ∪ v ∪ w) ∩ B = v ∧ (u ∪ v ∪ w) ∩ C = w := by
  have hab := Finset.disjoint_left.mp hAB
  have hac := Finset.disjoint_left.mp hAC
  have hbc := Finset.disjoint_left.mp hBC
  constructor
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hx | hx) | hx, hA⟩
      · exact hx
      · exact False.elim (hab hA (hv hx))
      · exact False.elim (hac hA (hw hx))
    · intro hx
      exact ⟨Or.inl (Or.inl hx), hu hx⟩
  constructor
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hx | hx) | hx, hB⟩
      · exact False.elim (hab (hu hx) hB)
      · exact hx
      · exact False.elim (hbc hB (hw hx))
    · intro hx
      exact ⟨Or.inl (Or.inr hx), hv hx⟩
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hx | hx) | hx, hC⟩
      · exact False.elim (hac (hu hx) hC)
      · exact False.elim (hbc (hv hx) hC)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hw hx⟩

private theorem decompose {α : Type*} [DecidableEq α] (s A B C : Finset α)
    (hs : s ⊆ A ∪ B ∪ C) : (s ∩ A) ∪ (s ∩ B) ∪ (s ∩ C) = s := by
  ext x
  have hx := fun (h : x ∈ s) => hs h
  simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
  aesop

/-- A fixed intersection-vector class, restricted to the three parts. -/
private def vectorFamily {α : Type*} [Fintype α] [DecidableEq α]
    (A B C : Finset α) (a b c : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun s => s ⊆ A ∪ B ∪ C ∧
    (s ∩ A).card = a ∧ (s ∩ B).card = b ∧ (s ∩ C).card = c)

private theorem mem_vectorFamily {α : Type*} [Fintype α] [DecidableEq α]
    (A B C s : Finset α) (a b c : ℕ) :
    s ∈ vectorFamily A B C a b c ↔ s ⊆ A ∪ B ∪ C ∧
      (s ∩ A).card = a ∧ (s ∩ B).card = b ∧ (s ∩ C).card = c := by
  simp [vectorFamily]

private theorem vectorFamily_card {α : Type*} [Fintype α] [DecidableEq α]
    (A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (a b c : ℕ) :
    (vectorFamily A B C a b c).card = A.card.choose a * B.card.choose b * C.card.choose c := by
  symm
  calc
    _ = ((A.powersetCard a ×ˢ B.powersetCard b) ×ˢ C.powersetCard c).card := by
      simp
    _ = _ := by
      apply Finset.card_bij (fun p _ => p.1.1 ∪ p.1.2 ∪ p.2)
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp, hw⟩
        rcases Finset.mem_product.mp hp with ⟨hu, hv⟩
        rcases Finset.mem_powersetCard.mp hu with ⟨hu, huc⟩
        rcases Finset.mem_powersetCard.mp hv with ⟨hv, hvc⟩
        rcases Finset.mem_powersetCard.mp hw with ⟨hw, hwc⟩
        have hr := recover A B C _ _ _ hAB hAC hBC hu hv hw
        apply (mem_vectorFamily A B C _ a b c).mpr
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hu hx))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hv hx))
          · exact Finset.mem_union_right _ (hw hx)
        · simp only [hr.1, hr.2.1, hr.2.2, huc, hvc, hwc, and_self]
      · intro p hp r hr he
        rcases Finset.mem_product.mp hp with ⟨hp, hpw⟩
        rcases Finset.mem_product.mp hp with ⟨hpu, hpv⟩
        rcases Finset.mem_product.mp hr with ⟨hr, hrw⟩
        rcases Finset.mem_product.mp hr with ⟨hru, hrv⟩
        have hpr := recover A B C _ _ _ hAB hAC hBC
          (Finset.mem_powersetCard.mp hpu).1 (Finset.mem_powersetCard.mp hpv).1
          (Finset.mem_powersetCard.mp hpw).1
        have hrr := recover A B C _ _ _ hAB hAC hBC
          (Finset.mem_powersetCard.mp hru).1 (Finset.mem_powersetCard.mp hrv).1
          (Finset.mem_powersetCard.mp hrw).1
        have hu := congrArg (fun s => s ∩ A) he
        have hv := congrArg (fun s => s ∩ B) he
        have hw := congrArg (fun s => s ∩ C) he
        rw [hpr.1, hrr.1] at hu
        rw [hpr.2.1, hrr.2.1] at hv
        rw [hpr.2.2, hrr.2.2] at hw
        exact Prod.ext (Prod.ext hu hv) hw
      · intro s hs
        rcases (mem_vectorFamily A B C s a b c).mp hs with ⟨hs, ha, hb, hc⟩
        refine ⟨((s ∩ A, s ∩ B), s ∩ C), ?_, decompose s A B C hs⟩
        simp [Finset.mem_powersetCard, ha, hb, hc]

private theorem intersection_sum {α : Type*} [DecidableEq α]
    (s A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) :
    (s ∩ A).card + (s ∩ B).card + (s ∩ C).card = (s ∩ (A ∪ B ∪ C)).card := by
  have hab : Disjoint (s ∩ A) (s ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hac : Disjoint (s ∩ A) (s ∩ C) :=
    hAC.mono Finset.inter_subset_right Finset.inter_subset_right
  have hbc : Disjoint (s ∩ B) (s ∩ C) :=
    hBC.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩),
    Finset.card_union_of_disjoint hab]

private theorem allowed_sum (a b c : ℕ) (h : allowed a b c) : a + b + c = 3 := by
  rcases h with h | h | h | h <;> omega

/-- Every edge is supported on the three parts; leftover vertices are isolated. -/
theorem edges_supported (n : ℕ) (s : Finset (Fin n)) (hs : s ∈ edges n) :
    s ⊆ partA n ∪ partB n ∪ partC n := by
  rcases (mem_edges n s).mp hs with ⟨hsize, hallowed⟩
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  have hsum := intersection_sum s _ _ _ hab hac hbc
  have he : s ∩ (partA n ∪ partB n ∪ partC n) = s :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [← hsum, hsize, allowed_sum _ _ _ hallowed])
  exact Finset.inter_eq_left.mp he

/-- The canonical leftover vertices, all of which are absent from every edge. -/
def isolated (n : ℕ) : Finset (Fin n) :=
  Finset.univ \ (partA n ∪ partB n ∪ partC n)

example : (isolated 8).card = 2 := by decide
example : isolated 0 = ∅ := by decide

/-- At most two vertices lie outside the three equal parts. -/
theorem isolated_card (n : ℕ) : (isolated n).card + 3 * (n / 3) = n ∧
    (isolated n).card ≤ 2 := by
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  rcases parts_card n with ⟨ha, hb, hc⟩
  have hu : (partA n ∪ partB n ∪ partC n).card = 3 * (n / 3) := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩),
      Finset.card_union_of_disjoint hab, ha, hb, hc]
    omega
  have hs := Finset.card_sdiff_of_subset
    (Finset.subset_univ (partA n ∪ partB n ∪ partC n))
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  change (isolated n).card = n - (partA n ∪ partB n ∪ partC n).card at hs
  rw [hu] at hs
  omega

private theorem vectorFamily_size {α : Type*} [Fintype α] [DecidableEq α]
    (A B C s : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (a b c : ℕ) (hs : s ∈ vectorFamily A B C a b c) :
    s.card = a + b + c := by
  rcases (mem_vectorFamily A B C s a b c).mp hs with ⟨hsub, ha, hb, hc⟩
  have hsum := intersection_sum s A B C hAB hAC hBC
  rw [Finset.inter_eq_left.mpr hsub, ha, hb, hc] at hsum
  exact hsum.symm

private theorem vectorFamily_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (A B C : Finset α) (a b c a' b' c' : ℕ)
    (hne : a ≠ a' ∨ b ≠ b' ∨ c ≠ c') :
    Disjoint (vectorFamily A B C a b c) (vectorFamily A B C a' b' c') := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  have hs' := (mem_vectorFamily A B C s a b c).mp hs
  have ht' := (mem_vectorFamily A B C s a' b' c').mp ht
  omega

private theorem edges_eq_union (n : ℕ) :
    edges n = ((vectorFamily (partA n) (partB n) (partC n) 1 1 1 ∪
      vectorFamily (partA n) (partB n) (partC n) 2 1 0) ∪
      vectorFamily (partA n) (partB n) (partC n) 0 2 1) ∪
      vectorFamily (partA n) (partB n) (partC n) 1 0 2 := by
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  ext s
  simp only [Finset.mem_union]
  constructor
  · intro hs
    have hsub := edges_supported n s hs
    have ht := ((mem_edges n s).mp hs).2
    rcases ht with ht | ht | ht | ht
    · exact Or.inl (Or.inl (Or.inl ((mem_vectorFamily _ _ _ _ _ _ _).mpr ⟨hsub, ht⟩)))
    · exact Or.inl (Or.inl (Or.inr ((mem_vectorFamily _ _ _ _ _ _ _).mpr ⟨hsub, ht⟩)))
    · exact Or.inl (Or.inr ((mem_vectorFamily _ _ _ _ _ _ _).mpr ⟨hsub, ht⟩))
    · exact Or.inr ((mem_vectorFamily _ _ _ _ _ _ _).mpr ⟨hsub, ht⟩)
  · intro hs
    apply (mem_edges n s).mpr
    rcases hs with ((hs | hs) | hs) | hs
    · have hsize := vectorFamily_size _ _ _ s hab hac hbc 1 1 1 hs
      exact ⟨hsize, Or.inl ((mem_vectorFamily _ _ _ _ _ _ _).mp hs).2⟩
    · have hsize := vectorFamily_size _ _ _ s hab hac hbc 2 1 0 hs
      exact ⟨hsize, Or.inr (Or.inl ((mem_vectorFamily _ _ _ _ _ _ _).mp hs).2)⟩
    · have hsize := vectorFamily_size _ _ _ s hab hac hbc 0 2 1 hs
      exact ⟨hsize, Or.inr (Or.inr (Or.inl ((mem_vectorFamily _ _ _ _ _ _ _).mp hs).2))⟩
    · have hsize := vectorFamily_size _ _ _ s hab hac hbc 1 0 2 hs
      exact ⟨hsize, Or.inr (Or.inr (Or.inr ((mem_vectorFamily _ _ _ _ _ _ _).mp hs).2))⟩

/-- The four disjoint unordered types contribute `q^3 + 3 * choose q 2 * q` edges. -/
theorem edges_card (n : ℕ) :
    (edges n).card = (n / 3)^3 + 3 * (n / 3).choose 2 * (n / 3) := by
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  rcases parts_card n with ⟨ha, hb, hc⟩
  have hd (a b c a' b' c' : ℕ) (h : a ≠ a' ∨ b ≠ b' ∨ c ≠ c') :=
    vectorFamily_disjoint (partA n) (partB n) (partC n) a b c a' b' c' h
  have h12 := hd 1 1 1 2 1 0 (by omega)
  have h13 := hd 1 1 1 0 2 1 (by omega)
  have h14 := hd 1 1 1 1 0 2 (by omega)
  have h23 := hd 2 1 0 0 2 1 (by omega)
  have h24 := hd 2 1 0 1 0 2 (by omega)
  have h34 := hd 0 2 1 1 0 2 (by omega)
  rw [edges_eq_union, Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h14, h24⟩, h34⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h13, h23⟩),
    Finset.card_union_of_disjoint h12]
  simp only [vectorFamily_card _ _ _ hab hac hbc, ha, hb, hc,
    Nat.choose_one_right, Nat.choose_zero_right, mul_one, one_mul]
  ring

private theorem choose_two_identity (q : ℕ) : 2 * q.choose 2 + q = q^2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- The exact subtraction-free count identity, valid also at `q = 0, 1`. -/
theorem edges_card_identity (n : ℕ) :
    2 * (edges n).card + 3 * (n / 3)^2 = 5 * (n / 3)^3 := by
  rw [edges_card]
  have hchoose := choose_two_identity (n / 3)
  nlinarith

private theorem erase_inter_card_of_mem {α : Type*} [DecidableEq α]
    (S A : Finset α) (x : α) (hx : x ∈ S ∩ A) :
    (S.erase x ∩ A).card = (S ∩ A).card - 1 := by
  rw [Finset.erase_inter, Finset.card_erase_of_mem hx]

private theorem erase_inter_card_of_notMem {α : Type*} [DecidableEq α]
    (S A : Finset α) (x : α) (hx : x ∉ A) :
    (S.erase x ∩ A).card = (S ∩ A).card := by
  rw [Finset.erase_inter, Finset.erase_eq_of_notMem (by simp [hx])]

private theorem impossible_four_counts (a b c : ℕ) (hs : a + b + c = 4)
    (ha : 0 < a → allowed (a - 1) b c)
    (hb : 0 < b → allowed a (b - 1) c)
    (hc : 0 < c → allowed a b (c - 1)) : False := by
  -- This finite arithmetic step keeps the cyclic orientations exactly as defined.
  simp only [allowed] at ha hb hc
  omega

/-- Every actual four-element vertex set has an actual three-subset absent from `edges n`.
This is non-induced tetrahedron exclusion, with no certificate hypothesis. -/
theorem four_set_missing (n : ℕ) (S : Finset (Fin n)) (hS : S.card = 4) :
    ∃ s : Finset (Fin n), s ⊆ S ∧ s.card = 3 ∧ s ∉ edges n := by
  classical
  by_contra hnone
  push Not at hnone
  have herase (x : Fin n) (hx : x ∈ S) : S.erase x ∈ edges n := by
    apply hnone (S.erase x) (Finset.erase_subset x S)
    rw [Finset.card_erase_of_mem hx, hS]
  have hsupport : S ⊆ partA n ∪ partB n ∪ partC n := by
    intro x hx
    have hrest : (S.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx, hS]
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (S.erase x).card by omega)
    have hyS := Finset.mem_of_mem_erase hy
    have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
    exact edges_supported n (S.erase y) (herase y hyS)
      (Finset.mem_erase.mpr ⟨hxy, hx⟩)
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  have hsum : (S ∩ partA n).card + (S ∩ partB n).card + (S ∩ partC n).card = 4 := by
    rw [intersection_sum S _ _ _ hab hac hbc, Finset.inter_eq_left.mpr hsupport, hS]
  have ha : 0 < (S ∩ partA n).card →
      allowed ((S ∩ partA n).card - 1) (S ∩ partB n).card (S ∩ partC n).card := by
    intro ha
    obtain ⟨x, hx⟩ := Finset.card_pos.mp ha
    have hxS := (Finset.mem_inter.mp hx).1
    have hxA := (Finset.mem_inter.mp hx).2
    have hxB : x ∉ partB n := Finset.disjoint_left.mp hab hxA
    have hxC : x ∉ partC n := Finset.disjoint_left.mp hac hxA
    have ht := ((mem_edges n (S.erase x)).mp (herase x hxS)).2
    rw [erase_inter_card_of_mem S _ x hx, erase_inter_card_of_notMem S _ x hxB,
      erase_inter_card_of_notMem S _ x hxC] at ht
    exact ht
  have hb : 0 < (S ∩ partB n).card →
      allowed (S ∩ partA n).card ((S ∩ partB n).card - 1) (S ∩ partC n).card := by
    intro hb
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hb
    have hxS := (Finset.mem_inter.mp hx).1
    have hxB := (Finset.mem_inter.mp hx).2
    have hxA : x ∉ partA n := Finset.disjoint_left.mp hab.symm hxB
    have hxC : x ∉ partC n := Finset.disjoint_left.mp hbc hxB
    have ht := ((mem_edges n (S.erase x)).mp (herase x hxS)).2
    rw [erase_inter_card_of_notMem S _ x hxA, erase_inter_card_of_mem S _ x hx,
      erase_inter_card_of_notMem S _ x hxC] at ht
    exact ht
  have hc : 0 < (S ∩ partC n).card →
      allowed (S ∩ partA n).card (S ∩ partB n).card ((S ∩ partC n).card - 1) := by
    intro hc
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hc
    have hxS := (Finset.mem_inter.mp hx).1
    have hxC := (Finset.mem_inter.mp hx).2
    have hxA : x ∉ partA n := Finset.disjoint_left.mp hac.symm hxC
    have hxB : x ∉ partB n := Finset.disjoint_left.mp hbc.symm hxC
    have ht := ((mem_edges n (S.erase x)).mp (herase x hxS)).2
    rw [erase_inter_card_of_notMem S _ x hxA, erase_inter_card_of_notMem S _ x hxB,
      erase_inter_card_of_mem S _ x hx] at ht
    exact ht
  exact impossible_four_counts _ _ _ hsum ha hb hc

/-- At zero vertices the same edge family is empty and satisfies the same exclusion theorem. -/
theorem fixture_zero : (edges 0).card = 0 ∧
    ∀ S : Finset (Fin 0), S.card = 4 →
      ∃ s : Finset (Fin 0), s ⊆ S ∧ s.card = 3 ∧ s ∉ edges 0 := by
  exact ⟨by decide, four_set_missing 0⟩

/-- At three vertices the same family has its single ABC edge and excludes tetrahedra. -/
theorem fixture_three : (edges 3).card = 1 ∧
    ∀ S : Finset (Fin 3), S.card = 4 →
      ∃ s : Finset (Fin 3), s ⊆ S ∧ s.card = 3 ∧ s ∉ edges 3 := by
  exact ⟨by decide, four_set_missing 3⟩

/-- At six vertices the same four-vector family has fourteen, not twenty, edges. -/
theorem fixture_six : (edges 6).card = 14 ∧
    ∀ S : Finset (Fin 6), S.card = 4 →
      ∃ s : Finset (Fin 6), s ⊆ S ∧ s.card = 3 ∧ s ∉ edges 6 := by
  exact ⟨by decide, four_set_missing 6⟩

/-- At eight vertices the same family has fourteen edges and exactly two leftover vertices. -/
theorem fixture_eight : (edges 8).card = 14 ∧ (isolated 8).card = 2 ∧
    ∀ S : Finset (Fin 8), S.card = 4 →
      ∃ s : Finset (Fin 8), s ⊆ S ∧ s.card = 3 ∧ s ∉ edges 8 := by
  exact ⟨by decide, by decide, four_set_missing 8⟩

example : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 ∧
    ({0, 2, 3} : Finset (Fin 6)) ⊆ {0, 1, 2, 3} ∧
    ({0, 2, 3} : Finset (Fin 6)).card = 3 ∧
    ({0, 2, 3} : Finset (Fin 6)) ∉ edges 6 := by decide
example : isolated 8 = {6, 7} := by decide

private theorem abc_mem_edges (n : ℕ) (a b c : Fin n)
    (ha : a ∈ partA n) (hb : b ∈ partB n) (hc : c ∈ partC n) :
    {a} ∪ {b} ∪ {c} ∈ edges n := by
  rcases parts_disjoint n with ⟨hab, hac, hbc⟩
  have ha' : {a} ⊆ partA n := Finset.singleton_subset_iff.mpr ha
  have hb' : {b} ⊆ partB n := Finset.singleton_subset_iff.mpr hb
  have hc' : {c} ⊆ partC n := Finset.singleton_subset_iff.mpr hc
  have hr := recover _ _ _ {a} {b} {c} hab hac hbc ha' hb' hc'
  have hsize : ({a} ∪ {b} ∪ {c} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨hac.mono ha' hc', hbc.mono hb' hc'⟩),
      Finset.card_union_of_disjoint (hab.mono ha' hb')]
    simp
  apply (mem_edges n _).mpr
  refine ⟨hsize, Or.inl ?_⟩
  simp only [hr.1, hr.2.1, hr.2.2, Finset.card_singleton, and_self]

/-- The canonical leftovers are exactly the vertices occurring in no edge, not merely
an upper bound on a preselected exceptional set. -/
theorem isolated_iff (n : ℕ) (x : Fin n) : x ∈ isolated n ↔
    ∀ s ∈ edges n, x ∉ s := by
  constructor
  · intro hx s hs hxs
    have hxU := edges_supported n s hs hxs
    exact (Finset.mem_sdiff.mp hx).2 hxU
  · intro hnone
    by_contra hx
    have hxU : x ∈ partA n ∪ partB n ∪ partC n := by
      by_contra hxU
      exact hx (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxU⟩)
    rcases parts_card n with ⟨ha, hb, hc⟩
    have hq : 0 < n / 3 := by
      rcases Finset.mem_union.mp hxU with hxAB | hxC
      · rcases Finset.mem_union.mp hxAB with hxA | hxB
        · have hp := Finset.card_pos.mpr (show (partA n).Nonempty from ⟨x, hxA⟩)
          omega
        · have hp := Finset.card_pos.mpr (show (partB n).Nonempty from ⟨x, hxB⟩)
          omega
      · have hp := Finset.card_pos.mpr (show (partC n).Nonempty from ⟨x, hxC⟩)
        omega
    obtain ⟨a, haA⟩ := Finset.card_pos.mp (show 0 < (partA n).card by omega)
    obtain ⟨b, hbB⟩ := Finset.card_pos.mp (show 0 < (partB n).card by omega)
    obtain ⟨c, hcC⟩ := Finset.card_pos.mp (show 0 < (partC n).card by omega)
    rcases Finset.mem_union.mp hxU with hxAB | hxC
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact hnone _ (abc_mem_edges n x b c hxA hbB hcC) (by simp)
      · exact hnone _ (abc_mem_edges n a x c haA hxB hcC) (by simp)
    · exact hnone _ (abc_mem_edges n a b x haA hbB hxC) (by simp)

end Erdos500.CyclicTripartition
