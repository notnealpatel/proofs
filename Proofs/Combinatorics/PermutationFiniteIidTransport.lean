import Combinatorics.PermutationFiniteIidCore
import Combinatorics.PermutationTwoAnchorKernel
set_option autoImplicit false
noncomputable section
namespace PermutationFiniteIidEndpointLaw
open PermutationFiniteWordPartition
attribute [local instance] Classical.propDecidable

/-- Physical positions of the free labels, with the right block increasing. -/
def freePosition {m n : ℕ} (hm : 2 ≤ m) (hn : 2*m ≤ n) :
    Fin (2*(m-1)) ↪ Fin n :=
  ⟨fun i => ⟨if i.val < m-1 then i.val+1 else n-m+(i.val-(m-1)), by
    split_ifs <;> omega⟩, by
    intro i j h
    have hv := congrArg Fin.val h
    dsimp at hv
    split_ifs at hv <;> apply Fin.ext <;> omega⟩

example : freePosition (by decide : 2 ≤ 2) (by decide : 2*2 ≤ 4) 1 = 2 := rfl

/-- The selected positions list begins with both anchors and then the free positions. -/
def selectedPosition {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q : Fin n) (hq : q.val+1=n) : Fin (2*(m-1)+2) ↪ Fin n :=
  ⟨fun i => ⟨if i.val=0 then 0 else if i.val=1 then q.val else
      if i.val-2 < m-1 then i.val-2+1 else n-m+(i.val-2-(m-1)), by
        split_ifs <;> omega⟩, by
    intro i j h
    have hv := congrArg Fin.val h
    change (if i.val=0 then 0 else if i.val=1 then q.val else
      if i.val-2 < m-1 then i.val-2+1 else n-m+(i.val-2-(m-1))) =
      (if j.val=0 then 0 else if j.val=1 then q.val else
      if j.val-2 < m-1 then j.val-2+1 else n-m+(j.val-2-(m-1))) at hv
    split_ifs at hv <;> apply Fin.ext <;> omega⟩

example : selectedPosition (by decide : 2 ≤ 2) (by decide : 2*2 ≤ 4)
    (3 : Fin 4) rfl 3 = 2 := by decide

/-- Selected labels consist of both anchors followed by the good free sample. -/
def selectedLabel {m n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (z : Fin (2*(m-1)) → Fin n) (hz : Good a b z) : Fin (2*(m-1)+2) ↪ Fin n :=
  ⟨fun i => if h0 : i.val=0 then a else if h1 : i.val=1 then b
    else z ⟨i.val-2, by omega⟩, by
    intro i j h
    dsimp at h
    split_ifs at h
    all_goals first
      | (apply Fin.ext; omega)
      | exact False.elim (hab h)
      | exact False.elim (hab h.symm)
      | exact False.elim ((hz.2 _).1 h)
      | exact False.elim ((hz.2 _).1 h.symm)
      | exact False.elim ((hz.2 _).2 h)
      | exact False.elim ((hz.2 _).2 h.symm)
      | (have he := congrArg Fin.val (hz.1 h); apply Fin.ext; dsimp at he; omega)⟩

example (z : Fin 2 → Fin 4) (hz : Good (m := 2) 0 3 z) :
    selectedLabel (m := 2) (0 : Fin 4) 3 (by decide) z hz 0 = 0 := rfl

/-- Restriction of an actual endpoint permutation to its free boundary labels. -/
def actualSample {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b) :
    Fin (2*(m-1)) → Fin n := fun i => π.val (freePosition hm hn i)

example {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n) (q a b : Fin n)
    (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b)
    (i : Fin (2*(m-1))) : actualSample hm hn q a b π i = π.val (freePosition hm hn i) := rfl

/-- Every actual sample is good, including when the middle block is empty. -/
theorem actualSample_good {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n)
    (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b) :
    Good a b (actualSample hm hn q a b π) := by
  refine ⟨π.val.injective.comp (freePosition hm hn).injective, ?_⟩
  intro i
  constructor
  · intro h
    have he := congrArg Fin.val (π.val.injective (h.trans π.property.1.symm))
    change (if i.val < m-1 then i.val+1 else n-m+(i.val-(m-1))) = 0 at he
    split_ifs at he <;> omega
  · intro h
    have he := congrArg Fin.val (π.val.injective (h.trans π.property.2.symm))
    change (if i.val < m-1 then i.val+1 else n-m+(i.val-(m-1))) = q.val at he
    split_ifs at he <;> omega

/-- Restricting to the selected list identifies each actual fiber with completions. -/
def actualSampleFiberEquiv {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n) (hab : a ≠ b)
    (z : Fin (2*(m-1)) → Fin n) (hz : Good a b z) :
    {π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b //
      actualSample hm hn q a b π = z} ≃
    {π : Equiv.Perm (Fin n) // ∀ i,
      π (selectedPosition hm hn q hq i) = selectedLabel a b hab z hz i} := by
  let forward (π : {π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b //
      actualSample hm hn q a b π = z}) :
      {π : Equiv.Perm (Fin n) // ∀ i,
        π (selectedPosition hm hn q hq i) = selectedLabel a b hab z hz i} :=
    ⟨π.val.val, by
      intro i
      by_cases h0 : i.val = 0
      · have he : selectedPosition hm hn q hq i = 0 := by
          apply Fin.ext
          change (if i.val = 0 then 0 else _) = (0 : Fin n).val
          rw [if_pos h0]
          rfl
        rw [he]
        change π.val.val 0 = (if h : i.val = 0 then a else _)
        rw [dif_pos h0]
        exact π.val.property.1
      · by_cases h1 : i.val = 1
        · have he : selectedPosition hm hn q hq i = q := by
            apply Fin.ext
            change (if i.val = 0 then 0 else if i.val = 1 then q.val else _) = q.val
            rw [if_neg h0, if_pos h1]
          rw [he]
          change π.val.val q = (if h : i.val = 0 then a else if h : i.val = 1 then b else _)
          rw [dif_neg h0, dif_pos h1]
          exact π.val.property.2
        · have he : selectedPosition hm hn q hq i = freePosition hm hn ⟨i.val-2, by omega⟩ := by
            apply Fin.ext
            change (if i.val = 0 then 0 else if i.val = 1 then q.val else _) = _
            rw [if_neg h0, if_neg h1]
            rfl
          rw [he]
          change π.val.val (freePosition hm hn ⟨i.val-2, by omega⟩) =
            (if h : i.val = 0 then a else if h : i.val = 1 then b else _)
          rw [dif_neg h0, dif_neg h1]
          exact congrFun π.property ⟨i.val-2, by omega⟩⟩
  let backward (π : {π : Equiv.Perm (Fin n) // ∀ i,
      π (selectedPosition hm hn q hq i) = selectedLabel a b hab z hz i}) :
      {π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b //
        actualSample hm hn q a b π = z} :=
    ⟨⟨π.val, by simpa [selectedPosition, selectedLabel] using π.property ⟨0, by omega⟩,
      by simpa [selectedPosition, selectedLabel] using π.property ⟨1, by omega⟩⟩, by
      funext i
      have hi := π.property ⟨i.val+2, by omega⟩
      change π.val (freePosition hm hn i) = z i
      change π.val ⟨if i.val+2=0 then 0 else if i.val+2=1 then q.val else
        if i.val+2-2 < m-1 then i.val+2-2+1 else n-m+(i.val+2-2-(m-1)), _⟩ =
        (if h : i.val+2=0 then a else if h : i.val+2=1 then b else z ⟨i.val+2-2, _⟩) at hi
      simp only [show i.val+2 ≠ 0 by omega, show i.val+2 ≠ 1 by omega,
        if_false, dite_false, Nat.add_sub_cancel] at hi
      calc
        π.val (freePosition hm hn i) = π.val ⟨if i.val < m-1 then i.val+1 else
            n-m+(i.val-(m-1)), by split_ifs <;> omega⟩ := by
          apply congrArg π.val
          apply Fin.ext
          rfl
        _ = z ⟨i.val, i.isLt⟩ := hi
        _ = z i := congrArg z (Fin.ext rfl)⟩
  exact ⟨forward, backward, fun _ => rfl, fun _ => rfl⟩

example {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n) (hab : a ≠ b)
    (z : Fin (2*(m-1)) → Fin n) (hz : Good a b z)
    (π : {π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b //
      actualSample hm hn q a b π = z}) :
    (actualSampleFiberEquiv hm hn q a b hq hab z hz π).val = π.val.val := rfl

/-- All actual good-sample fibers have the same factorial cardinality. -/
theorem card_actualSampleFiber {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n) (hab : a ≠ b)
    (z : Fin (2*(m-1)) → Fin n) (hz : Good a b z) :
    Fintype.card {π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b //
      actualSample hm hn q a b π = z} = (n-2*m).factorial := by
  rw [Fintype.card_congr (actualSampleFiberEquiv hm hn q a b hq hab z hz),
    PermutationTwoAnchorKernel.card_completion]
  congr 1
  omega

/-- Actual free restriction recovers both physically increasing boundary words. -/
theorem actualSample_words {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n)
    (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b) :
    sampledLeft (by omega : 0 < m) a (actualSample hm hn q a b π) =
      (fun i => π.val (prefixEmbedding (by omega : m ≤ n) i)) ∧
    sampledRight (by omega : 0 < m) b (actualSample hm hn q a b π) =
      (fun i => π.val (suffix (by omega : m ≤ n) i)) := by
  constructor
  · funext i
    dsimp [sampledLeft]
    split_ifs with h0
    · have hi : prefixEmbedding (by omega : m ≤ n) i = (0 : Fin n) := by
        apply Fin.ext
        change i.val = 0
        exact h0
      rw [hi, π.property.1]
    · change π.val (freePosition hm hn ⟨i.val-1, _⟩) = _
      congr 1
      apply Fin.ext
      change (if i.val-1 < m-1 then i.val-1+1 else _) = i.val
      rw [if_pos (by omega)]
      omega
  · funext i
    dsimp [sampledRight]
    split_ifs with hlast
    · have hi : suffix (by omega : m ≤ n) i = q := by
        apply Fin.ext
        change i.val + (n-m) = q.val
        omega
      rw [hi, π.property.2]
    · change π.val (freePosition hm hn ⟨m-1+i.val, _⟩) = _
      congr 1
      apply Fin.ext
      change (if m-1+i.val < m-1 then _ else n-m+(m-1+i.val-(m-1))) = i.val+(n-m)
      rw [if_neg (by omega)]
      omega

/-- Sample avoidance of an actual restriction is actual short avoidance. -/
theorem actualSample_avoid {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n)
    (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b) :
    SampleAvoid (by omega : 0 < m) a b (actualSample hm hn q a b π) ↔
      π ∈ PermutationEndpointProfile.shortAvoidFinset (m+1) q a b := by
  rw [sampleAvoid_iff_no_earliest, actual_short_iff_no_earliest hm hn q a b π,
    (actualSample_words hm hn q a b hq π).1,
    (actualSample_words hm hn q a b hq π).2]

/-- Counting an actual restriction event multiplies its good sample count by completions. -/
theorem card_actualSample_event {m n : ℕ} [NeZero n] (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (q a b : Fin n) (hq : q.val+1=n) (hab : a ≠ b)
    (P : (Fin (2*(m-1)) → Fin n) → Prop) :
    (Finset.univ.filter (fun π => P (actualSample hm hn q a b π))).card =
      (Finset.univ.filter (fun z => Good a b z ∧ P z)).card * (n-2*m).factorial := by
  classical
  let f := actualSample hm hn q a b
  let S := Finset.univ.filter (fun π => P (f π))
  let T := Finset.univ.filter (fun z => Good a b z ∧ P z)
  have hmap : (S : Set _).MapsTo f T := by
    intro π hπ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      actualSample_good hm hn q a b hq π, (Finset.mem_filter.mp hπ).2⟩
  have hc (z) (hz : z ∈ T) : (S.filter (fun π => f π = z)).card = (n-2*m).factorial := by
    have hzp := (Finset.mem_filter.mp hz).2
    have he : S.filter (fun π => f π = z) = Finset.univ.filter (fun π => f π = z) := by
      ext π
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.symm ▸ hzp.2, h⟩
    rw [he]
    exact (Fintype.card_subtype _).symm.trans
      (card_actualSampleFiber hm hn q a b hq hab z hzp.1)
  change S.card = T.card * _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  exact (Finset.sum_congr rfl hc).trans (by simp)

/-- The good sample count is the actual endpoint count divided by completions. -/
theorem actual_good_sample_identity_repaired {m n : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hn : 2*m ≤ n) (q a b : Fin n)
    (hq : q.val+1=n) (hab : a ≠ b) :
    let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
    let G := Finset.univ.filter (Good (m := m) a b)
    G.Nonempty ∧ PermutationEndpointProfile.shortFraction (m+1) q a b =
      ((E ∩ G).card : ℝ) / G.card := by
  classical
  let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
  let G := Finset.univ.filter (Good (m := m) a b)
  obtain ⟨π⟩ := PermutationEndpointCounting.fixedTwo_nonempty (0 : Fin n) q a b
    (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_zero] at hv; omega) hab
  have hG : G.Nonempty := ⟨actualSample hm hn q a b π,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, actualSample_good hm hn q a b hq π⟩⟩
  refine ⟨hG, ?_⟩
  have htotal := card_actualSample_event hm hn q a b hq hab (fun _ => True)
  simp only [and_true, Finset.filter_const, Finset.card_univ, if_true] at htotal
  have hevent := card_actualSample_event hm hn q a b hq hab
    (SampleAvoid (by omega : 0 < m) a b)
  have hsource : Finset.univ.filter (fun π =>
      SampleAvoid (by omega : 0 < m) a b (actualSample hm hn q a b π)) =
      PermutationEndpointProfile.shortAvoidFinset (m+1) q a b := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact actualSample_avoid hm hn q a b hq π
  have htarget : Finset.univ.filter (fun z => Good a b z ∧
      SampleAvoid (by omega : 0 < m) a b z) = E ∩ G := by
    ext z
    simp [E, G, and_comm]
  rw [hsource, htarget] at hevent
  change PermutationEndpointProfile.shortFraction (m+1) q a b = _
  unfold PermutationEndpointProfile.shortFraction
  rw [hevent, htotal]
  simp only [Nat.cast_mul]
  exact mul_div_mul_right _ _ (by positivity : ((n-2*m).factorial : ℝ) ≠ 0)
end PermutationFiniteIidEndpointLaw
