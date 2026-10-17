import Combinatorics.PermutationFiniteIidPatternPartition
set_option autoImplicit false
noncomputable section
namespace FiniteIidPatternRepair
open PermutationFiniteWordPartition PermutationFiniteIidEndpointLaw
attribute [local instance] Classical.propDecidable

/-- Reconstruct the free sample from its two boundary restrictions and its middle. -/
def assemble {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (f g : Fin k → Fin n) (u : Fin (2*(m-k)) → Fin n) :
    Fin (2*(m-1)) → Fin n := fun i =>
  if h : i.val < k-1 then f ⟨i.val+1, by omega⟩
  else if h' : i.val < 2*(m-1)-(k-1) then u ⟨i.val-(k-1), by omega⟩
  else g ⟨i.val-(2*(m-1)-(k-1)), by omega⟩

example (f g : Fin 2 → Fin 4) (u : Fin 0 → Fin 4) :
    assemble (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) f g u 0 = f 1 := rfl

/-- Reconstruction recovers the left anchored restriction. -/
theorem assemble_left {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (a : Fin n) (f g : Fin k → Fin n) (u : Fin (2*(m-k)) → Fin n)
    (hf : f ⟨0, by omega⟩ = a) :
    leftWord (sampledLeft (by omega : 0 < m) a (assemble ht hk f g u)) hk = f := by
  funext i
  change (if h : i.val = 0 then a else assemble ht hk f g u ⟨i.val-1, _⟩) = f i
  split_ifs with hi
  · have he : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [he, hf]
  · simp only [assemble, show i.val-1 < k-1 by omega, dite_true]
    congr 1
    apply Fin.ext
    simp only
    omega

/-- Reconstruction recovers the right anchored restriction in physical order. -/
theorem assemble_right {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (b : Fin n) (f g : Fin k → Fin n) (u : Fin (2*(m-k)) → Fin n)
    (hg : g ⟨k-1, by omega⟩ = b) :
    rightWord (sampledRight (by omega : 0 < m) b (assemble ht hk f g u)) hk = g := by
  funext i
  change (if h : i.val+(m-k) = m-1 then b else
    assemble ht hk f g u ⟨m-1+(i.val+(m-k)), _⟩) = g i
  split_ifs with hi
  · have he : i = ⟨k-1, by omega⟩ := by
      apply Fin.ext
      change i.val = k-1
      omega
    rw [he]
    exact hg.symm
  · simp only [assemble, show ¬ m-1+(i.val+(m-k)) < k-1 by omega,
      show ¬ m-1+(i.val+(m-k)) < 2*(m-1)-(k-1) by omega, dite_false]
    congr 1
    apply Fin.ext
    simp only
    omega

/-- The middle coordinates of reconstruction are exactly the supplied middle. -/
theorem assemble_middle {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (f g : Fin k → Fin n) (u : Fin (2*(m-k)) → Fin n)
    (i : Fin (2*(m-k))) :
    assemble ht hk f g u ⟨k-1+i.val, by omega⟩ = u i := by
  simp only [assemble, show ¬ k-1+i.val < k-1 by omega,
    show k-1+i.val < 2*(m-1)-(k-1) by omega, dite_false, dite_true]
  congr 1
  apply Fin.ext
  simp only
  omega

/-- Reconstructing a sample from its restrictions is the identity, without Good. -/
theorem assemble_restrict {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (a b : Fin n) (z : Fin (2*(m-1)) → Fin n) :
    assemble ht hk
      (leftWord (sampledLeft (by omega : 0 < m) a z) hk)
      (rightWord (sampledRight (by omega : 0 < m) b z) hk)
      (fun i => z ⟨k-1+i.val, by omega⟩) = z := by
  funext i
  dsimp only [assemble]
  split_ifs with h h'
  · change (if hi : i.val+1=0 then a else z ⟨i.val+1-1, _⟩) = z i
    simp only [show i.val+1 ≠ 0 by omega, dite_false, Nat.add_sub_cancel]
  · congr 1
    apply Fin.ext
    simp only
    omega
  · change (if hi : i.val-(2*(m-1)-(k-1))+(m-k)=m-1 then b else
      z ⟨m-1+(i.val-(2*(m-1)-(k-1))+(m-k)), _⟩) = z i
    rw [dif_neg (by omega)]
    congr 1
    apply Fin.ext
    simp only
    omega
end FiniteIidPatternRepair

namespace FiniteIidPatternRepair
open PermutationFiniteWordPartition PermutationFiniteIidEndpointLaw
attribute [local instance] Classical.propDecidable

/-- A common cell consists of independent anchored rank embeddings and arbitrary middle labels. -/
def commonCellEquiv {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (a b : Fin n) (σ : Equiv.Perm (Fin k)) :
    {z : Fin (2*(m-1)) → Fin n // Common
      (sampledLeft (by omega : 0 < m) a z) (sampledRight (by omega : 0 < m) b z) hk σ} ≃
    ({f : Fin k ↪ Fin n // f ⟨0, by omega⟩ = a ∧
      PermutationBoundaryStandardization.rank f = σ} ×
     {g : Fin k ↪ Fin n // g ⟨k-1, by omega⟩ = b ∧
      PermutationBoundaryStandardization.rank g = σ}) × (Fin (2*(m-k)) → Fin n) := by
  let forward (z : {z : Fin (2*(m-1)) → Fin n // Common
      (sampledLeft (by omega : 0 < m) a z) (sampledRight (by omega : 0 < m) b z) hk σ}) :=
    let h := (common_iff_rank _ _ hk σ).mp z.property
    ((⟨⟨_, h.1⟩, by
          change (if h : (0 : ℕ)=0 then a else z.val ⟨0, by omega⟩) = a
          rw [dif_pos rfl], h.2.2.1⟩ :
        {f : Fin k ↪ Fin n // f ⟨0, by omega⟩ = a ∧ PermutationBoundaryStandardization.rank f = σ}),
      (⟨⟨_, h.2.1⟩, by
          change (if h : k-1+(m-k)=m-1 then b else _) = b
          rw [dif_pos (show k-1+(m-k)=m-1 by omega)], h.2.2.2⟩ :
        {g : Fin k ↪ Fin n // g ⟨k-1, by omega⟩ = b ∧ PermutationBoundaryStandardization.rank g = σ}))
      |> fun p => (p, fun i : Fin (2*(m-k)) => z.val ⟨k-1+i.val, by omega⟩)
  let backward (p : ({f : Fin k ↪ Fin n // f ⟨0, by omega⟩ = a ∧
      PermutationBoundaryStandardization.rank f = σ} ×
     {g : Fin k ↪ Fin n // g ⟨k-1, by omega⟩ = b ∧
      PermutationBoundaryStandardization.rank g = σ}) × (Fin (2*(m-k)) → Fin n)) :
      {z : Fin (2*(m-1)) → Fin n // Common
        (sampledLeft (by omega : 0 < m) a z) (sampledRight (by omega : 0 < m) b z) hk σ} :=
    ⟨assemble ht hk p.1.1.val p.1.2.val p.2, by
      apply (common_iff_rank _ _ hk σ).mpr
      have hl := assemble_left ht hk a p.1.1.val p.1.2.val p.2 p.1.1.property.1
      have hr := assemble_right ht hk b p.1.1.val p.1.2.val p.2 p.1.2.property.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hl]; exact p.1.1.val.injective
      · rw [hr]; exact p.1.2.val.injective
      · convert p.1.1.property.2 using 1
        congr 1
        exact Function.Embedding.ext (congrFun hl)
      · convert p.1.2.property.2 using 1
        congr 1
        exact Function.Embedding.ext (congrFun hr)⟩
  refine ⟨forward, backward, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    exact assemble_restrict ht hk a b z.val
  · intro p
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        apply Function.Embedding.ext
        exact congrFun (assemble_left ht hk a p.1.1.val p.1.2.val p.2 p.1.1.property.1)
      · apply Subtype.ext
        apply Function.Embedding.ext
        exact congrFun (assemble_right ht hk b p.1.1.val p.1.2.val p.2 p.1.2.property.1)
    · funext i
      exact assemble_middle ht hk p.1.1.val p.1.2.val p.2 i

/-- The exact common-cell count includes only within-word injectivity. -/
theorem card_common_cell {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (a b : Fin n) (σ : Equiv.Perm (Fin k)) :
    (Finset.univ.filter (fun z => Common (sampledLeft (by omega : 0 < m) a z)
      (sampledRight (by omega : 0 < m) b z) hk σ)).card =
    ((Nat.choose a.val (σ ⟨0, by omega⟩).val *
      Nat.choose (n-1-a.val) (k-1-(σ ⟨0, by omega⟩).val)) *
     (Nat.choose b.val (σ ⟨k-1, by omega⟩).val *
      Nat.choose (n-1-b.val) (k-1-(σ ⟨k-1, by omega⟩).val))) * n^(2*(m-k)) := by
  calc
    _ = Nat.card {z : Fin (2*(m-1)) → Fin n // Common
        (sampledLeft (by omega : 0 < m) a z)
        (sampledRight (by omega : 0 < m) b z) hk σ} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := by
      rw [Nat.card_congr (commonCellEquiv ht hk a b σ), Nat.card_prod,
        card_independent_anchors]
      simp
end FiniteIidPatternRepair
namespace FiniteIidPatternRepair
open PermutationFiniteWordPartition PermutationFiniteIidEndpointLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Normalizing a common cell gives the original product of anchor weights. -/
theorem normalized_common_cell {m n k : ℕ} (ht : 2 ≤ k) (hk : k ≤ m)
    (hn : 0 < n) (a b : Fin n) (σ : Equiv.Perm (Fin k)) :
    ((Finset.univ.filter (fun z => ∃ hk : k ≤ m,
      Common (sampledLeft (by omega : 0 < m) a z)
        (sampledRight (by omega : 0 < m) b z) hk σ)).card : ℝ) /
        (n : ℝ)^(2*(m-1)) = patternWeight a b σ := by
  simp only [exists_prop_of_true hk]
  rw [card_common_cell ht hk a b σ]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : 2*(m-1) = (k-1)+(k-1)+2*(m-k) := by omega
  simp only [Nat.cast_mul, Nat.cast_pow, patternWeight, dif_pos (by omega : 0 < k),
    anchorWeight]
  rw [he, pow_add, pow_add]
  field_simp

/-- The exact iid identity for the actual avoiding permutation patterns. -/
theorem iid_pattern_identity_repaired {m n : ℕ} (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (a b : Fin n) :
    let E := Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)
    (E.card : ℝ)/(n : ℝ)^(2*(m-1)) = patternSum m a b := by
  dsimp only
  rw [normalized_sample_partition hm hn a b]
  unfold patternSum
  congr 1
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact normalized_common_cell (Finset.mem_Icc.mp hk).1
    (Finset.mem_Icc.mp hk).2 (by omega) a b σ

example : (Finset.univ.filter (fun z => Common
    (sampledLeft (by decide : 0 < 2) (0 : Fin 4) z)
    (sampledRight (by decide : 0 < 2) (3 : Fin 4) z)
    (by decide : 2 ≤ 2) (Equiv.refl (Fin 2)))).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_common_cell (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)]
  norm_num
end FiniteIidPatternRepair
