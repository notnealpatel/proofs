import Erdos.Erdos64.UniqueCubicClawCenterBlockInsertion
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter.CycleCount

/-- For blocks of length one or two, the flattened length plus the number of
singleton blocks is twice the number of indices. -/
theorem length_add_card_singletons {A : Type*} {m : ℕ}
    (blocks : Fin (m + 1) → List A)
    (h : ∀ i, (blocks i).length = 1 ∨ (blocks i).length = 2) :
    (List.ofFn blocks).flatten.length +
      (Finset.univ.filter (fun i => (blocks i).length = 1)).card = 2 * (m + 1) := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  have hpoint (i : Fin (m + 1)) :
      (blocks i).length + (if (blocks i).length = 1 then 1 else 0) = 2 := by
    rcases h i with hi | hi <;> simp [hi]
  have hs : (∑ i : Fin (m + 1),
      ((blocks i).length + (if (blocks i).length = 1 then 1 else 0))) =
      ∑ _i : Fin (m + 1), 2 :=
    Finset.sum_congr rfl (fun i _ => hpoint i)
  simpa [Finset.sum_add_distrib, Finset.sum_boole, Nat.mul_comm] using hs

/-- Optional insertions precisely at the selected indices count those indices,
independently of whether any inserted values coincide. -/
theorem card_isSome_selected {A : Type*} {m : ℕ}
    (s : Finset (Fin (m + 1))) (a : Fin (m + 1) → A) :
    (Finset.univ.filter (fun i =>
      (if i ∈ s then some (a i) else none).isSome)).card = s.card := by
  congr 1
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- Selecting a root outside the selected set adds exactly one insertion index. -/
theorem card_isSome_root_of_notMem {A : Type*} {m : ℕ}
    (z : Fin (m + 1)) (s : Finset (Fin (m + 1))) (hz : z ∉ s)
    (v : A) (a : Fin (m + 1) → A) :
    (Finset.univ.filter (fun i =>
      (if i = z then some v else if i ∈ s then some (a i) else none).isSome)).card =
        s.card + 1 := by
  have hset : (Finset.univ.filter (fun i =>
      (if i = z then some v else if i ∈ s then some (a i) else none).isSome)) =
      insert z s := by
    ext i
    by_cases hiz : i = z <;> by_cases hi : i ∈ s <;> simp [hiz, hi]
  rw [hset, Finset.card_insert_of_notMem hz]

/-- A root and a subset of the other cycle indices select exactly one more
insertion index than the subset alone. -/
theorem card_isSome_root_of_subset_erase {A : Type*} {m : ℕ}
    (z : Fin (m + 1)) (s : Finset (Fin (m + 1)))
    (hs : s ⊆ Finset.univ.erase z) (v : A) (a : Fin (m + 1) → A) :
    (Finset.univ.filter (fun i =>
      (if i = z then some v else if i ∈ s then some (a i) else none).isSome)).card =
        s.card + 1 := by
  apply card_isSome_root_of_notMem z s _ v a
  intro hz
  exact (Finset.mem_erase.mp (hs hz)).1 rfl

end Erdos64.UniqueCubicClawCenter.CycleCount
