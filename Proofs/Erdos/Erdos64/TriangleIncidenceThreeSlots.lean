import Erdos.Erdos64.TriangleIncidenceCompression
import Erdos.Erdos64.TriangleIncidenceSlots

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

noncomputable local instance (V : Type*) : DecidableEq V := Classical.decEq V

/-- The next label in a cyclic array of three-slot rows. -/
def threeSlotNext {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V)
    (i : Fin (m+1)) (r : Fin 3) : V :=
  if r = 2 then L (i+1) 0 else L i (r+1)

example {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : Fin (m+1)) :
    threeSlotNext L i 0 = L i 1 := by simp [threeSlotNext]
example {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : Fin (m+1)) :
    threeSlotNext L i 2 = L (i+1) 0 := by simp [threeSlotNext]

private def row (m i : ℕ) : Fin (m+1) := ⟨i % (m+1), Nat.mod_lt _ (Nat.succ_pos m)⟩
private def slot (t : ℕ) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩
private def seq {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (t : ℕ) : V :=
  L (row m (t/3)) (slot t)

private lemma row_succ (m i : ℕ) : row m (i+1) = row m i + 1 := by
  apply Fin.ext
  simp [row, Fin.add_def, Nat.add_mod]

private lemma seq_eval {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V)
    (i : ℕ) (r : Fin 3) : seq L (3*i+r.val) = L (row m i) r := by
  have hdiv : (3*i+r.val)/3 = i := by omega
  have hmod : (3*i+r.val)%3 = r.val := by omega
  simp only [seq, hdiv]
  congr 1
  exact Fin.ext hmod

private lemma seq_step {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (t : ℕ) :
    seq L (t+1) = threeSlotNext L (row m (t/3)) (slot t) := by
  have ht : t = 3*(t/3)+(t%3) := by omega
  have hr : t%3 < 3 := Nat.mod_lt _ (by decide)
  rcases (show t%3 = 0 ∨ t%3 = 1 ∨ t%3 = 2 by omega) with h | h | h
  · have heq : slot t = 0 := Fin.ext h
    have hn : t+1 = 3*(t/3)+(1 : Fin 3).val := by omega
    rw [hn, seq_eval, heq]
    simp [threeSlotNext]
  · have heq : slot t = 1 := Fin.ext h
    have hn : t+1 = 3*(t/3)+(2 : Fin 3).val := by omega
    rw [hn, seq_eval, heq]
    simp [threeSlotNext]
  · have heq : slot t = 2 := Fin.ext h
    have hn : t+1 = 3*(t/3+1)+(0 : Fin 3).val := by omega
    rw [hn, seq_eval, heq, row_succ]
    simp [threeSlotNext]

private lemma seq_zero {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : ℕ) :
    seq L (3*i) = L (row m i) 0 := by
  simpa using seq_eval L i 0

private lemma seq_one {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : ℕ) :
    seq L (3*i+1) = L (row m i) 1 := seq_eval L i 1

private lemma seq_two {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : ℕ) :
    seq L (3*i+2) = L (row m i) 2 := seq_eval L i 2

private lemma seq_three {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) (i : ℕ) :
    seq L (3*i+3) = L (row m i + 1) 0 := by
  rw [show 3*i+3 = 3*(i+1) by omega, seq_zero, row_succ]

private lemma seq_count {V : Type*} {m : ℕ} (L : Fin (m+1) → Fin 3 → V) :
    ((Finset.range (3*(m+1))).filter (fun t => seq L t ≠ seq L (t+1))).card =
      (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
      (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
      (Finset.univ.filter (fun i => L i 2 ≠ L (i+1) 0)).card := by
  classical
  rw [card_filter_triples]
  simp only [show ∀ i : ℕ, 3*i+1+1 = 3*i+2 by omega,
    show ∀ i : ℕ, 3*i+2+1 = 3*i+3 by omega,
    seq_zero, seq_one, seq_two, seq_three]
  change
    ((Finset.range (m+1)).filter (fun i => L (row m i) 0 ≠ L (row m i) 1)).card +
    ((Finset.range (m+1)).filter (fun i => L (row m i) 1 ≠ L (row m i) 2)).card +
    ((Finset.range (m+1)).filter (fun i => L (row m i) 2 ≠ L (row m i+1) 0)).card = _
  exact congrArg₂ (fun a b : ℕ => a+b)
    (congrArg₂ (fun a b : ℕ => a+b)
      (card_filter_range_mod (m+1) (Nat.succ_pos m) (fun i => L i 0 ≠ L i 1))
      (card_filter_range_mod (m+1) (Nat.succ_pos m) (fun i => L i 1 ≠ L i 2)))
    (card_filter_range_mod (m+1) (Nat.succ_pos m) (fun i => L i 2 ≠ L (i+1) 0))

/-- A cyclic three-slot array compresses to a simple cycle when its moving departures
are distinct and at least three of its within-row and connecting steps move. -/
theorem exists_cycle_of_three_slots {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (L : Fin (m+1) → Fin 3 → V)
    (hstep : ∀ i r, L i r = threeSlotNext L i r ∨ G.Adj (L i r) (threeSlotNext L i r))
    (hinj : ∀ i r j s, L i r ≠ threeSlotNext L i r → L j s ≠ threeSlotNext L j s →
      L i r = L j s → i = j ∧ r = s)
    (hlen : 3 ≤ (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
        (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
        (Finset.univ.filter (fun i => L i 2 ≠ L (i+1) 0)).card) :
    ∃ p : G.Walk (L 0 0) (L 0 0), p.IsCycle ∧
      p.length = (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
        (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
        (Finset.univ.filter (fun i => L i 2 ≠ L (i+1) 0)).card := by
  classical
  have hclosed : seq L (3*(m+1)) = seq L 0 := by
    rw [seq_zero, show 0 = 3*0 by omega, seq_zero]
    congr 1
    apply Fin.ext
    simp [row]
  have hs : ∀ t, t < 3*(m+1) → seq L t = seq L (t+1) ∨ G.Adj (seq L t) (seq L (t+1)) := by
    intro t ht
    rw [seq_step]
    exact hstep (row m (t/3)) (slot t)
  have hi : ∀ t u, t < 3*(m+1) → u < 3*(m+1) →
      seq L t ≠ seq L (t+1) → seq L u ≠ seq L (u+1) → seq L t = seq L u → t = u := by
    intro t u ht hu htn hun heq
    rw [seq_step] at htn hun
    obtain ⟨hrow, hslot⟩ := hinj (row m (t/3)) (slot t) (row m (u/3)) (slot u) htn hun heq
    have htdiv : t/3 < m+1 := by omega
    have hudiv : u/3 < m+1 := by omega
    have hq : t/3 = u/3 := by
      have hv := congrArg Fin.val hrow
      simpa only [row, Nat.mod_eq_of_lt htdiv, Nat.mod_eq_of_lt hudiv] using hv
    have hr : t%3 = u%3 := congrArg Fin.val hslot
    omega
  obtain ⟨p, hp, hlength⟩ := exists_cycle_of_reflexive_sequence G (seq L) (3*(m+1))
    hclosed hs hi (by rw [seq_count]; exact hlen)
  have hstart : seq L 0 = L 0 0 := by
    simpa [row] using seq_zero L 0
  refine ⟨p.copy hstart hstart, ?_, ?_⟩
  · simpa using hp
  · simpa only [SimpleGraph.Walk.length_copy, seq_count] using hlength

end Erdos64.TriangleIncidence
