import Erdos.Erdos64.TriangleIncidenceCycleAssembly

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph

universe u w

variable {V : Type u} {W : Type w} {G : SimpleGraph V} {K : SimpleGraph W}
  {v : V} {root : W}

/-- One can choose distinct, globally port-fresh triangle spares at exactly as
many turns as there are used zero connectors plus root occurrences. -/
theorem Model.exists_cycle_spares (D : Model G K v root) [DecidableEq V] [DecidableEq W]
    {m : ℕ} (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1))) :
    ∃ T : Finset (Fin (m + 1)), ∃ s : Fin (m + 1) → V,
      (∀ i ∈ T, c i ≠ root) ∧
      (∀ i ∈ T, s i ∈ D.triangle (c i) ∧
        s i ≠ D.port (c i) (c (i - 1)) ∧ s i ≠ D.port (c i) (c (i + 1))) ∧
      (∀ i ∈ T, ∀ j,
        s i ≠ D.port (c j) (c (j - 1)) ∧ s i ≠ D.port (c j) (c (j + 1))) ∧
      Set.InjOn s T ∧
      T.card = (Finset.univ.filter (fun i =>
        D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))).card +
        (Finset.univ.filter (fun i => c i = root)).card := by
  classical
  let Z := Finset.univ.filter (fun i =>
    D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
  have hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨S, q, hScard, hroot, hcycle, hexcept, hgood⟩ :=
    D.exists_detour_nodes hm c hc hadj Z hz
  obtain ⟨s, hs, hfresh, hsinj⟩ :=
    D.exists_joint_spares c hc hadj Z hz S q hroot hexcept hgood
  let T := Finset.univ.filter (fun i => c i ∈ S)
  have hTmem (i : Fin (m + 1)) : i ∈ T ↔ c i ∈ S := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have himage : T.image c = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
      exact he ▸ (hTmem i).mp hi
    · intro hx
      obtain ⟨i, hi⟩ := hcycle x hx
      exact Finset.mem_image.mpr ⟨i, (hTmem i).mpr (hi.symm ▸ hx), hi⟩
  have hTcard : T.card = S.card :=
    (Finset.card_image_of_injective T hc).symm.trans (congrArg Finset.card himage)
  refine ⟨T, s, ?_, ?_, ?_, ?_, hTcard.trans hScard⟩
  · intro i hi he
    exact hroot (he ▸ (hTmem i).mp hi)
  · intro i hi
    exact hs i ((hTmem i).mp hi)
  · intro i hi j
    exact hfresh i ((hTmem i).mp hi) j
  · intro i hi j hj he
    exact hsinj i j ((hTmem i).mp hi) ((hTmem j).mp hj) he

private theorem cycle_index_of_walk {a : W} (p : K.Walk a a) (hp : p.IsCycle) :
    ∃ m : ℕ, p.length = m + 1 ∧ 3 ≤ m + 1 ∧
      ∃ c : Fin (m + 1) → W, Function.Injective c ∧
        ∀ i, K.Adj (c i) (c (i + 1)) := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  let m := p.length - 1
  have hm : p.length = m + 1 := by
    dsimp only [m]
    omega
  let c : Fin (m + 1) → W := fun i => p.getVert i.val
  have hc : Function.Injective c := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn' (show i.val ≤ p.length - 1 by omega)
      (show j.val ≤ p.length - 1 by omega)
    exact hij
  refine ⟨m, hm, hm ▸ hlen, c, hc, ?_⟩
  intro i
  have hi : i.val < p.length := by omega
  have hone : (1 : Fin (m + 1)).val = 1 := by
    change 1 % (m + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hn : i.val + 1 < p.length
  · have ha := p.adj_getVert_succ (i := i.val) hi
    change K.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa only [Fin.val_add, hone,
      Nat.mod_eq_of_lt (show i.val + 1 < m + 1 by omega)] using ha
  · have he : i.val + 1 = p.length := by omega
    have hz : (i + 1 : Fin (m + 1)).val = 0 := by
      simp only [Fin.val_add, hone, ← hm, he, Nat.mod_self]
    have ha := p.adj_getVert_succ hi
    change K.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa only [hz, p.getVert_zero, he, p.getVert_length] using ha

/-- Every incidence cycle of length at least four lifts to a simple cycle
of exactly twice its length in the original graph. -/
theorem Model.exists_doubled_cycle (D : Model G K v root) {x : W}
    (p : K.Walk x x) (hp : p.IsCycle) (hlen : 4 ≤ p.length) :
    ∃ a, ∃ q : G.Walk a a, q.IsCycle ∧ q.length = 2 * p.length := by
  classical
  obtain ⟨m, heq, hm, c, hc, hadj⟩ := cycle_index_of_walk p hp
  have hm4 : 4 ≤ m + 1 := by omega
  obtain ⟨T, s, hTroot, hsp, hfresh, hinj, hcard⟩ :=
    D.exists_cycle_spares (by omega) c hc hadj
  obtain ⟨a, q, hq, hq_length⟩ :=
    D.exists_doubled_cycle_of_spares hm c hc hadj T s hTroot hsp hfresh hinj hcard
  exact ⟨a, q, hq, by simpa only [heq] using hq_length⟩

end Erdos64.TriangleIncidence
