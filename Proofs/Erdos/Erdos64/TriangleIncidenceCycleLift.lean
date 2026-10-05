import Erdos.Erdos64.TriangleIncidenceModel
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph

universe u w

variable {V : Type u} {W : Type w} {G : SimpleGraph V} {K : SimpleGraph W}
  {v : V} {root : W}

/-- Every point of a triangle other than its used zero port is different from the
root point and belongs to no other nonroot triangle. -/
theorem Model.private_of_zero (D : Model G K v root) {x y : W} {a : V}
    (hx : x ≠ root) (hxy : K.Adj x y) (hz : D.port x y = D.port y x)
    (ha : a ∈ D.triangle x) (hne : a ≠ D.port x y) :
    a ≠ v ∧ ∀ t, t ≠ x → t ≠ root → a ∉ D.triangle t := by
  have hav : a ≠ v := by
    intro he
    have hvx : v ∈ D.triangle x := he ▸ ha
    obtain ⟨hrx, hrz⟩ := (D.root_mem_iff x hx).mp hvx
    have hyr : y = root := D.zero_unique x y root hx hxy hz hrx.symm hrz.symm
    have hpv : D.port x y = v := by
      rw [hyr, ← hrz, D.root_port x hrx]
    exact hne (he.trans hpv.symm)
  refine ⟨hav, ?_⟩
  intro t htx htr hat
  rcases D.overlap x t a hx htr htx.symm ha hat with h | h
  · have hyt : y = t := D.zero_unique x y t hx hxy hz h.1 h.2.1
    exact hne (by simpa only [hyt] using h.2.2.symm)
  · exact hav h.1

/-- Distinct incidences at a nonroot node have distinct original ports. -/
theorem Model.ports_ne (D : Model G K v root) {x y z : W}
    (hx : x ≠ root) (hxy : K.Adj x y) (hxz : K.Adj x z) (hyz : y ≠ z) :
    D.port x y ≠ D.port x z := by
  intro h
  exact hyz (D.port_injective x y z hx hxy hxz h)

/-- A triangle contains a third point distinct from any prescribed two points. -/
theorem Model.exists_third (D : Model G K v root) {x : W} (hx : x ≠ root)
    (a b : V) : ∃ d ∈ D.triangle x, d ≠ a ∧ d ≠ b := by
  classical
  let s := (D.triangle x).erase a
  have hs : 1 < s.card := by
    have hcard := (D.triangle_clique x hx).card_eq
    by_cases ha : a ∈ D.triangle x
    · have he := Finset.card_erase_add_one ha
      dsimp only [s]
      omega
    · simpa only [s, Finset.erase_eq_of_notMem ha, hcard] using (by decide : 1 < 3)
  obtain ⟨d, hd, hdb⟩ := Finset.exists_mem_ne hs b
  exact ⟨d, (Finset.mem_erase.mp hd).2, (Finset.mem_erase.mp hd).1, hdb⟩

/-- Distinct members of a nonroot triangle are joined by an original edge. -/
theorem Model.triangle_adj (D : Model G K v root) {x : W} {a b : V}
    (hx : x ≠ root) (ha : a ∈ D.triangle x) (hb : b ∈ D.triangle x)
    (hab : a ≠ b) : G.Adj a b :=
  (D.triangle_clique x hx).isClique ha hb hab

/-- Two distinct nonroot nodes have a common port only across the corresponding
zero connector, or at the root point through two root zero connectors. -/
theorem Model.port_collision (D : Model G K v root) {x y t s : W}
    (hx : x ≠ root) (ht : t ≠ root) (hxt : x ≠ t)
    (hxy : K.Adj x y) (hts : K.Adj t s)
    (he : D.port x y = D.port t s) :
    (y = t ∧ s = x ∧ D.port x y = D.port y x) ∨
    (y = root ∧ s = root ∧ D.port x y = v) := by
  have ha := D.port_mem x y hx hxy
  have hb : D.port x y ∈ D.triangle t := he.symm ▸ D.port_mem t s ht hts
  rcases D.overlap x t (D.port x y) hx ht hxt ha hb with h | h
  · have hyt : y = t := D.port_injective x y t hx hxy h.1 h.2.2.symm
    have hsx : s = x := D.port_injective t s x ht hts h.1.symm
      (he.symm.trans (h.2.2.symm.trans h.2.1))
    exact Or.inl ⟨hyt, hsx, by simpa only [hyt] using h.2.1⟩
  · have hyr : y = root := D.port_injective x y root hx hxy h.2.1.symm
      (h.1.trans ((D.root_port x h.2.1).symm.trans h.2.2.1))
    have hsr : s = root := D.port_injective t s root ht hts h.2.2.2.1.symm
      (he.symm.trans (h.1.trans
        ((D.root_port t h.2.2.2.1).symm.trans h.2.2.2.2)))
    exact Or.inr ⟨hyr, hsr, h.1⟩

/-- A third point at a turn incident to a zero connector is globally private. -/
theorem Model.turn_private (D : Model G K v root) {x y z : W} {a : V}
    (hx : x ≠ root) (hxy : K.Adj x y) (hxz : K.Adj x z)
    (hz : D.port x y = D.port y x ∨ D.port x z = D.port z x)
    (ha : a ∈ D.triangle x)
    (hay : a ≠ D.port x y) (haz : a ≠ D.port x z) :
    a ≠ v ∧ ∀ t, t ≠ x → t ≠ root → a ∉ D.triangle t := by
  rcases hz with hy | hz
  · exact D.private_of_zero hx hxy hy ha hay
  · exact D.private_of_zero hx hxz hz ha haz

/-- A nonroot triangle without a root zero incidence does not contain the root point. -/
theorem Model.point_ne_root_of_nonstar (D : Model G K v root) {x : W} {a : V}
    (hx : x ≠ root) (hn : ¬ (K.Adj root x ∧ D.port root x = D.port x root))
    (ha : a ∈ D.triangle x) : a ≠ v := by
  intro he
  exact hn ((D.root_mem_iff x hx).mp (he ▸ ha))

/-- A nonroot node cannot use two different zero incidences. -/
theorem Model.zero_not_other (D : Model G K v root) {x y z : W}
    (hx : x ≠ root) (hxy : K.Adj x y) (hxz : K.Adj x z) (hyz : y ≠ z)
    (hz : D.port x y = D.port y x) : D.port x z ≠ D.port z x := by
  intro hz'
  exact hyz (D.zero_unique x y z hx hxy hz hxz hz')

/-- A turn's third point cannot equal another turn's port, provided the turns
reciprocate their used incidences. The only possible exception is the root point. -/
theorem Model.third_ne_other_port (D : Model G K v root) {x y z t s : W} {a : V}
    (hx : x ≠ root) (ht : t ≠ root) (hxt : x ≠ t)
    (hts : K.Adj t s)
    (ha : a ∈ D.triangle x) (hay : a ≠ D.port x y) (haz : a ≠ D.port x z)
    (hav : a ≠ v) (hrecip : s = x → t = y ∨ t = z) :
    a ≠ D.port t s := by
  intro he
  have hat : a ∈ D.triangle t := he.symm ▸ D.port_mem t s ht hts
  rcases D.overlap x t a hx ht hxt ha hat with h | h
  · have hsx : s = x := D.port_injective t s x ht hts h.1.symm
      (he.symm.trans (h.2.2.symm.trans h.2.1))
    rcases hrecip hsx with hty | htz
    · exact hay (by simpa only [hty] using h.2.2.symm)
    · exact haz (by simpa only [htz] using h.2.2.symm)
  · exact hav h.1

/-- Choosing a nonroot endpoint of each used zero edge of a simple cyclic
sequence chooses distinct nodes. This includes both zero edges at the root. -/
theorem Model.zero_endpoint_injOn (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
    (f : Fin (m + 1) → W)
    (hf : ∀ i ∈ Z, f i = c i ∨ f i = c (i + 1))
    (hn : ∀ i ∈ Z, f i ≠ root) : Set.InjOn f Z := by
  intro i hi j hj he
  rcases hf i hi with hfi | hfi <;> rcases hf j hj with hfj | hfj
  · exact hc (hfi.symm.trans (he.trans hfj))
  · have hec : c i = c (j + 1) := hfi.symm.trans (he.trans hfj)
    have hother : c (i + 1) = c j := D.zero_unique (c i) (c (i + 1)) (c j)
      (hfi ▸ hn i hi) (hadj i) (hz i hi) (hec.symm ▸ (hadj j).symm)
      (by simpa only [hec] using (hz j hj).symm)
    have hij : i = j + 1 := hc hec
    have hnext : i + 1 = j := hc hother
    exact False.elim (UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm j
      (by simpa only [hij] using hnext))
  · have hec : c j = c (i + 1) := hfj.symm.trans (he.symm.trans hfi)
    have hother : c (j + 1) = c i := D.zero_unique (c j) (c (j + 1)) (c i)
      (hfj ▸ hn j hj) (hadj j) (hz j hj) (hec.symm ▸ (hadj i).symm)
      (by simpa only [hec] using (hz i hi).symm)
    have hji : j = i + 1 := hc hec
    have hnext : j + 1 = i := hc hother
    exact False.elim (UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm i
      (by simpa only [hji] using hnext))
  · exact add_right_cancel (hc (hfi.symm.trans (he.trans hfj)))

/-- There is a set of exactly one distinct nonroot endpoint for every used zero
edge; every selected node is incident to a used zero connector. -/
theorem Model.exists_zero_selection (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i)) :
    ∃ S : Finset W, S.card = Z.card ∧ root ∉ S ∧
      ∀ x ∈ S, ∃ i ∈ Z, (x = c i ∨ x = c (i + 1)) := by
  classical
  let f : Fin (m + 1) → W := fun i => if c (i + 1) = root then c i else c (i + 1)
  have hf : ∀ i ∈ Z, f i = c i ∨ f i = c (i + 1) := by
    intro i hi
    dsimp only [f]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hn : ∀ i ∈ Z, f i ≠ root := by
    intro i hi
    dsimp only [f]
    split_ifs with h
    · exact fun he => (hadj i).ne (he.trans h.symm)
    · exact h
  refine ⟨Z.image f, Finset.card_image_of_injOn (D.zero_endpoint_injOn hm c hc hadj Z hz f hf hn), ?_, ?_⟩
  · intro hr
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hr
    exact hn i hi he
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi, hf i hi⟩

/-- Two used zero edges with a common nonroot endpoint have the same cyclic
index, regardless of the endpoint orientation. -/
theorem Model.zero_edges_eq_of_common (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)} {q : W} (hq : q ≠ root)
    (hi : q = c i ∨ q = c (i + 1)) (hj : q = c j ∨ q = c (j + 1))
    (hzi : D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
    (hzj : D.port (c j) (c (j + 1)) = D.port (c (j + 1)) (c j)) : i = j := by
  let Z : Finset (Fin (m + 1)) := {i, j}
  have hz : ∀ t ∈ Z, D.port (c t) (c (t + 1)) = D.port (c (t + 1)) (c t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hzi
    · exact Finset.mem_singleton.mp ht ▸ hzj
  have hf : ∀ t ∈ Z, (fun _ : Fin (m + 1) => q) t = c t ∨ q = c (t + 1) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hi
    · exact Finset.mem_singleton.mp ht ▸ hj
  exact D.zero_endpoint_injOn hm c hc hadj Z hz (fun _ => q) hf
    (fun _ _ => hq) (by simp [Z]) (by simp [Z]) rfl

/-- The root-star obstruction cannot cover every nonroot node of a simple cycle
through the root: two successive nodes after the root cannot both be star leaves. -/
theorem Model.exists_nonstar_on_root_cycle (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (r : Fin (m + 1)) (hr : c r = root) :
    ∃ i, c i ≠ root ∧ ¬ (K.Adj root (c i) ∧ D.port root (c i) = D.port (c i) root) := by
  have h1 : c (r + 1) ≠ root := by
    intro he
    exact UniqueCubicClawCenter.CycleIndex.succ_ne m (by omega) r (hc (he.trans hr.symm))
  have h2 : c (r + 1 + 1) ≠ root := by
    intro he
    exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm r (hc (he.trans hr.symm))
  by_cases hs : K.Adj root (c (r + 1)) ∧ D.port root (c (r + 1)) = D.port (c (r + 1)) root
  · refine ⟨r + 1 + 1, h2, ?_⟩
    intro ht
    exact D.root_leaves_nonadjacent _ _ hs.1 hs.2 ht.1 ht.2 (hadj (r + 1))
  · exact ⟨r + 1, h1, hs⟩

/-- The unchosen endpoint of a used zero edge is absent from the set of chosen
endpoints, even when the other endpoint is the root. -/
theorem Model.zero_selection_other_not_mem (D : Model G K v root) [DecidableEq W] {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
    (f : Fin (m + 1) → W)
    (hf : ∀ i ∈ Z, f i = c i ∨ f i = c (i + 1))
    (hn : ∀ i ∈ Z, f i ≠ root)
    {i : Fin (m + 1)} (hi : i ∈ Z) {q : W}
    (hqi : q = c i ∨ q = c (i + 1)) (hqf : q ≠ f i) : q ∉ Z.image f := by
  classical
  intro hq
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hq
  have hqn : q ≠ root := he ▸ hn j hj
  have hqj : q = c j ∨ q = c (j + 1) := by
    simpa only [he] using hf j hj
  have hij : i = j := D.zero_edges_eq_of_common hm c hc hadj hqn hqi hqj (hz i hi) (hz j hj)
  exact hqf (he.symm.trans (congrArg f hij.symm))

/-- When the root lies on the cycle, one can select one nonroot endpoint per
used zero edge and one additional distinct node. The additional node is either
incident to a used zero edge or is not a root zero-star leaf. -/
theorem Model.exists_root_detour_selection (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (r : Fin (m + 1)) (hr : c r = root)
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i)) :
    ∃ A : Finset W, ∃ q : W,
      A.card = Z.card ∧ root ∉ A ∧ q ∉ A ∧ q ≠ root ∧
      (∀ x ∈ A, ∃ i ∈ Z, x = c i ∨ x = c (i + 1)) ∧
      ((∃ i ∈ Z, q = c i ∨ q = c (i + 1)) ∨
        (∃ i, q = c i ∧ ¬ (K.Adj root q ∧ D.port root q = D.port q root))) := by
  classical
  let f : Fin (m + 1) → W := fun i => if c (i + 1) = root then c i else c (i + 1)
  have hf : ∀ i ∈ Z, f i = c i ∨ f i = c (i + 1) := by
    intro i hi
    dsimp only [f]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hn : ∀ i ∈ Z, f i ≠ root := by
    intro i hi
    dsimp only [f]
    split_ifs with h
    · exact fun he => (hadj i).ne (he.trans h.symm)
    · exact h
  let A := Z.image f
  have hcard : A.card = Z.card :=
    Finset.card_image_of_injOn (D.zero_endpoint_injOn hm c hc hadj Z hz f hf hn)
  have hroot : root ∉ A := by
    intro hroot
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hroot
    exact hn i hi he
  have hselected : ∀ x ∈ A, ∃ i ∈ Z, x = c i ∨ x = c (i + 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi, hf i hi⟩
  by_cases hmatching : ∃ i ∈ Z, c i ≠ root ∧ c (i + 1) ≠ root
  · obtain ⟨i, hi, hin, hnextn⟩ := hmatching
    rcases hf i hi with hfi | hfi
    · have hother : c (i + 1) ≠ f i := hfi.symm ▸ (hadj i).ne.symm
      have hfresh := D.zero_selection_other_not_mem hm c hc hadj Z hz f hf hn hi
        (Or.inr rfl) hother
      exact ⟨A, c (i + 1), hcard, hroot, hfresh, hnextn, hselected,
        Or.inl ⟨i, hi, Or.inr rfl⟩⟩
    · have hother : c i ≠ f i := hfi.symm ▸ (hadj i).ne
      have hfresh := D.zero_selection_other_not_mem hm c hc hadj Z hz f hf hn hi
        (Or.inl rfl) hother
      exact ⟨A, c i, hcard, hroot, hfresh, hin, hselected,
        Or.inl ⟨i, hi, Or.inl rfl⟩⟩
  · obtain ⟨j, hjn, hjstar⟩ := D.exists_nonstar_on_root_cycle hm c hc hadj r hr
    have hfresh : c j ∉ A := by
      intro hj
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
      rcases hf i hi with hfi | hfi
      · have hij : c i = c j := hfi.symm.trans he
        have hnext : c (i + 1) = root := by
          by_contra hnext
          exact hmatching ⟨i, hi, hij.symm ▸ hjn, hnext⟩
        exact hjstar ⟨hij ▸ hnext ▸ (hadj i).symm,
          by simpa only [hij, hnext] using (hz i hi).symm⟩
      · have hij : c (i + 1) = c j := hfi.symm.trans he
        have hstart : c i = root := by
          by_contra hstart
          exact hmatching ⟨i, hi, hstart, hij.symm ▸ hjn⟩
        exact hjstar ⟨hij ▸ hstart ▸ hadj i,
          by simpa only [hij, hstart] using hz i hi⟩
    exact ⟨A, c j, hcard, hroot, hfresh, hjn, hselected, Or.inr ⟨j, rfl, hjstar⟩⟩

/-- At a nonroot node, a port equal to the distinguished point is necessarily
its zero incidence to the root. -/
theorem Model.port_eq_root_point (D : Model G K v root) {x y : W}
    (hx : x ≠ root) (hxy : K.Adj x y) (hp : D.port x y = v) :
    y = root ∧ D.port x y = D.port y x := by
  have hv : v ∈ D.triangle x :=
    Eq.mp (congrArg (fun a : V => a ∈ D.triangle x) hp) (D.port_mem x y hx hxy)
  obtain ⟨hrx, hrz⟩ := (D.root_mem_iff x hx).mp hv
  have hyr : y = root := D.port_injective x y root hx hxy hrx.symm
    (hp.trans ((D.root_port x hrx).symm.trans hrz))
  exact ⟨hyr, by simpa only [hyr] using hrz.symm⟩

/-- A nonroot endpoint of an ordinary connector cannot be the distinguished point. -/
theorem Model.ordinary_port_ne_root (D : Model G K v root) {x y : W}
    (hx : x ≠ root) (hxy : K.Adj x y) (hn : D.port x y ≠ D.port y x) :
    D.port x y ≠ v := by
  intro hp
  exact hn (D.port_eq_root_point hx hxy hp).2

/-- Incoming cycle ports at distinct nonroot nodes are distinct, including root
zero-star incidences. -/
theorem Model.incoming_injective (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)} (hi : c i ≠ root) (hj : c j ≠ root)
    (he : D.port (c i) (c (i - 1)) = D.port (c j) (c (j - 1))) : i = j := by
  by_cases hij : i = j
  · exact hij
  have hprev (t : Fin (m + 1)) : K.Adj (c t) (c (t - 1)) := by
    simpa only [sub_add_cancel] using (hadj (t - 1)).symm
  rcases D.port_collision hi hj (fun h => hij (hc h)) (hprev i) (hprev j) he with h | h
  · have hp : i - 1 = j := hc h.1
    have hq : j - 1 = i := hc h.2.1
    have hp' : i = j + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hp
    have hq' : j = i + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hq
    exact False.elim (UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm i
      (by rw [← hq', ← hp']))
  · have hp : i - 1 = j - 1 := hc (h.1.trans h.2.1.symm)
    simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hp

/-- Outgoing ports that actually depart across ordinary connectors are distinct. -/
theorem Model.outgoing_injective (D : Model G K v root) {m : ℕ}
    (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)}
    (hi : D.port (c i) (c (i + 1)) ≠ D.port (c (i + 1)) (c i))
    (hj : D.port (c j) (c (j + 1)) ≠ D.port (c (j + 1)) (c j))
    (he : D.port (c i) (c (i + 1)) = D.port (c j) (c (j + 1))) : i = j := by
  by_cases hij : i = j
  · exact hij
  by_cases hir : c i = root
  · by_cases hjr : c j = root
    · exact hc (hir.trans hjr.symm)
    · have hp : D.port (c i) (c (i + 1)) = v := by
        simpa only [hir] using D.root_port (c (i + 1)) (hir ▸ hadj i)
      exact False.elim (D.ordinary_port_ne_root hjr (hadj j) hj (he.symm.trans hp))
  by_cases hjr : c j = root
  · have hp : D.port (c j) (c (j + 1)) = v := by
      simpa only [hjr] using D.root_port (c (j + 1)) (hjr ▸ hadj j)
    exact False.elim (D.ordinary_port_ne_root hir (hadj i) hi (he.trans hp))
  rcases D.port_collision hir hjr (fun h => hij (hc h)) (hadj i) (hadj j) he with h | h
  · exact False.elim (hi h.2.2)
  · exact False.elim (D.ordinary_port_ne_root hir (hadj i) hi h.2.2)

/-- An incoming turn port never coincides with a port that departs along an
ordinary connector, including an ordinary departure from the root. -/
theorem Model.incoming_ne_outgoing (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)} (hi : c i ≠ root)
    (hj : D.port (c j) (c (j + 1)) ≠ D.port (c (j + 1)) (c j)) :
    D.port (c i) (c (i - 1)) ≠ D.port (c j) (c (j + 1)) := by
  have hprev (t : Fin (m + 1)) : K.Adj (c t) (c (t - 1)) := by
    simpa only [sub_add_cancel] using (hadj (t - 1)).symm
  intro he
  by_cases hjr : c j = root
  · have hp : D.port (c j) (c (j + 1)) = v := by
      simpa only [hjr] using D.root_port (c (j + 1)) (hjr ▸ hadj j)
    obtain ⟨hpred, hz⟩ := D.port_eq_root_point hi (hprev i) (he.trans hp)
    have hij : i - 1 = j := hc (hpred.trans hjr.symm)
    have hij' : i = j + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hij
    exact hj (by simpa only [hij, hij', add_sub_cancel_right] using hz.symm)
  by_cases hij : i = j
  · subst j
    have hports : c (i - 1) ≠ c (i + 1) := by
      intro h
      have hindex := hc h
      have hindex' : i = i + 1 + 1 := by
        simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hindex
      exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm i hindex'.symm
    exact D.ports_ne hi (hprev i) (hadj i) hports he
  rcases D.port_collision hi hjr (fun h => hij (hc h)) (hprev i) (hadj j) he with h | h
  · exact hj (by simpa only [h.1, h.2.1] using h.2.2.symm)
  · exact D.ordinary_port_ne_root hjr (hadj j) hj (he.symm.trans h.2.2)

/-- The chosen detour nodes number the used zero connectors plus the presence
of the root. Every chosen node but at most one has a used zero incidence. -/
theorem Model.exists_detour_nodes (D : Model G K v root) [DecidableEq W] {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i)) :
    ∃ S : Finset W, ∃ q : W,
      S.card = Z.card + (Finset.univ.filter (fun i => c i = root)).card ∧
      root ∉ S ∧ (∀ x ∈ S, ∃ i, c i = x) ∧
      (∀ x ∈ S, x ≠ q → ∃ i ∈ Z, x = c i ∨ x = c (i + 1)) ∧
      (∀ x ∈ S, (∃ i ∈ Z, x = c i ∨ x = c (i + 1)) ∨
        ¬ (K.Adj root x ∧ D.port root x = D.port x root)) := by
  classical
  by_cases hroot : ∃ r, c r = root
  · obtain ⟨r, hr⟩ := hroot
    have hrcard : (Finset.univ.filter (fun i => c i = root)).card = 1 := by
      have hrset : Finset.univ.filter (fun i => c i = root) = {r} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun he => hc (he.trans hr.symm), fun he => he ▸ hr⟩
      rw [hrset, Finset.card_singleton]
    obtain ⟨A, q, hcard, hrA, hqA, hqr, hA, hq⟩ :=
      D.exists_root_detour_selection hm c hc hadj r hr Z hz
    refine ⟨insert q A, q, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hqA, hcard, hrcard]
    · simpa only [Finset.mem_insert, not_or] using And.intro hqr.symm hrA
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxe | hxA
      · subst x
        rcases hq with ⟨i, hi, hqi | hqi⟩ | ⟨i, hqi, hstar⟩
        · exact ⟨i, hqi.symm⟩
        · exact ⟨i + 1, hqi.symm⟩
        · exact ⟨i, hqi.symm⟩
      · obtain ⟨i, hi, hxi | hxi⟩ := hA x hxA
        · exact ⟨i, hxi.symm⟩
        · exact ⟨i + 1, hxi.symm⟩
    · intro x hx hxq
      exact hA x ((Finset.mem_insert.mp hx).resolve_left hxq)
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxe | hxA
      · subst x
        rcases hq with hq | ⟨i, hqi, hstar⟩
        · exact Or.inl hq
        · exact Or.inr hstar
      · exact Or.inl (hA x hxA)
  · have hrset : Finset.univ.filter (fun i => c i = root) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun he => hroot ⟨i, he⟩
    obtain ⟨S, hcard, hrS, hS⟩ := D.exists_zero_selection hm c hc hadj Z hz
    refine ⟨S, root, ?_, hrS, ?_, ?_, ?_⟩
    · simp only [hrset, Finset.card_empty, Nat.add_zero, hcard]
    · intro x hx
      obtain ⟨i, hi, hxi | hxi⟩ := hS x hx
      · exact ⟨i, hxi.symm⟩
      · exact ⟨i + 1, hxi.symm⟩
    · intro x hx hxroot
      exact hS x hx
    · intro x hx
      exact Or.inl (hS x hx)

/-- The two cycle ports of a nonroot turn are distinct. -/
theorem Model.cycle_ports_ne (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1))) {i : Fin (m + 1)} (hi : c i ≠ root) :
    D.port (c i) (c (i - 1)) ≠ D.port (c i) (c (i + 1)) := by
  have hprev : K.Adj (c i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using (hadj (i - 1)).symm
  apply D.ports_ne hi hprev (hadj i)
  intro he
  have hindex := hc he
  have hindex' : i = i + 1 + 1 := by
    simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hindex
  exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm i hindex'.symm

/-- A spare point different from the root point is fresh from all cycle ports,
not merely the two ports at its own turn. -/
theorem Model.cycle_spare_ne_ports (D : Model G K v root) {m : ℕ}
    (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i : Fin (m + 1)} {a : V} (hi : c i ≠ root)
    (ha : a ∈ D.triangle (c i))
    (hap : a ≠ D.port (c i) (c (i - 1)))
    (han : a ≠ D.port (c i) (c (i + 1))) (hav : a ≠ v) (j : Fin (m + 1)) :
    a ≠ D.port (c j) (c (j - 1)) ∧ a ≠ D.port (c j) (c (j + 1)) := by
  have hprev (t : Fin (m + 1)) : K.Adj (c t) (c (t - 1)) := by
    simpa only [sub_add_cancel] using (hadj (t - 1)).symm
  by_cases hjr : c j = root
  · constructor
    · simpa only [hjr, D.root_port _ (hjr ▸ hprev j)] using hav
    · simpa only [hjr, D.root_port _ (hjr ▸ hadj j)] using hav
  by_cases hij : i = j
  · subst j
    exact ⟨hap, han⟩
  have hnodes : c i ≠ c j := fun he => hij (hc he)
  constructor
  · apply D.third_ne_other_port hi hjr hnodes (hprev j) ha hap han hav
    intro he
    have hindex : j - 1 = i := hc he
    have hindex' : j = i + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) hindex
    exact Or.inr (congrArg c hindex')
  · apply D.third_ne_other_port hi hjr hnodes (hadj j) ha hap han hav
    intro he
    have hindex : j + 1 = i := hc he
    have hindex' : j = i - 1 := by
      simpa only [add_sub_cancel_right] using congrArg (fun t : Fin (m + 1) => t - 1) hindex
    exact Or.inl (congrArg c hindex')

/-- A spare at either nonroot endpoint of a used zero connector is globally
private among nonroot triangles. -/
theorem Model.cycle_spare_private (D : Model G K v root) {m : ℕ}
    (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    {i r : Fin (m + 1)} {a : V} (hi : c i ≠ root)
    (hz : D.port (c r) (c (r + 1)) = D.port (c (r + 1)) (c r))
    (hend : c i = c r ∨ c i = c (r + 1))
    (ha : a ∈ D.triangle (c i))
    (hap : a ≠ D.port (c i) (c (i - 1)))
    (han : a ≠ D.port (c i) (c (i + 1))) :
    a ≠ v ∧ ∀ t, t ≠ c i → t ≠ root → a ∉ D.triangle t := by
  rcases hend with he | he
  · have hir : i = r := hc he
    subst r
    exact D.private_of_zero hi (hadj i) hz ha han
  · have hir : i = r + 1 := hc he
    have hzero : D.port (c i) (c r) = D.port (c r) (c i) := by
      simpa only [hir] using hz.symm
    have hnot : a ≠ D.port (c i) (c r) := by
      simpa only [hir, add_sub_cancel_right] using hap
    exact D.private_of_zero hi (he.symm ▸ (hadj r).symm) hzero ha hnot

/-- Spares at selected turns can be chosen simultaneously, fresh from every
used cycle port and pairwise distinct, with only one possibly nonprivate turn. -/
theorem Model.exists_joint_spares (D : Model G K v root) {m : ℕ}
    (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1)))
    (Z : Finset (Fin (m + 1)))
    (hz : ∀ i ∈ Z, D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
    (S : Finset W) (q : W) (hroot : root ∉ S)
    (hexcept : ∀ x ∈ S, x ≠ q → ∃ i ∈ Z, x = c i ∨ x = c (i + 1))
    (hgood : ∀ x ∈ S, (∃ i ∈ Z, x = c i ∨ x = c (i + 1)) ∨
      ¬ (K.Adj root x ∧ D.port root x = D.port x root)) :
    ∃ s : Fin (m + 1) → V,
      (∀ i, c i ∈ S → s i ∈ D.triangle (c i) ∧
        s i ≠ D.port (c i) (c (i - 1)) ∧ s i ≠ D.port (c i) (c (i + 1))) ∧
      (∀ i, c i ∈ S → ∀ j,
        s i ≠ D.port (c j) (c (j - 1)) ∧ s i ≠ D.port (c j) (c (j + 1))) ∧
      (∀ i j, c i ∈ S → c j ∈ S → s i = s j → i = j) := by
  classical
  have hex : ∀ i : Fin (m + 1), ∃ a : V, c i ≠ root →
      a ∈ D.triangle (c i) ∧ a ≠ D.port (c i) (c (i - 1)) ∧
        a ≠ D.port (c i) (c (i + 1)) := by
    intro i
    by_cases hi : c i = root
    · exact ⟨v, fun hn => False.elim (hn hi)⟩
    · obtain ⟨a, ha, hap, han⟩ := D.exists_third hi
        (D.port (c i) (c (i - 1))) (D.port (c i) (c (i + 1)))
      exact ⟨a, fun _ => ⟨ha, hap, han⟩⟩
  choose s hs using hex
  have hnonroot {i : Fin (m + 1)} (hi : c i ∈ S) : c i ≠ root := by
    intro he
    exact hroot (he ▸ hi)
  have hspec {i : Fin (m + 1)} (hi : c i ∈ S) := hs i (hnonroot hi)
  have hprivate {i : Fin (m + 1)} (hi : c i ∈ S) (hiq : c i ≠ q) :
      s i ≠ v ∧ ∀ t, t ≠ c i → t ≠ root → s i ∉ D.triangle t := by
    obtain ⟨r, hr, hend⟩ := hexcept (c i) hi hiq
    exact D.cycle_spare_private c hc hadj (hnonroot hi) (hz r hr) hend
      (hspec hi).1 (hspec hi).2.1 (hspec hi).2.2
  have hnev {i : Fin (m + 1)} (hi : c i ∈ S) : s i ≠ v := by
    rcases hgood (c i) hi with ⟨r, hr, hend⟩ | hstar
    · exact (D.cycle_spare_private c hc hadj (hnonroot hi) (hz r hr) hend
        (hspec hi).1 (hspec hi).2.1 (hspec hi).2.2).1
    · exact D.point_ne_root_of_nonstar (hnonroot hi) hstar (hspec hi).1
  refine ⟨s, fun i hi => hspec hi, ?_, ?_⟩
  · intro i hi j
    exact D.cycle_spare_ne_ports c hc hadj (hnonroot hi)
      (hspec hi).1 (hspec hi).2.1 (hspec hi).2.2 (hnev hi) j
  · intro i j hi hj he
    by_contra hij
    have hnodes : c i ≠ c j := fun hcij => hij (hc hcij)
    by_cases hiq : c i = q
    · have hjq : c j ≠ q := fun heq => hnodes (hiq.trans heq.symm)
      exact (hprivate hj hjq).2 (c i) hnodes (hnonroot hi)
        (he ▸ (hspec hi).1)
    · exact (hprivate hi hiq).2 (c j) hnodes.symm (hnonroot hj)
        (he.symm ▸ (hspec hj).1)

end Erdos64.TriangleIncidence
