import Erdos.Erdos64.CubicFewClawCentersQuotient
import Erdos.Erdos64.TriangleIncidenceThreeSlots
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex

/-!
# Original-hypothesis cubic at-most-two-claw-center exclusion

The auxiliary module constructs the finite canonical triangle/singleton quotient,
proves it cubic and strictly smaller, and obtains a quotient dyadic cycle by minimality.
Here an arbitrary ordinary quotient cycle of length at least four is lifted to a
literal original-graph ordinary cycle of twice its length. Singleton turns are
compensated by long turns at distinct triangles. The three-slot walk assembler skips
repeated ports, preserving vertex injectivity and the exact departure count.

`hasPowerOfTwoCycle_original` and `false_of_at_most_two_claw_centers` use only the
original graph hypotheses. No quotient, representation, or lift certificate is
supplied by the caller. The at-most-two induced-claw-center condition is explicit;
this does not prove the unrestricted Erdős–Gyárfás conjecture or reduce arbitrary
counterexamples to the cubic case.
-/

set_option autoImplicit false

namespace Erdos64.CubicFewClawCenters

open SimpleGraph

universe u

noncomputable local instance (V : Type*) : DecidableEq V := Classical.decEq V
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem row_departure_injective {A : Type*} (a b d : A)
    (D : Fin 3 → Prop) (hshape : b = a ∨ (a ≠ b ∧ a ≠ d ∧ b ≠ d))
    (h0 : D 0 → a ≠ b) (h1 : D 1 → b ≠ d) :
    ∀ r s : Fin 3, D r → D s →
      (if r = 0 then a else if r = 1 then b else d) =
        (if s = 0 then a else if s = 1 then b else d) → r = s := by
  intro r s hr hs heq
  rcases hshape with hab | ⟨hab, had, hbd⟩
  · subst b
    fin_cases r <;> fin_cases s <;> simp_all
  · fin_cases r <;> fin_cases s <;> simp_all

private theorem exists_third_mem {V : Type u} {s : Finset V} (hs : s.card = 3)
    (a b : V) : ∃ d ∈ s, d ≠ a ∧ d ≠ b := by
  classical
  let t := s.erase a
  have ht : 1 < t.card := by
    by_cases ha : a ∈ s
    · have hc := Finset.card_erase_add_one ha
      dsimp only [t]
      omega
    · simpa only [t, Finset.erase_eq_of_notMem ha, hs] using (by decide : 1 < 3)
  obtain ⟨d, hd, hdb⟩ := Finset.exists_mem_ne ht b
  exact ⟨d, (Finset.mem_erase.mp hd).2, (Finset.mem_erase.mp hd).1, hdb⟩

/-- An injective block sequence contains at most as many singleton turns as the original
number of claw centers. This bound does not assume any supplied lift. -/
theorem singleton_turn_count_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    {m : ℕ} (c : Fin (m + 1) → Block G) (hc : Function.Injective c) :
    (Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)).card ≤
      Nat.card {x : V // UniqueCubicClawCenter.Claw G x} := by
  classical
  let R := Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)
  have hex (i : R) : ∃ x : V, UniqueCubicClawCenter.Claw G x ∧ (c i.val).val = {x} := by
    have hn := (Finset.mem_filter.mp i.property).2
    exact (c i.val).property.resolve_left hn
  let f : R → {x : V // UniqueCubicClawCenter.Claw G x} := fun i =>
    ⟨Classical.choose (hex i), (Classical.choose_spec (hex i)).1⟩
  have hf (i : R) : (c i.val).val = { (f i).val } :=
    (Classical.choose_spec (hex i)).2
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply hc
    apply Subtype.ext
    rw [hf i, hf j, he]
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- Actual quotient-cycle edges give original entry and exit ports. The ports differ
exactly at triangle turns; at singleton turns the same original vertex is repeated. -/
theorem exists_indexed_ports {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {m : ℕ} (hm : 3 ≤ m + 1) (c : Fin (m + 1) → Block G)
    (hc : Function.Injective c) (hadj : ∀ i, (quotient G).Adj (c i) (c (i + 1))) :
    ∃ I O : Fin (m + 1) → V,
      (∀ i, I i ∈ (c i).val) ∧ (∀ i, O i ∈ (c i).val) ∧
      (∀ i, G.Adj (O i) (I (i + 1))) ∧
      (∀ i, I i ≠ O i ↔ G.IsNClique 3 (c i).val) := by
  classical
  choose O hO B hB hE using fun i => (hadj i).2
  let I : Fin (m + 1) → V := fun i => B (i - 1)
  have hI (i : Fin (m + 1)) : I i ∈ (c i).val := by
    simpa only [I, sub_add_cancel] using hB (i - 1)
  have hconn (i : Fin (m + 1)) : G.Adj (O i) (I (i + 1)) := by
    simpa only [I, add_sub_cancel_right] using hE i
  refine ⟨I, O, hI, hO, hconn, ?_⟩
  intro i
  constructor
  · intro hne
    rcases (c i).property with ht | ⟨x, _, he⟩
    · exact ht
    · have hIx : I i = x := by simpa [he] using hI i
      have hOx : O i = x := by simpa [he] using hO i
      exact False.elim (hne (hIx.trans hOx.symm))
  · intro ht he
    have hprev : c i ≠ c (i - 1) := by
      simpa only [sub_add_cancel] using (hadj (i - 1)).1.symm
    have hout : O (i - 1) ∉ (c i).val := fun h =>
      Finset.disjoint_left.mp (blocks_disjoint G hG hCubic hprev) h (hO (i - 1))
    have hbout : B i ∉ (c i).val := fun h =>
      Finset.disjoint_left.mp (blocks_disjoint G hG hCubic (hadj i).1) h (hB i)
    have hentry : G.Adj (I i) (O (i - 1)) := (hE (i - 1)).symm
    have hexit : G.Adj (I i) (B i) := by rw [he]; exact hE i
    have hports := triangle_external_unique G hCubic ht (hI i) hentry hout hexit hbout
    have htarget : c (i - 1) = c (i + 1) :=
      blocks_eq_of_mem G hG hCubic (hO (i - 1)) (hports.symm ▸ hB i)
    have hidx := hc htarget
    exact UniqueCubicClawCenter.CycleIndex.succ_succ_ne m hm (i - 1)
      (by simpa only [sub_add_cancel] using hidx.symm)

/-- There are enough visited triangles to select one extra internal edge for each
visited singleton. Selected triangles have a third original vertex distinct from both ports. -/
theorem exists_selected_turns {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2)
    {m : ℕ} (hm : 4 ≤ m + 1) (c : Fin (m + 1) → Block G)
    (hc : Function.Injective c) (I O : Fin (m + 1) → V) :
    ∃ T : Finset (Fin (m + 1)), ∃ spare : Fin (m + 1) → V,
      (∀ i ∈ T, G.IsNClique 3 (c i).val) ∧
      (∀ i ∈ T, spare i ∈ (c i).val ∧ spare i ≠ I i ∧ spare i ≠ O i) ∧
      T.card = (Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)).card := by
  classical
  let A := Finset.univ.filter (fun i => G.IsNClique 3 (c i).val)
  let R := Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)
  have hR : R.card ≤ 2 := (singleton_turn_count_le G c hc).trans hFew
  have hsum : A.card + R.card = m + 1 := by
    simpa only [A, R, Finset.card_univ, Fintype.card_fin] using
      (Finset.univ : Finset (Fin (m + 1))).card_filter_add_card_filter_not
        (fun i => G.IsNClique 3 (c i).val)
  obtain ⟨T, hTA, hcard⟩ := Finset.exists_subset_card_eq (show R.card ≤ A.card by omega)
  have hT (i : Fin (m + 1)) (hi : i ∈ T) : G.IsNClique 3 (c i).val :=
    (Finset.mem_filter.mp (hTA hi)).2
  let spare : Fin (m + 1) → V := fun i => if hi : i ∈ T then
    Classical.choose (exists_third_mem (hT i hi).card_eq (I i) (O i)) else I i
  have hsp (i : Fin (m + 1)) (hi : i ∈ T) :
      spare i ∈ (c i).val ∧ spare i ≠ I i ∧ spare i ≠ O i := by
    dsimp only [spare]
    rw [dif_pos hi]
    exact Classical.choose_spec (exists_third_mem (hT i hi).card_eq (I i) (O i))
  exact ⟨T, spare, hT, hsp, hcard⟩

/-- Every injectively indexed actual quotient cycle with at least four vertices lifts to
an ordinary original-graph cycle of exactly twice its length. Singleton turns are
compensated by long turns in distinct actual triangles. -/
theorem exists_doubled_indexed_cycle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2)
    {m : ℕ} (hm : 4 ≤ m + 1) (c : Fin (m + 1) → Block G)
    (hc : Function.Injective c) (hadj : ∀ i, (quotient G).Adj (c i) (c (i + 1))) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  obtain ⟨I, O, hI, hO, hconn, hturn⟩ :=
    exists_indexed_ports G hG hCubic (by omega) c hc hadj
  obtain ⟨T, spare, hT, hsp, hcard⟩ := exists_selected_turns G hFew hm c hc I O
  let M : Fin (m + 1) → V := fun i => if i ∈ T then spare i else I i
  let L : Fin (m + 1) → Fin 3 → V := fun i r =>
    if r = 0 then I i else if r = 1 then M i else O i
  have hmem (i : Fin (m + 1)) (r : Fin 3) : L i r ∈ (c i).val := by
    fin_cases r
    · simpa [L] using hI i
    · by_cases hi : i ∈ T
      · simpa [L, M, hi] using (hsp i hi).1
      · simpa [L, M, hi] using hI i
    · simpa [L] using hO i
  have hstep : ∀ i r, L i r = TriangleIncidence.threeSlotNext L i r ∨
      G.Adj (L i r) (TriangleIncidence.threeSlotNext L i r) := by
    intro i r
    fin_cases r
    · by_cases hi : i ∈ T
      · right
        simpa [L, M, TriangleIncidence.threeSlotNext, hi] using
          (hT i hi).isClique (hI i) (hsp i hi).1 (Ne.symm (hsp i hi).2.1)
      · left
        simp [L, M, TriangleIncidence.threeSlotNext, hi]
    · by_cases hi : i ∈ T
      · right
        simpa [L, M, TriangleIncidence.threeSlotNext, hi] using
          (hT i hi).isClique (hsp i hi).1 (hO i) (hsp i hi).2.2
      · by_cases ht : G.IsNClique 3 (c i).val
        · right
          simpa [L, M, TriangleIncidence.threeSlotNext, hi] using
            ht.isClique (hI i) (hO i) ((hturn i).mpr ht)
        · left
          have he : I i = O i := not_not.mp (fun hn => ht ((hturn i).mp hn))
          simpa [L, M, TriangleIncidence.threeSlotNext, hi] using he
    · right
      simpa [L, TriangleIncidence.threeSlotNext] using hconn i
  have hlocal (i : Fin (m + 1)) (r s : Fin 3)
      (hr : L i r ≠ TriangleIncidence.threeSlotNext L i r)
      (hs : L i s ≠ TriangleIncidence.threeSlotNext L i s)
      (he : L i r = L i s) : r = s := by
    have hshape : M i = I i ∨ (I i ≠ M i ∧ I i ≠ O i ∧ M i ≠ O i) := by
      by_cases hi : i ∈ T
      · right
        simpa only [M, if_pos hi] using
          And.intro (Ne.symm (hsp i hi).2.1)
            (And.intro ((hturn i).mpr (hT i hi)) (hsp i hi).2.2)
      · left
        simp [M, hi]
    exact row_departure_injective (I i) (M i) (O i)
      (fun t => L i t ≠ TriangleIncidence.threeSlotNext L i t) hshape
      (by intro h; simpa [L, TriangleIncidence.threeSlotNext] using h)
      (by intro h; simpa [L, TriangleIncidence.threeSlotNext] using h) r s hr hs he
  have hinj : ∀ i r j s, L i r ≠ TriangleIncidence.threeSlotNext L i r →
      L j s ≠ TriangleIncidence.threeSlotNext L j s → L i r = L j s → i = j ∧ r = s := by
    intro i r j s hr hs he
    have hb : c i = c j :=
      blocks_eq_of_mem G hG hCubic (hmem i r) (he.symm ▸ hmem j s)
    have hij : i = j := hc hb
    subst j
    exact ⟨rfl, hlocal i r s hr hs he⟩
  have hcount0 : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)) = T := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, M, hi, Ne.symm (hsp i hi).2.1]
    · simp [L, M, hi]
  have hcount1 : (Finset.univ.filter (fun i => L i 1 ≠ L i 2)) =
      Finset.univ.filter (fun i => G.IsNClique 3 (c i).val) := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, M, hi, (hsp i hi).2.2, hT i hi]
    · simp [L, M, hi, hturn i]
  have hcount2 : (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)) = Finset.univ := by
    ext i
    simp [L, (hconn i).ne]
  have htotal : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
      (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
      (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)).card = 2 * (m + 1) := by
    rw [hcount0, hcount1, hcount2]
    have hcard' : T.card =
        (Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)).card := by
      exact hcard.trans (congrArg Finset.card
        (Finset.filter_congr_decidable (Finset.univ : Finset (Fin (m + 1)))
          (fun i => ¬ G.IsNClique 3 (c i).val) _))
    rw [hcard']
    have hsum : (Finset.univ.filter (fun i => G.IsNClique 3 (c i).val)).card +
        (Finset.univ.filter (fun i => ¬ G.IsNClique 3 (c i).val)).card = m + 1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.univ : Finset (Fin (m + 1))).card_filter_add_card_filter_not
          (fun i => G.IsNClique 3 (c i).val)
    simp only [Finset.card_univ, Fintype.card_fin] at ⊢
    omega
  obtain ⟨p, hp, hlen⟩ := TriangleIncidence.exists_cycle_of_three_slots G m L hstep hinj
    (by rw [htotal]; omega)
  exact ⟨L 0 0, p, hp, hlen.trans htotal⟩

private theorem cycle_index_of_walk {W : Type u} (K : SimpleGraph W) {a : W}
    (p : K.Walk a a) (hp : p.IsCycle) :
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

/-- Every ordinary cycle of length at least four in the actual canonical quotient lifts
to a literal ordinary original-graph cycle of exactly twice its length. -/
theorem exists_doubled_cycle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2)
    {x : Block G} (p : (quotient G).Walk x x) (hp : p.IsCycle) (hlen : 4 ≤ p.length) :
    ∃ a, ∃ q : G.Walk a a, q.IsCycle ∧ q.length = 2 * p.length := by
  obtain ⟨m, heq, _, c, hc, hadj⟩ := cycle_index_of_walk (quotient G) p hp
  obtain ⟨a, q, hq, hqlen⟩ := exists_doubled_indexed_cycle G hG hCubic hFew
    (by omega) c hc hadj
  exact ⟨a, q, hq, by simpa only [heq] using hqlen⟩

/-- Under the original cubic-at-most-two-claw-center hypotheses and unrestricted
same-universe smaller-order minimality, the original graph itself has a dyadic cycle.
The quotient and its doubled ordinary cycle are constructed internally. -/
theorem hasPowerOfTwoCycle_original {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2) :
    HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, x, p, hp, hlen⟩ := quotient_hasPowerOfTwoCycle G hG hminimal hCubic hFew
  have hfour : 4 ≤ p.length := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    rw [hlen]
    exact hpow
  obtain ⟨a, q, hq, hqlen⟩ := exists_doubled_cycle G hG hCubic hFew p hp hfour
  refine ⟨k + 1, by omega, a, q, hq, ?_⟩
  calc
    q.length = 2 * p.length := hqlen
    _ = 2 * 2 ^ k := by rw [hlen]
    _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

/-- A finite nonempty cubic counterexample with at most two induced-claw centers cannot
satisfy unrestricted smaller-order minimality in the same universe. This is an explicit
bounded branch exclusion, not a reduction of arbitrary graphs to the cubic case. -/
theorem false_of_at_most_two_claw_centers {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2) : False := by
  exact hG.not_hasPowerOfTwoCycle (hasPowerOfTwoCycle_original G hG hminimal hCubic hFew)

end Erdos64.CubicFewClawCenters
