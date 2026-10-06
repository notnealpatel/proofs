import Erdos.Erdos64.TwoCubicClawCentersWalkIndex
import Erdos.Erdos64.TwoCubicClawCentersOrder

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter

universe u

/-- In a counterexample, any auxiliary square has adjacent retained roots.
Squares with at most one root double, and opposite roots yield an original eight-cycle. -/
theorem four_cycle_roots_adjacent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (c : Fin 4 → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1))) :
    (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩) := by
  classical
  have hmissing (r : ULift.{u} Bool) (hmiss : ∀ i, c i ≠ .inl r) : False := by
    have hcount := triangle_count_of_missing_root G c hc r hmiss
    obtain ⟨a, p, hp, hl⟩ := exists_doubled_cycle_of_many_triangles G hG huv hCenters
      hcu hcv hdu hdv hHIGH (m := 3) (by decide) c hc hadj (by omega)
    exact hG.not_hasPowerOfTwoCycle ⟨3, by decide, a, p, hp, by simpa using hl⟩
  have hU : ∃ i, c i = .inl ⟨false⟩ := by
    by_contra hn
    exact hmissing ⟨false⟩ (not_exists.mp hn)
  have hV : ∃ i, c i = .inl ⟨true⟩ := by
    by_contra hn
    exact hmissing ⟨true⟩ (not_exists.mp hn)
  obtain ⟨iu, hu⟩ := hU
  obtain ⟨iv, hv⟩ := hV
  let d : Fin 4 → Node G := fun i => c (i + iu)
  have hd : Function.Injective d := by
    intro i j he
    exact add_right_cancel (hc he)
  have hda (i : Fin 4) : (auxiliary G u v).Adj (d i) (d (i + 1)) := by
    simpa only [d, add_assoc, add_comm, add_left_comm] using hadj (i + iu)
  have h0 : d 0 = .inl ⟨false⟩ := by simpa only [d, zero_add] using hu
  have hj : d (iv - iu) = .inl ⟨true⟩ := by simpa only [d, sub_add_cancel] using hv
  generalize hjidx : iv - iu = j at hj
  fin_cases j
  · change d 0 = .inl ⟨true⟩ at hj
    exact (roots_ne G (h0.symm.trans hj)).elim
  · change d 1 = .inl ⟨true⟩ at hj
    simpa only [h0, hj, show (0 : Fin 4) + 1 = 1 from rfl] using hda 0
  · change d 2 = .inl ⟨true⟩ at hj
    exact (alternating_four_cycle_false G hG huv hCenters hcu hcv hdu hdv d hd hda h0 hj).elim
  · change d 3 = .inl ⟨true⟩ at hj
    simpa only [h0, hj, show (3 : Fin 4) + 1 = 0 from rfl] using (hda 3).symm

/-- Original order minimality forces adjacency of the two retained auxiliary roots:
all dyadic auxiliary cycles of length at least eight double, while a square forces adjacency. -/
theorem roots_adjacent_of_minimal {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩) := by
  classical
  obtain ⟨k, hk, x, p, hp, hl⟩ := auxiliary_hasPowerOfTwoCycle G hG hminimal huv
    hCenters hcu hcv hdu hdv hHIGH
  obtain ⟨m, hm, hlen, c, hc, hadj⟩ := walk_cycle_index p hp
  by_cases hk2 : k = 2
  · have h4 : m + 1 = 4 := by
      have heq := hm.symm.trans hl
      rw [hk2] at heq
      norm_num at heq
      exact heq
    subst k
    have hm3 : m = 3 := by omega
    subst m
    exact four_cycle_roots_adjacent G hG huv hCenters hcu hcv hdu hdv hHIGH c hc hadj
  · have h8 : 8 ≤ m + 1 := by
      have hp8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨a, q, hq, hqlen⟩ := exists_doubled_cycle_of_large G hG huv hCenters
      hcu hcv hdu hdv hHIGH (by omega) c hc hadj
    have hdyad : q.length = 2 ^ (k + 1) := by
      rw [hqlen, ← hm, hl, pow_succ, Nat.mul_comm]
    exact (hG.not_hasPowerOfTwoCycle ⟨k + 1, by omega, a, q, hq, hdyad⟩).elim

/-- The forced auxiliary root edge is an actual edge between the original cubic centers. -/
theorem centers_adjacent_of_minimal {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) : G.Adj u v := by
  have he := roots_adjacent_of_minimal G hG hminimal huv hCenters hcu hcv hdu hdv hHIGH
  have ho := root_connector_edge G hG huv hcu hcv hdu hdv he
  rw [root_port G hG he.symm] at ho
  exact ho.1

end Erdos64.TwoCubicClawCentersQuotient
