import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.Books

open Finset SimpleGraph

/-- The number of common neighbours of two vertices. -/
def bookSize {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : ℕ :=
  (univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card

/-- Every edge has a common neighbour. -/
abbrev EveryEdgeInTriangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ u v, G.Adj u v → 1 ≤ bookSize G u v

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    bookSize G u v = (univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card := rfl

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    EveryEdgeInTriangle G ↔ ∀ u v, G.Adj u v → 1 ≤ bookSize G u v := Iff.rfl

/-- The real-valued adjacency indicator (one for an edge, zero otherwise). -/
private def a {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : ℝ := if G.Adj u v then 1 else 0

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    a G u v = 1 ↔ G.Adj u v := by simp [a]

private theorem a_symm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : a G u v = a G v u := by
  simp only [a, G.adj_comm]

private theorem a_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : 0 ≤ a G u v := by
  unfold a
  split <;> norm_num

private theorem sum_a {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : ∑ v, a G u v = (G.degree u : ℝ) := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter,
    natCast_card_filter]
  rfl

private theorem sum_aa {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : ∑ w, a G u w * a G v w = (bookSize G u v : ℝ) := by
  simp only [a, bookSize, natCast_card_filter]
  apply sum_congr rfl
  intro w hw
  by_cases hu : G.Adj u w <;> by_cases hv : G.Adj v w <;> simp [hu, hv]

private theorem cyclic_sum {α : Type*} [Fintype α] (F : α → α → α → ℝ) :
    (∑ u, ∑ v, ∑ w, F v w u) = ∑ u, ∑ v, ∑ w, F u v w := by
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  rw [sum_comm]

private theorem majority {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v w x : Fin n) :
    1 ≤ (a G u x * a G v x + (1 - a G u x) * (1 - a G v x)) +
      (a G v x * a G w x + (1 - a G v x) * (1 - a G w x)) +
      (a G w x * a G u x + (1 - a G w x) * (1 - a G u x)) := by
  unfold a
  split_ifs <;> norm_num

/-- The ordered triangle count is six times the unordered count; the
right-hand sum is over oriented edges, hence twice the unordered edge sum.
For each triangle and each vertex, at least one of its three edges has
matching adjacency bits. Vertices on the triangle are included. -/
private theorem count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n : ℝ) * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ)) ≤
      3 * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ) *
        ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v)) := by
  let t := fun u v w => a G u v * a G u w * a G v w
  let e := fun u v => ∑ x, (a G u x * a G v x +
    (1 - a G u x) * (1 - a G v x))
  have ht (u v w : Fin n) : 0 ≤ t u v w :=
    mul_nonneg (mul_nonneg (a_nonneg G u v) (a_nonneg G u w)) (a_nonneg G v w)
  have hcyc (u v w : Fin n) : t v w u = t u v w := by
    dsimp [t]
    rw [a_symm G v u, a_symm G w u]
    ring
  have he (u v : Fin n) : e u v =
      (n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v := by
    dsimp [e]
    simp_rw [show ∀ p q : ℝ, p * q + (1-p)*(1-q) = 1-p-q+2*(p*q) by
      intros; ring]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_a, sum_aa,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have htw (u v : Fin n) : ∑ w, t u v w = a G u v * (bookSize G u v : ℝ) := by
    dsimp [t]
    simp_rw [mul_assoc]
    rw [← mul_sum, sum_aa]
  have hp (u v w : Fin n) : (n : ℝ) * t u v w ≤
      t u v w * (e u v + e v w + e w u) := by
    have h := sum_le_sum (s := (univ : Finset (Fin n)))
      (fun x hx => mul_le_mul_of_nonneg_left (majority G u v w x) (ht u v w))
    simpa [e, mul_add, sum_add_distrib, ← mul_sum, mul_comm] using h
  have hc1 : (∑ u, ∑ v, ∑ w, t u v w * e v w) =
      ∑ u, ∑ v, ∑ w, t u v w * e u v := by
    calc
      _ = ∑ u, ∑ v, ∑ w, t v w u * e v w := by simp_rw [hcyc]
      _ = _ := cyclic_sum (fun u v w => t u v w * e u v)
  have hc2 : (∑ u, ∑ v, ∑ w, t u v w * e w u) =
      ∑ u, ∑ v, ∑ w, t u v w * e u v := by
    calc
      _ = ∑ u, ∑ v, ∑ w, t v w u * e w u := by simp_rw [hcyc]
      _ = ∑ u, ∑ v, ∑ w, t u v w * e v w :=
        cyclic_sum (fun u v w => t u v w * e v w)
      _ = _ := hc1
  have h : (∑ u, ∑ v, ∑ w, (n : ℝ) * t u v w) ≤
      ∑ u, ∑ v, ∑ w, t u v w * (e u v + e v w + e w u) :=
    sum_le_sum (fun u hu => sum_le_sum (fun v hv =>
      sum_le_sum (fun w hw => hp u v w)))
  simp only [mul_add, sum_add_distrib] at h
  rw [hc1, hc2] at h
  simp only [← mul_sum, ← sum_mul, htw] at h
  simp_rw [he] at h
  linarith

private theorem equal_status {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    (n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v =
      ∑ x, (a G u x * a G v x + (1 - a G u x) * (1 - a G v x)) := by
  symm
  simp_rw [show ∀ p q : ℝ, p * q + (1-p)*(1-q) = 1-p-q+2*(p*q) by
    intros; ring]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_a, sum_aa,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private theorem equal_status_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) :
    0 ≤ (n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v := by
  rw [equal_status]
  apply sum_nonneg
  intro x hx
  unfold a
  split_ifs <;> norm_num

private theorem weighted_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∑ u, ∑ v, a G u v * ((G.degree u : ℝ) + G.degree v)) =
      2 * ∑ u, (G.degree u : ℝ)^2 := by
  have hleft : (∑ u, ∑ v, a G u v * (G.degree u : ℝ)) =
      ∑ u, (G.degree u : ℝ)^2 := by
    simp only [← sum_mul, sum_a, sq]
  have hright : (∑ u, ∑ v, a G u v * (G.degree v : ℝ)) =
      ∑ u, (G.degree u : ℝ)^2 := by
    rw [sum_comm]
    simp_rw [a_symm G]
    exact hleft
  simp only [mul_add, sum_add_distrib]
  rw [hleft, hright]
  ring

private theorem sum_equal_status {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∑ u, ∑ v, a G u v * ((n : ℝ) - G.degree u - G.degree v +
      2 * bookSize G u v)) =
    (n : ℝ) * (∑ u, (G.degree u : ℝ)) -
      2 * (∑ u, (G.degree u : ℝ)^2) +
      2 * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ)) := by
  have hp (u v : Fin n) :
      a G u v * ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v) =
      (n : ℝ) * a G u v - a G u v * ((G.degree u : ℝ) + G.degree v) +
        2 * (a G u v * (bookSize G u v : ℝ)) := by ring
  simp_rw [hp]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_a, weighted_degree]

private theorem positive_defect {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hn : 0 < n) (he : n^2 < 4 * G.edgeFinset.card) :
    0 < 2 * (∑ u, (G.degree u : ℝ)^2) -
      (n : ℝ) * (∑ u, (G.degree u : ℝ)) := by
  let d : ℝ := ∑ u, (G.degree u : ℝ)
  let s : ℝ := ∑ u, (G.degree u : ℝ)^2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : d = 2 * (G.edgeFinset.card : ℝ) := by
    dsimp [d]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have her : (n : ℝ)^2 < 4 * (G.edgeFinset.card : ℝ) := by exact_mod_cast he
  have hdp : 0 < d := by nlinarith [sq_nonneg (n : ℝ)]
  have hc : d^2 ≤ (n : ℝ) * s := by
    simpa only [card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n)))
        (f := fun u => (G.degree u : ℝ)))
  have hp : (n : ℝ)^2 * d < 2 * d^2 := by
    have hh : (n : ℝ)^2 < 2*d := by linarith
    have hh' := mul_lt_mul_of_pos_right hh hdp
    nlinarith
  change 0 < 2*s - (n : ℝ)*d
  nlinarith

/-- Edwards' and Khadzhiivanov–Nikiforov's dense-graph book bound,
with the archive's division-free, floor-safe weakening. The proof uses
ordered versions of the triangle/equal-adjacency counts in Bollobás and
Nikiforov, *Books in graphs*, European J. Combin. 26 (2005), 259–270,
Theorem 1 (arXiv:math/0405080). No induced four-vertex counts are needed.
The triangle hypothesis is retained in the archive contract, although
this dense-graph conclusion does not require it. -/
theorem edwards_kn_book {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 6 ≤ n) (he : n^2 < 4 * G.edgeFinset.card)
    (_ht : EveryEdgeInTriangle G) :
    ∃ u v : Fin n, G.Adj u v ∧ n ≤ 6 * bookSize G u v + 5 := by
  by_contra h
  push Not at h
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb (u v : Fin n) (huv : G.Adj u v) : (bookSize G u v : ℝ) ≤ (n : ℝ)/6 := by
    have hnat : 6 * bookSize G u v < n := by
      have hh := h u v huv
      omega
    have hreal : 6 * (bookSize G u v : ℝ) < (n : ℝ) := by exact_mod_cast hnat
    linarith
  have hpoint (u v : Fin n) :
      a G u v * (bookSize G u v : ℝ) *
        ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v) ≤
      ((n : ℝ)/6) * (a G u v *
        ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v)) := by
    by_cases huv : G.Adj u v
    · simpa only [a, if_pos huv, one_mul] using
        mul_le_mul_of_nonneg_right (hb u v huv) (equal_status_nonneg G u v)
    · simp [a, huv]
  have hbound :
      (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ) *
        ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v)) ≤
      ((n : ℝ)/6) * (∑ u, ∑ v, a G u v *
        ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v)) := by
    simp only [mul_sum]
    exact sum_le_sum (fun u hu => sum_le_sum (fun v hv => hpoint u v))
  have hfinal :
      (n : ℝ) * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ)) ≤
      ((n : ℝ)/2) * ((n : ℝ) * (∑ u, (G.degree u : ℝ)) -
        2 * (∑ u, (G.degree u : ℝ)^2) +
        2 * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ))) := by
    calc
      _ ≤ 3 * (∑ u, ∑ v, a G u v * (bookSize G u v : ℝ) *
          ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v)) := count G
      _ ≤ 3 * (((n : ℝ)/6) * (∑ u, ∑ v, a G u v *
          ((n : ℝ) - G.degree u - G.degree v + 2 * bookSize G u v))) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by rw [sum_equal_status]; ring
  have hdefect := positive_defect G (show 0 < n by omega) he
  have hstrict := mul_pos hnr hdefect
  nlinarith

example : (6 : ℕ) ≤ 6 ∧
    (6 : ℕ)^2 < 4 * (⊤ : SimpleGraph (Fin 6)).edgeFinset.card ∧
    EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 6)) := by
  unfold EveryEdgeInTriangle
  decide

end ErdosCandidates.Books
