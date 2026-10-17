import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
namespace ElementaryLoomisWhitneyStability

/-- A binary real entry is idempotent. -/
theorem binary_sq (x : ℝ) (hx : x = 0 ∨ x = 1) : x ^ 2 = x := by
  rcases hx with rfl | rfl <;> norm_num

/-- The sum of the squared binary minors is twice the energy deficit. -/
theorem binary_minor_identity {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) (hf : ∀ i j, f i j = 0 ∨ f i j = 1) :
    (∑ i, ∑ k, ∑ j, ∑ l, (f i j * f k l - f i l * f k j) ^ 2) =
      2 * ((∑ i, ∑ j, f i j) ^ 2 - ∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2) := by
  have hrow (i k : I) :
      (∑ j, ∑ l, (f i j * f k l - f i l * f k j) ^ 2) =
        2 * ((∑ j, f i j) * (∑ l, f k l) - (∑ j, f i j * f k j) ^ 2) := by
    have hfirst : (∑ j, ∑ l, (f i j * f k l) ^ 2) =
        (∑ j, f i j) * (∑ l, f k l) := by
      simp_rw [mul_pow, binary_sq _ (hf _ _), Finset.sum_mul, Finset.mul_sum]
    have hlast : (∑ j, ∑ l, (f i l * f k j) ^ 2) =
        (∑ j, f i j) * (∑ l, f k l) := by
      rw [Finset.sum_comm]
      simp_rw [mul_pow, binary_sq _ (hf _ _), Finset.sum_mul, Finset.mul_sum]
    have hcross : (∑ j, ∑ l, f i j * f k l * (f i l * f k j)) =
        (∑ j, f i j * f k j) ^ 2 := by
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum] at *
    rw [hfirst, hlast]
    have hc : (∑ j, ∑ l, 2 * (f i j * f k l) * (f i l * f k j)) =
        2 * (∑ j, f i j * f k j) ^ 2 := by
      rw [← hcross, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hc]
    ring
  simp_rw [hrow, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

example : (∀ i j : Fin 1, (fun _ _ => (1 : ℝ)) i j = 0 ∨
    (fun _ _ => (1 : ℝ)) i j = 1) ∧
    0 < ∑ _i : Fin 1, ∑ _j : Fin 1, (1 : ℝ) := by
  constructor
  · intro i j
    exact Or.inr rfl
  · norm_num

/-- A nonzero binary matrix has a one-entry pivot with squared error at most
 twice its energy deficit divided by its mass. -/
theorem exists_binary_pivot {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) (hf : ∀ i j, f i j = 0 ∨ f i j = 1)
    (hm : 0 < ∑ i, ∑ j, f i j) :
    ∃ i j, f i j = 1 ∧
      (∑ k, ∑ l, (f k l - f k j * f i l) ^ 2) ≤
        2 * ((∑ i, ∑ j, f i j) ^ 2 - ∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2) /
          (∑ i, ∑ j, f i j) := by
  classical
  let s := (Finset.univ : Finset (I × J)).filter (fun p => f p.1 p.2 = 1)
  let c := fun (p : I × J) => ∑ k, ∑ l, (f k l - f k p.2 * f p.1 l) ^ 2
  let L := 2 * ((∑ i, ∑ j, f i j) ^ 2 - ∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2)
  have hmass : (∑ p ∈ s, (1 : ℝ)) = ∑ i, ∑ j, f i j := by
    simp only [s, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rcases hf i j with he | he <;> simp [he]
  have hs : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he] at hmass
    simp only [Finset.sum_empty] at hmass
    linarith
  have hp (i : I) (j : J) :
      (if f i j = 1 then c (i,j) else 0) ≤
        ∑ k, ∑ l, (f i j * f k l - f i l * f k j) ^ 2 := by
    by_cases he : f i j = 1
    · simp only [he, if_true, one_mul, c]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      ring
    · simp only [he, if_false]
      exact Finset.sum_nonneg fun k hk => Finset.sum_nonneg fun l hl => sq_nonneg _
  have hcost : (∑ p ∈ s, c p) ≤ L := by
    calc
      _ = ∑ i, ∑ j, if f i j = 1 then c (i,j) else 0 := by
        simp only [s, Finset.sum_filter, Fintype.sum_prod_type]
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l,
          (f i j * f k l - f i l * f k j) ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i j
      _ = ∑ i, ∑ k, ∑ j, ∑ l,
          (f i j * f k l - f i l * f k j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = L := binary_minor_identity f hf
  have havg : (∑ p ∈ s, c p) ≤ ∑ _p ∈ s, L / (∑ i, ∑ j, f i j) := by
    calc
      _ ≤ L := hcost
      _ = (∑ p ∈ s, (1 : ℝ)) * (L / (∑ i, ∑ j, f i j)) := by
        rw [hmass]
        field_simp
      _ = _ := by simp only [Finset.sum_mul, one_mul]
  obtain ⟨p, hp, hc⟩ := Finset.exists_le_of_sum_le hs havg
  exact ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, hc⟩

/-- The real indicator of a finite bipartite graph. -/
noncomputable def edge {I J : Type*} [DecidableEq I] [DecidableEq J]
    (F : Finset (I × J)) (i : I) (j : J) : ℝ :=
  if (i,j) ∈ F then 1 else 0

/-- The indicator is one precisely on the graph. -/
theorem edge_eq_one {I J : Type*} [DecidableEq I] [DecidableEq J]
    (F : Finset (I × J)) (i : I) (j : J) : edge F i j = 1 ↔ (i,j) ∈ F := by
  simp [edge]

example : edge ({(0,0)} : Finset (Fin 1 × Fin 1)) 0 0 = 1 := by simp [edge]
example : edge (∅ : Finset (Fin 1 × Fin 1)) 0 0 = 0 := by simp [edge]

/-- Finite edge indicators are binary. -/
theorem edge_binary {I J : Type*} [DecidableEq I] [DecidableEq J]
    (F : Finset (I × J)) (i : I) (j : J) : edge F i j = 0 ∨ edge F i j = 1 := by
  unfold edge
  split_ifs <;> simp

/-- Summing the graph indicator over the finite ambient types counts edges. -/
theorem sum_edge {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (F : Finset (I × J)) :
    (∑ i, ∑ j, edge F i j) = (F.card : ℝ) := by
  rw [← Fintype.sum_prod_type (fun p : I × J => edge F p.1 p.2)]
  change (∑ p : I × J, if p ∈ F then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp

/-- Squared differences of binary indicators count the literal symmetric difference. -/
theorem sum_edge_sub_sq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (F R : Finset (I × J)) :
    (∑ i, ∑ j, (edge F i j - edge R i j) ^ 2) =
      (((F \ R) ∪ (R \ F)).card : ℝ) := by
  rw [← sum_edge ((F \ R) ∪ (R \ F))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hf : (i,j) ∈ F <;> by_cases hr : (i,j) ∈ R <;> simp [edge, hf, hr]

/-- A finite nonempty graph is close to a pivot rectangle, with the error
 controlled by twice its binary overlap-energy deficit divided by its edge count. -/
theorem exists_pivot_rectangle {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (F : Finset (I × J)) (hF : F.Nonempty) :
    ∃ U : Finset I, ∃ V : Finset J, U.Nonempty ∧ V.Nonempty ∧
      ((((F \ (U ×ˢ V)) ∪ ((U ×ˢ V) \ F)).card : ℝ)) ≤
        2 * ((F.card : ℝ) ^ 2 -
          ∑ i, ∑ k, (∑ j, edge F i j * edge F k j) ^ 2) / F.card := by
  have hm : 0 < ∑ i, ∑ j, edge F i j := by
    rw [sum_edge]
    exact_mod_cast Finset.card_pos.mpr hF
  obtain ⟨i,j,hij,hcost⟩ := exists_binary_pivot (edge F) (edge_binary F) hm
  have hijF := (edge_eq_one F i j).mp hij
  let U := Finset.univ.filter (fun k => (k,j) ∈ F)
  let V := Finset.univ.filter (fun l => (i,l) ∈ F)
  have hU : i ∈ U := by simp [U, hijF]
  have hV : j ∈ V := by simp [V, hijF]
  have hprod (k : I) (l : J) :
      edge (U ×ˢ V) k l = edge F k j * edge F i l := by
    by_cases hk : (k,j) ∈ F <;> by_cases hl : (i,l) ∈ F <;>
      simp [edge, U, V, hk, hl]
  refine ⟨U,V,⟨i,hU⟩,⟨j,hV⟩,?_⟩
  rw [← sum_edge_sub_sq]
  simpa only [hprod, sum_edge] using hcost

/-- Expanding and reindexing finite overlap squares gives the column-overlap pairing. -/
theorem overlap_reindex {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → ℝ) (g : K → J → ℝ) :
    (∑ i, ∑ k, (∑ j, f i j * g k j) ^ 2) =
      ∑ j, ∑ l, (∑ i, f i j * f i l) * (∑ k, g k j * g k l) := by
  have hexpand (i : I) (k : K) : (∑ j, f i j * g k j) ^ 2 =
      ∑ j, ∑ l, (f i j * f i l) * (g k j * g k l) := by
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp_rw [hexpand]
  calc
    _ = ∑ i, ∑ j, ∑ l, ∑ k, (f i j * f i l) * (g k j * g k l) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, ∑ k, (f i j * f i l) * (g k j * g k l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Row and column overlap energies of a finite real matrix coincide. -/
theorem energy_transpose {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) :
    (∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2) =
      ∑ j, ∑ l, (∑ i, f i j * f i l) ^ 2 := by
  simpa only [← sq] using overlap_reindex f f

/-- Cauchy–Schwarz bounds the square of cross-overlap energy by the two graph energies. -/
theorem overlap_energy_cs {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → ℝ) (g : K → J → ℝ) :
    (∑ i, ∑ k, (∑ j, f i j * g k j) ^ 2) ^ 2 ≤
      (∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2) *
        (∑ i, ∑ k, (∑ j, g i j * g k j) ^ 2) := by
  rw [overlap_reindex, energy_transpose f, energy_transpose g]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (J × J))
    (fun p => ∑ i, f i p.1 * f i p.2) (fun p => ∑ k, g k p.1 * g k p.2)
  simpa only [Fintype.sum_prod_type] using hcs

/-- Binary overlap energy never exceeds the square of the edge mass. -/
theorem binary_energy_le {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) (hf : ∀ i j, f i j = 0 ∨ f i j = 1) :
    (∑ i, ∑ k, (∑ j, f i j * f k j) ^ 2) ≤ (∑ i, ∑ j, f i j) ^ 2 := by
  have hn : 0 ≤ ∑ i, ∑ k, ∑ j, ∑ l,
      (f i j * f k l - f i l * f k j) ^ 2 :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk =>
      Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun l hl => sq_nonneg _
  rw [binary_minor_identity f hf] at hn
  linarith

/-- The outer Cauchy–Schwarz inequality for a finite triangle sum. -/
theorem triangle_cs {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → ℝ) (g : K → J → ℝ) (h : I → K → ℝ) :
    (∑ i, ∑ k, h i k * (∑ j, f i j * g k j)) ^ 2 ≤
      (∑ i, ∑ k, h i k ^ 2) * (∑ i, ∑ k, (∑ j, f i j * g k j) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (I × K))
    (fun p => h p.1 p.2) (fun p => ∑ j, f p.1 j * g p.2 j)
  simpa only [Fintype.sum_prod_type] using hcs

/-- The scalar energy argument: near equality in the triangle bound forces
 a binary graph's overlap-energy deficit to be at most twice epsilon times mass squared. -/
theorem energy_deficit_le (a b c N Q E E' ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 ≤ ε)
    (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hE' : E' ≤ b ^ 2)
    (hprod : a*b*c ≤ (1+ε)*N^2) (hN : N^2 ≤ c*Q)
    (hcs : Q^2 ≤ E*E') : a^2 - E ≤ 2*ε*a^2 := by
  have he1 : 0 ≤ 1+ε := by linarith
  have hcancel : a*b ≤ (1+ε)*Q := by
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      _ = a*b*c := by ring
      _ ≤ (1+ε)*N^2 := hprod
      _ ≤ (1+ε)*(c*Q) := mul_le_mul_of_nonneg_left hN he1
      _ = _ := by ring
  have hsquare : (a*b)^2 ≤ ((1+ε)*Q)^2 :=
    (sq_le_sq₀ (mul_nonneg ha.le hb.le) (mul_nonneg he1 hQ)).mpr hcancel
  have henergy : a^2 ≤ (1+ε)^2*E := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hb)).mp
    calc
      _ = (a*b)^2 := by ring
      _ ≤ ((1+ε)*Q)^2 := hsquare
      _ = (1+ε)^2*Q^2 := by ring
      _ ≤ (1+ε)^2*(E*E') := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ (1+ε)^2*(E*b^2) := by gcongr
      _ = _ := by ring
  by_cases hsmall : 0 ≤ 1-2*ε
  · have hcoef : (1-2*ε)*(1+ε)^2 ≤ 1 := by
      nlinarith [sq_nonneg ε, mul_nonneg he (sq_nonneg ε)]
    have hscaled := mul_le_mul_of_nonneg_left henergy hsmall
    have hlast := mul_le_mul_of_nonneg_right hcoef hE
    nlinarith only [hscaled, hlast]
  · have hlarge : 1 ≤ 2*ε := by linarith
    have hscaled := mul_le_mul_of_nonneg_right hlarge (sq_nonneg a)
    linarith

/-- A finite binary triangle system near its product bound has a small
 energy deficit for its first graph. All overlap and Cauchy–Schwarz steps are internal. -/
theorem binary_triangle_deficit {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → ℝ) (g : K → J → ℝ) (h : I → K → ℝ)
    (hf : ∀ i j, f i j = 0 ∨ f i j = 1)
    (hg : ∀ k j, g k j = 0 ∨ g k j = 1)
    (hh : ∀ i k, h i k = 0 ∨ h i k = 1)
    (N ε : ℝ) (he : 0 ≤ ε)
    (ha : 0 < ∑ i, ∑ j, f i j) (hb : 0 < ∑ k, ∑ j, g k j)
    (hc : 0 < ∑ i, ∑ k, h i k)
    (hprod : (∑ i, ∑ j, f i j) * (∑ k, ∑ j, g k j) * (∑ i, ∑ k, h i k) ≤
      (1+ε)*N^2)
    (hN : N^2 ≤ (∑ i, ∑ k, h i k * (∑ j, f i j * g k j))^2) :
    (∑ i, ∑ j, f i j)^2 - ∑ i, ∑ k, (∑ j, f i j * f k j)^2 ≤
      2*ε*(∑ i, ∑ j, f i j)^2 := by
  have houter := triangle_cs f g h
  simp_rw [binary_sq _ (hh _ _)] at houter
  exact energy_deficit_le _ _ _ N _ _ _ ε ha hb hc he
    (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => sq_nonneg _)
    (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => sq_nonneg _)
    (binary_energy_le g hg) hprod (hN.trans houter) (overlap_energy_cs f g)

example : let f := fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)
    (∀ i j, f i j = 0 ∨ f i j = 1) ∧ 0 < ∑ i, ∑ j, f i j ∧
      (∑ i, ∑ j, f i j) ^ 3 ≤ (1+(1/4:ℝ))*1^2 ∧
      (1:ℝ)^2 ≤ (∑ i, ∑ k, f i k * (∑ j, f i j*f k j))^2 := by
  norm_num

/-- Near equality for a finite triangle system yields a genuine finite rectangle
 approximating its first graph, with relative symmetric-difference error four epsilon. -/
theorem exists_rectangle_of_near_triangle {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (K × J)) (H : Finset (I × K))
    (hF : F.Nonempty) (hG : G.Nonempty) (hH : H.Nonempty)
    (N ε : ℝ) (he : 0 ≤ ε)
    (hprod : (F.card : ℝ)*G.card*H.card ≤ (1+ε)*N^2)
    (hN : N^2 ≤ (∑ i, ∑ k, edge H i k * (∑ j, edge F i j * edge G k j))^2) :
    ∃ U : Finset I, ∃ V : Finset J, U.Nonempty ∧ V.Nonempty ∧
      ((((F \ (U ×ˢ V)) ∪ ((U ×ˢ V) \ F)).card : ℝ)) ≤ 4*ε*F.card := by
  have ha : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  have hb : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hc : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hdef := binary_triangle_deficit (edge F) (edge G) (edge H)
    (edge_binary F) (edge_binary G) (edge_binary H) N ε he
    (by simpa only [sum_edge] using ha) (by simpa only [sum_edge] using hb)
    (by simpa only [sum_edge] using hc) (by simpa only [sum_edge] using hprod) hN
  simp only [sum_edge] at hdef
  obtain ⟨U,V,hU,hV,herr⟩ := exists_pivot_rectangle F hF
  refine ⟨U,V,hU,hV,herr.trans ?_⟩
  apply (div_le_iff₀ ha).mpr
  nlinarith only [hdef]

/-- The finite supported-triangle set of three bipartite graphs. -/
def triangles {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    Finset (I × J × K) :=
  Finset.univ.filter fun t => (t.1,t.2.1) ∈ F ∧ (t.1,t.2.2) ∈ G ∧ (t.2.1,t.2.2) ∈ H

/-- Membership in the supported-triangle set means all three edges are present. -/
theorem mem_triangles {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K))
    (t : I × J × K) : t ∈ triangles F G H ↔
      (t.1,t.2.1) ∈ F ∧ (t.1,t.2.2) ∈ G ∧ (t.2.1,t.2.2) ∈ H := by
  simp [triangles]

example : triangles ({(0,0)} : Finset (Fin 1 × Fin 1))
    ({(0,0)} : Finset (Fin 1 × Fin 1)) {(0,0)} =
    {(0,0,0)} := by decide
example : triangles (∅ : Finset (Fin 1 × Fin 1))
    ({(0,0)} : Finset (Fin 1 × Fin 1)) {(0,0)} = ∅ := by decide

/-- The triangle count is exactly the finite indicator contraction. -/
theorem card_triangles_eq_sum {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    ((triangles F G H).card : ℝ) =
      ∑ i, ∑ k, edge G i k * (∑ j, edge F i j * edge H j k) := by
  simp only [triangles, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hf : (i,j) ∈ F <;> by_cases hg : (i,k) ∈ G <;>
    by_cases hh : (j,k) ∈ H <;> simp [edge, hf, hg, hh]

/-- Every supported-triangle count satisfies the sharp finite triangle bound. -/
theorem card_triangles_sq_le {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    (triangles F G H).card ^ 2 ≤ F.card*G.card*H.card := by
  suffices ht : ((triangles F G H).card : ℝ)^2 ≤ (F.card : ℝ)*G.card*H.card by
    exact_mod_cast ht
  let Q : ℝ := ∑ i, ∑ k, (∑ j, edge F i j * edge H j k)^2
  have hF := binary_energy_le (edge F) (edge_binary F)
  have hH := binary_energy_le (fun k j => edge H j k) (fun k j => edge_binary H j k)
  have hmassH : (∑ k, ∑ j, edge H j k) = (H.card : ℝ) := by
    rw [Finset.sum_comm, sum_edge]
  rw [sum_edge] at hF
  rw [hmassH] at hH
  have hcs := overlap_energy_cs (edge F) (fun k j => edge H j k)
  have hQsq : Q^2 ≤ (F.card : ℝ)^2*(H.card : ℝ)^2 :=
    hcs.trans (mul_le_mul hF hH (by positivity) (by positivity))
  have hQ : Q ≤ (F.card : ℝ)*H.card := by
    apply (sq_le_sq₀ (by dsimp only [Q]; positivity) (by positivity)).mp
    simpa only [mul_pow] using hQsq
  have hT := triangle_cs (edge F) (fun k j => edge H j k) (edge G)
  simp_rw [binary_sq _ (edge_binary G _ _)] at hT
  rw [sum_edge] at hT
  rw [card_triangles_eq_sum]
  calc
    _ ≤ (G.card : ℝ)*Q := hT
    _ ≤ (G.card : ℝ)*((F.card : ℝ)*H.card) := by gcongr
    _ = _ := by ring

/-- Swapping a finite graph swaps its indicator arguments. -/
theorem edge_swap {I J : Type*} [DecidableEq I] [DecidableEq J]
    (F : Finset (I × J)) (j : J) (i : I) :
    edge (F.image Prod.swap) j i = edge F i j := by
  have hm : (j,i) ∈ F.image Prod.swap ↔ (i,j) ∈ F := by
    constructor
    · intro h
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
      have hh : p = (i,j) := by simpa using congrArg Prod.swap he
      exact hh ▸ hp
    · intro h
      exact Finset.mem_image.mpr ⟨(i,j),h,rfl⟩
  simp only [edge, hm]

/-- A supported-triangle system near equality has a finite rectangle
 approximating its XY graph with relative error four epsilon. -/
theorem exists_rectangle_of_triangles {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K))
    (hF : F.Nonempty) (hG : G.Nonempty) (hH : H.Nonempty)
    (N ε : ℝ) (he : 0 ≤ ε)
    (hprod : (F.card : ℝ)*G.card*H.card ≤ (1+ε)*N^2)
    (hN : N^2 ≤ ((triangles F G H).card : ℝ)^2) :
    ∃ U : Finset I, ∃ V : Finset J, U.Nonempty ∧ V.Nonempty ∧
      ((((F \ (U ×ˢ V)) ∪ ((U ×ˢ V) \ F)).card : ℝ)) ≤ 4*ε*F.card := by
  apply exists_rectangle_of_near_triangle F (H.image Prod.swap) G hF (hH.image _) hG N ε he
  · rw [Finset.card_image_of_injective _ Prod.swap_injective]
    nlinarith only [hprod]
  · simpa only [edge_swap, ← card_triangles_eq_sum] using hN

/-- Literal finite symmetric differences satisfy the cardinal triangle inequality. -/
theorem card_symm_triangle {T : Type*} [DecidableEq T] (A B C : Finset T) :
    ((A \ C) ∪ (C \ A)).card ≤
      ((A \ B) ∪ (B \ A)).card + ((B \ C) ∪ (C \ B)).card := by
  have hs : (A \ C) ∪ (C \ A) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((B \ C) ∪ (C \ B)) := by
    intro t ht
    simp only [Finset.mem_union, Finset.mem_sdiff] at ht ⊢
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

/-- Replacing the XY graph charges every changed triangle to a literal edge error,
 including added edges. -/
theorem triangles_change_xy {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F R : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    ((triangles F G H \ triangles R G H) ∪
      (triangles R G H \ triangles F G H)).card ^ 2 ≤
      ((F \ R) ∪ (R \ F)).card * G.card * H.card := by
  have he : ((triangles F G H \ triangles R G H) ∪
      (triangles R G H \ triangles F G H)) = triangles ((F \ R) ∪ (R \ F)) G H := by
    ext t
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_triangles]
    tauto
  rw [he]
  exact card_triangles_sq_le _ _ _

/-- Replacing the XZ graph charges every changed triangle to its literal edge error. -/
theorem triangles_change_xz {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G R : Finset (I × K)) (H : Finset (J × K)) :
    ((triangles F G H \ triangles F R H) ∪
      (triangles F R H \ triangles F G H)).card ^ 2 ≤
      F.card * ((G \ R) ∪ (R \ G)).card * H.card := by
  have he : ((triangles F G H \ triangles F R H) ∪
      (triangles F R H \ triangles F G H)) = triangles F ((G \ R) ∪ (R \ G)) H := by
    ext t
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_triangles]
    tauto
  rw [he]
  exact card_triangles_sq_le _ _ _

/-- Replacing the YZ graph charges every changed triangle to its literal edge error. -/
theorem triangles_change_yz {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H R : Finset (J × K)) :
    ((triangles F G H \ triangles F G R) ∪
      (triangles F G R \ triangles F G H)).card ^ 2 ≤
      F.card * G.card * ((H \ R) ∪ (R \ H)).card := by
  have he : ((triangles F G H \ triangles F G R) ∪
      (triangles F G R \ triangles F G H)) = triangles F G ((H \ R) ∪ (R \ H)) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_triangles]
    tauto
  rw [he]
  exact card_triangles_sq_le _ _ _

/-- Triangles of three rectangles form the Cartesian product of pairwise intersections. -/
theorem triangles_rectangles {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (U U' : Finset I) (V V' : Finset J) (W W' : Finset K) :
    triangles (U ×ˢ V) (U' ×ˢ W) (V' ×ˢ W') =
      (U ∩ U') ×ˢ ((V ∩ V') ×ˢ (W ∩ W')) := by
  ext t
  simp only [mem_triangles, Finset.mem_product, Finset.mem_inter]
  tauto

/-- A pair belongs to a swapped graph exactly when its reversal belongs to the graph. -/
theorem mem_swap_graph {I J : Type*} [DecidableEq I] [DecidableEq J]
    (F : Finset (I × J)) (j : J) (i : I) :
    (j,i) ∈ F.image Prod.swap ↔ (i,j) ∈ F := by
  rw [← edge_eq_one, edge_swap, edge_eq_one]

/-- Interchanging the last two coordinates preserves the supported-triangle count. -/
theorem card_triangles_swap_yz {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    (triangles F G H).card = (triangles G F (H.image Prod.swap)).card := by
  apply Finset.card_bij (fun t _ => (t.1,t.2.2,t.2.1))
  · intro t ht
    simp only [mem_triangles, mem_swap_graph] at ht ⊢
    tauto
  · rintro ⟨i,j,k⟩ ht ⟨i',j',k'⟩ ht' he
    simp only [Prod.mk.injEq] at he ⊢
    tauto
  · rintro ⟨i,k,j⟩ ht
    refine ⟨(i,j,k),?_,rfl⟩
    simp only [mem_triangles, mem_swap_graph] at ht ⊢
    tauto

/-- Cyclically rotating coordinates preserves the supported-triangle count. -/
theorem card_triangles_rotate {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K)) :
    (triangles F G H).card =
      (triangles H (F.image Prod.swap) (G.image Prod.swap)).card := by
  apply Finset.card_bij (fun t _ => (t.2.1,t.2.2,t.1))
  · intro t ht
    simp only [mem_triangles, mem_swap_graph] at ht ⊢
    tauto
  · rintro ⟨i,j,k⟩ ht ⟨i',j',k'⟩ ht' he
    simp only [Prod.mk.injEq] at he ⊢
    tauto
  · rintro ⟨j,k,i⟩ ht
    refine ⟨(i,j,k),?_,rfl⟩
    simp only [mem_triangles, mem_swap_graph] at ht ⊢
    tauto

/-- All three projection graphs in a near-extremal finite triangle system
 admit rectangles with relative error four epsilon. -/
theorem exists_three_rectangles {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F : Finset (I × J)) (G : Finset (I × K)) (H : Finset (J × K))
    (hF : F.Nonempty) (hG : G.Nonempty) (hH : H.Nonempty)
    (N ε : ℝ) (he : 0 ≤ ε)
    (hprod : (F.card : ℝ)*G.card*H.card ≤ (1+ε)*N^2)
    (hN : N^2 ≤ ((triangles F G H).card : ℝ)^2) :
    ∃ U U' : Finset I, ∃ V V' : Finset J, ∃ W W' : Finset K,
      ((((F \ (U ×ˢ V)) ∪ ((U ×ˢ V) \ F)).card : ℝ)) ≤ 4*ε*F.card ∧
      ((((G \ (U' ×ˢ W)) ∪ ((U' ×ˢ W) \ G)).card : ℝ)) ≤ 4*ε*G.card ∧
      ((((H \ (V' ×ˢ W')) ∪ ((V' ×ˢ W') \ H)).card : ℝ)) ≤ 4*ε*H.card := by
  obtain ⟨U,V,hU,hV,hFerr⟩ := exists_rectangle_of_triangles F G H hF hG hH N ε he hprod hN
  have hprodG : (G.card : ℝ)*F.card*(H.image Prod.swap).card ≤ (1+ε)*N^2 := by
    rw [Finset.card_image_of_injective _ Prod.swap_injective]
    nlinarith only [hprod]
  have hNG : N^2 ≤ ((triangles G F (H.image Prod.swap)).card : ℝ)^2 := by
    rwa [← card_triangles_swap_yz]
  obtain ⟨U',W,hU',hW,hGerr⟩ := exists_rectangle_of_triangles G F (H.image Prod.swap)
    hG hF (hH.image _) N ε he hprodG hNG
  have hprodH : (H.card : ℝ)*(F.image Prod.swap).card*(G.image Prod.swap).card ≤
      (1+ε)*N^2 := by
    simp only [Finset.card_image_of_injective _ Prod.swap_injective]
    nlinarith only [hprod]
  have hNH : N^2 ≤
      ((triangles H (F.image Prod.swap) (G.image Prod.swap)).card : ℝ)^2 := by
    rwa [← card_triangles_rotate]
  obtain ⟨V',W',hV',hW',hHerr⟩ := exists_rectangle_of_triangles H (F.image Prod.swap)
    (G.image Prod.swap) hH (hF.image _) (hG.image _) N ε he hprodH hNH
  exact ⟨U,U',V,V',W,W',hFerr,hGerr,hHerr⟩

/-- A finite set's size is bounded by a comparison set plus their literal symmetric difference. -/
theorem card_le_add_symm {T : Type*} [DecidableEq T] (A B : Finset T) :
    A.card ≤ B.card + ((B \ A) ∪ (A \ B)).card := by
  have hs : A ⊆ B ∪ ((B \ A) ∪ (A \ B)) := by
    intro t ht
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

/-- The exact three-step triangle estimate uses the rational bound sqrt(2) at most 10/7. -/
theorem three_step_error_le (x y z δ P : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hx2 : x^2 ≤ δ*P) (hy2 : y^2 ≤ 2*δ*P) (hz2 : z^2 ≤ 4*δ*P) :
    x+y+z ≤ (31/7 : ℝ)*Real.sqrt δ*Real.sqrt P := by
  let b := Real.sqrt δ * Real.sqrt P
  have hb : 0 ≤ b := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb2 : b^2 = δ*P := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt hδ, Real.sq_sqrt hP]
  have hxb : x ≤ b := by nlinarith only [hx, hb, hx2, hb2]
  have hyb : y ≤ (10/7:ℝ)*b := by
    nlinarith only [hy, hb, hy2, hb2, sq_nonneg (y-(10/7:ℝ)*b)]
  have hzb : z ≤ 2*b := by nlinarith only [hz, hb, hz2, hb2]
  change x+y+z ≤ (31/7:ℝ)*Real.sqrt δ*Real.sqrt P
  dsimp only [b] at hxb hyb hzb
  linarith

/-- Three literal edge replacements telescope to a supported-triangle error bound;
 rectangle sizes and added ghost edges are fully charged. -/
theorem triangle_replacement_bound {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F R : Finset (I × J)) (G S : Finset (I × K)) (H T : Finset (J × K))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hF : (((F \ R) ∪ (R \ F)).card : ℝ) ≤ δ*F.card)
    (hG : (((G \ S) ∪ (S \ G)).card : ℝ) ≤ δ*G.card)
    (hH : (((H \ T) ∪ (T \ H)).card : ℝ) ≤ δ*H.card) :
    (((triangles F G H \ triangles R S T) ∪
      (triangles R S T \ triangles F G H)).card : ℝ) ≤
      (31/7:ℝ)*Real.sqrt δ*Real.sqrt ((F.card : ℝ)*G.card*H.card) := by
  let A := triangles F G H
  let B := triangles R G H
  let C := triangles R S H
  let D := triangles R S T
  let x : ℝ := ((A \ B) ∪ (B \ A)).card
  let y : ℝ := ((B \ C) ∪ (C \ B)).card
  let z : ℝ := ((C \ D) ∪ (D \ C)).card
  have hR : (R.card : ℝ) ≤ 2*F.card := by
    have hc : (R.card : ℝ) ≤ F.card + ((F \ R) ∪ (R \ F)).card := by
      exact_mod_cast card_le_add_symm R F
    have hmul := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg F.card : (0:ℝ) ≤ F.card)
    linarith
  have hS : (S.card : ℝ) ≤ 2*G.card := by
    have hc : (S.card : ℝ) ≤ G.card + ((G \ S) ∪ (S \ G)).card := by
      exact_mod_cast card_le_add_symm S G
    have hmul := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg G.card : (0:ℝ) ≤ G.card)
    linarith
  have hx : x^2 ≤ δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : x^2 ≤ (((F \ R) ∪ (R \ F)).card : ℝ)*G.card*H.card := by
      dsimp only [x,A,B]
      exact_mod_cast triangles_change_xy F R G H
    calc
      _ ≤ _ := hc
      _ ≤ (δ*F.card)*G.card*H.card := by gcongr
      _ = _ := by ring
  have hy : y^2 ≤ 2*δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : y^2 ≤ (R.card : ℝ)*((G \ S) ∪ (S \ G)).card*H.card := by
      dsimp only [y,B,C]
      exact_mod_cast triangles_change_xz R G S H
    calc
      _ ≤ _ := hc
      _ ≤ (2*F.card)*(δ*G.card)*H.card := by gcongr
      _ = _ := by ring
  have hz : z^2 ≤ 4*δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : z^2 ≤ (R.card : ℝ)*S.card*((H \ T) ∪ (T \ H)).card := by
      dsimp only [z,C,D]
      exact_mod_cast triangles_change_yz R S H T
    calc
      _ ≤ _ := hc
      _ ≤ (2*F.card)*(2*G.card)*(δ*H.card) := by gcongr
      _ = _ := by ring
  have htel : (((A \ D) ∪ (D \ A)).card : ℝ) ≤ x+y+z := by
    have h1 := card_symm_triangle A B D
    have h2 := card_symm_triangle B C D
    dsimp only [x,y,z]
    exact_mod_cast (show ((A \ D) ∪ (D \ A)).card ≤
      ((A \ B) ∪ (B \ A)).card + ((B \ C) ∪ (C \ B)).card +
        ((C \ D) ∪ (D \ C)).card by omega)
  exact htel.trans (three_step_error_le x y z δ _ (by dsimp [x]; positivity)
    (by dsimp [y]; positivity) (by dsimp [z]; positivity) hδ (by positivity) hx hy hz)

/-- A finite supported completion under the near-product square bound adds at most
 epsilon over two times the original volume; no identification of the two sets is made. -/
theorem completion_error_le {T : Type*} [DecidableEq T] (A S : Finset T)
    (hAS : A ⊆ S) (ε : ℝ) (he : 0 ≤ ε)
    (hsq : (S.card : ℝ)^2 ≤ (1+ε)*(A.card : ℝ)^2) :
    ((S \ A).card : ℝ) ≤ (ε/2)*A.card := by
  have hcard : (A.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hAS
  have hA : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  have hS : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have heA : 0 ≤ ε*(A.card : ℝ) := mul_nonneg he hA
  have htarget : (S.card : ℝ) ≤ (1+ε/2)*A.card := by
    have hsquare : (S.card : ℝ)^2 ≤ ((1+ε/2)*A.card)^2 := by
      nlinarith only [hsq, sq_nonneg (ε*(A.card : ℝ))]
    exact (sq_le_sq₀ hS (by positivity)).mp hsquare
  have hpartition : ((S \ A).card : ℝ) + A.card = S.card := by
    have hi : S ∩ A = A := Finset.inter_eq_right.mpr hAS
    have hcount := Finset.card_sdiff_add_card_inter S A
    rw [hi] at hcount
    exact_mod_cast hcount
  linarith

/-- Exact small-epsilon arithmetic, retaining the constant 143/14 before the endpoint 12. -/
theorem small_epsilon_constant (ε N P : ℝ) (he : 0 ≤ ε) (he4 : ε ≤ 1/4)
    (hN : 0 ≤ N) (hP : 0 ≤ P) (hprod : P ≤ (1+ε)*N^2) :
    (ε/2)*N + (31/7:ℝ)*Real.sqrt (4*ε)*Real.sqrt P ≤
      (143/14:ℝ)*Real.sqrt ε*N := by
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt ε)^2 = ε := Real.sq_sqrt he
  have hs_half : Real.sqrt ε ≤ 1/2 := by nlinarith only [hs, hs2, he4]
  have he_s : ε/2 ≤ Real.sqrt ε/4 := by nlinarith only [hs, hs2, hs_half]
  have hroot : Real.sqrt P ≤ (9/8:ℝ)*N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hmul := mul_le_mul_of_nonneg_right he4 (sq_nonneg N)
      nlinarith only [hprod, hmul, sq_nonneg N]
  have hfour : Real.sqrt (4*ε) = 2*Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [hfour]
  have hfirst := mul_le_mul_of_nonneg_right he_s hN
  have hsecond := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (31/7:ℝ)*(2*Real.sqrt ε) by positivity)
  nlinarith only [hfirst, hsecond]

example : let F : Finset (Fin 1 × Fin 1) := {(0,0)}
    F.Nonempty ∧ (0:ℝ) ≤ 1/4 ∧ (1/4:ℝ) ≤ 1 ∧
      (F.card : ℝ)*F.card*F.card ≤ (1+1/4:ℝ)*1^2 ∧
      (1:ℝ)^2 ≤ ((triangles F F F).card : ℝ)^2 := by
  norm_num [triangles]
  exact ⟨(0,0,0), by simp⟩

/-- The product of the three ordinary pair-projection sizes, each counted once. -/
def projectionProduct {I J K : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (A : Finset (I × J × K)) : ℕ :=
  (A.image (fun t => (t.1,t.2.1))).card *
    (A.image (fun t => (t.1,t.2.2))).card *
    (A.image (fun t => (t.2.1,t.2.2))).card

example : projectionProduct ({(1,2,3)} : Finset (ℤ × ℤ × ℤ)) = 1 := by decide
example : projectionProduct (∅ : Finset (ℤ × ℤ × ℤ)) = 0 := rfl

/-- Near equality in finite three-coordinate Loomis--Whitney gives a Cartesian box
 with literal symmetric-difference error at most twelve square-root epsilon times volume. -/
theorem near_box_finite {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (A : Finset (I × J × K)) (hA : A.Nonempty) (ε : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1)
    (hprod : (projectionProduct A : ℝ) ≤ (1+ε)*(A.card : ℝ)^2) :
    ∃ X : Finset I, ∃ Y : Finset J, ∃ Z : Finset K,
      (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
        12*Real.sqrt ε*A.card := by
  have hN : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  by_cases he4 : ε ≤ 1/4
  · let F := A.image (fun t => (t.1,t.2.1))
    let G := A.image (fun t => (t.1,t.2.2))
    let H := A.image (fun t => (t.2.1,t.2.2))
    let S := triangles F G H
    have hAS : A ⊆ S := by
      intro t ht
      exact (mem_triangles F G H t).mpr ⟨Finset.mem_image_of_mem _ ht,
        Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
    have hNS : (A.card : ℝ)^2 ≤ (S.card : ℝ)^2 := by
      exact_mod_cast Nat.pow_le_pow_left (Finset.card_le_card hAS) 2
    have hprod' : (F.card : ℝ)*G.card*H.card ≤ (1+ε)*(A.card : ℝ)^2 := by
      simpa only [projectionProduct, Nat.cast_mul] using hprod
    obtain ⟨U,U',V,V',W,W',hF,hG,hH⟩ := exists_three_rectangles F G H
      (hA.image _) (hA.image _) (hA.image _) A.card ε he.le hprod' hNS
    let B := (U ∩ U') ×ˢ ((V ∩ V') ×ˢ (W ∩ W'))
    have hSB : (((S \ B) ∪ (B \ S)).card : ℝ) ≤
        (31/7:ℝ)*Real.sqrt (4*ε)*Real.sqrt (projectionProduct A : ℝ) := by
      have hr := triangle_replacement_bound F (U ×ˢ V) G (U' ×ˢ W) H
        (V' ×ˢ W') (4*ε) (by positivity) (by linarith) hF hG hH
      rw [triangles_rectangles] at hr
      simpa only [S,B,projectionProduct,Nat.cast_mul] using hr
    have hSsq : (S.card : ℝ)^2 ≤ (1+ε)*(A.card : ℝ)^2 := by
      have hc : (S.card : ℝ)^2 ≤ (F.card : ℝ)*G.card*H.card := by
        exact_mod_cast card_triangles_sq_le F G H
      exact hc.trans hprod'
    have hcomplete := completion_error_le A S hAS ε he.le hSsq
    have hSA : ((A \ S) ∪ (S \ A)) = S \ A := by
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hAS, Finset.empty_union]
    have htel : (((A \ B) ∪ (B \ A)).card : ℝ) ≤
        ((S \ A).card : ℝ) + ((S \ B) ∪ (B \ S)).card := by
      have ht := card_symm_triangle A S B
      rw [hSA] at ht
      exact_mod_cast ht
    have hsmall := small_epsilon_constant ε A.card (projectionProduct A) he.le he4 hN
      (Nat.cast_nonneg _) hprod
    refine ⟨U ∩ U',V ∩ V',W ∩ W',?_⟩
    change (((A \ B) ∪ (B \ A)).card : ℝ) ≤ _
    have hrootN : 0 ≤ Real.sqrt ε * (A.card : ℝ) := mul_nonneg (Real.sqrt_nonneg _) hN
    linarith
  · obtain ⟨⟨i,j,k⟩,ht⟩ := hA
    refine ⟨{i},{j},{k},?_⟩
    have hbox : (({i} : Finset I) ×ˢ (({j} : Finset J) ×ˢ ({k} : Finset K))) = ({(i,j,k)} : Finset (I × J × K)) := by simp
    rw [hbox]
    have hsingle : ({(i,j,k)} : Finset (I × J × K)) ⊆ A := Finset.singleton_subset_iff.mpr ht
    have hs : (((A \ {(i,j,k)}) ∪ ({(i,j,k)} \ A)).card : ℝ) ≤ A.card := by
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsingle, Finset.union_empty]
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A \ {(i,j,k)} ⊆ A)
    have hroot : 1/2 ≤ Real.sqrt ε := by
      have hs2 := Real.sq_sqrt he.le
      have hs0 := Real.sqrt_nonneg ε
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hroot hN
    exact hs.trans (by linarith)

/-- Injective coordinate maps preserve all ordinary pair-projection sizes. -/
theorem projectionProduct_image {I J K I' J' K' : Type*}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [DecidableEq I'] [DecidableEq J'] [DecidableEq K']
    (A : Finset (I × J × K)) (f : I → I') (g : J → J') (h : K → K')
    (hf : Function.Injective f) (hg : Function.Injective g) (hh : Function.Injective h) :
    projectionProduct (A.image (Prod.map f (Prod.map g h))) = projectionProduct A := by
  have hxy : (A.image (Prod.map f (Prod.map g h))).image (fun t => (t.1,t.2.1)) =
      (A.image (fun t => (t.1,t.2.1))).image (Prod.map f g) := by
    simp only [Finset.image_image]
    rfl
  have hxz : (A.image (Prod.map f (Prod.map g h))).image (fun t => (t.1,t.2.2)) =
      (A.image (fun t => (t.1,t.2.2))).image (Prod.map f h) := by
    simp only [Finset.image_image]
    rfl
  have hyz : (A.image (Prod.map f (Prod.map g h))).image (fun t => (t.2.1,t.2.2)) =
      (A.image (fun t => (t.2.1,t.2.2))).image (Prod.map g h) := by
    simp only [Finset.image_image]
    rfl
  simp only [projectionProduct, hxy, hxz, hyz,
    Finset.card_image_of_injective _ (hf.prodMap hg),
    Finset.card_image_of_injective _ (hf.prodMap hh),
    Finset.card_image_of_injective _ (hg.prodMap hh)]

/-- Injective transport preserves the literal symmetric-difference cardinality. -/
theorem card_symm_image {T U : Type*} [DecidableEq T] [DecidableEq U]
    (A B : Finset T) (f : T → U) (hf : Function.Injective f) :
    ((A.image f \ B.image f) ∪ (B.image f \ A.image f)).card =
      ((A \ B) ∪ (B \ A)).card := by
  rw [← Finset.image_sdiff A B hf, ← Finset.image_sdiff B A hf,
    ← Finset.image_union, Finset.card_image_of_injective _ hf]

/-- For every nonempty finite integer triple set, near equality in ordinary
 Loomis--Whitney gives a finite box within twelve square-root epsilon times its size. -/
theorem near_box (A : Finset (ℤ × ℤ × ℤ)) (hA : A.Nonempty) (ε : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1)
    (hprod : (projectionProduct A : ℝ) ≤ (1+ε)*(A.card : ℝ)^2) :
    ∃ X Y Z : Finset ℤ,
      (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
        12*Real.sqrt ε*A.card := by
  let I := ↥(A.image (fun t => t.1))
  let J := ↥(A.image (fun t => t.2.1))
  let K := ↥(A.image (fun t => t.2.2))
  let f : I → ℤ := Subtype.val
  let g : J → ℤ := Subtype.val
  let h : K → ℤ := Subtype.val
  let q := Prod.map f (Prod.map g h)
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := Subtype.val_injective
  have hh : Function.Injective h := Subtype.val_injective
  have hq : Function.Injective q := hf.prodMap (hg.prodMap hh)
  let A' : Finset (I × J × K) := Finset.univ.filter (fun t => q t ∈ A)
  have him : A'.image q = A := by
    ext t
    constructor
    · intro ht
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hs).2
    · intro ht
      let s : I × J × K := (⟨t.1,Finset.mem_image_of_mem _ ht⟩,
        ⟨t.2.1,Finset.mem_image_of_mem _ ht⟩,⟨t.2.2,Finset.mem_image_of_mem _ ht⟩)
      exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩
  have hc : A'.card = A.card := by
    rw [← him, Finset.card_image_of_injective _ hq]
  have hp : projectionProduct A' = projectionProduct A := by
    exact (projectionProduct_image A' f g h hf hg hh).symm.trans
      (congrArg (fun B : Finset (ℤ × ℤ × ℤ) => projectionProduct B) him)
  have hA' : A'.Nonempty := by
    have hi : (A'.image q).Nonempty := him.symm ▸ hA
    exact Finset.image_nonempty.mp hi
  obtain ⟨X,Y,Z,hbox⟩ := near_box_finite A' hA' ε he he1 (by simpa only [hc,hp] using hprod)
  refine ⟨X.image f,Y.image g,Z.image h,?_⟩
  have hb : (X ×ˢ (Y ×ˢ Z)).image q = X.image f ×ˢ (Y.image g ×ˢ Z.image h) := by
    dsimp only [q]
    rw [Finset.prodMap_image_product, Finset.prodMap_image_product]
  have herr := card_symm_image A' (X ×ˢ (Y ×ˢ Z)) q hq
  rw [him,hb] at herr
  rw [herr,← hc]
  exact hbox

example : ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)).Nonempty ∧
    (0:ℝ) < 1/4 ∧ (1/4:ℝ) ≤ 1 ∧
    (projectionProduct ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) : ℝ) ≤
      (1+1/4:ℝ)*(({(0,0,0)} : Finset (ℤ × ℤ × ℤ)).card : ℝ)^2 := by
  norm_num [projectionProduct]

end ElementaryLoomisWhitneyStability
