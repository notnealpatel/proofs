import Erdos.Erdos132.TwoInteriorCircle
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos132.KnownFivePoint
open Erdos132.TwoInteriorCircle
open scoped RealInnerProductSpace

private theorem gram_plane (u v p q : Plane) :
    (⟪u,u⟫ * ⟪v,v⟫ - ⟪u,v⟫ ^ 2) * ⟪p,q⟫ =
      ⟪v,v⟫ * ⟪u,p⟫ * ⟪u,q⟫ -
      ⟪u,v⟫ * (⟪u,p⟫ * ⟪v,q⟫ + ⟪v,p⟫ * ⟪u,q⟫) +
      ⟪u,u⟫ * ⟪v,p⟫ * ⟪v,q⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    star_trivial, Pi.star_apply]
  ring

private theorem dist_sq (a b : Plane) :
    dist a b ^ 2 = ⟪a-b,a-b⟫ := by
  rw [dist_eq_norm, real_inner_self_eq_norm_sq]

private theorem inner_sub_sq (a b c : Plane) :
    2 * ⟪b-a,c-a⟫ = dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2 := by
  simp only [dist_sq, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

private theorem equilateral_pair_identity (a b c p q : Plane) (r : ℝ)
    (hr : 0 < r) (hab : dist a b = r) (hac : dist a c = r)
    (hbc : dist b c = r) :
    3*r^2*dist p q^2 = 3*r^2*(dist a p^2 + dist a q^2) -
      (2*(r^2+dist a p^2-dist b p^2)*(r^2+dist a q^2-dist b q^2) -
       (r^2+dist a p^2-dist b p^2)*(r^2+dist a q^2-dist c q^2) -
       (r^2+dist a p^2-dist c p^2)*(r^2+dist a q^2-dist b q^2) +
       2*(r^2+dist a p^2-dist c p^2)*(r^2+dist a q^2-dist c q^2)) := by
  have huu : ⟪b-a,b-a⟫ = r^2 := by
    rw [← dist_sq, dist_comm, hab]
  have hvv : ⟪c-a,c-a⟫ = r^2 := by
    rw [← dist_sq, dist_comm, hac]
  have huv : ⟪b-a,c-a⟫ = r^2/2 := by
    have h := inner_sub_sq a b c
    rw [hab, hac, hbc] at h
    linarith
  have hup : ⟪b-a,p-a⟫ = (r^2+dist a p^2-dist b p^2)/2 := by
    have h := inner_sub_sq a b p
    rw [hab] at h
    linarith
  have hvp : ⟪c-a,p-a⟫ = (r^2+dist a p^2-dist c p^2)/2 := by
    have h := inner_sub_sq a c p
    rw [hac] at h
    linarith
  have huq : ⟪b-a,q-a⟫ = (r^2+dist a q^2-dist b q^2)/2 := by
    have h := inner_sub_sq a b q
    rw [hab] at h
    linarith
  have hvq : ⟪c-a,q-a⟫ = (r^2+dist a q^2-dist c q^2)/2 := by
    have h := inner_sub_sq a c q
    rw [hac] at h
    linarith
  have hpq : ⟪p-a,q-a⟫ = (dist a p^2+dist a q^2-dist p q^2)/2 := by
    have h := inner_sub_sq a p q
    linarith
  have hgram := gram_plane (b-a) (c-a) (p-a) (q-a)
  rw [huu, hvv, huv, hup, hvp, huq, hvq, hpq] at hgram
  apply mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos hr))
  linear_combination -8 * hgram

private theorem normalized_pair_identity (a b c p q : Plane) (r : ℝ)
    (hr : 0 < r) (hab : dist a b = r) (hac : dist a c = r)
    (hbc : dist b c = r) :
    3*(dist p q^2/r^2) = 3*(dist a p^2/r^2 + dist a q^2/r^2) -
      (2*(1+dist a p^2/r^2-dist b p^2/r^2)*(1+dist a q^2/r^2-dist b q^2/r^2) -
       (1+dist a p^2/r^2-dist b p^2/r^2)*(1+dist a q^2/r^2-dist c q^2/r^2) -
       (1+dist a p^2/r^2-dist c p^2/r^2)*(1+dist a q^2/r^2-dist b q^2/r^2) +
       2*(1+dist a p^2/r^2-dist c p^2/r^2)*(1+dist a q^2/r^2-dist c q^2/r^2)) := by
  have h := equilateral_pair_identity a b c p q r hr hab hac hbc
  field_simp [ne_of_gt hr]
  linear_combination h

private theorem normalized_self_identity (a b c p : Plane) (r : ℝ)
    (hr : 0 < r) (hab : dist a b = r) (hac : dist a c = r)
    (hbc : dist b c = r) :
    3*(dist a p^2/r^2) = (1+dist a p^2/r^2-dist b p^2/r^2)^2 -
      (1+dist a p^2/r^2-dist b p^2/r^2)*(1+dist a p^2/r^2-dist c p^2/r^2) +
      (1+dist a p^2/r^2-dist c p^2/r^2)^2 := by
  have h := normalized_pair_identity a b c p p r hr hab hac hbc
  simp only [dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero] at h
  nlinarith only [h]

set_option maxHeartbeats 1000000 in
private theorem algebra (t pa pb pc qa qb qc pq : ℝ)
    (ht : 0 < t) (hne : t ≠ 1)
    (hpa : pa = 1 ∨ pa = t) (hpb : pb = 1 ∨ pb = t)
    (hpc : pc = 1 ∨ pc = t) (hqa : qa = 1 ∨ qa = t)
    (hqb : qb = 1 ∨ qb = t) (hqc : qc = 1 ∨ qc = t)
    (hpq : pq = 1 ∨ pq = t)
    (hp : 3*pa = (1+pa-pb)^2 - (1+pa-pb)*(1+pa-pc) + (1+pa-pc)^2)
    (hq : 3*qa = (1+qa-qb)^2 - (1+qa-qb)*(1+qa-qc) + (1+qa-qc)^2)
    (hpq' : 3*pq = 3*(pa+qa) - (2*(1+pa-pb)*(1+qa-qb) -
      (1+pa-pb)*(1+qa-qc) - (1+pa-pc)*(1+qa-qb) +
      2*(1+pa-pc)*(1+qa-qc))) : False := by
  have hsep : 0 < (t-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  rcases hpa with hpa | hpa <;> rcases hpb with hpb | hpb <;>
    rcases hpc with hpc | hpc <;> rcases hqa with hqa | hqa <;>
    rcases hqb with hqb | hqb <;> rcases hqc with hqc | hqc <;>
    rcases hpq with hpq | hpq <;>
    simp only [hpa, hpb, hpc, hqa, hqb, hqc, hpq] at hp hq hpq' <;>
    nlinarith

private theorem five_point_obstruction (a c d p q : Plane) (r b : ℝ)
    (hr : 0 < r) (hb : 0 < b) (hrb : r ≠ b)
    (hac : dist a c = r) (had : dist a d = r) (hcd : dist c d = r)
    (hap : dist a p = r ∨ dist a p = b)
    (hcp : dist c p = r ∨ dist c p = b)
    (hdp : dist d p = r ∨ dist d p = b)
    (haq : dist a q = r ∨ dist a q = b)
    (hcq : dist c q = r ∨ dist c q = b)
    (hdq : dist d q = r ∨ dist d q = b)
    (hpq : dist p q = r ∨ dist p q = b) : False := by
  let t := b^2/r^2
  have ht : 0 < t := div_pos (sq_pos_of_pos hb) (sq_pos_of_pos hr)
  have hne : t ≠ 1 := by
    intro he
    have he' : b^2 = r^2 := (div_eq_one_iff_eq (ne_of_gt (sq_pos_of_pos hr))).mp he
    apply hrb
    nlinarith
  have choice (x y : Plane) (h : dist x y = r ∨ dist x y = b) :
      dist x y^2/r^2 = 1 ∨ dist x y^2/r^2 = t := by
    rcases h with h | h
    · left
      rw [h, div_self (ne_of_gt (sq_pos_of_pos hr))]
    · right
      rw [h]
  exact algebra t _ _ _ _ _ _ _ ht hne
    (choice a p hap) (choice c p hcp) (choice d p hdp)
    (choice a q haq) (choice c q hcq) (choice d q hdq) (choice p q hpq)
    (normalized_self_identity a c d p r hr hac had hcd)
    (normalized_self_identity a c d q r hr hac had hcd)
    (normalized_pair_identity a c d p q r hr hac had hcd)

/-- Five planar points with two positive distinct allowed distances contain no
three distinct members forming an equilateral triangle of the first distance. -/
theorem no_equilateral_triangle_of_two_distances (X : Finset Plane) (hX : X.card = 5)
    (r b : ℝ) (hr : 0 < r) (hb : 0 < b) (hrb : r ≠ b)
    (hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = r ∨ dist x y = b)
    (a c d : Plane) (ha : a ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d) :
    ¬ (dist a c = r ∧ dist a d = r ∧ dist c d = r) := by
  classical
  intro htriangle
  let T : Finset Plane := {a,c,d}
  have hT : T.card = 3 := by simp [T, hac, had, hcd]
  have hsub : T ⊆ X := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hc
    · exact hd
  have hleft : (X \ T).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsub, hX, hT]
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (X \ T).card)
  have hpX := (Finset.mem_sdiff.mp hp).1
  have hqX := (Finset.mem_sdiff.mp hq).1
  have hpn : p ≠ a ∧ p ≠ c ∧ p ≠ d := by
    simpa [T] using (Finset.mem_sdiff.mp hp).2
  have hqn : q ≠ a ∧ q ≠ c ∧ q ≠ d := by
    simpa [T] using (Finset.mem_sdiff.mp hq).2
  exact five_point_obstruction a c d p q r b hr hb hrb
    htriangle.1 htriangle.2.1 htriangle.2.2
    (hallowed a ha p hpX hpn.1.symm)
    (hallowed c hc p hpX hpn.2.1.symm)
    (hallowed d hd p hpX hpn.2.2.symm)
    (hallowed a ha q hqX hqn.1.symm)
    (hallowed c hc q hqX hqn.2.1.symm)
    (hallowed d hd q hqX hqn.2.2.symm)
    (hallowed p hpX q hqX hpq)

private theorem no_three_common (v w a b c : Plane) (r : ℝ)
    (hvw : v ≠ w) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hav : dist a v = r) (hbv : dist b v = r) (hcv : dist c v = r)
    (haw : dist a w = r) (hbw : dist b w = r) (hcw : dist c w = r) : False := by
  classical
  have h := radial_card_le_two {a,b,c} v w r r (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hav
    · exact hbv
    · exact hcv) hvw.symm
  have he : ({a,b,c} : Finset Plane).filter (fun x => dist x w = r) = {a,b,c} := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haw
    · exact hbw
    · exact hcw
  rw [he] at h
  have hcard : ({a,b,c} : Finset Plane).card = 3 := by simp [hab, hac, hbc]
  omega

private theorem boole_le_one (P : Prop) [Decidable P] :
    (if P then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega

private theorem three_bound (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (h : ¬ (P ∧ Q ∧ R)) :
    (if P then 1 else 0 : ℕ) + (if Q then 1 else 0) + (if R then 1 else 0) ≤ 2 := by
  split_ifs <;> simp_all

private theorem six_bound (P Q R S T U : Prop)
    [Decidable P] [Decidable Q] [Decidable R] [Decidable S] [Decidable T] [Decidable U]
    (h : ¬ (P ∧ Q ∧ R ∧ S ∧ T ∧ U)) :
    (if P then 1 else 0 : ℕ) + (if Q then 1 else 0) + (if R then 1 else 0) +
    (if S then 1 else 0) + (if T then 1 else 0) + (if U then 1 else 0) ≤ 5 := by
  split_ifs <;> simp_all

private theorem pairs_five (a b c d e : Plane) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e) :
    pairs ({a,b,c,d,e} : Finset Plane) = {s(a,b), s(a,c), s(a,d), s(a,e), s(b,c), s(b,d), s(b,e), s(c,d), s(c,e), s(d,e)} := by
  classical
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  ext z
  induction z using Sym2.ind with
  | _ x y =>
    simp only [mk_mem_pairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    aesop

set_option maxHeartbeats 2000000 in
private theorem multiplicity_five (a b c d e : Plane) (r : ℝ) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e) :
    multiplicity ({a,b,c,d,e} : Finset Plane) r =
      (if dist a b = r then 1 else 0) + (if dist a c = r then 1 else 0) + (if dist a d = r then 1 else 0) + (if dist a e = r then 1 else 0) + (if dist b c = r then 1 else 0) + (if dist b d = r then 1 else 0) + (if dist b e = r then 1 else 0) + (if dist c d = r then 1 else 0) + (if dist c e = r then 1 else 0) + (if dist d e = r then 1 else 0) := by
  classical
  rw [TwoInteriorCircle.multiplicity, pairs_five a b c d e h, Finset.card_filter]
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, eq_self_iff_true, and_true, true_and, and_false, false_and, or_false, false_or, not_false_eq_true, add_assoc, Sym2.eq_iff, pairDist_mk, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, h01.symm, h02.symm, h03.symm, h04.symm, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm]
  rfl

private theorem graph_bound (e01 : ℕ) (e02 : ℕ) (e03 : ℕ) (e04 : ℕ) (e12 : ℕ) (e13 : ℕ) (e14 : ℕ) (e23 : ℕ) (e24 : ℕ) (e34 : ℕ)
    (he01 : e01 ≤ 1)
    (he02 : e02 ≤ 1)
    (he03 : e03 ≤ 1)
    (he04 : e04 ≤ 1)
    (he12 : e12 ≤ 1)
    (he13 : e13 ≤ 1)
    (he14 : e14 ≤ 1)
    (he23 : e23 ≤ 1)
    (he24 : e24 ≤ 1)
    (he34 : e34 ≤ 1)
    (ht012 : e01 + e02 + e12 ≤ 2)
    (ht013 : e01 + e03 + e13 ≤ 2)
    (ht014 : e01 + e04 + e14 ≤ 2)
    (ht023 : e02 + e03 + e23 ≤ 2)
    (ht024 : e02 + e04 + e24 ≤ 2)
    (ht034 : e03 + e04 + e34 ≤ 2)
    (ht123 : e12 + e13 + e23 ≤ 2)
    (ht124 : e12 + e14 + e24 ≤ 2)
    (ht134 : e13 + e14 + e34 ≤ 2)
    (ht234 : e23 + e24 + e34 ≤ 2)
    (hk01 : e02 + e03 + e04 + e12 + e13 + e14 ≤ 5)
    (hk02 : e01 + e03 + e04 + e12 + e23 + e24 ≤ 5)
    (hk03 : e01 + e02 + e04 + e13 + e23 + e34 ≤ 5)
    (hk04 : e01 + e02 + e03 + e14 + e24 + e34 ≤ 5)
    (hk12 : e01 + e13 + e14 + e02 + e23 + e24 ≤ 5)
    (hk13 : e01 + e12 + e14 + e03 + e23 + e34 ≤ 5)
    (hk14 : e01 + e12 + e13 + e04 + e24 + e34 ≤ 5)
    (hk23 : e02 + e12 + e24 + e03 + e13 + e34 ≤ 5)
    (hk24 : e02 + e12 + e23 + e04 + e14 + e34 ≤ 5)
    (hk34 : e03 + e13 + e23 + e04 + e14 + e24 ≤ 5)
    : e01 + e02 + e03 + e04 + e12 + e13 + e14 + e23 + e24 + e34 ≤ 5 := by
  by_cases h0 : e01 + e02 + e03 + e04 ≤ 2
  · by_cases h1 : e01 + e12 + e13 + e14 ≤ 2
    · by_cases h2 : e02 + e12 + e23 + e24 ≤ 2
      · by_cases h3 : e03 + e13 + e23 + e34 ≤ 2
        · by_cases h4 : e04 + e14 + e24 + e34 ≤ 2
          · omega
          · interval_cases e04 <;> interval_cases e14 <;> interval_cases e24 <;> interval_cases e34 <;> omega
        · interval_cases e03 <;> interval_cases e13 <;> interval_cases e23 <;> interval_cases e34 <;> omega
      · interval_cases e02 <;> interval_cases e12 <;> interval_cases e23 <;> interval_cases e24 <;> omega
    · interval_cases e01 <;> interval_cases e12 <;> interval_cases e13 <;> interval_cases e14 <;> omega
  · interval_cases e01 <;> interval_cases e02 <;> interval_cases e03 <;> interval_cases e04 <;> omega

private theorem multiplicity_le_five_of_no_triangle (X : Finset Plane) (hX : X.card = 5)
    (r : ℝ)
    (ht : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
      ¬ (dist a b = r ∧ dist a c = r ∧ dist b c = r)) :
    multiplicity X r ≤ 5 := by
  classical
  obtain ⟨a, Y, ha, hXY, hY⟩ := Finset.card_eq_succ.mp hX
  obtain ⟨b, c, d, e, h12, h13, h14, h23, h24, h34, hYe⟩ := Finset.card_eq_four.mp hY
  subst Y
  have han : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e := by simpa using ha
  rcases han with ⟨h01,h02,h03,h04⟩
  have hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have hm (x : Plane) (hx : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) : x ∈ X := by
    rw [← hXY]
    simpa using hx
  have hmem : a ∈ X ∧ b ∈ X ∧ c ∈ X ∧ d ∈ X ∧ e ∈ X := by
    rw [← hXY]
    simp
  rcases hmem with ⟨haX,hbX,hcX,hdX,heX⟩
  have tri (x y z : Plane) (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (if dist x y = r then 1 else 0 : ℕ) + (if dist x z = r then 1 else 0) +
      (if dist y z = r then 1 else 0) ≤ 2 :=
    three_bound _ _ _ (ht x hx y hy z hz hxy hxz hyz)
  have common (v w x y z : Plane) (hvw : v ≠ w)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (if dist v x = r then 1 else 0 : ℕ) + (if dist v y = r then 1 else 0) +
      (if dist v z = r then 1 else 0) + (if dist w x = r then 1 else 0) +
      (if dist w y = r then 1 else 0) + (if dist w z = r then 1 else 0) ≤ 5 := by
    apply six_bound
    rintro ⟨hxv,hyv,hzv,hxw,hyw,hzw⟩
    exact no_three_common v w x y z r hvw hxy hxz hyz
      (by simpa only [dist_comm] using hxv) (by simpa only [dist_comm] using hyv)
      (by simpa only [dist_comm] using hzv) (by simpa only [dist_comm] using hxw)
      (by simpa only [dist_comm] using hyw) (by simpa only [dist_comm] using hzw)
  rw [← hXY, multiplicity_five a b c d e r hdist]
  apply graph_bound
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact boole_le_one _
  · exact tri a b c haX hbX hcX h01 h02 h12
  · exact tri a b d haX hbX hdX h01 h03 h13
  · exact tri a b e haX hbX heX h01 h04 h14
  · exact tri a c d haX hcX hdX h02 h03 h23
  · exact tri a c e haX hcX heX h02 h04 h24
  · exact tri a d e haX hdX heX h03 h04 h34
  · exact tri b c d hbX hcX hdX h12 h13 h23
  · exact tri b c e hbX hcX heX h12 h14 h24
  · exact tri b d e hbX hdX heX h13 h14 h34
  · exact tri c d e hcX hdX heX h23 h24 h34
  · simpa only [dist_comm] using common a b c d e h01 h23 h24 h34
  · simpa only [dist_comm] using common a c b d e h02 h13 h14 h34
  · simpa only [dist_comm] using common a d b c e h03 h12 h14 h24
  · simpa only [dist_comm] using common a e b c d h04 h12 h13 h23
  · simpa only [dist_comm] using common b c a d e h12 h03 h04 h34
  · simpa only [dist_comm] using common b d a c e h13 h02 h04 h24
  · simpa only [dist_comm] using common b e a c d h14 h02 h03 h23
  · simpa only [dist_comm] using common c d a b e h23 h01 h04 h14
  · simpa only [dist_comm] using common c e a b d h24 h01 h03 h13
  · simpa only [dist_comm] using common d e a b c h34 h01 h02 h12

private theorem no_one_distance (X : Finset Plane) (hX : X.card = 5) (r : ℝ)
    (h : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = r) : False := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < X.card by omega)
  let H := X \ {a,b}
  have hsub : ({a,b} : Finset Plane) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcard : H.card = 3 := by
    rw [Finset.card_sdiff_of_subset hsub, hX]
    simp [hab]
  have hcircle : ∀ x ∈ H, dist x a = r := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact h x hx'.1 a ha (by intro hxa; exact hx'.2 (by simp [hxa]))
  have hfilter : H.filter (fun x => dist x b = r) = H := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact h x hx'.1 b hb (by intro hxb; exact hx'.2 (by simp [hxb]))
  have hbound := radial_card_le_two H a b r r hcircle hab.symm
  rw [hfilter, hcard] at hbound
  omega

private theorem positive_occurring (X : Finset Plane) (r : ℝ)
    (hr : r ∈ (pairs X).image pairDist) : 0 < r := by
  classical
  obtain ⟨z,hz,hzr⟩ := Finset.mem_image.mp hr
  subst r
  induction z using Sym2.ind with
  | _ a b =>
    exact dist_pos.mpr (mk_mem_pairs X a b |>.mp hz).2.2

private theorem multiplicity_pos_of_occurring (X : Finset Plane) (r : ℝ)
    (hr : r ∈ (pairs X).image pairDist) : 1 ≤ multiplicity X r := by
  classical
  obtain ⟨z,hz,hzr⟩ := Finset.mem_image.mp hr
  exact Finset.one_le_card.mpr ⟨z, Finset.mem_filter.mpr ⟨hz,hzr⟩⟩

private theorem multiplicity_add_le_ten (X : Finset Plane) (hX : X.card = 5)
    (r b : ℝ) (hrb : r ≠ b) : multiplicity X r + multiplicity X b ≤ 10 := by
  classical
  let A := (pairs X).filter (fun z => pairDist z = r)
  let B := (pairs X).filter (fun z => pairDist z = b)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    exact hrb ((Finset.mem_filter.mp hzA).2.symm.trans (Finset.mem_filter.mp hzB).2)
  have hsub : A ∪ B ⊆ pairs X := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, card_pairs, hX] at hcard
  exact hcard

/-- Every five-point set in the ordinary Euclidean plane has two distinct positive
occurring distances, each occurring among at most five unordered pairs. -/
theorem exists_two_low_multiplicity_distances (X : Finset Plane) (hX : X.card = 5) :
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ 0 < d₁ ∧ 0 < d₂ ∧
      (∃ e₁ ∈ pairs X, pairDist e₁ = d₁) ∧
      (∃ e₂ ∈ pairs X, pairDist e₂ = d₂) ∧
      1 ≤ multiplicity X d₁ ∧ multiplicity X d₁ ≤ 5 ∧
      1 ≤ multiplicity X d₂ ∧ multiplicity X d₂ ≤ 5 := by
  classical
  let D := (pairs X).image pairDist
  let G := D.filter (fun r => multiplicity X r ≤ 5)
  have hG : 1 < G.card := by
    by_contra hsmall
    have hg : G.card ≤ 1 := by omega
    have hb : (D.filter (fun r => ¬ multiplicity X r ≤ 5)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro r hr b hb
      by_contra hrb
      have hsum := multiplicity_add_le_ten X hX r b hrb
      have hr' := (Finset.mem_filter.mp hr).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    have hpartition := Finset.card_filter_add_card_filter_not (s := D)
      (fun r => multiplicity X r ≤ 5)
    have hD : D.card ≤ 2 := by change G.card + _ = D.card at hpartition; omega
    have hDne : D.Nonempty := by
      have hp : (pairs X).Nonempty := Finset.card_pos.mp (by rw [card_pairs,hX]; decide)
      exact hp.image pairDist
    have hDtwo : D.card = 2 := by
      by_contra hn
      have hDsmall : D.card ≤ 1 := by omega
      obtain ⟨r,hr⟩ := hDne
      apply no_one_distance X hX r
      intro x hx y hy hxy
      apply Finset.card_le_one.mp hDsmall
      · exact Finset.mem_image.mpr ⟨s(x,y), (mk_mem_pairs X x y).mpr ⟨hx,hy,hxy⟩, rfl⟩
      · exact hr
    obtain ⟨r,b,hrb,hDb⟩ := Finset.card_eq_two.mp hDtwo
    have hrD : r ∈ D := by rw [hDb]; simp
    have hbD : b ∈ D := by rw [hDb]; simp
    have hrpos := positive_occurring X r hrD
    have hbpos := positive_occurring X b hbD
    have hallowed : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = r ∨ dist x y = b := by
      intro x hx y hy hxy
      have hm : dist x y ∈ D :=
        Finset.mem_image.mpr ⟨s(x,y), (mk_mem_pairs X x y).mpr ⟨hx,hy,hxy⟩, rfl⟩
      rw [hDb] at hm
      simpa using hm
    have hrbound : multiplicity X r ≤ 5 :=
      multiplicity_le_five_of_no_triangle X hX r
        (fun x hx y hy z hz => no_equilateral_triangle_of_two_distances X hX r b hrpos hbpos hrb hallowed x y z hx hy hz)
    have hallowed' : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dist x y = b ∨ dist x y = r := by
      intro x hx y hy hxy
      exact (hallowed x hx y hy hxy).symm
    have hbbound : multiplicity X b ≤ 5 :=
      multiplicity_le_five_of_no_triangle X hX b
        (fun x hx y hy z hz => no_equilateral_triangle_of_two_distances X hX b r hbpos hrpos hrb.symm hallowed' x y z hx hy hz)
    have hrG : r ∈ G := Finset.mem_filter.mpr ⟨hrD,hrbound⟩
    have hbG : b ∈ G := Finset.mem_filter.mpr ⟨hbD,hbbound⟩
    exact hrb (Finset.card_le_one.mp hg r hrG b hbG)
  obtain ⟨r,hr,b,hb,hrb⟩ := Finset.one_lt_card.mp hG
  have hrD := (Finset.mem_filter.mp hr).1
  have hbD := (Finset.mem_filter.mp hb).1
  exact ⟨r,b,hrb,positive_occurring X r hrD,positive_occurring X b hbD,
    Finset.mem_image.mp hrD,Finset.mem_image.mp hbD,
    multiplicity_pos_of_occurring X r hrD,(Finset.mem_filter.mp hr).2,
    multiplicity_pos_of_occurring X b hbD,(Finset.mem_filter.mp hb).2⟩

end Erdos132.KnownFivePoint
