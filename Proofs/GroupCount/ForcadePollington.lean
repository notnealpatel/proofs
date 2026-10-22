/-
# Forcade–Pollington: a group carrying an injective group map on `{1, …, k}` is abelian

## Source

J. M. Campbell, *Group maps on initial intervals*, arXiv:2610.12087 (October 2026),
Section 2, Lemmas 1–4 and Theorems 1–2.

A group map `φ : {1, …, k} → G` is injective and satisfies
`φ(ab) = φ(a) φ(b)` whenever `a`, `b`, and `ab` lie in the interval.
The Forcade–Pollington conjecture (1990) says that a group of positive
order `k` admitting such a map is abelian. This module proves the claim
uniformly for every `1 ≤ k`. Campbell's Theorem 2 uses an unpublished
bound of Hickerson, reported by Guy, for `k < 20`; the proof here does
not use that bound.

## Proof route (a uniform variant of the paper's argument)

Choose `t` with `t (t - 1) ≤ k < t (t + 1)` (stated without subtraction as
`t * t ≤ k + t` and `k < t * t + t`).  Distinct `a, b ≤ t` satisfy `ab ≤ k`, so the
elements `φ 1, …, φ t` pairwise commute and `H := ⟨φ 1, …, φ t⟩` is abelian (paper,
Lemmas 1–2).  The paper then injects coprime pairs `(a, b)` with `a ≤ t`, `b ≤ t - 1`
into `H` by `(a, b) ↦ φ a (φ b)⁻¹` (Lemma 3) and counts them (Lemma 4, `t ≥ 5`).

Here we compose the paper's encoding `F_t(x, y) = (r + (δ - 1) s, s)` (`δ = gcd(x, y)`,
`x = δ r`, `y = δ s`) directly with `(u, v) ↦ φ u (φ v)⁻¹`, on the triangle
`Δ_t = {1 ≤ x ≤ y ≤ t}` when `t² ≤ k`, and on `Δ_t \ {(t, t)}` when `k < t²`.  The only
encoded pair with first coordinate `t` is `F_t(t, t) = (t, 1)`, so all cross products
`u v'` that occur are `≤ k`; this gives an injection into `H` of a set of size
`> k / 2`, hence `H = G` by Lagrange.  This avoids the paper's case `t ≥ 5` and the
appeal to Hickerson for `k < 20`.
-/
import Mathlib

set_option autoImplicit false

namespace GroupCount.ForcadePollington

/-! ## Definitions -/

/-- A *group map* on the initial interval `{1, …, k}` (Forcade–Pollington 1990, as in
Campbell, arXiv:2610.12087, §2): `φ` is injective on `{1, …, k}` and
`φ (a * b) = φ a * φ b` whenever `a`, `b` and `a * b` lie in `{1, …, k}`.  Values of `φ`
outside `{1, …, k}` are irrelevant. -/
def IsGroupMap {G : Type*} [Group G] (k : ℕ) (φ : ℕ → G) : Prop :=
  Set.InjOn φ (Set.Icc 1 k) ∧
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a * b ≤ k → φ (a * b) = φ a * φ b

/-- The paper's encoding `F_t(x, y) = (r + (δ - 1) s, s)` where `δ = gcd(x, y)`,
`x = δ r`, `y = δ s` (Campbell, proof of Lemma 4). -/
def encode (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 / Nat.gcd p.1 p.2 + (Nat.gcd p.1 p.2 - 1) * (p.2 / Nat.gcd p.1 p.2),
    p.2 / Nat.gcd p.1 p.2)

/-- The triangle `Δ_t = {(x, y) : 1 ≤ x ≤ y ≤ t}` (Campbell, proof of Lemma 4). -/
def triangle (t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 t ×ˢ Finset.Icc 1 t).filter (fun p => p.1 ≤ p.2)

/-! ## Examples -/

example : encode (2, 4) = (3, 2) := by decide
example : encode (6, 6) = (6, 1) := by decide
example : encode (2, 3) = (2, 3) := by decide
example : (triangle 3).card = 6 := by decide

/-- The explicit group map `1 ↦ 0, 2 ↦ 1, 3 ↦ 3, 4 ↦ 2` into `ℤ/4` (written
multiplicatively). -/
def zmodFourMap (n : ℕ) : Multiplicative (ZMod 4) :=
  Multiplicative.ofAdd (([0, 0, 1, 3, 2] : List (ZMod 4)).getD n 0)

/-- The hypotheses of the main theorem are jointly satisfiable: `ℤ/4` carries a group map
on `{1, 2, 3, 4}`. -/
example : IsGroupMap (Nat.card (Multiplicative (ZMod 4))) zmodFourMap := by
  have hcard : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [hcard]
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    obtain ⟨ha1, ha4⟩ := ha
    obtain ⟨hb1, hb4⟩ := hb
    interval_cases a <;> interval_cases b <;> first | rfl | exact absurd hab (by decide)
  · intro a b ha hb hab
    have ha4 : a ≤ 4 := by nlinarith
    have hb4 : b ≤ 4 := by nlinarith
    interval_cases a <;> interval_cases b <;> first | omega | decide

/-- Non-example: the Klein four-group `ℤ/2 × ℤ/2` carries no group map on `{1, …, 4}`,
since `φ 4 = φ 2 ^ 2 = 1 = φ 1`. -/
example (φ : ℕ → Multiplicative (ZMod 2 × ZMod 2)) : ¬ IsGroupMap 4 φ := by
  rintro ⟨hinj, hmul⟩
  have h1 : φ 1 = 1 := by
    have h := hmul 1 1 le_rfl le_rfl (by norm_num)
    simpa using h
  have h4 : φ 4 = 1 := by
    have h := hmul 2 2 (by norm_num) (by norm_num) (by norm_num)
    rw [show (2 : ℕ) * 2 = 4 by norm_num] at h
    rw [h]
    generalize φ 2 = g
    revert g
    decide
  have h14 : (1 : ℕ) = 4 :=
    hinj (show (1 : ℕ) ∈ Set.Icc 1 4 by simp) (show (4 : ℕ) ∈ Set.Icc 1 4 by simp)
      (h1.trans h4.symm)
  omega

/-! ## The encoding `F_t` -/

/-- Normal form of a pair `1 ≤ x ≤ y`: with `δ = d + 1 = gcd(x, y)`, `x = δ r`, `y = δ s`,
`1 ≤ r ≤ s`, `gcd(r, s) = 1`, and `encode (x, y) = (r + d s, s)`. -/
lemma encode_spec {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∃ d r s : ℕ, x = (d + 1) * r ∧ y = (d + 1) * s ∧ 1 ≤ r ∧ r ≤ s ∧ Nat.Coprime r s ∧
      encode (x, y) = (r + d * s, s) := by
  have hgpos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
  have hg1 : Nat.gcd x y - 1 + 1 = Nat.gcd x y := Nat.sub_add_cancel hgpos
  refine ⟨Nat.gcd x y - 1, x / Nat.gcd x y, y / Nat.gcd x y, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [hg1, Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)]
  · rw [hg1, Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)]
  · exact Nat.div_pos (Nat.le_of_dvd hx (Nat.gcd_dvd_left x y)) hgpos
  · exact Nat.div_le_div_right hxy
  · exact Nat.coprime_div_gcd_div_gcd hgpos

/-- Euclidean-division uniqueness: `r + d s = r' + d' s` with `1 ≤ r, r' ≤ s` forces
`d = d'` and `r = r'`. -/
lemma param_unique {d r s d' r' : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hr' : 1 ≤ r')
    (hrs' : r' ≤ s) (h : r + d * s = r' + d' * s) : d = d' ∧ r = r' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · have hle : (d + 1) * s ≤ d' * s := Nat.mul_le_mul_right s hlt
    nlinarith
  · subst heq
    exact ⟨rfl, by omega⟩
  · have hle : (d' + 1) * s ≤ d * s := Nat.mul_le_mul_right s hgt
    nlinarith

/-- `F_t` is injective on pairs `1 ≤ x ≤ y` (Campbell, proof of Lemma 4). -/
lemma encode_injOn {x y x' y' : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hx' : 1 ≤ x')
    (hxy' : x' ≤ y') (h : encode (x, y) = encode (x', y')) : (x, y) = (x', y') := by
  obtain ⟨d, r, s, rfl, rfl, hr, hrs, -, he⟩ := encode_spec hx hxy
  obtain ⟨d', r', s', rfl, rfl, hr', hrs', -, he'⟩ := encode_spec hx' hxy'
  rw [he, he', Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := param_unique hr hrs hr' hrs' h1
  rfl

/-- Bounds and coprimality of `F_t(x, y) = (u, v)`: `1 ≤ u ≤ y`, `1 ≤ v ≤ y`,
`gcd(u, v) = 1`. -/
lemma encode_bounds {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    1 ≤ (encode (x, y)).1 ∧ (encode (x, y)).1 ≤ y ∧ 1 ≤ (encode (x, y)).2 ∧
      (encode (x, y)).2 ≤ y ∧ Nat.Coprime (encode (x, y)).1 (encode (x, y)).2 := by
  obtain ⟨d, r, s, -, rfl, hr, hrs, hcop, he⟩ := encode_spec hx hxy
  rw [he]
  refine ⟨by omega, by nlinarith, by omega, by nlinarith, ?_⟩
  exact (Nat.coprime_add_mul_right_left r s d).mpr hcop

/-- The first coordinate of `F_t(x, y)` equals `y` only on the diagonal: then `x = y`. -/
lemma encode_fst_eq {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (h : (encode (x, y)).1 = y) :
    x = y := by
  obtain ⟨d, r, s, rfl, rfl, hr, hrs, hcop, he⟩ := encode_spec hx hxy
  rw [he] at h
  have hrs' : r = s := by
    simp only at h
    nlinarith
  subst hrs'
  have hr1 : r = 1 := (Nat.coprime_self r).mp hcop
  subst hr1
  rfl

/-! ## The triangle `Δ_t` -/

/-- `|Δ_t| = t (t + 1) / 2`, stated as `2 |Δ_t| = t * t + t`. -/
lemma two_mul_card_triangle (t : ℕ) : 2 * (triangle t).card = t * t + t := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hsplit : triangle (t + 1) =
        triangle t ∪ (Finset.Icc 1 (t + 1)).image (fun x => (x, t + 1)) := by
      ext ⟨x, y⟩
      simp only [triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hx1, hxt⟩, hy1, hyt⟩, hxy⟩
        by_cases hy : y = t + 1
        · exact Or.inr ⟨x, ⟨hx1, by omega⟩, rfl, hy.symm⟩
        · exact Or.inl ⟨⟨⟨hx1, by omega⟩, hy1, by omega⟩, hxy⟩
      · rintro (⟨⟨⟨hx1, hxt⟩, hy1, hyt⟩, hxy⟩ | ⟨z, ⟨hz1, hzt⟩, rfl, rfl⟩)
        · exact ⟨⟨⟨hx1, by omega⟩, hy1, by omega⟩, hxy⟩
        · exact ⟨⟨⟨hz1, hzt⟩, by omega, le_rfl⟩, hzt⟩
    have hdisj : Disjoint (triangle t) ((Finset.Icc 1 (t + 1)).image (fun x => (x, t + 1))) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hp hq
      simp only [triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_image, Prod.mk.injEq] at hp hq
      omega
    have himg : ((Finset.Icc 1 (t + 1)).image (fun x => (x, t + 1))).card = t + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)]
      simp
    rw [hsplit, Finset.card_union_of_disjoint hdisj, himg]
    nlinarith

/-! ## The parameter `t` -/

/-- For every `k` there is `t` with `t (t - 1) ≤ k < t (t + 1)`, stated subtraction-free. -/
lemma exists_param (k : ℕ) : ∃ t : ℕ, t * t ≤ k + t ∧ k < t * t + t := by
  induction k with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨t, h1, h2⟩ := ih
    by_cases hlt : k + 1 < t * t + t
    · exact ⟨t, by omega, hlt⟩
    · exact ⟨t + 1, by nlinarith, by nlinarith⟩

/-- If `t (t - 1) ≤ k`, `a ≤ t` and `b < t`, then `a b ≤ k`. -/
lemma mul_le_of_le_of_lt {t k a b : ℕ} (ht : t * t ≤ k + t) (ha : a ≤ t) (hb : b < t) :
    a * b ≤ k := by
  have h1 : a * b ≤ t * b := Nat.mul_le_mul_right b ha
  have h2 : t * (b + 1) ≤ t * t := Nat.mul_le_mul_left t hb
  nlinarith

/-! ## Group-theoretic steps -/

section GroupSteps

variable {G : Type*} [Group G]

/-- Campbell, Lemma 1: if `a b ≤ k` then `φ a` and `φ b` commute. -/
lemma IsGroupMap.mul_comm_of_mul_le {k : ℕ} {φ : ℕ → G} (hφ : IsGroupMap k φ) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ k) : φ a * φ b = φ b * φ a := by
  rw [← hφ.2 a b ha hb hab, ← hφ.2 b a hb ha (by rwa [Nat.mul_comm]), Nat.mul_comm]

/-- Campbell, Lemma 2 (generators): the elements `φ 1, …, φ t` pairwise commute when
`t (t - 1) ≤ k`. -/
lemma IsGroupMap.pairwise_comm {k t : ℕ} {φ : ℕ → G} (hφ : IsGroupMap k φ)
    (ht : t * t ≤ k + t) :
    ∀ g ∈ φ '' Set.Icc 1 t, ∀ h ∈ φ '' Set.Icc 1 t, g * h = h * g := by
  rintro _ ⟨a, ⟨ha1, hat⟩, rfl⟩ _ ⟨b, ⟨hb1, hbt⟩, rfl⟩
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact hφ.mul_comm_of_mul_le ha1 hb1 (by rw [Nat.mul_comm]; exact mul_le_of_le_of_lt ht hbt (hlt.trans_le hbt))
  · rfl
  · exact hφ.mul_comm_of_mul_le ha1 hb1 (mul_le_of_le_of_lt ht hat (hgt.trans_le hat))

/-- Campbell, Lemma 3 (rearranged): if `φ u (φ v)⁻¹ = φ u' (φ v')⁻¹` with `u, v, u', v'` in
`{1, …, t}`, `gcd(u, v) = gcd(u', v') = 1` and both cross products `u v'`, `u' v` at most
`k`, then `(u, v) = (u', v')`. -/
lemma IsGroupMap.eq_of_mul_inv_eq {k t : ℕ} {φ : ℕ → G} (hφ : IsGroupMap k φ)
    (ht : t * t ≤ k + t) {u v u' v' : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : 1 ≤ u')
    (hv' : 1 ≤ v') (hvt : v ≤ t) (hvt' : v' ≤ t) (hcop : Nat.Coprime u v)
    (hcop' : Nat.Coprime u' v') (hk1 : u * v' ≤ k) (hk2 : u' * v ≤ k)
    (h : φ u * (φ v)⁻¹ = φ u' * (φ v')⁻¹) : u = u' ∧ v = v' := by
  have hc : φ v * φ v' = φ v' * φ v :=
    hφ.pairwise_comm ht _ ⟨v, ⟨hv, hvt⟩, rfl⟩ _ ⟨v', ⟨hv', hvt'⟩, rfl⟩
  have hcross : φ (u * v') = φ (u' * v) := by
    rw [hφ.2 u v' hu hv' hk1, hφ.2 u' v hu' hv hk2]
    calc φ u * φ v' = (φ u * (φ v)⁻¹) * (φ v * φ v') := by group
      _ = (φ u' * (φ v')⁻¹) * (φ v' * φ v) := by rw [h, hc]
      _ = φ u' * φ v := by group
  have hnat : u * v' = u' * v :=
    hφ.1 ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hk1⟩
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hk2⟩ hcross
  have hdvd1 : u ∣ u' := hcop.dvd_of_dvd_mul_right ⟨v', hnat.symm⟩
  have hdvd2 : u' ∣ u := hcop'.dvd_of_dvd_mul_right ⟨v, hnat⟩
  have huu : u = u' := Nat.dvd_antisymm hdvd1 hdvd2
  subst huu
  exact ⟨rfl, (Nat.eq_of_mul_eq_mul_left (by omega) hnat).symm⟩

end GroupSteps

/-! ## Main theorem -/

/-- Membership in the triangle `Δ_t`. -/
lemma mem_triangle {t : ℕ} {p : ℕ × ℕ} : p ∈ triangle t ↔ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ t := by
  simp only [triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **Forcade–Pollington conjecture** (Forcade–Pollington 1990; proved by Campbell,
arXiv:2610.12087, Theorem 2, there relying on Hickerson's bound for `|G| < 20`): if a
finite group `G` of order `k` admits a group map `φ` on `{1, …, k}` — injective on
`{1, …, k}`, with `φ (a b) = φ a φ b` whenever `a`, `b`, `a b ∈ {1, …, k}` — then `G` is
abelian.  The proof here is self-contained for every `k`. -/
theorem forcade_pollington {G : Type*} [Group G] [Finite G] (φ : ℕ → G)
    (hφ : IsGroupMap (Nat.card G) φ) (x y : G) : x * y = y * x := by
  classical
  set k := Nat.card G with hk
  have hk1 : 1 ≤ k := Nat.card_pos
  obtain ⟨t, ht1, ht2⟩ := exists_param k
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; omega
    · exact h
  set S : Set G := φ '' Set.Icc 1 t with hS
  set H : Subgroup G := Subgroup.closure S with hH
  have hcomm := hφ.pairwise_comm ht1
  -- The domain: `Δ_t` if `t² ≤ k`, and `Δ_t \ {(t, t)}` otherwise.
  let D : Finset (ℕ × ℕ) := if t * t ≤ k then triangle t else (triangle t).erase (t, t)
  have hDsub : ∀ p ∈ D, p ∈ triangle t := by
    intro p hp
    dsimp only [D] at hp
    split_ifs at hp
    · exact hp
    · exact Finset.mem_of_mem_erase hp
  have hDdiag : ∀ p ∈ D, p = (t, t) → t * t ≤ k := by
    intro p hp hpt
    dsimp only [D] at hp
    split_ifs at hp with h
    · exact h
    · subst hpt; simp at hp
  have hDcard : k < 2 * D.card := by
    have htri := two_mul_card_triangle t
    dsimp only [D]
    split_ifs with h
    · omega
    · have hmem : (t, t) ∈ triangle t := mem_triangle.mpr ⟨htpos, le_rfl, le_rfl⟩
      rw [Finset.card_erase_of_mem hmem]
      have ht2' : 2 ≤ t := by
        by_contra hlt
        have : t = 1 := by omega
        subst this; omega
      generalize t * t = T at h htri ht2
      have hc : 1 ≤ (triangle t).card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
  -- Every cross product of encoded coordinates stays within `{1, …, k}`.
  have hcross : ∀ p ∈ D, ∀ q ∈ D, (encode p).1 * (encode q).2 ≤ k := by
    intro p hp q hq
    obtain ⟨hp1, hp2, hp3⟩ := mem_triangle.mp (hDsub p hp)
    obtain ⟨hq1, hq2, hq3⟩ := mem_triangle.mp (hDsub q hq)
    obtain ⟨-, hu, -, hv, -⟩ := encode_bounds hp1 hp2
    obtain ⟨-, -, -, hv', -⟩ := encode_bounds hq1 hq2
    rcases Nat.lt_or_ge (encode q).2 t with hvlt | hvge
    · exact mul_le_of_le_of_lt ht1 (hu.trans hp3) hvlt
    · rcases Nat.lt_or_ge (encode p).1 t with hult | huge
      · rw [Nat.mul_comm]; exact mul_le_of_le_of_lt ht1 (hv'.trans hq3) hult
      · have hut : (encode p).1 = t := le_antisymm (hu.trans hp3) huge
        have hvt : (encode q).2 = t := le_antisymm (hv'.trans hq3) hvge
        have hy : p.2 = t := le_antisymm hp3 (hut ▸ hu)
        have hx : p.1 = p.2 := encode_fst_eq hp1 hp2 (by rw [hut, hy])
        have hpt : p = (t, t) := Prod.ext (hx.trans hy) hy
        rw [hut, hvt]
        exact hDdiag p hp hpt
  -- The injection `Δ_t ⊇ D → H`, `p ↦ φ u (φ v)⁻¹` with `(u, v) = F_t p`.
  let Φ : ℕ × ℕ → G := fun p => φ (encode p).1 * (φ (encode p).2)⁻¹
  have hmemS : ∀ n, 1 ≤ n → n ≤ t → φ n ∈ H := fun n h1 h2 =>
    Subgroup.subset_closure ⟨n, ⟨h1, h2⟩, rfl⟩
  have hmem : ∀ p ∈ (D : Set (ℕ × ℕ)), Φ p ∈ (H : Set G) := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_triangle.mp (hDsub p hp)
    obtain ⟨hu1, hu, hv1, hv, -⟩ := encode_bounds hp1 hp2
    exact H.mul_mem (hmemS _ hu1 (hu.trans hp3)) (H.inv_mem (hmemS _ hv1 (hv.trans hp3)))
  have hinj : Set.InjOn Φ (D : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, hp3⟩ := mem_triangle.mp (hDsub p hp)
    obtain ⟨hq1, hq2, hq3⟩ := mem_triangle.mp (hDsub q hq)
    obtain ⟨hu1, -, hv1, hv, hcop⟩ := encode_bounds hp1 hp2
    obtain ⟨hu1', -, hv1', hv', hcop'⟩ := encode_bounds hq1 hq2
    obtain ⟨h1, h2⟩ := hφ.eq_of_mul_inv_eq ht1 hu1 hv1 hu1' hv1' (hv.trans hp3)
      (hv'.trans hq3) hcop hcop' (hcross p hp q hq) (hcross q hq p hp) hpq
    have henc : encode (p.1, p.2) = encode (q.1, q.2) := Prod.ext h1 h2
    exact encode_injOn hp1 hp2 hq1 hq2 henc
  have hcardH : D.card ≤ Nat.card H := by
    rw [← Set.ncard_coe_finset, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard_of_injOn Φ hmem hinj (Set.toFinite _)
  -- Lagrange: a subgroup of order `> k / 2` is all of `G`.
  have htop : H = ⊤ := by
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card H
    have heq : Nat.card H = k := by
      rcases m with _ | _ | m
      · omega
      · omega
      · nlinarith
    exact (Subgroup.card_eq_iff_eq_top H).mp heq
  have hxH : x ∈ H := htop ▸ Subgroup.mem_top x
  have hyH : y ∈ H := htop ▸ Subgroup.mem_top y
  exact Set.centralizer_centralizer_comm_of_comm hcomm x
    (Subgroup.closure_le_centralizer_centralizer S hxH) y
    (Subgroup.closure_le_centralizer_centralizer S hyH)

end GroupCount.ForcadePollington
