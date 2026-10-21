/-
# Erdős–Heilbronn conjecture over `ZMod p`
  (Dias da Silva–Hamidoune; Alon–Nathanson–Ruzsa)

Date: 2026-10-21.

## Source

* Conjectured by P. Erdős and H. Heilbronn (1964).
* J. A. Dias da Silva, Y. O. Hamidoune, "Cyclic spaces for Grassmann
  derivatives and additive theory", Bull. London Math. Soc. 26 (1994)
  140–146 (first proof, via exterior algebra).
* N. Alon, M. B. Nathanson, I. Ruzsa, "Adding distinct congruence classes
  modulo a prime", Amer. Math. Monthly 102 (1995) 250–255, Theorem 1.1
  (the polynomial method proof formalized here, including the |A| ≠ |B|
  version).
* N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8
  (1999), §4 (Theorem 4.1 and its proof).

## Informal statement (verbatim from the target specification)

  For a prime p and nonempty A, B ⊆ ZMod p with |A| ≠ |B|, the restricted
  sumset A ∔ B = {a+b : a∈A, b∈B, a≠b} satisfies |A ∔ B| ≥ min(p, |A|+|B|−2).
  In particular |A ∔ A| ≥ min(p, 2|A|−3).

## Formalization

* `restrictedSumset A B` is the `Finset` image of `(a, b) ↦ a + b` over the
  off-diagonal part of `A ×ˢ B`; Mathlib has no restricted sumset.  It agrees
  pointwise with the repository's `Set`-valued `Erdos880.restrictedSumset`
  (`Proofs/Erdos/Erdos880/RestrictedSumset.lean`), via `mem_restrictedSumset`.
* `min_le_card_restrictedSumset_of_card_ne` : the |A| ≠ |B| statement.
* `erdos_heilbronn` : |A ∔ A| ≥ min(p, 2|A| − 3), under `2 ≤ |A|` (for
  |A| ≤ 1 the informal bound is nonpositive; the hypothesis only keeps the
  natural-number subtraction off truncation).
* Proof: Alon's Combinatorial Nullstellensatz
  (`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`) applied to
  `(x − y) · ∏_{c ∈ A ∔ B} (x + y − c)`, whose coefficient at `x^i y^j`
  (`i + j = |A ∔ B| + 1`) is `C(m, i−1) − C(m, i)`, nonzero mod `p` when
  `i ≠ j` and `m = |A ∔ B| < p` (`anr_core`).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosHeilbronnRestrictedSumset

open MvPolynomial Finsupp Finset

/-- The *restricted sumset* `A ∔ B = {a + b : a ∈ A, b ∈ B, a ≠ b}`. -/
def restrictedSumset {α : Type*} [DecidableEq α] [Add α] (A B : Finset α) : Finset α :=
  ((A ×ˢ B).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)

/-- Membership in the restricted sumset. -/
theorem mem_restrictedSumset {α : Type*} [DecidableEq α] [Add α] {A B : Finset α} {c : α} :
    c ∈ restrictedSumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a + b = c := by
  simp only [restrictedSumset, mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
    exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩

/-- The exponent of the monomial `x^i y^j` in two variables. -/
noncomputable abbrev expo (i j : ℕ) : Fin 2 →₀ ℕ := single 0 i + single 1 j

/-- Exponents `x^i y^j` are determined by `(i, j)`. -/
theorem expo_eq_iff {i j k l : ℕ} : expo k l = expo i j ↔ k = i ∧ l = j := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Coefficient of `x^i y^j` in the monomial `x^k y^l`. -/
theorem coeff_X_pow_mul_X_pow {R : Type*} [CommRing R] (i j k l : ℕ) :
    coeff (expo i j) (X 0 ^ k * X 1 ^ l : MvPolynomial (Fin 2) R) =
      if k = i ∧ l = j then 1 else 0 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, coeff_monomial, one_mul]
  exact if_congr expo_eq_iff rfl rfl

/-- Coefficient of `x^i y^j` (with `i + j = m + 1`) in `(x - y) (x + y)^m`:
it is `C(m, i - 1) - C(m, i)`, with the convention `C(m, -1) = 0`. -/
theorem coeff_sub_mul_add_pow {R : Type*} [CommRing R] (m i j : ℕ) (hij : i + j = m + 1) :
    coeff (expo i j) ((X 0 - X 1) * (X 0 + X 1) ^ m : MvPolynomial (Fin 2) R) =
      (if 1 ≤ i then (m.choose (i - 1) : R) else 0) - m.choose i := by
  rw [add_pow, Finset.mul_sum, coeff_sum]
  have key : ∀ k ∈ range (m + 1),
      coeff (expo i j) ((X 0 - X 1) * (X 0 ^ k * X 1 ^ (m - k) *
        ((m.choose k : ℕ) : MvPolynomial (Fin 2) R))) =
      (if k + 1 = i then (m.choose k : R) else 0) - (if k = i then (m.choose k : R) else 0) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hexp : (X 0 - X 1) * (X 0 ^ k * X 1 ^ (m - k) *
        ((m.choose k : ℕ) : MvPolynomial (Fin 2) R)) =
        (m.choose k) • (X 0 ^ (k + 1) * X 1 ^ (m - k)) -
          (m.choose k) • (X 0 ^ k * X 1 ^ (m - k + 1)) := by
      simp only [nsmul_eq_mul]
      ring
    rw [hexp, coeff_sub, coeff_smul, coeff_smul, coeff_X_pow_mul_X_pow, coeff_X_pow_mul_X_pow]
    have c1 : (k + 1 = i ∧ m - k = j) ↔ k + 1 = i := by omega
    have c2 : (k = i ∧ m - k + 1 = j) ↔ k = i := by omega
    simp only [c1, c2]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  congr 1
  · rcases i with _ | i
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega)), if_pos (by omega),
        Nat.add_sub_cancel]
  · split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by rw [Finset.mem_range] at h; omega)]
      simp

/-- For a prime `p`, `C(m, k) ≢ 0 (mod p)` whenever `k ≤ m < p`. -/
theorem choose_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] {m k : ℕ} (hk : k ≤ m) (hm : m < p) :
    (m.choose k : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hfac : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk, mul_assoc]
    exact Dvd.dvd.mul_right h _
  exact absurd ((Nat.Prime.dvd_factorial hp.out).mp hfac) (by omega)

/-- The Alon–Nathanson–Ruzsa coefficient `C(m, i - 1) - C(m, i)` (with `C(m, -1) = 0`)
is nonzero in `ZMod p` when `i + j = m + 1`, `i ≠ j`, and `i, j, m < p`. -/
theorem anr_coeff_ne_zero {p : ℕ} [hp : Fact p.Prime] {m i j : ℕ} (hij : i + j = m + 1)
    (hne : i ≠ j) (hi : i < p) (hj : j < p) (hm : m < p) :
    (if 1 ≤ i then (m.choose (i - 1) : ZMod p) else 0) - m.choose i ≠ 0 := by
  rcases i with _ | i
  · simp
  · rw [if_pos (by omega), Nat.add_sub_cancel]
    intro h
    have hrec : ((m.choose (i + 1) : ℕ) : ZMod p) * ((i + 1 : ℕ) : ZMod p) =
        (m.choose i : ZMod p) * (j : ZMod p) := by
      have hnat := Nat.choose_succ_right_eq m i
      rw [show m - i = j by omega] at hnat
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) hnat
      push_cast at hcast ⊢
      exact hcast
    have hij' : ((i + 1 : ℕ) : ZMod p) ≠ (j : ZMod p) := by
      rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact hne
    have hc : (m.choose i : ZMod p) ≠ 0 := choose_ne_zero_zmod (by omega) hm
    have heq : (m.choose i : ZMod p) = m.choose (i + 1) := sub_eq_zero.mp h
    rw [← heq] at hrec
    exact hij' (mul_left_cancel₀ hc hrec)

/-- The polynomial `(x - y) (x + y)^k` is homogeneous of degree `k + 1`. -/
theorem isHomogeneous_sub_mul_add_pow {R : Type*} [CommRing R] (k : ℕ) :
    ((X 0 - X 1) * (X 0 + X 1) ^ k : MvPolynomial (Fin 2) R).IsHomogeneous (k + 1) := by
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
    (isHomogeneous_X R 0).sub (isHomogeneous_X R 1)
  have h2 : (X 0 + X 1 : MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
    (isHomogeneous_X R 0).add (isHomogeneous_X R 1)
  have h3 := h1.mul (h2.pow k)
  rwa [one_mul, Nat.add_comm 1 k] at h3

/-- **Alon–Nathanson–Ruzsa core.** Over `ZMod p`, if `m = |A ∔ B| < p`, there are no
`i < |A|`, `j < |B|` with `i + j = m + 1` and `i ≠ j`. -/
theorem anr_core {p : ℕ} [hp : Fact p.Prime] (A B : Finset (ZMod p)) {i j : ℕ}
    (hi : i < #A) (hj : j < #B) (hij : i + j = #(restrictedSumset A B) + 1) (hne : i ≠ j)
    (hm : #(restrictedSumset A B) < p) : False := by
  set C := restrictedSumset A B with hC
  set m := #C with hmdef
  let Q : Polynomial (ZMod p) := ∏ c ∈ C, (Polynomial.X - Polynomial.C c)
  have hQmonic : Q.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)
  have hQdeg : Q.natDegree = m := by
    simp [Q, Polynomial.natDegree_prod_of_monic, Polynomial.monic_X_sub_C, hmdef]
  let h : ℕ → MvPolynomial (Fin 2) (ZMod p) := fun k => (X 0 - X 1) * (X 0 + X 1) ^ k
  let f : MvPolynomial (Fin 2) (ZMod p) :=
    (X 0 - X 1) * Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) Q
  have hcoeff : ∀ d, coeff d f = ∑ k ∈ range (m + 1), Q.coeff k * coeff d (h k) := by
    intro d
    simp only [f, h, Polynomial.aeval_eq_sum_range, hQdeg, Finset.mul_sum, coeff_sum,
      mul_smul_comm, coeff_smul, smul_eq_mul]
  have hdeg_le : f.totalDegree ≤ m + 1 := by
    rw [totalDegree]
    apply Finset.sup_le
    intro d hd
    by_contra hlt
    apply (MvPolynomial.mem_support_iff.mp hd)
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [(isHomogeneous_sub_mul_add_pow (R := ZMod p) k).coeff_eq_zero, mul_zero]
    rw [Finsupp.degree_apply]
    simp only [Finsupp.sum] at hlt
    omega
  set t := expo i j with ht
  have htdeg : t.degree = m + 1 := by
    simp [t, hij]
  have hcoeff_t : coeff t f = coeff t (h m) := by
    rw [hcoeff, Finset.sum_eq_single m]
    · rw [← hQdeg, hQmonic.coeff_natDegree, one_mul]
    · intro k _ hkm
      rw [(isHomogeneous_sub_mul_add_pow (R := ZMod p) k).coeff_eq_zero, mul_zero]
      omega
    · intro hmem
      exact absurd (Finset.self_mem_range_succ m) hmem
  have hA : #A ≤ p := by simpa using Finset.card_le_univ A
  have hB : #B ≤ p := by simpa using Finset.card_le_univ B
  have hft : coeff t f ≠ 0 := by
    rw [hcoeff_t]
    simp only [h, t]
    rw [coeff_sub_mul_add_pow m i j hij]
    exact anr_coeff_ne_zero hij hne (by omega) (by omega) hm
  have htot : f.totalDegree = t.degree := by
    apply le_antisymm (htdeg ▸ hdeg_le)
    have hle := le_totalDegree (MvPolynomial.mem_support_iff.mpr hft)
    rw [Finsupp.degree_apply]
    exact hle
  obtain ⟨s, hs, hev⟩ := combinatorial_nullstellensatz_exists_eval_nonzero f t hft htot ![A, B]
    (by
      intro k
      fin_cases k
      · simpa [t] using hi
      · simpa [t] using hj)
  apply hev
  have hs0 : s 0 ∈ A := by simpa using hs 0
  have hs1 : s 1 ∈ B := by simpa using hs 1
  simp only [f, map_mul]
  by_cases hab : s 0 = s 1
  · simp [hab]
  · have hmem : s 0 + s 1 ∈ C := mem_restrictedSumset.mpr ⟨s 0, hs0, s 1, hs1, hab, rfl⟩
    have hQ : Q.eval (s 0 + s 1) = 0 := by
      simp only [Q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact Finset.prod_eq_zero hmem (sub_self _)
    have hev2 : eval s (Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) Q) =
        Q.eval (s 0 + s 1) := by
      have key := Polynomial.aeval_algHom_apply
        (MvPolynomial.aeval s : MvPolynomial (Fin 2) (ZMod p) →ₐ[ZMod p] ZMod p) (X 0 + X 1) Q
      simpa [MvPolynomial.coe_aeval_eq_eval] using key.symm
    rw [hev2, hQ, mul_zero]

/-- **Erdős–Heilbronn for distinct sizes** (Alon–Nathanson–Ruzsa 1995).
For a prime `p` and nonempty `A, B ⊆ ZMod p` with `|A| ≠ |B|`,
`|A ∔ B| ≥ min(p, |A| + |B| - 2)`. (Nonemptiness keeps the natural-number
subtraction off its truncation: `|A| + |B| ≥ 2`.) -/
theorem min_le_card_restrictedSumset_of_card_ne {p : ℕ} [Fact p.Prime] {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) (hne : #A ≠ #B) :
    min p (#A + #B - 2) ≤ #(restrictedSumset A B) := by
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨hmp, hmab⟩ := hlt
  have ha := hA.card_pos
  have hb := hB.card_pos
  set m := #(restrictedSumset A B) with hm
  by_cases h1 : min (#A - 1) (m + 1) ≠ m + 1 - min (#A - 1) (m + 1)
  · exact anr_core A B (i := min (#A - 1) (m + 1)) (j := m + 1 - min (#A - 1) (m + 1))
      (by omega) (by omega) (by omega) h1 hmp
  · exact anr_core A B (i := m + 1 - min (#B - 1) (m + 1)) (j := min (#B - 1) (m + 1))
      (by omega) (by omega) (by omega) (by omega) hmp

/-- **Erdős–Heilbronn conjecture** (Dias da Silva–Hamidoune 1994; Alon–Nathanson–Ruzsa 1995).
For a prime `p` and `A ⊆ ZMod p` with `|A| ≥ 2`, the set `A ∔ A` of sums of two distinct
elements of `A` satisfies `|A ∔ A| ≥ min(p, 2|A| - 3)`. (For `|A| ≤ 1` the informal bound
is `≤ 0` and trivial; the hypothesis `2 ≤ |A|` keeps `2|A| - 3` off natural-number
truncation.) -/
theorem erdos_heilbronn {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)} (hA : 2 ≤ #A) :
    min p (2 * #A - 3) ≤ #(restrictedSumset A A) := by
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨hmp, hmaa⟩ := hlt
  set m := #(restrictedSumset A A) with hm
  exact anr_core A A (i := min (#A - 1) (m + 1)) (j := m + 1 - min (#A - 1) (m + 1))
    (by omega) (by omega) (by omega) (by omega) hmp

/-! ## Ground truth and satisfiability -/

/-- `{0,1,2} ∔ {0,1,2} = {1,2,3}` in `ZMod 7`: the Erdős–Heilbronn bound `2·3 - 3 = 3`
is attained by an arithmetic progression. -/
example : restrictedSumset ({0, 1, 2} : Finset (ZMod 7)) {0, 1, 2} = {1, 2, 3} := by decide

/-- The diagonal `a = b` is excluded: `{0,1} ∔ {0,1} = {1}`, while `{0,1} + {0,1} = {0,1,2}`. -/
example : restrictedSumset ({0, 1} : Finset (ZMod 5)) {0, 1} = {1} := by decide

/-- Asymmetric case: `{0} ∔ {0,1,2} = {1,2}` in `ZMod 5`, of size `1 + 3 - 2 = 2`. -/
example : restrictedSumset ({0} : Finset (ZMod 5)) {0, 1, 2} = {1, 2} := by decide

/-- In `ZMod 3`, `{0,1,2} ∔ {0,1,2} = ZMod 3`, so the `min` with `p` is active. -/
example : restrictedSumset ({0, 1, 2} : Finset (ZMod 3)) {0, 1, 2} = {0, 1, 2} := by decide

/-- The hypotheses of `min_le_card_restrictedSumset_of_card_ne` are jointly satisfiable. -/
example : min 5 (#({0} : Finset (ZMod 5)) + #({0, 1, 2} : Finset (ZMod 5)) - 2) ≤
    #(restrictedSumset ({0} : Finset (ZMod 5)) {0, 1, 2}) :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  min_le_card_restrictedSumset_of_card_ne (by decide) (by decide) (by decide)

/-- The hypothesis of `erdos_heilbronn` is satisfiable. -/
example : min 7 (2 * #({0, 1, 2} : Finset (ZMod 7)) - 3) ≤
    #(restrictedSumset ({0, 1, 2} : Finset (ZMod 7)) {0, 1, 2}) :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  erdos_heilbronn (by decide)

end ErdosHeilbronnRestrictedSumset
