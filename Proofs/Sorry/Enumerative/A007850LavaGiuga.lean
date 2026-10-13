/-
# A007850 — compatibility façade for Lava's Giuga conjecture

Source: OEIS A007850, Paolo P. Lava's comment (Nov 16 2009):
"Giuga numbers are the solution of the differential equation n' = n + 1,
where n' is the arithmetic derivative of n."
J. M. Grau and A. M. Oller-Marcén, *Giuga numbers and the arithmetic derivative*,
arXiv:1103.2298, characterize Giuga numbers by `n' = a*n + 1` with `0 < a`.

The arithmetic derivative, Giuga predicate, proven implication, and numeral
witnesses are canonical in `NumberComplexity.GiugaDerivative`. The genuinely
open converse (that the multiplier is always one) and its dependent equivalence
are archived in `Sorry.NumberComplexity.GiugaDerivative`. This façade preserves
the historical `Candidates.A007850` API; it does not certify the conjecture.
-/
import Sorry.NumberComplexity.GiugaDerivative
import NumberComplexity.GiugaCharacterization

set_option autoImplicit false

namespace Candidates.A007850

/-- Compatibility alias for the canonical arithmetic derivative (A003415). -/
abbrev ad := GiugaDerivative.ad

/-- Compatibility alias for the canonical Giuga-number predicate (A007850). -/
abbrev IsGiuga := GiugaDerivative.IsGiuga

/-- Lava's equivalence for `1 < n`; depends on the archived open converse. -/
theorem lava_giuga_iff (n : ℕ) (hn : 1 < n) : IsGiuga n ↔ ad n = n + 1 :=
  GiugaDerivative.lava_conjecture n

/-- The proven direction: `n' = n + 1` implies that `n` is a Giuga number. -/
theorem isGiuga_of_ad_eq_succ (n : ℕ) (hn : 1 < n) (h : ad n = n + 1) : IsGiuga n :=
  GiugaDerivative.isGiuga_of_ad_eq_succ h

/-- The genuinely open converse: every Giuga number satisfies `n' = n + 1`.
This wrapper depends on the canonical archive's admission, not a proof. -/
theorem ad_eq_succ_of_isGiuga (n : ℕ) (h : IsGiuga n) : ad n = n + 1 :=
  GiugaDerivative.ad_eq_succ_of_isGiuga h

/-- Grau–Oller-Marcén's characterization with a positive multiplier,
proved by reuse of the canonical characterization theorem. -/
theorem grauRibas_isGiuga_iff (n : ℕ) (hn : 1 < n) :
    IsGiuga n ↔ ∃ a : ℕ, 0 < a ∧ ad n = a * n + 1 :=
  GiugaDerivative.grauRibas_isGiuga_iff n hn

/-- The arithmetic derivative of a prime is one. -/
theorem ad_prime {p : ℕ} (hp : p.Prime) : ad p = 1 :=
  GiugaDerivative.ad_prime hp

/-- The Leibniz rule for positive coprime inputs. -/
theorem ad_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    ad (m * n) = ad m * n + m * ad n :=
  GiugaDerivative.ad_mul_coprime (Nat.ne_of_gt hm) (Nat.ne_of_gt hn) h

/-- Every prime in the derivative's summation support divides `n`, so its
natural-number division by that prime is exact. -/
theorem ad_eq_sum_of_dvd (n : ℕ) :
    ∀ p ∈ n.primeFactors, p ∣ n := by
  intro p hp
  exact Nat.dvd_of_mem_primeFactors hp

/-- Giuga numbers are squarefree, proved by reuse of the canonical structural theorem. -/
theorem isGiuga_squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n :=
  GiugaDerivative.isGiuga_squarefree h

-- Ground truth for the aliases and joint satisfiability of the API hypotheses.
example : ad = GiugaDerivative.ad := rfl
example : IsGiuga = GiugaDerivative.IsGiuga := rfl
example : ad 0 = 0 := GiugaDerivative.ad_zero
example : ad 1 = 0 := GiugaDerivative.ad_one
example : ad 2 = 1 := GiugaDerivative.ad_prime (by norm_num)
example : 1 < 30 ∧ IsGiuga 30 ∧ ad 30 = 30 + 1 :=
  ⟨by norm_num, GiugaDerivative.isGiuga_30, GiugaDerivative.ad_30⟩
example : ad 858 = 859 := GiugaDerivative.ad_858
example : ad 1722 = 1723 := GiugaDerivative.ad_1722
example : IsGiuga 858 ∧ IsGiuga 1722 :=
  ⟨GiugaDerivative.isGiuga_858, GiugaDerivative.isGiuga_1722⟩
example : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.Coprime m n :=
  ⟨2, 3, by norm_num, by norm_num, by norm_num⟩
example : ∃ a : ℕ, 0 < a ∧ ad 30 = a * 30 + 1 :=
  ⟨1, by norm_num, by simpa using GiugaDerivative.ad_30⟩

end Candidates.A007850
