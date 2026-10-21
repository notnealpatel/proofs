/-
# Fuchs' problem for p-groups: characteristics admitting a 2-group of units

## Source

arXiv:1901.10081, Sunil K. Chebolu and Keir Lockridge, "Fuchs' problem for
p-groups".  Section 3 ("Rings of odd characteristic"), Theorem 3.1
(`\label{2fchar}`), restated in the introduction as Theorem 1.1 (1) ⇔ (2).

Verbatim (Theorem 3.1):

  Let $n$ be a positive integer. The following statements are equivalent.
  (1) A $2$-group is realizable in characteristic $n$.
  (2) The positive integer $n$ is of the form $2^ap_1p_2 \cdots p_k$ where the
      $p_i$'s are distinct Fermat primes, $a \ge 0$ and $k \ge 0$.
  (3) It is possible to construct a regular $n$-gon with straightedge and
      compass.

Here "$G$ is realizable in characteristic $n$" means $G \cong R^\times$ for
some ring $R$ of characteristic $n$, and a $2$-group is a group in which every
element has order a power of $2$ (Mathlib's `IsPGroup 2`).

## Status

Proved in the paper (elementary argument: `(ZMod n)ˣ` embeds in `Rˣ`, and
`ZMod n` itself is the witness).  Recorded 2026-10-21.  Item (3) is the
Gauss–Wantzel theorem and is not formalized here; we formalize (1) ⇔ (2) with
(2) expressed through the prime factorization of `n`, together with the
number-theoretic equivalence "`φ n` is a power of `2`" that underlies
Gauss–Wantzel, and the Fermat-number form of the odd prime factors.
-/
import Mathlib

set_option autoImplicit false

namespace GroupCount.FuchsProblemTwoGroupUnits

/-- The paper's condition (2) in factorization form: every odd prime `p`
dividing `n` divides it exactly once and is of the form `2 ^ k + 1`. -/
def FermatShape (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 → ¬ p ^ 2 ∣ n ∧ ∃ k : ℕ, p = 2 ^ k + 1

/-- `FermatShape 60` holds: `60 = 2 ^ 2 * 3 * 5` with `3 = 2 + 1` and
`5 = 2 ^ 2 + 1` (a regular 60-gon is constructible). -/
example : FermatShape 60 := by
  intro p hp hpn hp2
  have hp60 : p ≤ 60 := Nat.le_of_dvd (by norm_num) hpn
  interval_cases p <;> (try exact absurd rfl hp2) <;> (try (exfalso; revert hpn; decide)) <;>
    (try (exfalso; revert hp; decide))
  · exact ⟨by decide, 1, rfl⟩
  · exact ⟨by decide, 2, rfl⟩

/-- `FermatShape 9` fails: `3 ^ 2 ∣ 9`. -/
example : ¬ FermatShape 9 := fun h =>
  (h 3 Nat.prime_three (by norm_num) (by norm_num)).1 (by norm_num)

/-- `FermatShape 7` fails: `7` is not of the form `2 ^ k + 1`. -/
example : ¬ FermatShape 7 := by
  intro h
  obtain ⟨k, hk⟩ := (h 7 (by norm_num) dvd_rfl (by norm_num)).2
  have h6 : 2 ^ k = 6 := by omega
  have hk3 : k < 3 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at h6

/-- Forward number theory: if `φ n` is a power of `2`, then every odd prime
divisor `p` of `n` satisfies `p ^ 2 ∤ n` and `p = 2 ^ k + 1`. -/
theorem fermatShape_of_totient_eq_two_pow {n m : ℕ} (h : n.totient = 2 ^ m) :
    FermatShape n := by
  intro p hp hpn hp2
  refine ⟨?_, ?_⟩
  · intro hsq
    have hdvd : (p ^ 2).totient ∣ 2 ^ m := h ▸ Nat.totient_dvd_of_dvd hsq
    rw [Nat.totient_prime_pow hp (by norm_num), pow_one] at hdvd
    have hp_dvd : p ∣ 2 ^ m := (Dvd.intro _ rfl).trans hdvd
    have hp_two : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp_two)
  · have hdvd : p.totient ∣ 2 ^ m := h ▸ Nat.totient_dvd_of_dvd hpn
    rw [Nat.totient_prime hp] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, by have := hp.two_le; omega⟩

/-- Backward number theory: if `n ≠ 0` has Fermat shape, then `φ n` is a
power of `2`. -/
theorem exists_totient_eq_two_pow_of_fermatShape {n : ℕ} (hn : n ≠ 0)
    (h : FermatShape n) : ∃ m : ℕ, n.totient = 2 ^ m := by
  rw [Nat.totient_eq_prod_factorization hn]
  refine Finset.prod_induction _ (fun x => ∃ m : ℕ, x = 2 ^ m) ?_ ⟨0, rfl⟩ ?_
  · rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (pow_add 2 i j).symm⟩
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpn, -⟩ := hp
    by_cases hp2 : p = 2
    · subst hp2
      exact ⟨n.factorization 2 - 1, by simp⟩
    · obtain ⟨hsq, k, hk⟩ := h p hpp hpn hp2
      have hpos : 0 < n.factorization p := hpp.factorization_pos_of_dvd hn hpn
      have hle : n.factorization p < 2 := by
        by_contra hcon
        exact hsq ((hpp.pow_dvd_iff_le_factorization hn).2 (by omega))
      have hone : n.factorization p = 1 := by omega
      refine ⟨k, ?_⟩
      rw [hone, hk]
      simp

/-- Gauss–Wantzel, number-theoretic half: for `n > 0`, `φ n` is a power of `2`
iff every odd prime `p ∣ n` has `p ^ 2 ∤ n` and `p = 2 ^ k + 1`. -/
theorem exists_totient_eq_two_pow_iff {n : ℕ} (hn : 0 < n) :
    (∃ m : ℕ, n.totient = 2 ^ m) ↔ FermatShape n :=
  ⟨fun ⟨_, hm⟩ => fermatShape_of_totient_eq_two_pow hm,
    exists_totient_eq_two_pow_of_fermatShape hn.ne'⟩

/-- The unit group of `ZMod n` is a `2`-group iff `φ n` is a power of `2`
(for `n > 0`). -/
theorem isPGroup_two_units_zmod_iff {n : ℕ} (hn : 0 < n) :
    IsPGroup 2 (ZMod n)ˣ ↔ ∃ m : ℕ, n.totient = 2 ^ m := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- If a ring of characteristic `n` has a `2`-group of units, so does
`ZMod n`: the canonical map `ZMod n → R` is injective and induces an
injective group homomorphism `(ZMod n)ˣ →* Rˣ`. -/
theorem isPGroup_two_units_zmod_of_charP {n : ℕ} {R : Type*} [Ring R] [CharP R n]
    (hR : IsPGroup 2 Rˣ) : IsPGroup 2 (ZMod n)ˣ :=
  hR.of_injective (Units.map (ZMod.castHom (dvd_refl n) R).toMonoidHom)
    (Units.map_injective (ZMod.castHom_injective R))

/-- **Chebolu–Lockridge, Theorem 3.1 (1) ⇔ (2)** (arXiv:1901.10081).
For `n > 0`, there is a ring `R` of characteristic `n` whose group of units is
a `2`-group iff every odd prime `p` dividing `n` satisfies `p ^ 2 ∤ n` and
`p = 2 ^ k + 1` for some `k`. -/
theorem exists_charP_units_isPGroup_two_iff {n : ℕ} (hn : 0 < n) :
    (∃ (R : Type) (_ : Ring R) (_ : CharP R n), IsPGroup 2 Rˣ) ↔ FermatShape n := by
  rw [← exists_totient_eq_two_pow_iff hn, ← isPGroup_two_units_zmod_iff hn]
  constructor
  · rintro ⟨R, _, _, hR⟩
    exact isPGroup_two_units_zmod_of_charP hR
  · intro hZ
    exact ⟨ZMod n, inferInstance, inferInstance, hZ⟩

/-- An odd prime of the form `2 ^ k + 1` is a Fermat number `2 ^ (2 ^ m) + 1`,
and conversely every Fermat number has that form. -/
theorem exists_eq_two_pow_add_one_iff_fermat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ k : ℕ, p = 2 ^ k + 1) ↔ ∃ m : ℕ, p = Nat.fermatNumber m := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k ≠ 0 := by
      rintro rfl
      exact hp2 rfl
    obtain ⟨m, rfl⟩ := Nat.pow_of_pow_add_prime (by norm_num) hk hp
    exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨2 ^ m, rfl⟩

/-- **Chebolu–Lockridge, Theorem 3.1, Fermat-prime form.** For `n > 0`, some
ring of characteristic `n` has a `2`-group of units iff every odd prime `p`
dividing `n` divides it exactly once and is a Fermat number
`2 ^ (2 ^ m) + 1`. -/
theorem exists_charP_units_isPGroup_two_iff_fermat {n : ℕ} (hn : 0 < n) :
    (∃ (R : Type) (_ : Ring R) (_ : CharP R n), IsPGroup 2 Rˣ) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 →
        ¬ p ^ 2 ∣ n ∧ ∃ m : ℕ, p = Nat.fermatNumber m := by
  rw [exists_charP_units_isPGroup_two_iff hn]
  refine forall_congr' fun p => forall_congr' fun hp => forall_congr' fun _ =>
    forall_congr' fun hp2 => and_congr_right' (exists_eq_two_pow_add_one_iff_fermat hp hp2)

/-- The paper's condition (2) verbatim: `n = 2 ^ a * p₁ * ⋯ * pₖ` where the
`pᵢ` are distinct Fermat primes (`Nat.fermatNumber m = 2 ^ (2 ^ m) + 1`);
distinctness is enforced by indexing over a `Finset`. -/
def PaperShape (n : ℕ) : Prop :=
  ∃ (a : ℕ) (s : Finset ℕ), (∀ p ∈ s, p.Prime ∧ ∃ m : ℕ, p = Nat.fermatNumber m) ∧
    n = 2 ^ a * ∏ p ∈ s, p

/-- `PaperShape 60` holds: `60 = 2 ^ 2 * (3 * 5)`, `3 = F₀`, `5 = F₁`. -/
example : PaperShape 60 :=
  ⟨2, {3, 5}, by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨Nat.prime_three, 0, rfl⟩
    · exact ⟨Nat.prime_five, 1, rfl⟩, by decide⟩

/-- Every positive `n` of Fermat shape has the paper's form
`2 ^ a * p₁ * ⋯ * pₖ` with distinct Fermat primes `pᵢ`. -/
theorem paperShape_of_fermatShape {n : ℕ} (hn : n ≠ 0) (h : FermatShape n) :
    PaperShape n := by
  classical
  refine ⟨n.factorization 2, n.primeFactors.erase 2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp2, hpf⟩ := Finset.mem_erase.1 hp
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.1 hpf
    exact ⟨hpp, (exists_eq_two_pow_add_one_iff_fermat hpp hp2).1 (h p hpp hpn hp2).2⟩
  · have hodd : ∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p =
        ∏ p ∈ n.primeFactors.erase 2, p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨hp2, hpf⟩ := Finset.mem_erase.1 hp
      obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.1 hpf
      have hpos : 0 < n.factorization p := hpp.factorization_pos_of_dvd hn hpn
      have hle : n.factorization p < 2 := by
        by_contra hcon
        exact (h p hpp hpn hp2).1 ((hpp.pow_dvd_iff_le_factorization hn).2 (by omega))
      rw [show n.factorization p = 1 by omega, pow_one]
    rw [← hodd]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    by_cases h2 : 2 ∈ n.primeFactors
    · exact (Finset.mul_prod_erase _ (fun p => p ^ n.factorization p) h2).symm
    · have h0 : n.factorization 2 = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact h2
      rw [Finset.erase_eq_of_notMem h2, h0, pow_zero, one_mul]

/-- Every `n` of the paper's form `2 ^ a * p₁ * ⋯ * pₖ` (distinct Fermat
primes `pᵢ`) has Fermat shape. -/
theorem fermatShape_of_paperShape {n : ℕ} (h : PaperShape n) : FermatShape n := by
  classical
  obtain ⟨a, s, hs, rfl⟩ := h
  intro p hp hpn hp2
  have hcop : Nat.Coprime p (2 ^ a) :=
    Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hmem_of_dvd : ∀ t : Finset ℕ, t ⊆ s → p ∣ ∏ q ∈ t, q → p ∈ t := by
    intro t ht hdvd
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hs q (ht hq)).1).1 hpq]
  have hps : p ∈ s := hmem_of_dvd s subset_rfl (hcop.dvd_of_dvd_mul_left hpn)
  refine ⟨?_, (exists_eq_two_pow_add_one_iff_fermat hp hp2).2 (hs p hps).2⟩
  intro hsq
  have hsq' : p * p ∣ p * ∏ q ∈ s.erase p, q := by
    rw [Finset.mul_prod_erase s (fun q => q) hps, ← pow_two]
    exact (Nat.Coprime.pow_left 2 hcop).dvd_of_dvd_mul_left hsq
  have hdvd : p ∣ ∏ q ∈ s.erase p, q := Nat.dvd_of_mul_dvd_mul_left hp.pos hsq'
  exact Finset.notMem_erase p s (hmem_of_dvd _ (Finset.erase_subset p s) hdvd)

/-- **Chebolu–Lockridge, Theorem 3.1 (1) ⇔ (2), verbatim form**
(arXiv:1901.10081). For `n > 0`, a `2`-group is realizable in characteristic
`n` (some ring `R` with `CharP R n` has `Rˣ` a `2`-group) iff
`n = 2 ^ a * p₁ * ⋯ * pₖ` with the `pᵢ` distinct Fermat primes. -/
theorem thm_3_1 {n : ℕ} (hn : 0 < n) :
    (∃ (R : Type) (_ : Ring R) (_ : CharP R n), IsPGroup 2 Rˣ) ↔ PaperShape n := by
  rw [exists_charP_units_isPGroup_two_iff hn]
  exact ⟨paperShape_of_fermatShape hn.ne', fermatShape_of_paperShape⟩

end GroupCount.FuchsProblemTwoGroupUnits
