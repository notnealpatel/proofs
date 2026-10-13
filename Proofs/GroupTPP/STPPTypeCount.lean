import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

namespace GroupTPP.STPPWreath.TypeCount

/-- The number of indexed words with prescribed label multiplicities is the multinomial. -/
theorem card_words (n N : ℕ) (μ : Fin n → ℕ) (hμ : ∑ i, μ i = N) :
    Fintype.card {f : Fin N → Fin n //
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card = μ i} =
      Nat.multinomial Finset.univ μ := by
  classical
  let X := {f : Fin N → Fin n //
    ∀ i, (Finset.univ.filter (fun j => f j = i)).card = μ i}
  let B := Σ i : Fin n, Fin (μ i)
  let D := fun f : X => ∀ i : Fin n, {j : Fin N // f.val j = i} ≃ Fin (μ i)
  let assemble : (Σ f : X, D f) → (Fin N ≃ B) := fun p =>
    (Equiv.sigmaFiberEquiv p.1.val).symm.trans (Equiv.sigmaCongrRight p.2)
  have assemble_apply (p : Σ f : X, D f) (j : Fin N) :
      assemble p j = ⟨p.1.val j, p.2 (p.1.val j) ⟨j, rfl⟩⟩ := rfl
  let fiberEquiv : (e : Fin N ≃ B) → (i : Fin n) →
      {j : Fin N // (e j).1 = i} ≃ Fin (μ i) := fun e i =>
    (e.subtypeEquiv (fun j => Iff.rfl)).trans (Equiv.sigmaSubtype i)
  have fiber_card (e : Fin N ≃ B) (i : Fin n) :
      (Finset.univ.filter (fun j => (e j).1 = i)).card = μ i := by
    simpa only [Fintype.card_subtype, Fintype.card_fin] using
      Fintype.card_congr (fiberEquiv e i)
  have hinj : Function.Injective assemble := by
    intro p q hpq
    have hf : p.1 = q.1 := by
      apply Subtype.ext
      funext j
      exact congrArg Sigma.fst (Equiv.congr_fun hpq j)
    cases p with
    | mk f d =>
      cases q with
      | mk g c =>
        dsimp at hf
        subst g
        congr 1
        funext i
        apply Equiv.ext
        intro j
        have hj := Equiv.congr_fun hpq j.val
        rw [assemble_apply, assemble_apply] at hj
        cases j with
        | mk j hjlabel =>
          change f.val j = i at hjlabel
          subst i
          exact eq_of_heq (Sigma.mk.inj_iff.mp hj).2
  have hsurj : Function.Surjective assemble := by
    intro e
    let f : X := ⟨fun j => (e j).1, fiber_card e⟩
    refine ⟨⟨f, fiberEquiv e⟩, ?_⟩
    apply Equiv.ext
    intro j
    change ⟨(e j).1, (fiberEquiv e (e j).1) ⟨j, rfl⟩⟩ = e j
    rfl
  have hcount : Fintype.card X * (∏ i, Nat.factorial (μ i)) = Nat.factorial N := by
    have hD (f : X) : Fintype.card (D f) = ∏ i, Nat.factorial (μ i) := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro i hi
      let e : {j : Fin N // f.val j = i} ≃ Fin (μ i) :=
        Fintype.equivOfCardEq (by
          simpa only [Fintype.card_subtype, Fintype.card_fin] using f.property i)
      rw [Fintype.card_equiv e]
      congr 1
      simpa only [Fintype.card_subtype] using f.property i
    have hB : Fintype.card B = N := by
      simpa only [B, Fintype.card_sigma, Fintype.card_fin] using hμ
    let eB : Fin N ≃ B := Fintype.equivOfCardEq (by simpa using hB.symm)
    have hc := Fintype.card_congr (Equiv.ofBijective assemble ⟨hinj, hsurj⟩)
    rw [Fintype.card_sigma, Fintype.card_equiv eB, Fintype.card_fin] at hc
    simpa only [hD, Finset.sum_const, Finset.card_univ, smul_eq_mul] using hc
  have hpos : 0 < ∏ i : Fin n, Nat.factorial (μ i) :=
    Finset.prod_pos (fun i hi => Nat.factorial_pos (μ i))
  have hspec := Nat.multinomial_spec (s := Finset.univ) (f := μ)
  rw [hμ, Nat.mul_comm] at hspec
  exact Nat.eq_of_mul_eq_mul_right hpos (hcount.trans hspec.symm)

/-- A product over the positions of a prescribed-type word regroups by label multiplicity. -/
theorem prod_word (n N : ℕ) (μ : Fin n → ℕ)
    (f : {f : Fin N → Fin n //
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card = μ i})
    (v : Fin n → ℕ) :
    (∏ j, v (f.val j)) = ∏ i, v i ^ μ i := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ f.val (fun j => v (f.val j))]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    (∏ j ∈ Finset.univ.filter (fun j => f.val j = i), v (f.val j)) =
        v i ^ (Finset.univ.filter (fun j => f.val j = i)).card := by
      apply Finset.prod_eq_pow_card
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = v i ^ μ i := by rw [f.property i]

example : (∑ _i : Fin 2, (1 : ℕ)) = 2 ∧
    ∃ f : Fin 2 → Fin 2,
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card = 1 := by
  constructor
  · decide
  · exact ⟨id, by decide⟩

example : (∑ _i : Fin 0, (0 : ℕ)) = 0 ∧
    ∃ f : Fin 0 → Fin 0,
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card = 0 := by
  constructor
  · decide
  · exact ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩

example : (∑ _i : Fin 2, (0 : ℕ)) = 0 ∧
    ∃ f : Fin 0 → Fin 2,
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card = 0 := by
  constructor
  · decide
  · exact ⟨Fin.elim0, by decide⟩

example : (∑ i : Fin 2, if i = 0 then 0 else 2) = 2 ∧
    ∃ f : Fin 2 → Fin 2,
      ∀ i, (Finset.univ.filter (fun j => f j = i)).card =
        if i = 0 then 0 else 2 := by
  constructor
  · decide
  · exact ⟨fun _ => 1, by decide⟩

end GroupTPP.STPPWreath.TypeCount
