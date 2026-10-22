/-
# Paley graph clique number at most `sqrt p` (classical bound)

## Source

* MathOverflow question 48591, "Clique number of Paley graphs"
  <https://mathoverflow.net/questions/48591>.  The question recalls the
  classical bounds `(1/2 - o(1)) log₂ p < c(p) ≤ sqrt p` for the clique number
  `c(p)` of the Paley graph `P(p)`, `p ≡ 1 (mod 4)`, and asks for improvements;
  the accepted answer discusses the upper bound.
* Later improvement outside the thread: B. Hanson and G. Petridis,
  "Refined estimates concerning sumsets contained in the roots of unity"
  (arXiv:1905.09134, Proc. LMS 2021), `c(p) ≤ (sqrt(2p - 1) + 1) / 2`.
  That sharper bound is not formalized here.

## Statement

"If `A` is a subset of `ZMod p` (`p` an odd prime) and every difference of
distinct elements of `A` is a nonzero square, then `|A|^2 ≤ p`."

## Proof

For a fixed nonsquare `ν`, the map `(a, b) ↦ a + ν b` is
injective on `A × A`; a collision with `b ≠ b'` would make `ν` the quotient of
two nonzero squares.  The hypothesis is stated on ordered pairs, so `-1` being
a square is not needed for the counting bound; it is needed only to make the
Paley adjacency symmetric (`paleyGraph` below).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.PaleyCliqueBound

/-- The Paley graph on `ZMod p` for a prime `p ≡ 1 (mod 4)`: distinct `a, b` are
adjacent iff `a - b` is a square.  The hypothesis `p % 4 = 1` makes `-1` a square,
hence the relation symmetric. -/
def paleyGraph (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : SimpleGraph (ZMod p) where
  Adj a b := a ≠ b ∧ IsSquare (a - b)
  symm := by
    constructor
    rintro a b ⟨hab, hsq⟩
    refine ⟨hab.symm, ?_⟩
    have hneg : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hba : b - a = -1 * (a - b) := by ring
    rw [hba]
    exact hneg.mul hsq
  loopless := ⟨fun a h => h.1 rfl⟩

/-- `5` is prime; used only to instantiate the examples on `P(5)`. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- In `P(5)`, `0` and `1` are adjacent (`0 - 1 = -1 = 4 = 2²`). -/
example : (paleyGraph 5 (by norm_num)).Adj 0 1 :=
  ⟨by decide, ⟨2, by decide⟩⟩

/-- In `P(5)`, `0` and `2` are not adjacent (`0 - 2 = 3` is a
nonsquare mod 5). -/
example : ¬ (paleyGraph 5 (by norm_num)).Adj 0 2 := by
  rintro ⟨-, r, hr⟩
  revert r
  decide

/-- `{0, 1}` is a clique of `P(5)`, and `2² ≤ 5`. -/
example : (paleyGraph 5 (by norm_num)).IsClique ({0, 1} : Set (ZMod 5)) := by
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact ⟨by decide, ⟨2, by decide⟩⟩
  · exact ⟨by decide, ⟨1, by decide⟩⟩
  · exact absurd rfl hab

/-- In a field, a nonsquare cannot be the quotient of a square by a nonzero square:
if `s² = ν t²` with `t ≠ 0`, then `ν` is a square. -/
theorem isSquare_of_sq_eq_mul_sq {F : Type*} [Field F] {ν s t : F} (ht : t ≠ 0)
    (h : s * s = ν * (t * t)) : IsSquare ν :=
  ⟨s / t, by field_simp; linear_combination -h⟩

/-- **Classical Paley clique bound** (MathOverflow 48591; folklore).  For an odd
prime `p`, if `A ⊆ ZMod p` and every difference `a - b` of distinct elements of
`A` is a square, then `|A|² ≤ p`. -/
theorem card_sq_le_of_forall_isSquare_sub {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (A : Finset (ZMod p)) (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsSquare (a - b)) :
    A.card ^ 2 ≤ p := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hchar
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hν ⟨0, by ring⟩
  -- The map `(a, b) ↦ a + ν b` is injective on `A × A`.
  have hinj : Set.InjOn (fun x : ZMod p × ZMod p => x.1 + ν * x.2) ↑(A ×ˢ A) := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hab hab'
    simp only at heq
    by_cases hb : b = b'
    · subst hb
      have ha : a = a' := by simpa using heq
      rw [ha]
    · exfalso
      have hdiff : a - a' = ν * (b' - b) := by linear_combination heq
      have hbb : b' - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      have ha : a ≠ a' := by
        intro ha
        rw [ha, sub_self] at hdiff
        exact mul_ne_zero hν0 hbb hdiff.symm
      obtain ⟨s, hs⟩ := hA a hab.1 a' hab'.1 ha
      obtain ⟨t, ht⟩ := hA b' hab'.2 b hab.2 (Ne.symm hb)
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hbb (by rw [ht, mul_zero])
      refine hν (isSquare_of_sq_eq_mul_sq (s := s) ht0 ?_)
      rw [← hs, ← ht, hdiff]
  have hcard := Finset.card_le_card_of_injOn _ (fun x _ => Finset.mem_univ _) hinj
  rw [Finset.card_product, Finset.card_univ, ZMod.card] at hcard
  rw [sq]
  exact hcard

/-- **Paley clique bound, graph form.**  For a prime `p ≡ 1 (mod 4)`, every clique
`s` of the Paley graph `P(p)` satisfies `|s|² ≤ p`; i.e. the clique number of
`P(p)` is at most `sqrt p` (MathOverflow 48591, classical). -/
theorem paleyGraph_isClique_card_sq_le {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    (s : Finset (ZMod p)) (hs : (paleyGraph p hp).IsClique (s : Set (ZMod p))) :
    s.card ^ 2 ≤ p := by
  refine card_sq_le_of_forall_isSquare_sub (by omega) s ?_
  intro a ha b hb hab
  exact (hs (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab).2

end Candidates.PaleyCliqueBound
