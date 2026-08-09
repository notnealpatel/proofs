import Mathlib
import GroupTPP.IsoclinismInvariants

/-!
# A strengthened lower bound for the commuting probability (Nath–Das 2.4.1)

For a finite group `G`, Mathlib provides
`inv_card_commutator_le_commProb : 1 / |G'| ≤ Pr(G)`.
Nath and Das (arXiv:1009.5526, Theorem 2.4.1) strengthen this to

  `Pr(G) ≥ 1/|G'| · (1 + (|G'| - 1)/|G : Z(G)|)`,

which is strictly larger than `1/|G'|` whenever `G` is nonabelian.

## Proof outline (Burnside counting)

Write `k = |ConjClasses G|`, `z = |Z(G)|`, `c = |G'|`, `m = [G : Z(G)] = |G|/z`.
Then `Pr(G) = k / |G|` (`commProb_def'`).

The class equation gives `k = z + n_c`, where `n_c` is the number of *non-central*
conjugacy classes, and `|G| = z + Σ |Cl|` summed over the non-central classes.

**Key lemma.** Every conjugacy class `Cl(x)` is contained in the coset `G'·x`
(because `g x g⁻¹ = ⁅g, x⁆ · x ∈ G'·x`), so `|Cl(x)| ≤ |G'| = c`.

Hence `|G| - z = Σ |Cl| ≤ n_c · c`, i.e. `n_c ≥ (|G| - z)/c`. Therefore
`Pr(G) = (z + n_c)/|G| ≥ (z + (|G|-z)/c)/|G| = (c + m - 1)/(c·m)`,
which is exactly `1/c · (1 + (c-1)/m)`.

The task statement's informal sketch had the class-size bound and the resulting
`n_c` inequality reversed; the corrected argument above is what we formalize.

## Reference
* R. K. Nath and A. K. Das, *Commutativity Degree, Its Generalizations, and
  Classification of Finite Groups*, arXiv:1009.5526, Theorem 2.4.1.
-/

open scoped Classical

namespace CommProbBound

variable {G : Type*} [Group G]

/-! ### The key per-class size bound: `|Cl(x)| ≤ |G'|` -/

/-- A conjugate `g * x * g⁻¹` lies in the coset `G' * x` of the commutator subgroup:
indeed `g * x * g⁻¹ = ⁅g, x⁆ * x` with `⁅g, x⁆ ∈ G'`. -/
theorem conj_mem_commutator_mul (x g : G) :
    g * x * g⁻¹ * x⁻¹ ∈ commutator G := by
  rw [← commutatorElement_def, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)

/-- If `y` is conjugate to `x` then `y * x⁻¹ ∈ G'`. -/
theorem mul_inv_mem_commutator_of_mem_carrier {x y : G}
    (hy : y ∈ (ConjClasses.mk x).carrier) : y * x⁻¹ ∈ commutator G := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm,
    isConj_iff] at hy
  obtain ⟨g, hg⟩ := hy
  rw [← hg]
  exact conj_mem_commutator_mul x g

/-- **Key lemma.** Each conjugacy class has cardinality at most `|G'|`. The map
`y ↦ y * x⁻¹` injects the class of `x` into the commutator subgroup. -/
theorem card_carrier_le_card_commutator [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier ≤ Nat.card (commutator G) := by
  apply Nat.card_le_card_of_injective
    (fun y : (ConjClasses.mk x).carrier =>
      (⟨(y : G) * x⁻¹, mul_inv_mem_commutator_of_mem_carrier y.2⟩ : commutator G))
  intro a b hab
  apply Subtype.ext
  have : (a : G) * x⁻¹ = (b : G) * x⁻¹ := by
    have := congrArg (Subtype.val) hab
    simpa using this
  exact mul_right_cancel this

/-- The same bound, phrased for an arbitrary conjugacy class `c : ConjClasses G`. -/
theorem card_carrier_le_card_commutator' [Finite G] (c : ConjClasses G) :
    Nat.card c.carrier ≤ Nat.card (commutator G) := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  exact card_carrier_le_card_commutator x

/-! ### The class equation and the lower bound on `n_c`

The statements below are phrased entirely with `Nat.card` (so they elaborate from
`[Finite G]` alone); the `Finset`/`Fintype` machinery is confined to the proofs. -/

/-- **The non-central counting bound.** The non-central elements, `|G| - |Z(G)|`
many, partition into `n_c = |noncenter G|` classes each of size `≤ |G'|`, hence
`|G| - |Z(G)| ≤ n_c · |G'|`. -/
theorem card_sub_center_le [Finite G] :
    Nat.card G - Nat.card (Subgroup.center G)
      ≤ Nat.card (ConjClasses.noncenter G) * Nat.card (commutator G) := by
  classical
  haveI := Fintype.ofFinite G
  -- The sum of non-central class sizes equals `|G| - |Z(G)|` (class equation).
  have hsum : ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card
      = Nat.card G - Nat.card (Subgroup.center G) := by
    have key := Group.card_center_add_sum_card_noncenter_eq_card G
    rw [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card (α := Subgroup.center G)]
    omega
  -- Each class size is `≤ |G'|`.
  have hbound : ∀ x ∈ (ConjClasses.noncenter G).toFinset,
      x.carrier.toFinset.card ≤ Nat.card (commutator G) := by
    intro x _
    rw [← Nat.card_eq_card_toFinset]
    exact card_carrier_le_card_commutator' x
  -- Bound the sum by `(number of classes) · |G'|`.
  rw [← hsum, Nat.card_eq_card_toFinset (ConjClasses.noncenter G), ← smul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ hbound

/-! ### The main theorem -/

/-- **Nath–Das 2.4.1.** For a finite group `G`,
`Pr(G) ≥ 1/|G'| · (1 + (|G'| - 1)/|G : Z(G)|)`. -/
theorem commProb_ge [Finite G] :
    (1 / (Nat.card (commutator G) : ℚ))
        * (1 + ((Nat.card (commutator G) : ℚ) - 1) / ((Subgroup.center G).index : ℚ))
      ≤ commProb G := by
  classical
  haveI := Fintype.ofFinite G
  -- Abbreviations and positivity facts.
  set N : ℕ := Nat.card G with hNdef
  set Z : ℕ := Nat.card (Subgroup.center G) with hZdef
  set C : ℕ := Nat.card (commutator G) with hCdef
  set m : ℕ := (Subgroup.center G).index with hmdef
  set nf : ℕ := Nat.card (ConjClasses.noncenter G) with hnfdef
  have hN0 : 0 < N := Nat.card_pos
  have hZ0 : 0 < Z := Nat.card_pos
  have hC0 : 0 < C := Nat.card_pos
  -- Lagrange: `Z * m = N`, whence `0 < m` and `Z ≤ N`.
  have hZmN : Z * m = N := Subgroup.card_mul_index (Subgroup.center G)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hZmN; omega
    · exact h
  have hZleN : Z ≤ N := by rw [← hZmN]; nlinarith
  -- Class equation: `k = Z + n_c`.
  have hK : Nat.card (ConjClasses G) = Z + nf := by
    rw [IsoclinismInvariants.card_conjClasses_eq_center_add_nc, IsoclinismInvariants.nc]
  -- The non-central counting bound, in ℕ then ℚ.
  have hcount : N - Z ≤ nf * C := card_sub_center_le
  have hcountℚ : (N : ℚ) - (Z : ℚ) ≤ (nf : ℚ) * (C : ℚ) := by
    have := (Nat.cast_le (α := ℚ)).2 hcount
    push_cast [Nat.cast_sub hZleN] at this ⊢
    linarith
  -- Cast the key equalities to ℚ.
  have hZmNℚ : (Z : ℚ) * (m : ℚ) = (N : ℚ) := by exact_mod_cast hZmN
  have hKℚ : (Nat.card (ConjClasses G) : ℚ) = (Z : ℚ) + (nf : ℚ) := by exact_mod_cast hK
  have hC0ℚ : (0 : ℚ) < (C : ℚ) := by exact_mod_cast hC0
  have hm0ℚ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm0
  have hN0ℚ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN0
  -- Rewrite the commuting probability and collapse the LHS to a single fraction.
  rw [commProb_def', hKℚ, ← hNdef]
  have hLHS : (1 / (C : ℚ)) * (1 + ((C : ℚ) - 1) / (m : ℚ))
      = ((m : ℚ) + (C : ℚ) - 1) / ((C : ℚ) * (m : ℚ)) := by
    field_simp
    ring
  rw [hLHS, div_le_div_iff₀ (by positivity) hN0ℚ]
  -- The cross-multiplied goal follows from `hcountℚ`, `hZmNℚ`, positivity.
  nlinarith [hcountℚ, hZmNℚ, hm0ℚ, hC0ℚ, mul_le_mul_of_nonneg_right hcountℚ (le_of_lt hm0ℚ)]

end CommProbBound
