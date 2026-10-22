/-
# A counterexample for elementary symmetric partitions

Hadelyn–Niergarth–Li–Li, *Counterexamples regarding elementary symmetric
partitions*, arXiv:2606.00420, Conjecture 1.3 (`conj:our conjecture`) and
Definition 2.1 (`def:flip`). Here `pre_j` is the multiset of products of
j-element selections of positive parts, with multiplicity.
The distinct length-8 partitions `(16,4^6,1)` and `(8^4,2^4)` have the same
pair-product multiset `{64^6,16^16,4^6}`, but `8 ≠ 2·2`, refuting the conjecture.
Their sizes are 41 and 40: this does not contradict Li's fixed-size
injectivity theorem. The exponent construction is the pair-sum phenomenon
attributed to Selfridge–Straus (1958).
-/
import Mathlib

set_option autoImplicit false

namespace ElementarySymmetricPartitionsCounterexample

/-! ## Definitions mirroring the source -/

/-- The elementary symmetric partition `pre_j(λ)`: the multiset of products of
`j` parts of `λ` taken from `j` distinct positions (Ballantine–Beck–Merca;
arXiv:2606.00420, Section 1). Partitions are identified with multisets of parts. -/
def pre (j : ℕ) (lam : Multiset ℕ) : Multiset ℕ :=
  (lam.powersetCard j).map Multiset.prod

/-- The map `flip_j` of Definition 2.1 of arXiv:2606.00420, on multisets:
`flip_j(λ) = (λ_1 ⋯ λ_ℓ)^{1/j} · {1/λ_i}`, a multiset of reals. -/
noncomputable def flip (j : ℕ) (lam : Multiset ℕ) : Multiset ℝ :=
  lam.map fun x => ((lam.prod : ℝ) ^ ((j : ℝ)⁻¹)) / (x : ℝ)

/-- Conjecture 1.3 of arXiv:2606.00420: for distinct partitions `λ, μ` (positive
parts) of common length `ℓ` and any `2 ≤ j < ℓ`, `pre_j(λ) = pre_j(μ)` iff
`ℓ = 2j` and `flip_j(λ) = μ` (the latter compared as real multisets). -/
def Conjecture13 : Prop :=
  ∀ (ℓ j : ℕ) (lam mu : Multiset ℕ), (∀ x ∈ lam, 0 < x) → (∀ x ∈ mu, 0 < x) →
    Multiset.card lam = ℓ → Multiset.card mu = ℓ → lam ≠ mu → 2 ≤ j → j < ℓ →
    (pre j lam = pre j mu ↔ ℓ = 2 * j ∧ flip j lam = mu.map (fun x : ℕ => (x : ℝ)))

/-! ## Examples -/

-- The worked example of the paper: `pre_3(4,3,3,1) = (36,12,12,9)`.
example : pre 3 {4, 3, 3, 1} = {36, 12, 12, 9} := by decide

example : pre 2 {3, 2, 1} = {6, 3, 2} := by decide

-- `flip_1(3,2) = 6 · (1/2, 1/3) = (3, 2)`.
example : flip 1 {3, 2} = {2, 3} := by
  simp only [flip, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
    Nat.cast_one, inv_one, Real.rpow_one]
  norm_num [Multiset.cons_swap]

-- `flip_2(4,1) = 2 · (1, 1/4) = (2, 1/2)` (as a multiset).
example : flip 2 {4, 1} = {1 / 2, 2} := by
  have h4 : ((4 : ℕ) : ℝ) ^ (((2 : ℕ) : ℝ)⁻¹) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  simp only [flip, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
    mul_one, h4]
  norm_num [Multiset.cons_swap]

/-! ## The counterexample -/

/-- The partition `λ = (16,4,4,4,4,4,4,1)`. -/
def lam0 : Multiset ℕ := {16, 4, 4, 4, 4, 4, 4, 1}

/-- The partition `μ = (8,8,8,8,2,2,2,2)`. -/
def mu0 : Multiset ℕ := {8, 8, 8, 8, 2, 2, 2, 2}

/-- `pre_2(16,4^6,1) = pre_2(8^4,2^4)`; both equal `{64^6, 16^16, 4^6}`. -/
theorem pre_two_lam0_eq_mu0 : pre 2 lam0 = pre 2 mu0 := by decide

/-- The common value of `pre_2` on the counterexample pair. -/
theorem pre_two_lam0 :
    pre 2 lam0 = Multiset.replicate 6 64 + Multiset.replicate 16 16 + Multiset.replicate 6 4 := by
  decide

/-- The two partitions are distinct. -/
theorem lam0_ne_mu0 : lam0 ≠ mu0 := by decide

/-- Both partitions have length 8. -/
theorem card_lam0 : Multiset.card lam0 = 8 := by decide

/-- Both partitions have length 8. -/
theorem card_mu0 : Multiset.card mu0 = 8 := by decide

-- The sizes differ (41 vs 40), so this does not contradict injectivity of `pre_2`
-- on partitions of a fixed size `n` (Li).
example : lam0.sum = 41 ∧ mu0.sum = 40 := by decide

/-- `pre_2` is not injective on partitions of length `8` (no size condition): there
are distinct partitions of length `8` with equal elementary symmetric partitions
`pre_2`. This refutes the injectivity consequence stated after Conjecture 1.3 of
arXiv:2606.00420 (length `8 ∉ {2, 4}`). -/
theorem exists_ne_pre_two_eq :
    ∃ lam mu : Multiset ℕ, (∀ x ∈ lam, 0 < x) ∧ (∀ x ∈ mu, 0 < x) ∧
      Multiset.card lam = 8 ∧ Multiset.card mu = 8 ∧ lam ≠ mu ∧ pre 2 lam = pre 2 mu :=
  ⟨lam0, mu0, by decide, by decide, card_lam0, card_mu0, lam0_ne_mu0, pre_two_lam0_eq_mu0⟩

/-- Conjecture 1.3 of arXiv:2606.00420 is false: at `j = 2`, `ℓ = 8`, the distinct
partitions `(16,4^6,1)` and `(8^4,2^4)` have `pre_2(λ) = pre_2(μ)` but `ℓ ≠ 2j`. -/
theorem not_conjecture13 : ¬ Conjecture13 := by
  intro h
  have hpos_lam : ∀ x ∈ lam0, 0 < x := by decide
  have hpos_mu : ∀ x ∈ mu0, 0 < x := by decide
  have hconj := (h 8 2 lam0 mu0 hpos_lam hpos_mu card_lam0 card_mu0 lam0_ne_mu0
    le_rfl (by norm_num)).mp pre_two_lam0_eq_mu0
  have hlen : (8 : ℕ) = 2 * 2 := hconj.1
  omega

end ElementarySymmetricPartitionsCounterexample
