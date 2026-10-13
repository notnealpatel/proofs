import Mathlib

set_option autoImplicit false

namespace Sidon

/-- Only the two trivial reorderings can have equal sums within the set. -/
def IsSidon {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) :
    Decidable (IsSidon S) := by
  unfold IsSidon
  infer_instance

example : IsSidon ({1} : Finset ℕ) := by simp [IsSidon]
example : IsSidon (∅ : Finset ℕ) := by simp [IsSidon]

/-- A subset of a Sidon set is Sidon. -/
theorem IsSidon.subset {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {S U : Finset α} (h : IsSidon S) (hU : U ⊆ S) : IsSidon U := by
  intro a ha b hb c hc d hd hab
  exact h a (hU ha) b (hU hb) c (hU hc) d (hU hd) hab

/-- The empty set is Sidon. -/
theorem isSidon_empty {α : Type*} [AddCommMonoid α] [DecidableEq α] :
    IsSidon (∅ : Finset α) := by simp [IsSidon]

/-- Every singleton is Sidon. -/
theorem isSidon_singleton {α : Type*} [AddCommMonoid α] [DecidableEq α] (a : α) :
    IsSidon ({a} : Finset α) := by simp [IsSidon]

/-- The sum of an unordered pair, including a diagonal pair. -/
def pairSum {α : Type*} [AddCommMonoid α] : Sym2 α → α :=
  Sym2.lift ⟨fun a b => a + b, add_comm⟩

example : pairSum s(2, 3) = (5 : ℕ) := rfl

/-- Sidon means that sums are injective on the unordered pairs of the set. -/
theorem isSidon_iff_pairSum_injOn {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (S : Finset α) : IsSidon S ↔ Set.InjOn pairSum (S.sym2 : Set (Sym2 α)) := by
  constructor
  · intro h p
    refine Sym2.ind (fun a b => ?_) p
    intro hab q
    refine Sym2.ind (fun c d => ?_) q
    intro hcd heq
    obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hab
    obtain ⟨hc, hd⟩ := Finset.mk_mem_sym2_iff.mp hcd
    exact Sym2.eq.mpr (Sym2.rel_iff.mpr (h a ha b hb c hc d hd heq))
  · intro h a ha b hb c hc d hd heq
    exact Sym2.rel_iff.mp (Sym2.eq.mp
      (h (Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩)
        (Finset.mk_mem_sym2_iff.mpr ⟨hc, hd⟩) heq))

/-- Twice the number of unordered pairs with repetition is `k * (k+1)`. -/
theorem twice_choose_succ_two (k : ℕ) : 2 * Nat.choose (k + 1) 2 = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
    ring

/-- Counting distinct unordered sums bounds the size of a finite Sidon set. -/
theorem IsSidon.card_mul_succ_le {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {S T : Finset α} (h : IsSidon S)
    (hT : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ T) :
    S.card * (S.card + 1) ≤ 2 * T.card := by
  have hmaps : Set.MapsTo pairSum (S.sym2 : Set (Sym2 α)) (T : Set α) := by
    intro p
    refine Sym2.ind (fun a b => ?_) p
    intro hp
    obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hp
    exact hT a ha b hb
  have hc := Finset.card_le_card_of_injOn pairSum hmaps
    ((isSidon_iff_pairSum_injOn S).mp h)
  rw [Finset.card_sym2] at hc
  rw [← twice_choose_succ_two]
  exact Nat.mul_le_mul_left 2 hc

example : ({1, 2} : Finset ℕ).card * (({1, 2} : Finset ℕ).card + 1) ≤
    2 * ({2, 3, 4} : Finset ℕ).card := by
  have hs : IsSidon ({1, 2} : Finset ℕ) := by decide
  have ht : ∀ a ∈ ({1, 2} : Finset ℕ), ∀ b ∈ ({1, 2} : Finset ℕ),
      a + b ∈ ({2, 3, 4} : Finset ℕ) := by decide
  exact hs.card_mul_succ_le ht

/-- For natural numbers, the Sidon condition is uniqueness of sorted sums. -/
theorem isSidon_iff_sums_distinct (S : Finset ℕ) :
    IsSidon S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d := by
  constructor
  · intro h a ha b hb c hc d hd hab hcd heq
    rcases h a ha b hb c hc d hd heq with hsame | hswap
    · exact hsame
    · omega
  · intro h a ha b hb c hc d hd heq
    rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
    · exact Or.inl (h a ha b hb c hc d hd hab hcd heq)
    · exact Or.inr (h a ha b hb d hd c hc hab hdc (by omega))
    · obtain ⟨hbc, had⟩ := h b hb a ha c hc d hd hba hcd (by omega)
      exact Or.inr ⟨had, hbc⟩
    · obtain ⟨hbd, hac⟩ := h b hb a ha d hd c hc hba hdc (by omega)
      exact Or.inl ⟨hac, hbd⟩

end Sidon
