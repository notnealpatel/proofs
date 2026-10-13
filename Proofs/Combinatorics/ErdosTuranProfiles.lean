import Mathlib

set_option autoImplicit false

namespace Candidates.A265262

/-- The **profile** (representation function) of `A ⊆ ℕ`:
`pA n = #{(x, y) : x, y ∈ A, x ≤ y, x + y = n}`.

Uses `Finset.HasAntidiagonal.antidiagonal n` — the pairs summing to `n` — filtered by
membership and `x ≤ y`.  The `x ≤ y` is the OEIS's unordered convention; the
ordered convention would double every value except the diagonal and give a
different sequence. -/
noncomputable def profile (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2)).card

/-- `A` is an **order-2 additive basis** of `ℕ`: its profile has no zeros, i.e.
every `n` is a sum of two elements of `A`. -/
def IsBasis2 (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := ∀ n : ℕ, 0 < profile A n

/-- `A` is a **Sidon set**: its profile takes only values `0` and `1`. -/
def IsSidonSet (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := ∀ n : ℕ, profile A n ≤ 1

/-- A **hemitropic sequence** is the profile of a subset containing `0` and `1`
(so `pA 0 = pA 1 = 1`).  This is the OEIS's own terminology; the tree's rows
enumerate these. -/
def Hemitropic (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := (0 : ℕ) ∈ A ∧ (1 : ℕ) ∈ A

example : profile Set.univ 0 = 1 := by decide
example : profile Set.univ 1 = 1 := by decide
example : profile Set.univ 4 = 3 := by decide
example : IsSidonSet (∅ : Set ℕ) := by
  intro n
  simp [profile]
example : Hemitropic (Set.univ : Set ℕ) := ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Membership decisions through `n` determine the unordered profile at `n`. -/
theorem profile_eq_of_inter_eq {A A' : Set ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ A')] (n : ℕ)
    (h : ∀ k ≤ n, (k ∈ A ↔ k ∈ A')) : profile A n = profile A' n := by
  unfold profile
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hx : p.1 ≤ n := by omega
  have hy : p.2 ≤ n := by omega
  simp only [h p.1 hx, h p.2 hy]

/-- The full natural-number set has `n / 2 + 1` unordered representations at `n`. -/
theorem profile_univ (n : ℕ) : profile Set.univ n = n / 2 + 1 := by
  unfold profile
  rw [← Finset.card_range (n / 2 + 1)]
  symm
  apply Finset.card_bij (fun k _ => (k, n - k))
  · intro k hk
    have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_univ, true_and]
    constructor <;> omega
  · intro a ha b hb hab
    exact congrArg Prod.fst hab
  · intro p hp
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_univ, true_and] at hp
    refine ⟨p.1, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · exact Prod.ext rfl (by omega)

/-- The full natural-number set is an order-two basis, including at zero. -/
theorem isBasis2_univ : IsBasis2 (Set.univ : Set ℕ) := by
  intro n
  rw [profile_univ]
  omega

/-- The full natural-number set has an unbounded unordered profile. -/
theorem profile_univ_unbounded : ¬ BddAbove (Set.range (profile (Set.univ : Set ℕ))) := by
  rintro ⟨B, hB⟩
  have hb := hB (Set.mem_range_self (2 * B))
  rw [profile_univ] at hb
  omega

/-- A hemitropic set has the normalized initial profile values `1, 1`. -/
theorem profile_zero_of_hemitropic {A : Set ℕ} [DecidablePred (· ∈ A)]
    (h : Hemitropic A) : profile A 0 = 1 ∧ profile A 1 = 1 := by
  rcases h with ⟨h0, h1⟩
  constructor
  · simp [profile, Finset.filter_singleton, h0]
  · have hd : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
    simp [profile, hd, Finset.filter_insert, Finset.filter_singleton, h0, h1]

/-- Even natural numbers fail the order-two basis condition at one. -/
theorem not_isBasis2_even : ¬ IsBasis2 {n : ℕ | Even n} := by
  intro h
  have h1 := h 1
  have hd : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  have hz : profile {n : ℕ | Even n} 1 = 0 := by
    simp [profile, hd]
  rw [hz] at h1
  omega

/-- Unboundedness for every basis is equivalent to excluding a bounded zero-free profile. -/
theorem erdosTuran_iff_no_bounded_branch :
    (∀ (A : Set ℕ) (_ : DecidablePred (· ∈ A)), IsBasis2 A →
        ¬ BddAbove (Set.range (profile A)))
      ↔ ¬ ∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)) (B : ℕ),
          (∀ n, 0 < profile A n) ∧ (∀ n, profile A n ≤ B) := by
  constructor
  · intro h ⟨A, inst, B, hpos, hbound⟩
    exact h A inst hpos ⟨B, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  · intro h A inst hpos ⟨B, hbound⟩
    exact h ⟨A, inst, B, hpos, fun n => hbound (Set.mem_range_self n)⟩

/-- Rado selection turns uniformly bounded zero-free finite prefixes into a global profile.
This is the compactness step; it does not prove the Erdős–Turán conjecture. -/
theorem erdosTuran_konig (B : ℕ) :
    (∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)),
        (∀ n, 0 < profile A n) ∧ (∀ n, profile A n ≤ B))
      ↔ ∀ N : ℕ, ∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)),
          (∀ n ≤ N, 0 < profile A n) ∧ (∀ n ≤ N, profile A n ≤ B) := by
  classical
  constructor
  · rintro ⟨A, inst, hpos, hbound⟩ N
    exact ⟨A, inst, fun n _ => hpos n, fun n _ => hbound n⟩
  · intro h
    have hex : ∀ N : ℕ, ∃ A : Set ℕ,
        (∀ n ≤ N, 0 < profile A n) ∧ (∀ n ≤ N, profile A n ≤ B) := by
      intro N
      obtain ⟨A, inst, hpos, hbound⟩ := h N
      have hi : inst = (fun a => Classical.propDecidable (a ∈ A)) := Subsingleton.elim _ _
      refine ⟨A, ?_, ?_⟩
      · exact hi ▸ hpos
      · exact hi ▸ hbound
    choose A hA using hex
    let g : Finset ℕ → ℕ → Bool := fun t x => decide (x ∈ A (t.sup id))
    obtain ⟨χ, hχ⟩ := Finset.rado_selection g
    let C : Set ℕ := {x | χ x = true}
    have hc : ∀ n, 0 < profile C n ∧ profile C n ≤ B := by
      intro n
      let s := Finset.range (n + 1)
      obtain ⟨t, hst, ht⟩ := hχ s
      have hn : n ≤ t.sup id := Finset.le_sup (f := id) (hst (by simp [s]))
      have heq : profile C n = profile (A (t.sup id)) n := by
        apply profile_eq_of_inter_eq
        intro k hk
        have hks : k ∈ s := Finset.mem_range.mpr (by omega)
        have hkt := ht k hks
        change χ k = true ↔ k ∈ A (t.sup id)
        rw [hkt]
        simp [g]
      rw [heq]
      exact ⟨(hA (t.sup id)).1 n hn, (hA (t.sup id)).2 n hn⟩
    exact ⟨C, inferInstance, fun n => (hc n).1, fun n => (hc n).2⟩

/-- Inserting a new positive element `m` adds precisely `(0, m)` to the profile at `m`. -/
theorem profile_insert_self {A : Set ℕ} {m : ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ insert m A)] (h0 : (0 : ℕ) ∈ A) (hm : m ∉ A) (hm0 : 0 < m) :
    profile (insert m A) m = profile A m + 1 := by
  let F := (Finset.HasAntidiagonal.antidiagonal m).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2)
  have heq : (Finset.HasAntidiagonal.antidiagonal m).filter
      (fun p => p.1 ∈ insert m A ∧ p.2 ∈ insert m A ∧ p.1 ≤ p.2) =
      insert (0, m) F := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Set.mem_insert_iff, Finset.mem_insert, Prod.mk.injEq, F]
    constructor
    · rintro ⟨hsum, hx, hy, hxy⟩
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · omega
      · omega
      · left
        exact ⟨by omega, hy⟩
      · right
        exact ⟨hsum, hx, hy, hxy⟩
    · intro hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨hsum, hx, hy, hxy⟩
      · exact ⟨by omega, Or.inr h0, Or.inl rfl, by omega⟩
      · exact ⟨hsum, Or.inr hx, Or.inr hy, hxy⟩
  have hnew : (0, m) ∉ F := by
    simp [F, hm]
  change _ = F.card + 1
  rw [profile, heq, Finset.card_insert_of_notMem hnew]

example : profile {0, 1} 3 = 0 := by decide
example : profile {0, 1, 3} 3 = 1 := by decide
example : profile {0, 1, 2} 3 = 1 := by decide
example : profile {0, 1, 2, 3} 3 = 2 := by decide

example : profile (Set.univ : Set ℕ) 3 = profile Set.univ 3 :=
  profile_eq_of_inter_eq 3 (fun _ _ => Iff.rfl)
example : profile {0, 1} 0 = 1 ∧ profile {0, 1} 1 = 1 :=
  profile_zero_of_hemitropic ⟨by simp, by simp⟩
example : profile (insert 2 ({0, 1} : Set ℕ)) 2 = profile {0, 1} 2 + 1 :=
  profile_insert_self (by simp) (by simp) (by decide)
example : ∀ N : ℕ, ∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)),
    (∀ n ≤ N, 0 < profile A n) ∧ (∀ n ≤ N, profile A n ≤ N / 2 + 1) := by
  intro N
  refine ⟨Set.univ, inferInstance, fun n _ => isBasis2_univ n, ?_⟩
  intro n hn
  rw [profile_univ]
  omega

end Candidates.A265262
