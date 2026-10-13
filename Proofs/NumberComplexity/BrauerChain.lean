import NumberComplexity.AdditionChain

/-!
# Brauer chains

Star chains in the reversed-list convention of `AdditionChain`: every new
head is the previous head plus an existing member. Positive endpoints are
realizable; at zero the shortest length is the empty-infimum value, not a
chain length.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- A reversed Brauer (star) chain starts at `1` and extends the current head
by adding a member of the preceding chain. -/
inductive IsBrauerChain : List ℕ → Prop
  | one : IsBrauerChain [1]
  | star {c : List ℕ} {a b : ℕ} (hb : b ∈ (a :: c)) (hc : IsBrauerChain (a :: c)) :
      IsBrauerChain ((a + b) :: a :: c)

/-- A Brauer chain whose latest element is `n`. -/
abbrev BrauerChain (n : ℕ) : Type := {c : List ℕ // IsBrauerChain c ∧ c.head? = some n}

/-- The least number of additions in a Brauer chain for `n`; at `0`, the
empty infimum in `ℕ` is the junk value `0`. -/
noncomputable def lStar (n : ℕ) : ℕ := ⨅ c : BrauerChain n, chainSteps c.val

/-- A non-Brauer number has a strictly shorter general addition chain than
any Brauer chain. -/
def IsNonBrauer (n : ℕ) : Prop := l n < lStar n

example : IsBrauerChain [1] := .one
example : IsBrauerChain [2, 1] := .star (b := 1) (by simp) .one
example : BrauerChain 1 := ⟨[1], .one, rfl⟩
example (n : ℕ) : IsNonBrauer n ↔ l n < lStar n := Iff.rfl

/-- Every Brauer chain is an addition chain with the same list and steps. -/
theorem IsBrauerChain.isAddChain {c : List ℕ} (h : IsBrauerChain c) : IsAddChain c := by
  induction h with
  | one => exact .one
  | star hb hc ih => exact .add List.mem_cons_self hb ih

/-- Every successor endpoint has a Brauer chain, obtained by repeatedly adding
`1` to the current head. -/
theorem nonempty_brauerChain_succ (n : ℕ) : Nonempty (BrauerChain (n + 1)) := by
  induction n with
  | zero => exact ⟨⟨[1], .one, rfl⟩⟩
  | succ n ih =>
    obtain ⟨⟨c, hc, hh⟩⟩ := ih
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hc.isAddChain.ne_nil
    have ha : a = n + 1 := Option.some.inj hh
    subst a
    have hmem : 1 ∈ (n + 1) :: t := hc.isAddChain.one_mem
    exact ⟨⟨(n + 1 + 1) :: (n + 1) :: t, .star hmem hc, rfl⟩⟩

/-- Brauer chains exist for every nonzero natural endpoint, so their infimum
is not an empty infimum. -/
theorem nonempty_brauerChain_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Nonempty (BrauerChain n) := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ n => exact nonempty_brauerChain_succ n

/-- There is no Brauer chain ending at zero, since all its entries are positive. -/
instance instIsEmptyBrauerChainZero : IsEmpty (BrauerChain 0) :=
  ⟨fun c => by
    let d : AdditionChain 0 := ⟨c.val, c.property.1.isAddChain, c.property.2⟩
    have hpos : 1 ≤ (0 : ℕ) := d.property.1.one_le_of_mem 0 d.head_mem
    omega⟩

/-- At zero, `lStar` is the junk value of an empty infimum. -/
@[simp] theorem lStar_zero : lStar 0 = 0 := Nat.iInf_of_empty _

/-- Every explicit Brauer chain bounds its shortest-chain length from above. -/
theorem lStar_le_chainSteps {n : ℕ} (c : BrauerChain n) : lStar n ≤ chainSteps c.val :=
  Nat.sInf_le (Set.mem_range_self c)

/-- An explicit reversed Brauer chain provides an upper bound on `lStar`. -/
theorem lStar_le_of_isBrauerChain {n k : ℕ} (c : List ℕ) (hc : IsBrauerChain c)
    (hh : c.head? = some n) (hk : chainSteps c ≤ k) : lStar n ≤ k :=
  le_trans (lStar_le_chainSteps ⟨c, hc, hh⟩) hk

/-- General addition chains are at least as efficient as Brauer chains.
The zero case uses `l 0 = 0`; positive endpoints have nonempty chain types. -/
theorem l_le_lStar (n : ℕ) : l n ≤ lStar n := by
  by_cases hn : n = 0
  · subst n
    rw [l_zero]
    exact Nat.zero_le _
  · haveI : Nonempty (BrauerChain n) := nonempty_brauerChain_of_ne_zero hn
    apply le_ciInf
    intro c
    exact l_le_chainSteps ⟨c.val, c.property.1.isAddChain, c.property.2⟩

/-- The first eight Brauer lengths are `0,1,2,2,3,3,4,3`, the corresponding
A003313 values. Upper bounds use explicit star chains; lower bounds come from
shortest general addition chains. -/
theorem lStar_eq_A003313_of_le_eight :
    lStar 1 = 0 ∧ lStar 2 = 1 ∧ lStar 3 = 2 ∧ lStar 4 = 2 ∧
      lStar 5 = 3 ∧ lStar 6 = 3 ∧ lStar 7 = 4 ∧ lStar 8 = 3 := by
  have hsmall := lAsc_eq_A003313_of_le_eight
  simp only [← l_eq_lAsc] at hsmall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsmall
  have c2 : IsBrauerChain [2, 1] := .star (b := 1) (by simp) .one
  have c3 : IsBrauerChain [3, 2, 1] := .star (b := 1) (by simp) c2
  have c4 : IsBrauerChain [4, 2, 1] := .star (b := 2) (by simp) c2
  have c5 : IsBrauerChain [5, 4, 2, 1] := .star (b := 1) (by simp) c4
  have c6 : IsBrauerChain [6, 3, 2, 1] := .star (b := 3) (by simp) c3
  have c7 : IsBrauerChain [7, 6, 3, 2, 1] := .star (b := 1) (by simp) c6
  have c8 : IsBrauerChain [8, 4, 2, 1] := .star (b := 4) (by simp) c4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_antisymm (lStar_le_of_isBrauerChain [1] .one rfl (by decide))
      (h1 ▸ l_le_lStar 1)
  · exact le_antisymm (lStar_le_of_isBrauerChain [2, 1] c2 rfl (by decide))
      (h2 ▸ l_le_lStar 2)
  · exact le_antisymm (lStar_le_of_isBrauerChain [3, 2, 1] c3 rfl (by decide))
      (h3 ▸ l_le_lStar 3)
  · exact le_antisymm (lStar_le_of_isBrauerChain [4, 2, 1] c4 rfl (by decide))
      (h4 ▸ l_le_lStar 4)
  · exact le_antisymm (lStar_le_of_isBrauerChain [5, 4, 2, 1] c5 rfl (by decide))
      (h5 ▸ l_le_lStar 5)
  · exact le_antisymm (lStar_le_of_isBrauerChain [6, 3, 2, 1] c6 rfl (by decide))
      (h6 ▸ l_le_lStar 6)
  · exact le_antisymm (lStar_le_of_isBrauerChain [7, 6, 3, 2, 1] c7 rfl (by decide))
      (h7 ▸ l_le_lStar 7)
  · exact le_antisymm (lStar_le_of_isBrauerChain [8, 4, 2, 1] c8 rfl (by decide))
      (h8 ▸ l_le_lStar 8)

example : lStar 1 = 0 := lStar_eq_A003313_of_le_eight.1
example : ¬ IsNonBrauer 1 := by
  simp [IsNonBrauer, lStar_eq_A003313_of_le_eight.1]

end NumberComplexity
