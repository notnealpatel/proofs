import Mathlib

/-!
# A092482 challenge

This file gives a self-contained, zero-indexed greedy definition of A092482.  The
recursion starts from `{1}`.  Its sole exception permits the ordered arithmetic
progression `(1, 2, 3)`; every other ordered three-term arithmetic progression is
forbidden.  The map `binToTernary` reads the binary digits of its input as a base-3
numeral, so it is the zero-offset version of A005836.
-/

set_option autoImplicit false

namespace Palomar.A092482

/-- Reinterpret the binary digits of `n` as ternary digits.  In particular this map
starts `0, 1, 3, 4, 9, ...`, the zero-offset interpretation of A005836. -/
def binToTernary (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 n)

/-- Ground-truth check for the zero-offset digit map. -/
@[simp] theorem binToTernary_zero : binToTernary 0 = 0 := by
  simp [binToTernary]

/-- A set obeys the A092482 rule when every strictly ordered three-term arithmetic
progression in it is exactly the exceptional seed progression `(1, 2, 3)`. -/
def NoThreeAPExceptSeed (s : Set ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
    a < b → b < c → a + c = 2 * b → a = 1 ∧ b = 2 ∧ c = 3

/-- The singleton starting set satisfies the exceptional-progression rule. -/
theorem noThreeAPExceptSeed_singleton :
    NoThreeAPExceptSeed (↑({1} : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc hab hbc habc
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb hc
  omega

/-- The finite exceptional-progression rule is decidable. -/
instance decidableNoThreeAPExceptSeed (s : Finset ℕ) :
    Decidable (NoThreeAPExceptSeed (↑s : Set ℕ)) :=
  decidable_of_iff
    (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      a < b → b < c → a + c = 2 * b → a = 1 ∧ b = 2 ∧ c = 3)
    (by simp only [NoThreeAPExceptSeed, Finset.mem_coe])

/-- `k` is a legal next term when it exceeds the entire finite prefix and adjoining it
creates no strictly ordered three-term arithmetic progression other than `(1, 2, 3)`. -/
def IsGoodStep (s : Finset ℕ) (k : ℕ) : Prop :=
  (∀ a ∈ s, a < k) ∧ NoThreeAPExceptSeed (↑(insert k s) : Set ℕ)

/-- Legal-step membership is decidable. -/
instance (s : Finset ℕ) : DecidablePred (IsGoodStep s) := fun k =>
  inferInstanceAs (Decidable ((∀ a ∈ s, a < k) ∧
    NoThreeAPExceptSeed (↑(insert k s) : Set ℕ)))

/-- A finite legal prefix always has a legal extension; a value above twice its maximum
cannot complete a new arithmetic progression. -/
theorem exists_isGoodStep {s : Finset ℕ}
    (hs : NoThreeAPExceptSeed (↑s : Set ℕ)) : ∃ k, IsGoodStep s k := by
  have hM : ∀ x ∈ s, x ≤ s.sup id := fun x hx => Finset.le_sup (f := id) hx
  refine ⟨2 * s.sup id + 1, fun a ha => by have := hM a ha; omega, ?_⟩
  intro a ha b hb c hc hab hbc habc
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb hc
  rcases hc with rfl | hc
  · rcases ha with rfl | ha
    · omega
    · rcases hb with rfl | hb
      · omega
      · have h1 := hM a ha
        have h2 := hM b hb
        omega
  · have h3 := hM c hc
    rcases ha with rfl | ha
    · omega
    · rcases hb with rfl | hb
      · omega
      · exact hs a ha b hb c hc hab hbc habc

/-- The next greedy term is the least legal extension of `s`. -/
def nextGreedy (s : Finset ℕ) (hs : NoThreeAPExceptSeed (↑s : Set ℕ)) : ℕ :=
  Nat.find (exists_isGoodStep hs)

/-- The selected next term really is a legal extension. -/
theorem nextGreedy_isGoodStep (s : Finset ℕ)
    (hs : NoThreeAPExceptSeed (↑s : Set ℕ)) : IsGoodStep s (nextGreedy s hs) :=
  Nat.find_spec (exists_isGoodStep hs)

/-- Greedy prefix sets, bundled with the invariant that only the seed progression is
permitted.  The base prefix is `{1}`. -/
def greedyAux : ℕ → {s : Finset ℕ // NoThreeAPExceptSeed (↑s : Set ℕ)}
  | 0 => ⟨{1}, noThreeAPExceptSeed_singleton⟩
  | n + 1 =>
    ⟨insert (nextGreedy (greedyAux n).1 (greedyAux n).2) (greedyAux n).1,
      (nextGreedy_isGoodStep (greedyAux n).1 (greedyAux n).2).2⟩

/-- The finite prefix after `n` extensions of the starting singleton. -/
def prefixSet (n : ℕ) : Finset ℕ := (greedyAux n).1

/-- Every recursively constructed prefix obeys the exceptional-progression rule. -/
theorem prefixSet_noThreeAPExceptSeed (n : ℕ) :
    NoThreeAPExceptSeed (↑(prefixSet n) : Set ℕ) := (greedyAux n).2

/-- The zero-indexed increasing greedy sequence: it starts at `1`, and thereafter takes
the least integer above the whole preceding prefix which creates no progression except
the explicitly permitted `(1, 2, 3)`.  Thus `greedySeq r` represents OEIS `a(r+1)`. -/
def greedySeq : ℕ → ℕ
  | 0 => 1
  | n + 1 => nextGreedy (prefixSet n) (prefixSet_noThreeAPExceptSeed n)

/-- Ground-truth check for the initial index of the zero-indexed greedy sequence. -/
@[simp] theorem greedySeq_zero : greedySeq 0 = 1 := rfl

/-- The corrected closed form for A092482.  The OEIS index is one-based while
`greedySeq` is zero-based; `binToTernary (m+1)` is A005836 at zero offset. -/
theorem greedySeq_add_two (m : ℕ) :
    greedySeq (m + 2) =
      1 + 2 ^ Nat.log 2 (m + 1) + binToTernary (m + 1) := by
  sorry

end Palomar.A092482

#check @Palomar.A092482.greedySeq_add_two
