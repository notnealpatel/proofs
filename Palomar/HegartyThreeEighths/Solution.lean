import Enumerative.HegartyThreeEighths

/-!
# Hegarty's three-eighths solution

The challenge declarations are repeated here without importing `Challenge.lean`.  The
proof compares the two least-choice constructions extension by extension, identifies the
independently defined sequence with `A094870.a`, and applies the repository proof of
Hegarty's Theorem 3.3.
-/

set_option autoImplicit false

namespace Palomar.HegartyThreeEighths

/-- Admissibility of `t` after the reversed prefix `v`.  It requires positivity,
non-reuse, and excludes exactly the progressions whose last term would be `t`:
for `i = j+1`, `t + a(n-2i) ≠ 2*a(n-i)`. -/
def IsCandList (v : List ℕ) (t : ℕ) : Prop :=
  1 ≤ t ∧ t ∉ v ∧ ∀ j < v.length, 2 * j + 2 ≤ v.length →
    t + v.getD (2 * j + 1) 0 ≠ 2 * v.getD j 0

/-- Admissibility for a finite reversed prefix is decidable. -/
instance instDecidableIsCandList (v : List ℕ) (t : ℕ) : Decidable (IsCandList v t) := by
  unfold IsCandList
  infer_instance

example : IsCandList [] 1 := by simp [IsCandList]
example : ¬ IsCandList [] 0 := by simp [IsCandList]
example : IsCandList [1] 2 := by simp [IsCandList]
example : ¬ IsCandList [2, 1] 3 := by
  rintro ⟨_, _, hAP⟩
  exact (hAP 0 (by decide) (by decide)) (by decide)

/-- The largest entry of a list, with value `0` on the empty list. -/
def listMax (v : List ℕ) : ℕ := v.foldr max 0

example : listMax [] = 0 := rfl
example : listMax [3, 7, 2] = 7 := rfl

/-- Every list member is bounded by `listMax`. -/
theorem le_listMax : ∀ {v : List ℕ} {x : ℕ}, x ∈ v → x ≤ listMax v := by
  intro v
  induction v with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons b w ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_max_left _ _
    · exact (ih hx').trans (le_max_right _ _)

/-- An out-of-range lookup (which defaults to zero) is also bounded by `listMax`. -/
theorem getD_le_listMax (v : List ℕ) (k : ℕ) : v.getD k 0 ≤ listMax v := by
  by_cases hk : k < v.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact le_listMax (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- Every finite prefix has an admissible continuation. -/
theorem exists_isCandList (v : List ℕ) : ∃ t, IsCandList v t := by
  refine ⟨2 * listMax v + 1, by omega, ?_, ?_⟩
  · intro hmem
    have hbound := le_listMax hmem
    omega
  · intro j _ _
    have hleft := getD_le_listMax v (2 * j + 1)
    have hmid := getD_le_listMax v j
    omega

/-- The least positive, unused continuation that creates no forbidden arithmetic
progression. -/
def nextTerm (v : List ℕ) : ℕ := Nat.find (exists_isCandList v)

/-- `nextTerm` is characterized by admissibility and exclusion of all smaller values. -/
theorem nextTerm_eq {v : List ℕ} {t : ℕ} (ht : IsCandList v t)
    (hmin : ∀ k < t, ¬ IsCandList v k) : nextTerm v = t :=
  (Nat.find_eq_iff _).mpr ⟨ht, hmin⟩

example : nextTerm [] = 1 := by
  apply nextTerm_eq
  · simp [IsCandList]
  · intro k hk
    simp only [IsCandList, List.not_mem_nil, not_false_eq_true, List.length_nil,
      true_and]
    omega

/-- The reversed list of the first `n` values of the greedy sequence. -/
def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => nextTerm (pre n) :: pre n

example : pre 0 = [] := rfl

/-- Hegarty's greedy permutation with zero-based indexing: `a n = πg(n+1)`. -/
def a (n : ℕ) : ℕ := nextTerm (pre n)

example : a 0 = 1 := by
  change nextTerm [] = 1
  exact nextTerm_eq (by simp [IsCandList]) (by
    intro k hk
    simp only [IsCandList, List.not_mem_nil, not_false_eq_true, List.length_nil,
      true_and]
    omega)

private theorem nextTerm_eq_source (v : List ℕ) :
    nextTerm v = A094870.nextTerm v := by
  unfold nextTerm A094870.nextTerm
  apply Nat.le_antisymm
  · apply Nat.find_min' (exists_isCandList v)
    simpa only [IsCandList, A094870.IsCandList] using
      (Nat.find_spec (A094870.exists_isCandList v))
  · apply Nat.find_min' (A094870.exists_isCandList v)
    simpa only [IsCandList, A094870.IsCandList] using
      (Nat.find_spec (exists_isCandList v))

private theorem nextTerm_eq_source_of_eq {v w : List ℕ} (hvw : v = w) :
    nextTerm v = A094870.nextTerm w := by
  subst w
  exact nextTerm_eq_source v

private theorem pre_eq_source : ∀ n : ℕ, pre n = A094870.pre n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnext : nextTerm (pre n) = A094870.nextTerm (A094870.pre n) :=
      nextTerm_eq_source_of_eq ih
    exact congrArg₂ List.cons hnext ih

private theorem a_eq_source (n : ℕ) : a n = A094870.a n := by
  exact nextTerm_eq_source_of_eq (pre_eq_source n)

/-- Hegarty's published three-eighths lower bound, in zero-based indexing. -/
theorem hegarty_three_eighths (n : ℕ) : 3 * (n + 1) ≤ 8 * a n := by
  rw [a_eq_source]
  exact A094870.hegarty_three_eighths n

-- The statement is inhabited at its boundary index and the indexing convention is nonvacuous.
example : 3 * (0 + 1) ≤ 8 * a 0 := by
  have ha : a 0 = 1 := by
    change nextTerm [] = 1
    exact nextTerm_eq (by simp [IsCandList]) (by
      intro k hk
      simp only [IsCandList, List.not_mem_nil, not_false_eq_true, List.length_nil,
        true_and]
      omega)
  omega

#check @hegarty_three_eighths
#print axioms Palomar.HegartyThreeEighths.hegarty_three_eighths

end Palomar.HegartyThreeEighths
