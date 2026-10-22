import Sorry.Combinatorics.SelfridgeLacampagne
import Mathlib.Tactic

set_option autoImplicit false

namespace SelfridgeLacampagne

/-- The number of adjacent changes in a finite binary window. -/
def transitionCount : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a = b then 0 else 1) + transitionCount (b :: rest)

example : transitionCount [false, false, true, true, false] = 2 := rfl
example : transitionCount ([] : List Bool) = 0 := rfl
example : transitionCount [true] = 0 := rfl

/-- Appending one bit adds exactly the final edge to the transition count. -/
theorem transitionCount_append (a z y : Bool) (middle : List Bool) :
    transitionCount (a :: middle ++ [z, y]) =
      transitionCount (a :: middle ++ [z]) + (if z = y then 0 else 1) := by
  induction middle generalizing a with
  | nil => simp [transitionCount]
  | cons b rest ih =>
    have htail := ih b
    simp only [List.cons_append] at htail
    simp only [List.cons_append, transitionCount]
    rw [htail]
    omega

/-- The parity of the transition count records whether the endpoints differ. -/
theorem transitionCount_parity (a z : Bool) (middle : List Bool) :
    transitionCount (a :: middle ++ [z]) % 2 = (if a = z then 0 else 1) := by
  induction middle generalizing a with
  | nil => cases a <;> cases z <;> decide
  | cons b rest ih =>
    have hp := ih b
    simp only [List.cons_append, transitionCount]
    cases a <;> cases b <;> cases z <;> simp_all <;> omega

/-- A nonmonochromatic incoming/last/outgoing triple cannot lower half the
number of transitions, rounded down, when a binary window shifts. -/
theorem transitionCount_half_le_shift (a z y : Bool) (middle : List Bool)
    (hnae : ¬ (a = z ∧ z = y)) :
    transitionCount (a :: middle ++ [z]) / 2 ≤
      transitionCount (middle ++ [z, y]) / 2 := by
  cases middle with
  | nil =>
    cases a <;> cases z <;> cases y <;> decide
  | cons b rest =>
    have hp := transitionCount_parity a z (b :: rest)
    have ha := transitionCount_append b z y rest
    simp only [List.cons_append] at ha
    simp only [List.cons_append, transitionCount] at hp ⊢
    rw [ha]
    cases a <;> cases b <;> cases z <;> cases y <;> simp_all <;> omega

example : ¬ (false = true ∧ true = false) ∧
    transitionCount [false, false, true, true, false] / 2 = 1 := by decide

/-- Constant windows have no adjacent transitions, including at length zero. -/
theorem transitionCount_replicate (n : ℕ) (b : Bool) :
    transitionCount (List.replicate n b) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [List.replicate_succ, transitionCount] using ih

/-- Iterating genuine nonmonochromatic shifts preserves the window invariant.
The witnesses describe the entire old and new windows, not just their heights. -/
theorem transitionCount_half_mono (W : ℕ → List Bool) (N : ℕ)
    (hstep : ∀ i, i < N → ∃ a z y : Bool, ∃ middle : List Bool,
      W i = a :: middle ++ [z] ∧ W (i + 1) = middle ++ [z, y] ∧
      ¬ (a = z ∧ z = y)) :
    transitionCount (W 0) / 2 ≤ transitionCount (W N) / 2 := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    have hbefore := ih (fun i hi => hstep i (by omega))
    obtain ⟨a, z, y, middle, hold, hnew, hnae⟩ := hstep N (by omega)
    have hlast := transitionCount_half_le_shift a z y middle hnae
    rw [← hold, ← hnew] at hlast
    exact hbefore.trans hlast

/-- A window path starting with at least two transitions cannot end in a
constant window if every shift obeys the nonmonochromatic triple rule. -/
theorem no_constant_terminal_window (W : ℕ → List Bool) (N m : ℕ) (b : Bool)
    (hstart : 2 ≤ transitionCount (W 0))
    (hstep : ∀ i, i < N → ∃ a z y : Bool, ∃ middle : List Bool,
      W i = a :: middle ++ [z] ∧ W (i + 1) = middle ++ [z, y] ∧
      ¬ (a = z ∧ z = y))
    (hterminal : W N = List.replicate m b) : False := by
  have hmono := transitionCount_half_mono W N hstep
  rw [hterminal, transitionCount_replicate] at hmono
  omega

/-- A length-`m` window of indexed binary digits, starting at `i`. -/
def binaryWindow (s : ℕ → Bool) (i m : ℕ) : List Bool :=
  (List.range' i m).map s

example : binaryWindow (fun i => i % 2 == 1) 0 3 = [false, true, false] := rfl
example (s : ℕ → Bool) : binaryWindow s 7 0 = [] := rfl

/-- Deleting the first digit and appending the next digit shifts a window. -/
theorem binaryWindow_shift (s : ℕ → Bool) (i k : ℕ) :
    binaryWindow s i (k + 2) =
      s i :: binaryWindow s (i + 1) k ++ [s (i + k + 1)] ∧
    binaryWindow s (i + 1) (k + 2) =
      binaryWindow s (i + 1) k ++ [s (i + k + 1), s (i + k + 2)] := by
  constructor
  · rw [binaryWindow, List.range'_succ, List.map_cons, List.range'_concat]
    simp [binaryWindow, List.map_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · rw [binaryWindow, List.range'_concat, List.range'_concat]
    simp [binaryWindow, List.map_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      List.append_assoc]

/-- Indexed NAE digit constraints forbid a terminal zero block whenever the
initial window has at least two transitions. No disjointness is assumed. -/
theorem no_binary_terminal_window (s : ℕ → Bool) (N m : ℕ) (hm : 2 ≤ m)
    (hstart : 2 ≤ transitionCount (binaryWindow s 0 m))
    (hnae : ∀ i, i < N → ¬ (s i = s (i + m - 1) ∧ s (i + m - 1) = s (i + m)))
    (hterminal : ∀ j, j < m → s (N + j) = false) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  apply no_constant_terminal_window (fun i => binaryWindow s i (k + 2)) N (k + 2)
    false hstart
  · intro i hi
    refine ⟨s i, s (i + k + 1), s (i + k + 2), binaryWindow s (i + 1) k,
      (binaryWindow_shift s i k).1, (binaryWindow_shift s i k).2, ?_⟩
    have hindex : i + (k + 2) - 1 = i + k + 1 := by omega
    simpa only [hindex, Nat.add_assoc] using hnae i hi
  · unfold binaryWindow
    have ht : ∀ x ∈ List.range' N (k + 2), s x = false := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hx
      simpa only [Nat.one_mul] using hterminal j hj
    simpa using List.map_eq_replicate_iff.mpr ht

/-- Appending any suffix cannot remove transitions already present. -/
theorem transitionCount_le_append (L R : List Bool) :
    transitionCount L ≤ transitionCount (L ++ R) := by
  induction L with
  | nil => simp [transitionCount]
  | cons a tail ih =>
    cases tail with
    | nil => simp [transitionCount]
    | cons b rest =>
      simp only [List.cons_append, transitionCount] at ih ⊢
      omega

/-- Splitting the length splits an indexed binary window into consecutive pieces. -/
theorem binaryWindow_add (s : ℕ → Bool) (i p q : ℕ) :
    binaryWindow s i (p + q) = binaryWindow s i p ++ binaryWindow s (i + p) q := by
  simp only [binaryWindow, ← List.range'_append, Nat.one_mul, List.map_append]

/-- The first five digits of either `0011…` prefix already give two transitions;
no formula for the transition count of the remaining prefix is needed. -/
theorem two_le_transitionCount_of_first_five (s : ℕ → Bool) (m : ℕ)
    (hm : 5 ≤ m) (a : Bool)
    (hprefix : binaryWindow s 0 5 = [a, a, !a, !a, a]) :
    2 ≤ transitionCount (binaryWindow s 0 m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 5 + k := ⟨m - 5, by omega⟩
  rw [binaryWindow_add, hprefix]
  have hcount : transitionCount [a, a, !a, !a, a] = 2 := by cases a <;> rfl
  have hbound := transitionCount_le_append [a, a, !a, !a, a] (binaryWindow s (0 + 5) k)
  simpa only [hcount] using hbound

/-- A paired-bit prefix and NAE digit constraints rule out a terminal zero
window, including when the terminal window overlaps the initial window. -/
theorem no_binary_terminal_window_of_first_five (s : ℕ → Bool) (N m : ℕ)
    (hm : 5 ≤ m) (a : Bool)
    (hprefix : binaryWindow s 0 5 = [a, a, !a, !a, a])
    (hnae : ∀ i, i < N → ¬ (s i = s (i + m - 1) ∧ s (i + m - 1) = s (i + m)))
    (hterminal : ∀ j, j < m → s (N + j) = false) : False := by
  exact no_binary_terminal_window s N m (by omega)
    (two_le_transitionCount_of_first_five s m hm a hprefix) hnae hterminal

example : 5 ≤ (5 : ℕ) ∧
    binaryWindow (fun i => i == 2 || i == 3 || i == 5) 0 5 =
      [false, false, true, true, false] ∧
    (∀ i : ℕ, i < 1 →
      ¬ ((i == 2 || i == 3 || i == 5) =
          (i + 5 - 1 == 2 || i + 5 - 1 == 3 || i + 5 - 1 == 5) ∧
        (i + 5 - 1 == 2 || i + 5 - 1 == 3 || i + 5 - 1 == 5) =
          (i + 5 == 2 || i + 5 == 3 || i + 5 == 5))) := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have hzero : i = 0 := by omega
  subst i
  decide

example : binaryWindow (fun i => !(i == 2 || i == 3 || i == 5)) 0 5 =
    [true, true, false, false, true] := rfl

example : (∀ j : ℕ, j < 5 → (fun _ : ℕ => false) (1 + j) = false) ∧
    (List.replicate 5 false).length = 5 := by simp

end SelfridgeLacampagne
