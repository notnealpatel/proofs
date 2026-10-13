import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace WhitneyMachine

/-- Machine state: one natural number in cache and a list of natural numbers in memory. -/
structure MachineState where
  cache : ℕ
  memory : List ℕ
  deriving DecidableEq, Repr

/-- Instructions write the cache, read a memory position, or add a memory position. -/
inductive Instr where
  | write : Instr
  | read : ℕ → Instr
  | add : ℕ → Instr
  deriving DecidableEq, Repr

/-- Identify the read instructions. -/
def Instr.isRead : Instr → Bool
  | .read _ => true
  | _ => false

/-- Execute one instruction, appending writes and rejecting out-of-range reads and adds. -/
def step (s : MachineState) : Instr → Option MachineState
  | .write => some ⟨s.cache, s.memory ++ [s.cache]⟩
  | .read i => (s.memory[i]?).map fun v => ⟨v, s.memory⟩
  | .add i => (s.memory[i]?).map fun v => ⟨s.cache + v, s.memory⟩

/-- Execute a program, propagating any failed instruction. -/
def run : List Instr → MachineState → Option MachineState
  | [], s => some s
  | i :: p, s => (step s i).bind (run p)

/-- The initial cache is one and the initial memory is empty. -/
def initial : MachineState := ⟨1, []⟩

/-- A program computes a number when successful execution leaves that number in cache. -/
def Computes (p : List Instr) (n : ℕ) : Prop :=
  ∃ s : MachineState, run p initial = some s ∧ s.cache = n

/-- A program is read-free when none of its instructions is a read. -/
def ReadFree (p : List Instr) : Prop := ∀ i ∈ p, i.isRead = false

/-- The infimum of the program lengths computing a number; positive inputs have witnesses. -/
noncomputable def a293771 (n : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ p : List Instr, p.length = l ∧ Computes p n}

/-- A program has prescribed memory when its final memory is exactly the given list. -/
def MemoryIs (p : List Instr) (m : List ℕ) : Prop :=
  ∃ s : MachineState, run p initial = some s ∧ s.memory = m

example : Instr.isRead (.read 0) = true := rfl
example : Instr.isRead .write = false := rfl
example : Instr.isRead (.add 0) = false := rfl
example : initial = ⟨1, []⟩ := rfl
example : step ⟨2, [1]⟩ .write = some ⟨2, [1, 2]⟩ := rfl
example : step ⟨2, [1]⟩ (.read 0) = some ⟨1, [1]⟩ := rfl
example : step ⟨2, [1]⟩ (.add 0) = some ⟨3, [1]⟩ := rfl
example : run [Instr.read 0] initial = none := rfl
example : run [Instr.add 5] initial = none := rfl
example : Computes [] 1 := ⟨initial, rfl, rfl⟩
example : ReadFree [Instr.write, Instr.add 0] := by simp [ReadFree, Instr.isRead]
example : MemoryIs [Instr.write] [1] := ⟨⟨1, [1]⟩, rfl, rfl⟩
example (n : ℕ) : a293771 n =
    sInf {l : ℕ | ∃ p : List Instr, p.length = l ∧ Computes p n} := rfl

/-- Concatenating programs executes the first and then, on success, the second. -/
theorem run_append (p q : List Instr) (s : MachineState) :
    run (p ++ q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    simp only [List.cons_append, run, ih, Option.bind_assoc]

/-- Repeatedly adding a stored one increases the cache by the number of additions. -/
theorem run_replicate_add_zero (k : ℕ) (s : MachineState)
    (h : s.memory[0]? = some 1) :
    run (List.replicate k (Instr.add 0)) s = some ⟨s.cache + k, s.memory⟩ := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, run, step, h, Option.map_some, Option.bind]
    rw [ih ⟨s.cache + 1, s.memory⟩ h]
    simp [Nat.add_comm, Nat.add_left_comm]

example : (initial.memory ++ [initial.cache])[0]? = some 1 := rfl
example : (⟨1, [1]⟩ : MachineState).memory[0]? = some 1 := rfl

/-- Writing the initial one and adding it repeatedly computes every positive number. -/
theorem computes_write_replicate (n : ℕ) (hn : 0 < n) :
    Computes (Instr.write :: List.replicate (n - 1) (Instr.add 0)) n := by
  refine ⟨⟨1 + (n - 1), [1]⟩, ?_, ?_⟩
  · change run (List.replicate (n - 1) (Instr.add 0)) ⟨1, [1]⟩ = _
    exact run_replicate_add_zero (n - 1) ⟨1, [1]⟩ rfl
  · exact Nat.add_sub_of_le (Nat.succ_le_of_lt hn)

example : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- Every positive number has a nonempty set of successful program lengths. -/
theorem computes_nonempty (n : ℕ) (hn : 0 < n) :
    {l : ℕ | ∃ p : List Instr, p.length = l ∧ Computes p n}.Nonempty := by
  let p := Instr.write :: List.replicate (n - 1) (Instr.add 0)
  exact ⟨p.length, p, rfl, computes_write_replicate n hn⟩

/-- For every positive number, the infimum length is attained by a successful program. -/
theorem exists_minimal_program (n : ℕ) (hn : 0 < n) :
    ∃ p : List Instr, p.length = a293771 n ∧ Computes p n :=
  Nat.sInf_mem (computes_nonempty n hn)

/-- A successful program computing a number larger than one starts with a write. -/
theorem computes_starts_write (p : List Instr) (n : ℕ) (hn : 1 < n)
    (hp : Computes p n) : ∃ t, p = Instr.write :: t := by
  obtain ⟨s, hr, hc⟩ := hp
  cases p with
  | nil =>
    have hs : initial = s := Option.some.inj hr
    subst s
    exact False.elim ((Nat.ne_of_gt hn) hc.symm)
  | cons i t =>
    cases i with
    | write => exact ⟨t, rfl⟩
    | read i => simp [run, step, initial] at hr
    | add i => simp [run, step, initial] at hr

/-- For inputs larger than one, a redundant read after the first write adds one step
without changing the result. The stronger historical claim with only positivity is false. -/
theorem exists_read_program_one_longer (n : ℕ) (hn : 1 < n) :
    ∃ p : List Instr, p.length = a293771 n + 1 ∧ Computes p n ∧ ¬ ReadFree p := by
  obtain ⟨p, hl, hp⟩ := exists_minimal_program n (Nat.zero_lt_of_lt hn)
  obtain ⟨t, rfl⟩ := computes_starts_write p n hn hp
  refine ⟨Instr.write :: Instr.read 0 :: t, ?_, ?_, ?_⟩
  · simp only [List.length_cons] at hl ⊢
    rw [← hl]
  · obtain ⟨s, hr, hc⟩ := hp
    exact ⟨s, hr, hc⟩
  · intro hf
    have hread := hf (Instr.read 0) (by simp)
    change true = false at hread
    cases hread

/-- The initial cache computes one without any instructions, so its minimum length is zero. -/
theorem a293771_one : a293771 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨[], rfl, initial, rfl, rfl⟩

/-- No length-one successful program for one contains a read: the only successful
initial instruction is a write. This refutes the positivity-only historical claim. -/
theorem not_exists_read_program_one_longer_one :
    ¬ ∃ p : List Instr, p.length = a293771 1 + 1 ∧ Computes p 1 ∧ ¬ ReadFree p := by
  rintro ⟨p, hl, ⟨s, hr, hc⟩, hf⟩
  rw [a293771_one] at hl
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hl
  cases i with
  | write => exact hf (by simp [ReadFree, Instr.isRead])
  | read i => simp [run, step, initial] at hr
  | add i => simp [run, step, initial] at hr

example : 1 < (2 : ℕ) := by decide
example : Computes [Instr.write, Instr.add 0] 2 := ⟨⟨2, [1]⟩, rfl, rfl⟩

end WhitneyMachine
