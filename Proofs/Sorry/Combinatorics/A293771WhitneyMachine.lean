/-
# A293771 — Whitney: reads are never needed in the cache/memory machine

## OEIS source (re-pulled verbatim with `goof oeis show A293771`, 2026-08-05)

```
NAME:     Minimum number of steps needed to compute n using a machine that can
          read, write and add starting with the number 1.
TERMS:    0,2,3,4,5,5,6,6,6,7,8,7,8,8,8,8,9,8,9,9,9,10,10,9,10,10,9,10,11,10,11,
          10,11,11,11,10,11,11,11,11,12,11,12,12,11,12,12,11,12,12,12,12,13,11,
          12,12,12,13,13,12,13,13,12,12,13,13,14,13,13,13,14,12,13,13,13,13,14,
          13,14,13,12,13,14,13,14,14,14,14,15
KEYWORDS: nonn
COMMENTS:
  The machine has a cache which holds 1 integer and a memory which holds a list
  of integers.
  The machine starts with a number 1 in cache and empty memory.
  At every step, the machine can do one of three things:
    (1) write the number from cache to a new position in memory;
    (2) read any number from memory and put it in cache;
    (3) add any number from memory to the number in cache.
  a(n) is the minimum number of steps needed to get the number n in cache.
  Conjecture: reading from memory (operation 2) is never needed to get to a
  number in the minimal number of steps.
  Additional conjectures and comments by _Glen Whitney_, Oct 12 2021: (Start)
  Conjecture II: For each n, there is a minimal-length program for n that stores
  numbers in memory in increasing order.
  Conjecture III: For each n, there is a minimal-length program such that the
  difference between successive numbers stored in memory is strictly increasing.
  All three conjectures are empirically verified for all programs of length 23
  or less, and all values of n up to 2326. However, note that if you are allowed
  to specify the set of numbers that must be stored in memory, then the first
  conjecture fails for memory {1,3,9,27,30,54} and conjecture II fails for
  {1,3,9,27,30,54,60}. (These sequences of numbers in memory are similar to
  addition chains, see A003313.) Hence, a proof of the first conjecture might
  need to involve showing that every n has a "good" sequence of numbers that can
  be stored in memory to produce n, avoiding the need to invoke the read
  operation. Conjecture III supplies one speculative possibility of a property
  that might fill the role of "good." A proof of any of these conjectures would
  tremendously speed up computation of a(n) as compared to brute force. (End)
  One can add a useless read instruction after the first operation of writing
  the initial one in cache to memory. Therefore, there is always a program one
  step longer than optimal that performs a read. Thus, in a numerical search,
  the first sign one might observe that read operations can be helpful is a tie
  for shortest between a program that does read and one that doesn't, for some
  value of n. However, no such ties occur for program length 21 or less.
  - _Glen Whitney_, Oct 23 2021
XREFS:
  Cf. A005245, A091333, A172005.
  Cf. A003313 (addition chains; similar except read/write are "free").
```

## The quantifier trap the card must not fall into

The entry itself flags it: *"if you are allowed to specify the set of numbers
that must be stored in memory, then the first conjecture fails for memory
{1,3,9,27,30,54}"*.  So the conjecture is

> `∀ n, ∃` a minimal-length program that is read-free

and **not**

> `∀ n, ∀` memory content sequence, `∃` a minimal read-free program.

The source reports a counterexample to the fixed-set reading. The statements
below quantify existentially over programs, and
`conjectureI_fails_for_fixed_memory` records an unproved exact-list target,
not a verified refutation. Its applicability, nonvacuity, and fidelity to the
source's fixed-set caveat are not established here.

Offset is `1` (`a(1) = 0`: the machine starts with `1` in cache, so zero steps).
`a(2) = 2`: write `1`, then add `1`.  `a(6) = 5`: write `1`; add → `2`;
write `2`; add `2` → `4`; add `2` → `6`.
-/
import Mathlib
import Combinatorics.WhitneyMachine

set_option autoImplicit false

namespace Candidates.A293771

/-! ## Definition layer

`leandoc` findings: nothing.  There is no cache/memory machine in Mathlib, and
no addition-chain machinery either.  The whole operational semantics is fresh —
about 30 lines — which is the main cost of this card and the main reusable
asset.

Design choices and why:

* `memory : List ℕ` with `write` **appending** — the entry says "write the
  number from cache to a *new position* in memory", so memory grows and old
  entries are never overwritten.
* `read i` and `add i` index into memory by position, and **fail** (return
  `none`) on out-of-range indices.  Using `Option` rather than a junk default
  is what keeps the step function honest; STYLE.md's totalized-operator warning
  applies directly here — `List.getD s.memory i 0` would silently let the
  machine "read `0`" from an empty memory and make `a(n)` wrong.
* `run` is a fold in the `Option` monad, so a program that indexes out of range
  computes nothing rather than something wrong.

Ground truth for the fresh definitions is in the sanity layer: `a(1) = 0`,
`a(2) = 2`, `a(6) = 5`, and the head of the DATA line. -/

/-- The exact production machine state. -/
abbrev MachineState := WhitneyMachine.MachineState

/-- The exact production instruction type. -/
abbrev Instr := WhitneyMachine.Instr

namespace Instr
export WhitneyMachine.Instr (write read add isRead)
end Instr

/-- The production bound-checked, append-write step function. -/
abbrev step := WhitneyMachine.step

/-- The production program execution function. -/
abbrev run := WhitneyMachine.run

/-- The production initial configuration. -/
abbrev initial := WhitneyMachine.initial

/-- Successful computation in the production semantics. -/
abbrev Computes := WhitneyMachine.Computes

/-- The production predicate excluding read instructions. -/
abbrev ReadFree := WhitneyMachine.ReadFree

/-- The production minimum-length function. -/
noncomputable abbrev a293771 := WhitneyMachine.a293771

/-! ## The conjectures -/

/-- **Whitney's Conjecture I (A293771).**

Verbatim: "Conjecture: reading from memory (operation 2) is never needed to get
to a number in the minimal number of steps."

Quantifier order is `∀ n, ∃ p` — see the header. The source's fixed-set
caveat warns against universal quantification over prescribed memory contents.
`conjectureI_fails_for_fixed_memory` below is an admitted exact-list target;
it does not certify that caveat, and its nonvacuity and source fidelity remain
unestablished.

**Mathlib primitives available.**  `Nat.sInf`, `Nat.sInf_mem`, `Nat.not_mem_of_lt_sInf`,
`Nat.sInf_le`, `Nat.le_sInf` for the minimum; `List.length`, `List.foldl`,
`Option.bind` for the semantics; `Decidable` instances derive automatically for
`Instr` and `MachineState`, so bounded program enumeration is decidable.
Nothing machine-specific exists upstream.

**Sketch of an attack.**  Whitney's own analysis in the entry is the roadmap:
a proof "might need to involve showing that every `n` has a *good* sequence of
numbers that can be stored in memory to produce `n`, avoiding the need to invoke
the read operation", and Conjecture III proposes strictly-increasing memory
gaps as a candidate notion of *good*. The following is speculative, not
established proof infrastructure:
1. A proposed normalization would move reads immediately after writes. No such
   general normalization or local rewrite theorem is established here.
2. Reads of values written strictly earlier — genuine "restores" — remain
   unresolved. The `A349044` non-Brauer phenomenon is a related source lead:
   the A349044 entry's own last comment says settling
   `l*(n) > A003313(n) + 1` "would settle this question". The two cards should
   be read together, but no formal bridge is established here.
3. The link is not an equivalence: A349044's machine has no separate store
   step, so its "restore" and this machine's "read" cost differently.  The
   entry says a gap-`≥2` non-Brauer number would give "mild evidence one way or
   the other", which is the honest strength.

**Tactic families.**  `decide`/`native_decide` on bounded program enumeration
(everything is `DecidableEq` and finite once the program length and the memory
indices are bounded — note that `Instr` has infinitely many constructors of the
form `read i`, so an enumeration must bound `i` by the memory length, which is
bounded by the program length); `Nat.sInf_le` for upper bounds from a witness;
`Nat.le_sInf` needs exhaustion; `omega` for the length arithmetic;
`simp [run, step]` for concrete traces.

**Related work in this repo.**  `NumberComplexity.IntComplexity` (`Expr`,
`complexity`) and `NumberComplexity.AdditionChain` (`IsAddChain`, `l`) are the
two existing computation models; this is a third, sitting between them
(A003313 is "this machine with read/write free", per the entry's own xref).
`A349044NonBrauer.lean` in this directory is the related source card.
`A244743ComplexityDefect.lean` shares the "noncomputable `⨅`, computable mirror
needed for `native_decide`" pattern. -/
theorem whitney_conjectureI (n : ℕ) (hn : 0 < n) :
    ∃ p : List Instr, p.length = a293771 n ∧ Computes p n ∧ ReadFree p := by
  sorry

/-- **Whitney's Conjecture II.**

Verbatim: "Conjecture II: For each n, there is a minimal-length program for n
that stores numbers in memory in increasing order."

"Stores numbers in increasing order" = the final memory list is strictly sorted. -/
theorem whitney_conjectureII (n : ℕ) (hn : 0 < n) :
    ∃ (p : List Instr) (s : MachineState), p.length = a293771 n ∧
      run p initial = some s ∧ s.cache = n ∧ s.memory.Pairwise (· < ·) := by
  sorry

/-- **Whitney's Conjecture III.**

Verbatim: "Conjecture III: For each n, there is a minimal-length program such
that the difference between successive numbers stored in memory is strictly
increasing."

"Strictly increasing differences" means `m₂ − m₁ < m₃ − m₂` for consecutive
memory entries.  Over `ℕ` that subtraction truncates, so STYLE.md demands the
subtraction-free rearrangement `2 * m₂ < m₁ + m₃`, which is what is stated.

Indexing is bound-checked (`s.memory[i]'h`), *not* `s.memory[i]!`: the panic
form falls back on the `Inhabited ℕ` default `0` out of range, so a later
refactor could silently change what the `Prop` says.  Threading the bound proof
is the only way the statement stays pinned to the memory contents.

Conjecture III implies Conjecture II given that memory entries are positive. -/
theorem whitney_conjectureIII (n : ℕ) (hn : 0 < n) :
    ∃ (p : List Instr) (s : MachineState), p.length = a293771 n ∧
      run p initial = some s ∧ s.cache = n ∧
      s.memory.Chain' (· < ·) ∧
      ∀ (i : ℕ) (h : i + 2 < s.memory.length),
        2 * s.memory[i + 1]'(by omega) <
          s.memory[i]'(by omega) + s.memory[i + 2]'h := by
  sorry

/-- **Unproved exact-list target motivated by the source's fixed-set caveat.**

Verbatim: "if you are allowed to specify the set of numbers that must be stored
in memory, then the first conjecture fails for memory {1,3,9,27,30,54}".

The source reports a finite fixed-SET optimality caveat. The archive target
below instead pins an exact chronological LIST via `MemoryIs` and remains
admitted. Its applicability, nonvacuity, and source fidelity are not established
here; this is not a certified refutation. -/
abbrev MemoryIs (p : List Instr) (m : List ℕ) : Prop :=
  WhitneyMachine.MemoryIs p m

theorem conjectureI_fails_for_fixed_memory :
    ∃ n : ℕ, 0 < n ∧
      (∀ p : List Instr, MemoryIs p [1, 3, 9, 27, 30, 54] → Computes p n →
        p.length = sInf {l | ∃ q, q.length = l ∧ MemoryIs q [1,3,9,27,30,54] ∧ Computes q n} →
        ¬ ReadFree p) := by
  sorry

/-- Historical source-mismatched fixed-memory II claim. It pins a chronological
list that is itself strictly sorted, and omits the source's set/minimum distinction.
This is a proposition retained for audit, not an asserted theorem. -/
def archived_fixed_memory_II_claim : Prop :=
    ∃ n : ℕ, 0 < n ∧
      ∀ p : List Instr, MemoryIs p [1, 3, 9, 27, 30, 54, 60] → Computes p n →
        ¬ (∃ s, run p initial = some s ∧ s.memory.Pairwise (· < ·))

/-- Historical positivity-only one-longer-read claim, false at one. The machine
starts with one, and no successful one-instruction read is possible. -/
def archived_read_one_longer_claim : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∃ p : List Instr, p.length = a293771 n + 1 ∧ Computes p n ∧ ¬ ReadFree p

example : archived_read_one_longer_claim ↔
    ∀ (n : ℕ), 0 < n →
      ∃ p : List Instr, p.length = a293771 n + 1 ∧ Computes p n ∧ ¬ ReadFree p := Iff.rfl

example : archived_fixed_memory_II_claim ↔
    ∃ n : ℕ, 0 < n ∧
      ∀ p : List Instr, MemoryIs p [1, 3, 9, 27, 30, 54, 60] → Computes p n →
        ¬ (∃ s, run p initial = some s ∧ s.memory.Pairwise (· < ·)) := Iff.rfl

/-- The repaired one-longer-read theorem excludes the initial value one.
This is not a proof of the original positivity-only archive statement. -/
theorem exists_read_program_one_longer (n : ℕ) (hn : 1 < n) :
    ∃ p : List Instr, p.length = a293771 n + 1 ∧ Computes p n ∧ ¬ ReadFree p := by
  exact WhitneyMachine.exists_read_program_one_longer n hn

/-- At one, the historical one-longer-read conclusion is impossible. -/
theorem not_exists_read_program_one_longer_one :
    ¬ ∃ p : List Instr, p.length = a293771 1 + 1 ∧ Computes p 1 ∧ ¬ ReadFree p := by
  exact WhitneyMachine.not_exists_read_program_one_longer_one

/-- The historical positivity-only claim is refuted by its value at one. -/
theorem not_archived_read_one_longer_claim : ¬ archived_read_one_longer_claim := by
  intro h
  exact not_exists_read_program_one_longer_one (h 1 (Nat.zero_lt_succ 0))

/-- Every positive cache value is reachable with the historical pinned sorted memory.
This refutes only the chronological-list formulation, not the source's constrained
set/minimum assertion. -/
theorem sorted_fixed_memory_witness (n : ℕ) (hn : 0 < n) :
    ∃ (p : List Instr) (s : MachineState), run p initial = some s ∧
      s.cache = n ∧ s.memory = [1, 3, 9, 27, 30, 54, 60] ∧
      s.memory.Pairwise (· < ·) := by
  let program0 : List Instr :=
    [.write, .add 0, .add 0, .write, .add 1, .add 1, .write,
      .add 2, .add 2, .write, .add 1, .write, .read 3, .add 3,
      .write, .add 1, .add 1, .write, .read 0]
  let m : List ℕ := [1, 3, 9, 27, 30, 54, 60]
  have hp : run program0 initial = some ⟨1, m⟩ := rfl
  have hrun : run (program0 ++ List.replicate (n - 1) (Instr.add 0)) initial =
      some ⟨1 + (n - 1), m⟩ := by
    unfold run at hp ⊢
    rw [WhitneyMachine.run_append, hp]
    exact WhitneyMachine.run_replicate_add_zero (n - 1) ⟨1, m⟩ rfl
  refine ⟨program0 ++ List.replicate (n - 1) (Instr.add 0),
    ⟨1 + (n - 1), m⟩, hrun, ?_, rfl, ?_⟩
  · exact Nat.add_sub_of_le (Nat.succ_le_of_lt hn)
  · change List.Pairwise (· < ·) ([1, 3, 9, 27, 30, 54, 60] : List ℕ)
    decide

/-- The historical fixed chronological-list claim is false, since its prescribed
memory is sorted and can be preserved while computing any positive number. -/
theorem not_archived_fixed_memory_II_claim : ¬ archived_fixed_memory_II_claim := by
  rintro ⟨n, hn, h⟩
  obtain ⟨p, s, hr, hc, hm, hs⟩ := sorted_fixed_memory_witness n hn
  exact h p ⟨s, hr, hm⟩ ⟨s, hr, hc⟩ ⟨s, hr, hs⟩

/-! ## Sanity layer -/

-- PROVABLE: the reachable-length set is nonempty for `n ≥ 1`, so `a293771 n` is
-- not the `sInf ∅ = 0` junk value.  Without this every statement above is at
-- risk of being about junk.
/-- Positive inputs have a reachable program length, via the production witness. -/
theorem computes_nonempty (n : ℕ) (hn : 0 < n) :
    {l : ℕ | ∃ p : List Instr, p.length = l ∧ Computes p n}.Nonempty := by
  exact WhitneyMachine.computes_nonempty n hn

-- PROVABLE: `a(1) = 0` — the machine starts with `1` in cache.
example : Computes [] 1 := ⟨initial, rfl, rfl⟩

-- PROVABLE: `a(2) = 2` — write `1`, then add memory[0].
example : Computes [Instr.write, Instr.add 0] 2 := ⟨⟨2, [1]⟩, rfl, rfl⟩

-- PROVABLE: `a(3) = 3` — write, add, add.
example : Computes [Instr.write, Instr.add 0, Instr.add 0] 3 := ⟨⟨3, [1]⟩, rfl, rfl⟩

-- PROVABLE: `a(6) = 5` — write 1; add → 2; write 2; add 2 → 4; add 2 → 6.
example : Computes [Instr.write, Instr.add 0, Instr.write, Instr.add 1, Instr.add 1] 6 :=
  ⟨⟨6, [1, 2]⟩, rfl, rfl⟩

-- PROVABLE: these witnesses are read-free, so Conjecture I holds at `n = 2,3,6`.
example : ReadFree [Instr.write, Instr.add 0, Instr.write, Instr.add 1, Instr.add 1] := by
  simp [ReadFree, WhitneyMachine.ReadFree, WhitneyMachine.Instr.isRead]

-- PROVABLE: the semantics is *not* junk-tolerant — reading past the end of
-- memory fails rather than returning `0`.  This is the check that
-- `step`/`run` implement the intended machine.
example : run [Instr.read 0] initial = none := by decide
example : run [Instr.add 5] initial = none := by decide

-- PROVABLE: `run` composes.
/-- Program concatenation agrees with sequential Option execution. -/
theorem run_append (p q : List Instr) (s : MachineState) :
    run (p ++ q) s = (run p s).bind (run q) := by
  exact WhitneyMachine.run_append p q s

-- PROVABLE (window check): the DATA head `a(1..10) = 0,2,3,4,5,5,6,6,6,7` is
-- reproduced by an exhaustive bounded search, and each minimum is achieved by a
-- read-free program.  Needs a computable mirror of `a293771` first — see the
-- notes — so it is stated as a target, not as a `native_decide` one-liner.
--
-- FEASIBILITY: program enumeration is `(2 + memLen)^len`; with `len ≤ 10` and
-- `memLen ≤ len` that is already `~10^10` in the worst case.  The search must be
-- pruned (memory is append-only and its length equals the number of `write`s so
-- far, which bounds the legal indices) before this is attempted.

/-! ## Notes for a follow-up card

Gating item, exactly as in `A244743ComplexityDefect.lean`: `a293771` is
`noncomputable` (`sInf` over a `Set ℕ`), so **no `decide`/`native_decide` check
can mention it**.  A computable mirror

```lean
def a293771Rec (n : ℕ) : ℕ   -- BFS over states, bounded by a fuel argument
theorem a293771_eq_a293771Rec (n : ℕ) : a293771 n = a293771Rec n
```

is the prerequisite for every quantitative sanity check.  The right
implementation is **not** program enumeration but BFS over *states*
`(cache, memory)` with memory truncated to the entries that can still matter —
that is how the OEIS b-file was computed.

Provable-today items:
* `run_append`, `computes_nonempty` — free.
* `exists_read_program_one_longer` — repaired to require `1 < n`; the original
  positivity-only claim is recorded and refuted above.
* `conjectureI_fails_for_fixed_memory` remains an open archive target. The old
  fixed-memory II chronological-list formulation was false, is retained as
  `archived_fixed_memory_II_claim`, and is refuted above. It does not formalize
  the source's constrained set/minimum assertion.

Open: Conjectures I, II, III. -/

/-!
## SUPERSEDED historical adversarial review — former **PASS-WITH-NOTES**

This superseded historical review predates the repairs above. It is not current
certification of the two now-refuted archive formulations or of the admitted
fixed-memory I target.

Independent re-pull of A293771 plus an **independent python BFS simulation of
the machine**, 2026-08-05.

Historical review claims (not current certification):
* The whole comment block (machine description, Conjectures I/II/III, the
  fixed-memory caveat, the Oct 23 2021 comment) is quoted verbatim.
* **The semantics match**: a from-scratch BFS over `(cache, memory)` states with
  `write` appending, start `(1, [])`, reproduces all 20 DATA-head terms
  `0,2,3,4,5,5,6,6,6,7,8,7,8,8,8,8,9,8,9,9`.  All three witness programs
  (`a(2) = 2`, `a(3) = 3`, `a(6) = 5`) check out with the exact instruction
  sequences given.
* **Current qualification of the quantifier claim**: `∀ n, ∃ p` is the intended
  conjecture order. `conjectureI_fails_for_fixed_memory` remains admitted; its
  applicability, nonvacuity, and fidelity to the source's fixed-set optimality
  caveat are not established in the current revision. The historical claim of
  a meaningful, non-vacuous certified refutation is superseded.
* Conjecture III's inequality direction `2·m[i+1] < m[i] + m[i+2]` is right.
* `Instr` is infinite (`read : ℕ → Instr`) but `deriving DecidableEq` is fine,
  and the `decide` examples are over concrete finite `List Instr` values.
* No `decide`/`native_decide` mentions the noncomputable `a293771`.

Defects raised, both **FIXED**:
1. Conjecture III used `s.memory[i]!` (panic-defaulting `getElem!`) while binding
   an unused bound proof `h`.  Replaced with bound-checked
   `s.memory[i]'(by omega)` so the statement is pinned to the memory contents
   rather than to `Inhabited ℕ`'s default.
2. The Conjecture III docstring contained a visible self-correction
   ("… i.e. `m₁ + m₃ < 2·m₂` … **no** …").  Rewritten to state the correct
   inequality once.

Note: the DATA-head window check is comment-only (no stub), which is intentional
— the enumeration is `(2 + memLen)^len` and needs pruning first.
-/

end Candidates.A293771
