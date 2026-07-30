import Mathlib

/-!
# Addition chains and the shortest-chain length function (OEIS A003313)

An *addition chain* for `n` is a finite sequence `1 = a₀, a₁, …, a_r = n` in which
every element after the first is a sum `aᵢ = aⱼ + a_k` of two earlier elements
(`j, k < i`, the summands not necessarily distinct — `j = k` gives a doubling).
`l n` is the minimal number of additions `r` over all addition chains for `n`;
this is OEIS A003313 ("Length of shortest addition chain for n", equivalently the
minimal number of multiplications needed to compute an `n`-th power).

**Representation.** A chain is stored as a `List ℕ` in *reverse* order, most
recent element first: `IsAddChain c` holds when `c = [a_r, …, a₁, a₀]` with
`a₀ = 1` and each consed element the sum of two members of its tail (two earlier
chain elements).  The suffix order makes the inductive predicate and its
inversion lemmas structural.  `AdditionChain n` is the subtype of chains whose
head (the final chain element) is `n`, and

`l n = ⨅ c : AdditionChain n, chainSteps c.val`

is a subtype-indexed infimum over a possibly-empty *type* (never a bounded
infimum over a possibly-empty `Prop`).

Main declarations:

* `NumberComplexity.IsAddChain` — the chain predicate, in the permissive form
  (non-ascending, repeated values allowed; summands not necessarily distinct,
  as in Knuth TAOCP §4.6.3).  The OEIS entry's comment (M. F. Hasler,
  2025-11-14) states the ascending convention `1 = s(0) < s(1) < … = n`; the
  two conventions have the same minimum, since sorting and deduplicating any
  chain yields an ascending chain of no greater length, and agreement with the
  entry's values is certified below at every checked point.  The executable
  mirror `NumberComplexity.addChainB` gives decidability;
* `NumberComplexity.chainSteps` — number of additions of a chain, written
  subtraction-free as the length of the tail;
* `NumberComplexity.AdditionChain` — the addition chains for `n`, as a subtype;
* `NumberComplexity.l` — A003313, the shortest-chain length;
* `NumberComplexity.l_two_pow` — `l (2 ^ k) = k`;
* `NumberComplexity.le_two_pow_l`, `NumberComplexity.log_two_le_l` — the
  classical doubling lower bound `n ≤ 2 ^ l n`, i.e. `⌊log₂ n⌋ ≤ l n`;
* `NumberComplexity.l_succ_le`, `NumberComplexity.l_two_mul_le` — upper-bound
  helpers (staircase chain; doubling step);
* `NumberComplexity.l_le_iff` plus a `Decidable (l n ≤ k)` instance — a decision
  procedure for `l` by the exhaustive enumeration
  `NumberComplexity.chainsOfLength` of all chains with exactly `k` additions.

**Degenerate values.** No chain reaches `0` (every chain element is positive:
`IsAddChain.one_le_of_mem`), so `AdditionChain 0` is empty and `l 0 = 0` is the
junk value of the empty infimum in `ℕ` — pinned in `l_zero` and in
`l_eq_zero_iff : l n = 0 ↔ n ≤ 1`, whose `n = 1` case is honest (the trivial
chain `[1]`) and whose `n = 0` case is the junk.  `chainSteps [] = 0` is likewise
junk; actual chains are provably nonempty (`IsAddChain.ne_nil`).

**Trust.** Every ground check closes by kernel `decide`, `rfl`, or `norm_num`
(no `native_decide`, no `@[implemented_by]`/`@[extern]`/`@[csimp]` in this
file); the axiom audit at the bottom reports at most
`propext, Classical.choice, Quot.sound`.

Ground truth: `oeis show A003313`, pulled live 2026-07-29; terms (offset 1)
`0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4, …` with `a(32) = 5`,
`a(64) = 6`; spot-checked below.  The definition is cross-checked against the
entry (values, and the Hasler 2025-11-14 comment modulo the ascending-vs-
permissive convention noted above) and `Formalize/A003313-knuth-stolarsky.md`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## The chain predicate -/

/-- `IsAddChain c`: the list `c`, read head-first as "latest chain element
first", is an addition chain: the last list element (the chain start `a₀`) is
`1`, and every other element is the sum of two — not necessarily distinct —
members of its tail, i.e. of two earlier chain elements.  This is the
permissive (not necessarily ascending, repeats allowed) form of the OEIS
A003313 / Knuth TAOCP §4.6.3 notion; its minimal length agrees with the
entry's ascending convention (sort and deduplicate), as the module docstring
records. -/
inductive IsAddChain : List ℕ → Prop
  /-- The trivial chain `1 = a₀`. -/
  | one : IsAddChain [1]
  /-- Extend a chain by the sum of two of its members (`a = b` allowed). -/
  | add {c : List ℕ} {a b : ℕ} (ha : a ∈ c) (hb : b ∈ c) (hc : IsAddChain c) :
      IsAddChain ((a + b) :: c)

/-- Addition chains are nonempty lists. -/
theorem IsAddChain.ne_nil {c : List ℕ} (hc : IsAddChain c) : c ≠ [] := by
  cases hc <;> simp

/-- The empty list is not an addition chain. -/
theorem not_isAddChain_nil : ¬IsAddChain [] := fun h => h.ne_nil rfl

/-- Inversion at a singleton: the only one-element chain is `[1]`. -/
theorem isAddChain_singleton_iff {a : ℕ} : IsAddChain [a] ↔ a = 1 := by
  constructor
  · intro h
    cases h with
    | one => rfl
    | add ha _hb _hc => simp at ha
  · rintro rfl
    exact .one

/-- Inversion at a list of length at least two: the new element is a sum of two
members of the tail, and the tail is itself an addition chain. -/
theorem isAddChain_cons_cons_iff {x y : ℕ} {t : List ℕ} :
    IsAddChain (x :: y :: t) ↔
      (∃ a ∈ y :: t, ∃ b ∈ y :: t, x = a + b) ∧ IsAddChain (y :: t) := by
  constructor
  · intro h
    cases h with
    | add ha hb hc => exact ⟨⟨_, ha, _, hb, rfl⟩, hc⟩
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hc⟩
    exact .add ha hb hc

/-- Executable Boolean mirror of `IsAddChain` — the ground-truth check for the
inductive predicate and the source of its decidability. -/
def addChainB : List ℕ → Bool
  | [] => false
  | [a] => a == 1
  | x :: y :: t =>
      ((y :: t).any fun a => (y :: t).any fun b => x == a + b) && addChainB (y :: t)

/-- The executable mirror agrees with the inductive predicate. -/
theorem isAddChain_iff_addChainB : ∀ c : List ℕ, IsAddChain c ↔ addChainB c = true
  | [] => by
    simp only [addChainB, Bool.false_eq_true, iff_false]
    exact not_isAddChain_nil
  | [a] => by
    rw [isAddChain_singleton_iff]
    simp [addChainB]
  | x :: y :: t => by
    rw [isAddChain_cons_cons_iff, isAddChain_iff_addChainB (y :: t)]
    simp [addChainB, List.any_eq_true, Bool.and_eq_true]

/-- `IsAddChain` is decidable, through the executable mirror `addChainB`. -/
instance : DecidablePred IsAddChain := fun c =>
  decidable_of_iff (addChainB c = true) (isAddChain_iff_addChainB c).symm

-- ground checks for the predicate itself, positive and adversarial negative:
example : IsAddChain [1] := by decide
example : IsAddChain [2, 1] := by decide
example : IsAddChain [2, 2, 1] := by decide           -- repeated values are allowed
example : IsAddChain [5, 3, 2, 1] := by decide        -- 5 = 3 + 2, distinct summands
example : IsAddChain [15, 12, 6, 3, 2, 1] := by decide
example : ¬IsAddChain [] := by decide                 -- no empty chain
example : ¬IsAddChain [2] := by decide                -- a chain starts at 1
example : ¬IsAddChain [1, 1] := by decide             -- 1 is not a sum of members of [1]
example : ¬IsAddChain [5, 3, 1] := by decide          -- tail [3, 1] is not a chain
example : ¬IsAddChain [15, 6, 3, 2, 1] := by decide   -- 15 is not a sum of two members

/-- Every element of an addition chain is at least `1`; in particular no chain
contains (or reaches) `0`. -/
theorem IsAddChain.one_le_of_mem {c : List ℕ} (hc : IsAddChain c) : ∀ x ∈ c, 1 ≤ x := by
  induction hc with
  | one =>
    intro x hx
    rw [List.mem_singleton] at hx
    omega
  | @add c a b ha _hb _hc ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxab | hxc
    · have h1 : 1 ≤ a := ih a ha
      omega
    · exact ih x hxc

/-- The chain start `1` is a member of every addition chain. -/
theorem IsAddChain.one_mem {c : List ℕ} (hc : IsAddChain c) : 1 ∈ c := by
  induction hc with
  | one => exact List.mem_cons_self
  | add _ha _hb _hc ih => exact List.mem_cons_of_mem _ ih

/-- The last list element — the chain start `a₀` — is `1`.  This is the
"sequence starting at 1" clause of the informal definition, stated against the
reversed-list representation. -/
theorem IsAddChain.getLast?_eq_one {c : List ℕ} (hc : IsAddChain c) :
    c.getLast? = some 1 := by
  induction hc with
  | one => rfl
  | @add c a b _ha _hb hc ih =>
    obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
    rw [List.getLast?_cons_cons]
    exact ih

/-- Truncating a chain at any member yields a chain for that member: every
`n ∈ c` is the head of an addition chain of no greater length (a suffix of
`c`). -/
theorem IsAddChain.exists_head?_eq {c : List ℕ} (hc : IsAddChain c) :
    ∀ n ∈ c, ∃ d : List ℕ, IsAddChain d ∧ d.head? = some n ∧ d.length ≤ c.length := by
  induction hc with
  | one =>
    intro n hn
    rw [List.mem_singleton] at hn
    exact ⟨[1], .one, by rw [hn, List.head?_cons], le_refl _⟩
  | @add c a b ha hb hc ih =>
    intro n hn
    rcases List.mem_cons.mp hn with hnab | hnc
    · refine ⟨(a + b) :: c, .add ha hb hc, ?_, le_refl _⟩
      rw [List.head?_cons, hnab]
    · obtain ⟨d, hd, hdh, hdl⟩ := ih n hnc
      refine ⟨d, hd, hdh, ?_⟩
      rw [List.length_cons]
      omega

/-! ## Chain length in additions -/

/-- Number of additions performed by the chain `c`: its list length minus one,
written subtraction-free as the length of the tail.  On the (non-chain) empty
list the value is the junk `0`. -/
def chainSteps (c : List ℕ) : ℕ := c.tail.length

/-- `chainSteps` of a cons counts the whole tail. -/
theorem chainSteps_cons (x : ℕ) (c : List ℕ) : chainSteps (x :: c) = c.length := rfl

-- ground checks for `chainSteps`, including the documented junk value at `[]`:
example : chainSteps [15, 12, 6, 3, 2, 1] = 5 := rfl
example : chainSteps [2, 1] = 1 := rfl
example : chainSteps [1] = 0 := rfl
example : chainSteps ([] : List ℕ) = 0 := rfl

/-- A chain performing `chainSteps c` additions has `chainSteps c + 1`
elements. -/
theorem IsAddChain.length_eq_chainSteps_add_one {c : List ℕ} (hc : IsAddChain c) :
    c.length = chainSteps c + 1 := by
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
  simp [chainSteps]

/-- Each addition at most doubles the largest element present: every member of
an addition chain with `chainSteps c` additions is at most `2 ^ chainSteps c`.
This is the source of all lower bounds on `l`. -/
theorem IsAddChain.le_two_pow_chainSteps {c : List ℕ} (hc : IsAddChain c) :
    ∀ x ∈ c, x ≤ 2 ^ chainSteps c := by
  induction hc with
  | one =>
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    simp [chainSteps]
  | @add c a b ha hb hc ih =>
    intro x hx
    obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
    have hsteps : chainSteps ((a + b) :: y :: t) = chainSteps (y :: t) + 1 := by
      simp [chainSteps]
    have hpow : (2 : ℕ) ^ (chainSteps (y :: t) + 1) = 2 ^ chainSteps (y :: t) * 2 :=
      pow_succ 2 _
    rcases List.mem_cons.mp hx with hxab | hxc
    · have h1 : a ≤ 2 ^ chainSteps (y :: t) := ih a ha
      have h2 : b ≤ 2 ^ chainSteps (y :: t) := ih b hb
      rw [hsteps, hpow]
      omega
    · have h3 : x ≤ 2 ^ chainSteps (y :: t) := ih x hxc
      rw [hsteps, hpow]
      omega

/-! ## Addition chains for `n`, and the length function `l` -/

/-- `AdditionChain n`: the addition chains for `n` — chains whose head (the
final, largest-index chain element) is `n`.  For `n = 0` this type is empty
(`instIsEmptyAdditionChainZero`); for `n ≠ 0` it is nonempty
(`nonempty_additionChain_of_ne_zero`), so the infimum defining `l` is honest
for every `n ≠ 0`. -/
abbrev AdditionChain (n : ℕ) : Type :=
  {c : List ℕ // IsAddChain c ∧ c.head? = some n}

/-- The target `n` is a member of any addition chain for `n`. -/
theorem AdditionChain.head_mem {n : ℕ} (c : AdditionChain n) : n ∈ c.val := by
  obtain ⟨hc, hh⟩ := c.property
  obtain ⟨y, t, heq⟩ := List.exists_cons_of_ne_nil hc.ne_nil
  rw [heq, List.head?_cons, Option.some_inj] at hh
  rw [heq, ← hh]
  exact List.mem_cons_self

/-- No addition chain reaches `0` (all chain elements are positive). -/
instance instIsEmptyAdditionChainZero : IsEmpty (AdditionChain 0) :=
  ⟨fun c => by
    have h0 : (0 : ℕ) ∈ c.val := c.head_mem
    have h1 : 1 ≤ (0 : ℕ) := c.property.1.one_le_of_mem 0 h0
    omega⟩

/-- The staircase chain `[n, n - 1, …, 2, 1]` (each step adds `1`), witnessing
that every positive `n` has some addition chain, with `n - 1` additions. -/
def countdownChain : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: countdownChain n

/-- `1` belongs to every nonempty staircase chain. -/
theorem one_mem_countdownChain : ∀ n : ℕ, 1 ∈ countdownChain (n + 1)
  | 0 => List.mem_cons_self
  | n + 1 => List.mem_cons_of_mem _ (one_mem_countdownChain n)

/-- The staircase is an addition chain (each step is `k + 1` with both `k` and
`1` already present). -/
theorem isAddChain_countdownChain : ∀ n : ℕ, IsAddChain (countdownChain (n + 1))
  | 0 => by
    show IsAddChain [1]
    exact .one
  | n + 1 => by
    show IsAddChain ((n + 1 + 1) :: countdownChain (n + 1))
    exact .add (by show n + 1 ∈ (n + 1) :: countdownChain n; exact List.mem_cons_self)
      (one_mem_countdownChain n) (isAddChain_countdownChain n)

/-- The staircase chain for `n + 1` has head `n + 1`. -/
theorem head?_countdownChain (n : ℕ) : (countdownChain (n + 1)).head? = some (n + 1) := rfl

/-- The staircase chain has `n` elements. -/
theorem length_countdownChain : ∀ n : ℕ, (countdownChain n).length = n
  | 0 => rfl
  | n + 1 => by
    show ((n + 1) :: countdownChain n).length = n + 1
    rw [List.length_cons, length_countdownChain n]

/-- The staircase chain for `n + 1` performs `n` additions. -/
theorem chainSteps_countdownChain (n : ℕ) : chainSteps (countdownChain (n + 1)) = n := by
  show chainSteps ((n + 1) :: countdownChain n) = n
  rw [chainSteps_cons, length_countdownChain n]

/-- Every successor has an addition chain (the staircase). -/
instance instNonemptyAdditionChain (n : ℕ) : Nonempty (AdditionChain (n + 1)) :=
  ⟨⟨countdownChain (n + 1), isAddChain_countdownChain n, head?_countdownChain n⟩⟩

/-- Every `n ≠ 0` has an addition chain, so the infimum defining `l n` is
attained (`exists_chainSteps_eq_l`). -/
theorem nonempty_additionChain_of_ne_zero : ∀ {n : ℕ}, n ≠ 0 → Nonempty (AdditionChain n)
  | _ + 1, _ => instNonemptyAdditionChain _
  | 0, h => absurd rfl h

/-- **OEIS A003313**: `l n` is the length (number of additions) of a shortest
addition chain for `n`, as the subtype-indexed infimum
`⨅ c : AdditionChain n, chainSteps c.val` in `ℕ`.

Degenerate value: `AdditionChain 0` is empty, so `l 0 = 0` is the junk value of
the empty infimum (`Nat.sInf ∅ = 0`) — pinned in `l_zero` and `l_eq_zero_iff`.
The definition is noncomputable (`Nat.sInf`), but `l n ≤ k` is decidable via
`l_le_iff`; ground values are certified below against the OEIS entry. -/
noncomputable def l (n : ℕ) : ℕ :=
  ⨅ c : AdditionChain n, chainSteps c.val

/-- Any addition chain for `n` bounds `l n` from above. -/
theorem l_le_chainSteps {n : ℕ} (c : AdditionChain n) : l n ≤ chainSteps c.val :=
  Nat.sInf_le (Set.mem_range_self c)

/-- Upper-bound helper in raw-list form: an explicit chain with head `n` and at
most `k` additions gives `l n ≤ k`. -/
theorem l_le_of_isAddChain {n k : ℕ} (c : List ℕ) (hc : IsAddChain c)
    (hh : c.head? = some n) (hk : chainSteps c ≤ k) : l n ≤ k :=
  le_trans (l_le_chainSteps ⟨c, hc, hh⟩) hk

/-- For `n ≠ 0` the infimum defining `l n` is attained: some addition chain for
`n` has exactly `l n` additions.  This is the master lower-bound tool. -/
theorem exists_chainSteps_eq_l {n : ℕ} (hn : n ≠ 0) :
    ∃ c : AdditionChain n, chainSteps c.val = l n := by
  haveI hne : Nonempty (AdditionChain n) := nonempty_additionChain_of_ne_zero hn
  have h : l n ∈ Set.range fun c : AdditionChain n => chainSteps c.val :=
    Nat.sInf_mem (Set.range_nonempty _)
  rwa [Set.mem_range] at h

/-- Lower-bound helper: a uniform lower bound on the steps of every chain for
`n ≠ 0` is a lower bound on `l n`. -/
theorem le_l {n k : ℕ} (hn : n ≠ 0)
    (h : ∀ c : AdditionChain n, k ≤ chainSteps c.val) : k ≤ l n := by
  obtain ⟨c, hc⟩ := exists_chainSteps_eq_l hn
  rw [← hc]
  exact h c

/-- Degenerate value, pinned: `l 0 = 0` is the junk value of the infimum over
the empty type `AdditionChain 0` — there is **no** addition chain for `0`. -/
@[simp] theorem l_zero : l 0 = 0 :=
  Nat.iInf_of_empty _

/-- `l 1 = 0`: the trivial chain `[1]` performs no additions (OEIS `a(1) = 0`). -/
@[simp] theorem l_one : l 1 = 0 :=
  Nat.le_zero.mp (l_le_of_isAddChain [1] .one rfl (le_refl 0))

/-- Crude upper bound, subtraction-free form of `l n ≤ n - 1`: the staircase
chain gives `l (n + 1) ≤ n`. -/
theorem l_succ_le (n : ℕ) : l (n + 1) ≤ n :=
  l_le_of_isAddChain (countdownChain (n + 1)) (isAddChain_countdownChain n)
    (head?_countdownChain n) (le_of_eq (chainSteps_countdownChain n))

/-- The zero set of `l`, separating the honest zero (`n = 1`, trivial chain)
from the junk zero (`n = 0`, empty infimum): `l n = 0 ↔ n ≤ 1`. -/
theorem l_eq_zero_iff {n : ℕ} : l n = 0 ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn1
    have hn : n ≠ 0 := by omega
    obtain ⟨c, hc⟩ := exists_chainSteps_eq_l hn
    obtain ⟨hchain, hhead⟩ := c.property
    obtain ⟨y, t, heq⟩ := List.exists_cons_of_ne_nil hchain.ne_nil
    have hlen : c.val.length = 1 := by
      have hl := hchain.length_eq_chainSteps_add_one
      omega
    have ht : t = [] := by
      rw [heq, List.length_cons] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    rw [heq] at hchain hhead
    have hy : y = 1 := isAddChain_singleton_iff.mp hchain
    rw [List.head?_cons, Option.some_inj] at hhead
    omega
  · intro h
    interval_cases n
    · exact l_zero
    · exact l_one

/-! ## The doubling lower bound and `l (2 ^ k) = k` -/

/-- **Doubling lower bound**, exponential form: `n ≤ 2 ^ l n` for `0 < n` (each
addition at most doubles the maximum, and a shortest chain is attained).  The
guard keeps the claim off the junk chain-free case `n = 0`. -/
theorem le_two_pow_l (n : ℕ) (hn : 0 < n) : n ≤ 2 ^ l n := by
  obtain ⟨c, hc⟩ := exists_chainSteps_eq_l (by omega : n ≠ 0)
  have hb := c.property.1.le_two_pow_chainSteps n c.head_mem
  rwa [hc] at hb

/-- **Doubling lower bound**, logarithmic form: `⌊log₂ n⌋ ≤ l n` for `0 < n` —
the classical first theorem for addition chains (cf. the ROUTE section of
`Formalize/A003313-knuth-stolarsky.md`).  The guard keeps `Nat.log` off its
junk value at `0`. -/
theorem log_two_le_l (n : ℕ) (hn : 0 < n) : Nat.log 2 n ≤ l n :=
  calc Nat.log 2 n ≤ Nat.log 2 (2 ^ l n) := Nat.log_mono_right (le_two_pow_l n hn)
    _ = l n := Nat.log_pow Nat.one_lt_two _

/-- The doubling chain `[2 ^ k, …, 4, 2, 1]`. -/
def twoPowChain : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => 2 ^ (k + 1) :: twoPowChain k

/-- `2 ^ k` heads its doubling chain, so in particular is a member. -/
theorem two_pow_mem_twoPowChain : ∀ k : ℕ, 2 ^ k ∈ twoPowChain k
  | 0 => by
    show (2 : ℕ) ^ 0 ∈ [1]
    norm_num
  | k + 1 => by
    show (2 : ℕ) ^ (k + 1) ∈ 2 ^ (k + 1) :: twoPowChain k
    exact List.mem_cons_self

/-- The doubling chain is an addition chain (`2 ^ (k+1) = 2 ^ k + 2 ^ k`). -/
theorem isAddChain_twoPowChain : ∀ k : ℕ, IsAddChain (twoPowChain k)
  | 0 => by
    show IsAddChain [1]
    exact .one
  | k + 1 => by
    show IsAddChain (2 ^ (k + 1) :: twoPowChain k)
    have h : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    rw [h]
    exact .add (two_pow_mem_twoPowChain k) (two_pow_mem_twoPowChain k)
      (isAddChain_twoPowChain k)

/-- The doubling chain for `2 ^ k` has head `2 ^ k`. -/
theorem head?_twoPowChain : ∀ k : ℕ, (twoPowChain k).head? = some (2 ^ k)
  | 0 => by
    show ([1] : List ℕ).head? = some (2 ^ 0)
    simp
  | _ + 1 => rfl

/-- The doubling chain for `2 ^ k` has `k + 1` elements. -/
theorem length_twoPowChain : ∀ k : ℕ, (twoPowChain k).length = k + 1
  | 0 => rfl
  | k + 1 => by
    show (2 ^ (k + 1) :: twoPowChain k).length = k + 2
    rw [List.length_cons, length_twoPowChain k]

/-- The doubling chain for `2 ^ k` performs `k` additions. -/
theorem chainSteps_twoPowChain : ∀ k : ℕ, chainSteps (twoPowChain k) = k
  | 0 => rfl
  | k + 1 => by
    show chainSteps (2 ^ (k + 1) :: twoPowChain k) = k + 1
    rw [chainSteps_cons, length_twoPowChain k]

/-- **`l (2 ^ k) = k`**: repeated doubling is an optimal addition chain for
powers of two.  Upper bound from `twoPowChain`; lower bound from the doubling
bound `2 ^ k ≤ 2 ^ chainSteps c` for every chain `c` for `2 ^ k`. -/
theorem l_two_pow (k : ℕ) : l (2 ^ k) = k := by
  have hub : l (2 ^ k) ≤ k :=
    l_le_of_isAddChain (twoPowChain k) (isAddChain_twoPowChain k) (head?_twoPowChain k)
      (le_of_eq (chainSteps_twoPowChain k))
  have hlb : k ≤ l (2 ^ k) := by
    refine le_l (Nat.two_pow_pos k).ne' ?_
    intro c
    have hb := c.property.1.le_two_pow_chainSteps (2 ^ k) c.head_mem
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp hb
  omega

/-- `l 2 = 1` (OEIS `a(2) = 1`), the case `k = 1` of `l_two_pow`. -/
theorem l_two : l 2 = 1 := by
  have h := l_two_pow 1
  norm_num at h
  exact h

/-- Doubling upper-bound helper: `l (2 * n) ≤ l n + 1` (extend an optimal chain
for `n` by one doubling).  At `n = 0` both sides are junk-free and the claim is
trivially true. -/
theorem l_two_mul_le (n : ℕ) : l (2 * n) ≤ l n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · obtain ⟨c, hc⟩ := exists_chainSteps_eq_l (by omega : n ≠ 0)
    obtain ⟨hchain, hhead⟩ := c.property
    have hd : IsAddChain ((n + n) :: c.val) := .add c.head_mem c.head_mem hchain
    have hh : ((n + n) :: c.val).head? = some (2 * n) := by
      rw [List.head?_cons, Option.some_inj]
      omega
    refine l_le_of_isAddChain ((n + n) :: c.val) hd hh ?_
    rw [chainSteps_cons, hchain.length_eq_chainSteps_add_one, hc]

/-! ## Decision procedure: exhaustive enumeration of chains of a given length

`chainsOfLength k` lists every addition chain performing exactly `k` additions
(so of `k + 1` elements; elements are automatically bounded by `2 ^ k` by
`IsAddChain.le_two_pow_chainSteps`, so the enumeration is complete with no
pruning argument needed).  `l n ≤ k` then reduces to membership of `n` in some
enumerated chain (`l_le_iff`): a chain of `m ≤ k` steps for `n` can be padded
to exactly `k` steps keeping `n` a member (`chainPad`), and conversely a chain
containing `n` truncates to a chain for `n` (`IsAddChain.exists_head?_eq`). -/

/-- All one-step extensions of the list `c` by a sum of two of its members. -/
def chainExtensions (c : List ℕ) : List (List ℕ) :=
  c.flatMap fun a => c.map fun b => (a + b) :: c

/-- All addition chains performing exactly `k` additions. -/
def chainsOfLength : ℕ → List (List ℕ)
  | 0 => [[1]]
  | k + 1 => (chainsOfLength k).flatMap chainExtensions

-- ground checks for the enumeration:
example : chainExtensions [2, 1] = [[4, 2, 1], [3, 2, 1], [3, 2, 1], [2, 2, 1]] := by decide
example : chainsOfLength 0 = [[1]] := by decide
example : chainsOfLength 1 = [[2, 1]] := by decide
example : chainsOfLength 2 = [[4, 2, 1], [3, 2, 1], [3, 2, 1], [2, 2, 1]] := by decide

/-- Soundness of the enumeration: members of `chainsOfLength k` are addition
chains with `k + 1` elements. -/
theorem of_mem_chainsOfLength : ∀ {k : ℕ} {c : List ℕ}, c ∈ chainsOfLength k →
    IsAddChain c ∧ c.length = k + 1
  | 0, c, hc => by
    simp only [chainsOfLength, List.mem_singleton] at hc
    subst hc
    exact ⟨.one, rfl⟩
  | k + 1, c, hc => by
    simp only [chainsOfLength, List.mem_flatMap] at hc
    obtain ⟨d, hd, hcd⟩ := hc
    simp only [chainExtensions, List.mem_flatMap, List.mem_map] at hcd
    obtain ⟨a, ha, b, hb, rfl⟩ := hcd
    obtain ⟨hchain, hlen⟩ := of_mem_chainsOfLength hd
    refine ⟨.add ha hb hchain, ?_⟩
    rw [List.length_cons, hlen]

/-- Completeness of the enumeration: every addition chain appears in
`chainsOfLength` at its own step count. -/
theorem IsAddChain.mem_chainsOfLength {c : List ℕ} (hc : IsAddChain c) :
    c ∈ chainsOfLength (chainSteps c) := by
  induction hc with
  | one => simp [chainsOfLength, chainSteps]
  | @add c a b ha hb hc ih =>
    obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
    have hsteps : chainSteps ((a + b) :: y :: t) = chainSteps (y :: t) + 1 := by
      simp [chainSteps]
    rw [hsteps]
    simp only [chainsOfLength, List.mem_flatMap]
    refine ⟨y :: t, ih, ?_⟩
    simp only [chainExtensions, List.mem_flatMap, List.mem_map]
    exact ⟨a, ha, b, hb, rfl⟩

/-- The enumeration is exact: `c ∈ chainsOfLength k ↔` `c` is an addition chain
with `k + 1` elements. -/
theorem mem_chainsOfLength_iff {k : ℕ} {c : List ℕ} :
    c ∈ chainsOfLength k ↔ IsAddChain c ∧ c.length = k + 1 := by
  constructor
  · exact of_mem_chainsOfLength
  · rintro ⟨hc, hlen⟩
    have h := hc.mem_chainsOfLength
    have hsteps : chainSteps c = k := by
      have h2 := hc.length_eq_chainSteps_add_one
      omega
    rwa [hsteps] at h

/-- Pad a list by `j` doubling steps of its head (`h :: t ↦ (h+h) :: h :: t`,
`j` times).  Used to normalize a chain of at most `k` steps to exactly `k`
steps without losing members. -/
def chainPad (c : List ℕ) : ℕ → List ℕ
  | 0 => c
  | j + 1 => ((chainPad c j).headI + (chainPad c j).headI) :: chainPad c j

/-- Padding adds exactly `j` elements. -/
theorem length_chainPad (c : List ℕ) : ∀ j : ℕ, (chainPad c j).length = c.length + j
  | 0 => rfl
  | j + 1 => by
    show (((chainPad c j).headI + (chainPad c j).headI) :: chainPad c j).length
      = c.length + (j + 1)
    rw [List.length_cons, length_chainPad c j]
    omega

/-- Padding preserves membership. -/
theorem mem_chainPad {c : List ℕ} {x : ℕ} (hx : x ∈ c) : ∀ j : ℕ, x ∈ chainPad c j
  | 0 => hx
  | j + 1 => List.mem_cons_of_mem _ (mem_chainPad hx j)

/-- Padding preserves the chain property (each padding step is the doubling of
the current head, a member). -/
theorem isAddChain_chainPad {c : List ℕ} (hc : IsAddChain c) :
    ∀ j : ℕ, IsAddChain (chainPad c j)
  | 0 => hc
  | j + 1 => by
    have ih := isAddChain_chainPad hc j
    obtain ⟨y, t, heq⟩ := List.exists_cons_of_ne_nil ih.ne_nil
    show IsAddChain (((chainPad c j).headI + (chainPad c j).headI) :: chainPad c j)
    rw [heq]
    exact .add List.mem_cons_self List.mem_cons_self (heq ▸ ih)

/-- **Decision procedure for `l`**: for `n ≠ 0`, `l n ≤ k` iff `n` occurs in
some enumerated chain of exactly `k` additions.  (The guard is necessary: for
`n = 0` the left side is the junk `l 0 = 0 ≤ k` while the right side is false —
no chain contains `0`.) -/
theorem l_le_iff {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    l n ≤ k ↔ ∃ c ∈ chainsOfLength k, n ∈ c := by
  constructor
  · intro h
    obtain ⟨c₀, hsteps⟩ := exists_chainSteps_eq_l hn
    obtain ⟨hchain, hhead⟩ := c₀.property
    have hle : chainSteps c₀.val ≤ k := by omega
    set d := chainPad c₀.val (k - chainSteps c₀.val) with hd_def
    have hdchain : IsAddChain d := isAddChain_chainPad hchain _
    have hdlen : d.length = k + 1 := by
      rw [hd_def, length_chainPad, hchain.length_eq_chainSteps_add_one]
      omega
    have hdsteps : chainSteps d = k := by
      have hl2 := hdchain.length_eq_chainSteps_add_one
      omega
    have hmem := hdchain.mem_chainsOfLength
    rw [hdsteps] at hmem
    exact ⟨d, hmem, mem_chainPad c₀.head_mem _⟩
  · rintro ⟨c, hck, hnc⟩
    obtain ⟨hchain, hlen⟩ := of_mem_chainsOfLength hck
    obtain ⟨d, hdchain, hdhead, hdlen⟩ := hchain.exists_head?_eq n hnc
    have hd1 := hdchain.length_eq_chainSteps_add_one
    refine l_le_of_isAddChain d hdchain hdhead ?_
    omega

/-- `l n ≤ k` is decidable: by `l_zero` for `n = 0` and by the exhaustive
enumeration `l_le_iff` otherwise.  Kernel-`decide`-friendly (all data involved
is structurally recursive). -/
instance decidableLLe (n k : ℕ) : Decidable (l n ≤ k) :=
  if hn : n = 0 then
    isTrue (by rw [hn, l_zero]; exact Nat.zero_le k)
  else
    decidable_of_iff (∃ c ∈ chainsOfLength k, n ∈ c) (l_le_iff hn k).symm

/-! ## Ground checks against `oeis show A003313` (pulled live 2026-07-29)

Terms (offset 1): `a(1)..a(16) = 0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4`;
also `a(32) = 5`, `a(64) = 6`.  Each value `l n = v` below is certified by an
explicit optimal chain (upper bound, via `l_le_of_isAddChain`) together with
kernel-`decide` exhaustion of all chains of `v - 1` additions (lower bound, via
the `Decidable (l n ≤ k)` instance).  `a(15) = 5` is the classical witness that
the binary method (which needs `6` multiplications for `x^15`) is not optimal.
Powers of two are checked through `l_two_pow`, consistently with
`a(2), a(4), a(8), a(16), a(32), a(64) = 1, 2, 3, 4, 5, 6`, and `a(4)`, `a(8)`
are re-checked against the enumeration. -/

example : l 0 = 0 := l_zero            -- junk value, documented at `l`
example : l 1 = 0 := l_one             -- a(1) = 0
example : l 2 = 1 := l_two             -- a(2) = 1
example : l 2 ≤ 1 := by decide         -- decision procedure, positive branch
example : ¬l 2 ≤ 0 := by decide        -- decision procedure, negative branch
example : l 0 ≤ 0 := by decide         -- decision procedure, junk branch

example : l 3 = 2 := by                -- a(3) = 2
  have h1 : l 3 ≤ 2 := l_le_of_isAddChain [3, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 3 ≤ 1 := by decide
  omega

example : l 4 = 2 := by                -- a(4) = 2
  have h := l_two_pow 2
  norm_num at h
  exact h

example : ¬l 4 ≤ 1 := by decide        -- a(4) = 2, enumeration cross-check

example : l 5 = 3 := by                -- a(5) = 3
  have h1 : l 5 ≤ 3 := l_le_of_isAddChain [5, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 5 ≤ 2 := by decide
  omega

example : l 6 = 3 := by                -- a(6) = 3
  have h1 : l 6 ≤ 3 := l_le_of_isAddChain [6, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 6 ≤ 2 := by decide
  omega

example : l 7 = 4 := by                -- a(7) = 4
  have h1 : l 7 ≤ 4 := l_le_of_isAddChain [7, 6, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 7 ≤ 3 := by decide
  omega

example : l 8 = 3 := by                -- a(8) = 3
  have h := l_two_pow 3
  norm_num at h
  exact h

example : ¬l 8 ≤ 2 := by decide        -- a(8) = 3, enumeration cross-check

example : l 15 = 5 := by               -- a(15) = 5: binary method (6) beaten
  have h1 : l 15 ≤ 5 := l_le_of_isAddChain [15, 12, 6, 3, 2, 1] (by decide) rfl (by decide)
  -- `+kernel`: evaluate the 576-chain enumeration in the kernel only (the
  -- elaborator's evaluator hits `maxRecDepth` first).  This is NOT
  -- `native_decide`: the certificate is still checked by kernel reduction and
  -- the trust surface is unchanged.
  have h2 : ¬l 15 ≤ 4 := by decide +kernel
  omega

example : l 16 = 4 := by               -- a(16) = 4
  have h := l_two_pow 4
  norm_num at h
  exact h

example : l 32 = 5 := by               -- a(32) = 5
  have h := l_two_pow 5
  norm_num at h
  exact h

example : l 64 = 6 := by               -- a(64) = 6
  have h := l_two_pow 6
  norm_num at h
  exact h

/-! ## Satisfiability of hypotheses at concrete models

Every hypothesis-bearing theorem above is jointly instantiated at a concrete
model: `l_le_iff` and `exists_chainSteps_eq_l` at small `n ≠ 0` (also exercised
transitively by every `decide` ground check through `decidableLLe`), the
doubling bounds at `n = 5` and `n = 15`, `le_l` at `n = 2 ^ k` inside
`l_two_pow` (concretely at `k = 2, 3, 4, 5, 6` in the checks above), and the
`IsAddChain.*` lemmas at the explicit chain `[15, 12, 6, 3, 2, 1]`. -/

example : (l 3 ≤ 2) ↔ ∃ c ∈ chainsOfLength 2, 3 ∈ c := l_le_iff (by norm_num) 2
example : ∃ c : AdditionChain 2, chainSteps c.val = l 2 :=
  exists_chainSteps_eq_l (by norm_num)
example : (5 : ℕ) ≤ 2 ^ l 5 := le_two_pow_l 5 (by norm_num)
example : Nat.log 2 15 ≤ l 15 := log_two_le_l 15 (by norm_num)
example : l 6 ≤ l 3 + 1 := l_two_mul_le 3     -- consistent: 3 ≤ 2 + 1
example : l 8 ≤ 7 := l_succ_le 7              -- crude staircase bound at n = 8
example : ([15, 12, 6, 3, 2, 1] : List ℕ).getLast? = some 1 :=
  (show IsAddChain [15, 12, 6, 3, 2, 1] by decide).getLast?_eq_one
example : (1 : ℕ) ∈ [15, 12, 6, 3, 2, 1] :=
  (show IsAddChain [15, 12, 6, 3, 2, 1] by decide).one_mem

/-! ## Axiom audit -/

#print axioms l
#print axioms l_zero
#print axioms l_one
#print axioms l_two
#print axioms l_two_pow
#print axioms l_succ_le
#print axioms l_eq_zero_iff
#print axioms l_two_mul_le
#print axioms le_two_pow_l
#print axioms log_two_le_l
#print axioms l_le_chainSteps
#print axioms l_le_of_isAddChain
#print axioms exists_chainSteps_eq_l
#print axioms le_l
#print axioms l_le_iff
#print axioms decidableLLe
#print axioms isAddChain_iff_addChainB
#print axioms mem_chainsOfLength_iff
#print axioms of_mem_chainsOfLength
#print axioms IsAddChain.mem_chainsOfLength
#print axioms IsAddChain.ne_nil
#print axioms IsAddChain.one_le_of_mem
#print axioms IsAddChain.one_mem
#print axioms IsAddChain.getLast?_eq_one
#print axioms IsAddChain.exists_head?_eq
#print axioms IsAddChain.length_eq_chainSteps_add_one
#print axioms IsAddChain.le_two_pow_chainSteps
#print axioms AdditionChain.head_mem

end NumberComplexity
