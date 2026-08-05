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
  as in Knuth TAOCP §4.6.3).  The executable mirror
  `NumberComplexity.addChainB` gives decidability;
* `NumberComplexity.chainSteps` — number of additions of a chain, written
  subtraction-free as the length of the tail;
* `NumberComplexity.AdditionChain` — the addition chains for `n`, as a subtype;
* `NumberComplexity.l` — A003313, the shortest-chain length;
* `NumberComplexity.IsAscAddChain`, `NumberComplexity.lAsc`,
  `NumberComplexity.l_eq_lAsc` — the OEIS entry's own *ascending* convention
  (the Hasler comment quoted verbatim below: `1 = s 0 < ⋯ < s r = n`, each
  `s k` for `1 ≤ k ≤ r` a sum of two strictly earlier entries), the minimum it
  defines, and the theorem `l n = lAsc n` that the two conventions compute the
  same function.  Earlier revisions of this file *asserted* that agreement in
  prose; it is now proved;
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

**Ground truth**, from `goof oeis show A003313`, pulled live 2026-07-29 and
re-pulled 2026-08-05 with identical content.  Quoted verbatim:

> Length of shortest addition chain for n.

> 0,1,2,2,3,3,4,3,4,4,5,4,5,5,5,4,5,5,6,5,6,6,6,5,6,6,6,6,7,6,7,5,6,6,7,6,
> 7,7,7,6,7,7,7,7,7,7,8,6,7,7,7,7,8,7,8,7,8,8,8,7,8,8,8,6,7,7,8,7,8,8,9,7,
> 8,8,8,8,8,8,9,7,8,8,8,8,8,8,9,8,9,8,9,8,9,9,9,7,8,8,8,8

> Equivalently, minimal number of multiplications required to compute the n-th
> power.

> An addition chain for n, of length r, is a finite sequence s with
> 1 = s(0) < s(1) < ... < s(r) = n and s(k) = s(l) + s(m) for some l, m < k,
> for all k <= r. - _M. F. Hasler_, Nov 14 2025

The offset is `1`, so the terms above are `a(1), a(2), …, a(100)`; in
particular `a(1..16) = 0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4`,
`a(32) = 5` and `a(64) = 6`, all spot-checked below.  The Hasler comment is the
`IsAscAddChain` predicate; `l_eq_lAsc` reconciles it with the permissive
`IsAddChain` used for the development.  Secondary cross-reference:
`Formalize/A003313-knuth-stolarsky.md`.
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
entry's ascending convention `IsAscAddChain` — that is the content of
`l_eq_lAsc`. -/
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

/-! ## The ascending convention of OEIS A003313

The entry's own definition — the comment of M. F. Hasler, Nov 14 2025, quoted
verbatim in the module docstring — is the *ascending* one: a chain for `n` of
length `r` is a strictly increasing sequence `1 = s 0 < s 1 < ⋯ < s r = n` in
which every entry `s k` with `1 ≤ k ≤ r` is a sum `s i + s j` of two strictly
earlier entries.  `IsAscAddChain` is that predicate, written on the list
`s = [s 0, s 1, …, s r]` in the entry's own increasing order and indexed by
`Fin s.length`; `lAsc` is the minimum it defines; `l_eq_lAsc` proves the two
conventions compute the same function.

*Reading note.*  The entry writes the sum clause "for all `k <= r`".  At
`k = 0` there are no indices `l, m < 0`, and `s 0 = 1` is already fixed by the
first clause, so the intended (and only possible) range is `1 ≤ k ≤ r`; that is
the `0 < (k : ℕ)` guard on the `get_eq_add` field.

*Proof of `l_eq_lAsc`.*  One direction is the reversal of a list
(`IsAscAddChain.isAddChain_reverse`): an ascending chain, read backwards, is a
permissive chain with the same number of additions.  The other is the
normalization `ascNormalize c n`, which keeps the members of the permissive
chain `c` that do not exceed `n` and lists them increasingly without repetition.
The `≤ n` filter is load-bearing, not cosmetic: a permissive chain for `n` may
*overshoot* `n` — `[3, 4, 2, 1]` is a chain with head `3` that contains `4` —
and the overshooting members must be dropped.  They can be dropped, because
every chain member other than the start `1` is a sum of two *strictly smaller*
members (`IsAddChain.exists_lt_add_of_mem`); so the two witnesses for a member
`x ≤ n` are themselves `< x ≤ n`, survive the filter, and — being smaller —
precede `x` in the increasing order.  Deduplication can only shorten the list,
which is where `chainSteps_ascNormalize_le` comes from. -/

/-- The head of a strictly increasing list of naturals is its minimum: if `m`
belongs to a strictly sorted list and is a lower bound for its members, then
`m` is the head. -/
theorem head?_eq_of_sortedLT {s : List ℕ} (hs : s.SortedLT) {m : ℕ}
    (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) : s.head? = some m := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hm)
  rw [List.head?_cons, Option.some_inj]
  have hma : m ≤ a := hmin a List.mem_cons_self
  have ham : a ≤ m := by
    rcases List.mem_cons.mp hm with hm_head | hm_tail
    · omega
    · exact le_of_lt ((List.pairwise_cons.mp hs.pairwise).1 m hm_tail)
  omega

/-- The last entry of a strictly increasing list of naturals is its maximum: if
`M` belongs to a strictly sorted list and is an upper bound for its members,
then `M` is the last entry. -/
theorem getLast?_eq_of_sortedLT : ∀ {s : List ℕ}, s.SortedLT → ∀ {M : ℕ}, M ∈ s →
    (∀ x ∈ s, x ≤ M) → s.getLast? = some M
  | [], _, _, hM, _ => absurd hM List.not_mem_nil
  | [a], _, M, hM, _ => by
    rw [List.mem_singleton] at hM
    rw [List.getLast?_singleton, hM]
  | a :: b :: t, hs, M, hM, hmax => by
    rw [List.getLast?_cons_cons]
    refine getLast?_eq_of_sortedLT hs.pairwise.of_cons.sortedLT ?_ ?_
    · rcases List.mem_cons.mp hM with hM_head | hM_tail
      · exfalso
        have hab : a < b := (List.pairwise_cons.mp hs.pairwise).1 b List.mem_cons_self
        have hbM : b ≤ M := hmax b (List.mem_cons_of_mem _ List.mem_cons_self)
        omega
      · exact hM_tail
    · exact fun x hx => hmax x (List.mem_cons_of_mem _ hx)

/-- **The ascending convention of OEIS A003313.**  `IsAscAddChain n s` holds
when the list `s = [s 0, s 1, …, s r]`, read in the entry's own increasing
order, is an addition chain for `n` in the sense of the Hasler comment:
`s 0 = 1`, `s r = n`, `s 0 < s 1 < ⋯ < s r`, and every `s k` with `1 ≤ k ≤ r`
equals `s i + s j` for two indices `i, j < k`.

Contrast `IsAddChain`, the permissive convention (any two earlier members,
repeats and descents allowed) stored in reverse order.  The two conventions
define the same minimum: `l_eq_lAsc`. -/
structure IsAscAddChain (n : ℕ) (s : List ℕ) : Prop where
  /-- `1 = s 0`. -/
  head_eq_one : s.head? = some 1
  /-- `s r = n`, where `r + 1 = s.length`. -/
  getLast_eq : s.getLast? = some n
  /-- `s 0 < s 1 < ⋯ < s r`. -/
  sortedLT : s.SortedLT
  /-- `s k = s i + s j` for some `i, j < k`, for every `k` with `1 ≤ k ≤ r`. -/
  get_eq_add : ∀ k : Fin s.length, 0 < (k : ℕ) →
    ∃ i : Fin s.length, ∃ j : Fin s.length,
      (i : ℕ) < (k : ℕ) ∧ (j : ℕ) < (k : ℕ) ∧ s.get k = s.get i + s.get j

/-- The structure `IsAscAddChain` unfolded to a conjunction; the source of its
decidability. -/
theorem isAscAddChain_iff {n : ℕ} {s : List ℕ} :
    IsAscAddChain n s ↔
      s.head? = some 1 ∧ s.getLast? = some n ∧ s.SortedLT ∧
        ∀ k : Fin s.length, 0 < (k : ℕ) →
          ∃ i : Fin s.length, ∃ j : Fin s.length,
            (i : ℕ) < (k : ℕ) ∧ (j : ℕ) < (k : ℕ) ∧ s.get k = s.get i + s.get j :=
  ⟨fun h => ⟨h.head_eq_one, h.getLast_eq, h.sortedLT, h.get_eq_add⟩,
   fun ⟨hhead, hlast, hsorted, hsum⟩ => ⟨hhead, hlast, hsorted, hsum⟩⟩

/-- `IsAscAddChain n` is decidable: all four clauses range over the finite index
type `Fin s.length`. -/
instance instDecidableIsAscAddChain (n : ℕ) : DecidablePred (IsAscAddChain n) := fun _ =>
  decidable_of_iff _ isAscAddChain_iff.symm

-- ground checks for the predicate, positive and adversarial negative:
example : IsAscAddChain 1 [1] := by decide                    -- r = 0
example : IsAscAddChain 2 [1, 2] := by decide                 -- r = 1
example : IsAscAddChain 15 [1, 2, 3, 6, 12, 15] := by decide  -- r = 5
example : ¬IsAscAddChain 3 [2, 3] := by decide                -- does not start at 1
example : ¬IsAscAddChain 4 [1, 2, 3] := by decide             -- does not end at n
example : ¬IsAscAddChain 5 [1, 2, 5] := by decide             -- 5 is no sum of 1, 2
example : ¬IsAscAddChain 3 [1, 2, 2, 3] := by decide          -- repeat: not strict
example : ¬IsAscAddChain 2 [1, 3, 2] := by decide             -- descends

/-- Ascending chains are nonempty lists (they contain `s 0 = 1`). -/
theorem IsAscAddChain.ne_nil {n : ℕ} {s : List ℕ} (h : IsAscAddChain n s) : s ≠ [] := by
  intro hnil
  have hhead := h.head_eq_one
  rw [hnil, List.head?_nil] at hhead
  simp at hhead

/-! ### Ascending ⟹ permissive -/

/-- Every initial segment `[s 0, …, s (m-1)]` of an ascending chain, reversed,
is a permissive chain: induction on `m`, the inductive step supplying the two
earlier entries `s i`, `s j` from the `get_eq_add` field. -/
theorem IsAscAddChain.isAddChain_reverse_take {n : ℕ} {s : List ℕ} (h : IsAscAddChain n s) :
    ∀ m : ℕ, 0 < m → m ≤ s.length → IsAddChain (s.take m).reverse := by
  intro m
  induction m with
  | zero => intro h0; exact absurd h0 (lt_irrefl 0)
  | succ m ih =>
    intro _ hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
      have hy : y = 1 := by
        have hhead := h.head_eq_one
        rw [List.head?_cons, Option.some_inj] at hhead
        exact hhead
      subst hy
      show IsAddChain (((1 : ℕ) :: t).take 1).reverse
      simp only [List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
        List.nil_append]
      exact .one
    · have hmlen : m < s.length := by omega
      have hlen_take : (s.take m).length = m := by
        rw [List.length_take]; omega
      have htake : s.take (m + 1) = s.take m ++ [s[m]'hmlen] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hmlen]
        rfl
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append]
      obtain ⟨i, j, hik, hjk, hsum⟩ := h.get_eq_add ⟨m, hmlen⟩ hmpos
      have hik' : (i : ℕ) < m := hik
      have hjk' : (j : ℕ) < m := hjk
      have hmemi : s.get i ∈ (s.take m).reverse := by
        rw [List.mem_reverse, List.get_eq_getElem]
        have hi : (i : ℕ) < (s.take m).length := by omega
        have hmem := List.getElem_mem hi
        rwa [List.getElem_take] at hmem
      have hmemj : s.get j ∈ (s.take m).reverse := by
        rw [List.mem_reverse, List.get_eq_getElem]
        have hj : (j : ℕ) < (s.take m).length := by omega
        have hmem := List.getElem_mem hj
        rwa [List.getElem_take] at hmem
      have hchain : IsAddChain ((s.get i + s.get j) :: (s.take m).reverse) :=
        IsAddChain.add hmemi hmemj (ih hmpos (by omega))
      rw [← hsum, List.get_eq_getElem] at hchain
      exact hchain

/-- An ascending chain, read backwards, is a permissive chain. -/
theorem IsAscAddChain.isAddChain_reverse {n : ℕ} {s : List ℕ} (h : IsAscAddChain n s) :
    IsAddChain s.reverse := by
  have h0 : 0 < s.length := List.length_pos_of_ne_nil h.ne_nil
  have hres := h.isAddChain_reverse_take s.length h0 le_rfl
  rwa [List.take_length] at hres

/-- Reading an ascending chain for `n` backwards puts `n = s r` at the head, the
convention of `AdditionChain`. -/
theorem IsAscAddChain.head?_reverse {n : ℕ} {s : List ℕ} (h : IsAscAddChain n s) :
    s.reverse.head? = some n := by
  rw [List.head?_reverse]
  exact h.getLast_eq

/-- Reversal does not change the number of additions. -/
theorem chainSteps_reverse (c : List ℕ) : chainSteps c.reverse = chainSteps c := by
  simp only [chainSteps, List.length_tail, List.length_reverse]

/-! ### Permissive ⟹ ascending -/

/-- Every member of a permissive chain other than the start `1` is the sum of
two *strictly smaller* members: the summands of `a + b` are each at least `1`,
hence each strictly below `a + b`.  This is what makes sorting a chain produce
a chain: after sorting, the two witnesses still precede the value. -/
theorem IsAddChain.exists_lt_add_of_mem {c : List ℕ} (hc : IsAddChain c) :
    ∀ x ∈ c, x ≠ 1 → ∃ a ∈ c, ∃ b ∈ c, a < x ∧ b < x ∧ x = a + b := by
  induction hc with
  | one =>
    intro x hx hx1
    rw [List.mem_singleton] at hx
    exact absurd hx hx1
  | @add c a b ha hb hc ih =>
    intro x hx hx1
    rcases List.mem_cons.mp hx with hxab | hxc
    · have h1a : 1 ≤ a := hc.one_le_of_mem a ha
      have h1b : 1 ≤ b := hc.one_le_of_mem b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, by omega, by omega,
        by omega⟩
    · obtain ⟨a', ha', b', hb', hlta, hltb, heq⟩ := ih x hxc hx1
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', hlta, hltb, heq⟩

/-- The ascending normalization of a permissive chain `c` at a target `n`: the
members of `c` that do not exceed `n`, listed in increasing order without
repetition.  Implemented as a filter of `List.range (n + 1)` so that it is
structurally recursive and reduces under kernel `decide`. -/
def ascNormalize (c : List ℕ) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun x => decide (x ∈ c))

-- ground checks for `ascNormalize`, including the overshoot case that motivates
-- the `≤ n` filter (`4` is a member of the chain `[3, 4, 2, 1]` for `3`):
example : ascNormalize [3, 4, 2, 1] 3 = [1, 2, 3] := by decide
example : ascNormalize [15, 12, 6, 3, 2, 1] 15 = [1, 2, 3, 6, 12, 15] := by decide
example : ascNormalize [2, 2, 1] 2 = [1, 2] := by decide   -- repeats collapse

/-- Membership in the normalization: the members of `c` bounded by `n`. -/
theorem mem_ascNormalize {c : List ℕ} {n x : ℕ} :
    x ∈ ascNormalize c n ↔ x ∈ c ∧ x ≤ n := by
  simp only [ascNormalize, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hrange, hmem⟩
    exact ⟨hmem, by omega⟩
  · rintro ⟨hmem, hle⟩
    exact ⟨by omega, hmem⟩

/-- The normalization is strictly increasing (it is a sublist of a range). -/
theorem sortedLT_ascNormalize (c : List ℕ) (n : ℕ) : (ascNormalize c n).SortedLT :=
  (List.Pairwise.sublist List.filter_sublist (List.sortedLT_range (n + 1)).pairwise).sortedLT

/-- The normalization is no longer than the chain it normalizes: it is
duplicate-free and contained in the chain. -/
theorem length_ascNormalize_le (c : List ℕ) (n : ℕ) :
    (ascNormalize c n).length ≤ c.length := by
  have hnodup : (ascNormalize c n).Nodup := List.Nodup.filter _ List.nodup_range
  have hsub : ascNormalize c n ⊆ c := fun _ hx => (mem_ascNormalize.mp hx).1
  exact (List.subperm_of_subset hnodup hsub).length_le

/-- **Normalization is correct**: for a permissive chain `c` and a member
`n ∈ c`, the list `ascNormalize c n` is an ascending chain for `n` in the sense
of the OEIS entry.  The sum clause holds because a member `x` of `c` with
`1 < x` is a sum of two members strictly smaller than `x`
(`IsAddChain.exists_lt_add_of_mem`); those are `≤ n` too, so they survive the
filter, and strict sortedness turns "smaller value" into "earlier index". -/
theorem isAscAddChain_ascNormalize {c : List ℕ} (hc : IsAddChain c) {n : ℕ} (hn : n ∈ c) :
    IsAscAddChain n (ascNormalize c n) := by
  have hsort : (ascNormalize c n).SortedLT := sortedLT_ascNormalize c n
  have hn1 : 1 ≤ n := hc.one_le_of_mem n hn
  have hone : (1 : ℕ) ∈ ascNormalize c n := mem_ascNormalize.mpr ⟨hc.one_mem, hn1⟩
  have hnmem : n ∈ ascNormalize c n := mem_ascNormalize.mpr ⟨hn, le_refl n⟩
  refine ⟨?_, ?_, hsort, ?_⟩
  · refine head?_eq_of_sortedLT hsort hone ?_
    intro x hx
    exact hc.one_le_of_mem x (mem_ascNormalize.mp hx).1
  · refine getLast?_eq_of_sortedLT hsort hnmem ?_
    intro x hx
    exact (mem_ascNormalize.mp hx).2
  · intro k hk0
    have h0 : 0 < (ascNormalize c n).length := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have hzero_mem : (ascNormalize c n).get ⟨0, h0⟩ ∈ ascNormalize c n := by
      rw [List.get_eq_getElem]
      exact List.getElem_mem h0
    have hzero_pos : 1 ≤ (ascNormalize c n).get ⟨0, h0⟩ :=
      hc.one_le_of_mem _ (mem_ascNormalize.mp hzero_mem).1
    have hzero_lt : (ascNormalize c n).get ⟨0, h0⟩ < (ascNormalize c n).get k :=
      hsort.strictMono_get (Fin.lt_def.mpr hk0)
    have hk_mem : (ascNormalize c n).get k ∈ ascNormalize c n := by
      rw [List.get_eq_getElem]
      exact List.getElem_mem k.isLt
    obtain ⟨hk_c, hk_le⟩ := mem_ascNormalize.mp hk_mem
    obtain ⟨a, ha, b, hb, hax, hbx, hsum⟩ := hc.exists_lt_add_of_mem _ hk_c (by omega)
    have ha_mem : a ∈ ascNormalize c n := mem_ascNormalize.mpr ⟨ha, by omega⟩
    have hb_mem : b ∈ ascNormalize c n := mem_ascNormalize.mpr ⟨hb, by omega⟩
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha_mem
    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb_mem
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_, ?_⟩
    · have hlti : (ascNormalize c n).get ⟨i, hi⟩ < (ascNormalize c n).get k := by
        rw [List.get_eq_getElem, hia]
        omega
      exact Fin.lt_def.mp (hsort.strictMono_get.lt_iff_lt.mp hlti)
    · have hltj : (ascNormalize c n).get ⟨j, hj⟩ < (ascNormalize c n).get k := by
        rw [List.get_eq_getElem, hjb]
        omega
      exact Fin.lt_def.mp (hsort.strictMono_get.lt_iff_lt.mp hltj)
    · rw [← hia, ← hjb] at hsum
      simpa only [List.get_eq_getElem] using hsum

/-- Normalizing never costs additions: dropping members and duplicates can only
shorten the list. -/
theorem chainSteps_ascNormalize_le {c : List ℕ} (hc : IsAddChain c) {n : ℕ} (hn : n ∈ c) :
    chainSteps (ascNormalize c n) ≤ chainSteps c := by
  have hlen : (ascNormalize c n).length ≤ c.length := length_ascNormalize_le c n
  have hc1 : c.length = chainSteps c + 1 := hc.length_eq_chainSteps_add_one
  have hs1 : (ascNormalize c n).length = chainSteps (ascNormalize c n) + 1 := by
    obtain ⟨y, t, heq⟩ := List.exists_cons_of_ne_nil (isAscAddChain_ascNormalize hc hn).ne_nil
    rw [heq]
    simp only [List.length_cons, chainSteps, List.tail_cons]
  omega

/-! ### The ascending minimum, and the equality of conventions -/

/-- `AscAdditionChain n`: the ascending (OEIS A003313 convention) addition
chains for `n`, as a subtype.  Empty for `n = 0`
(`instIsEmptyAscAdditionChainZero`), nonempty for `n ≠ 0`
(`nonempty_ascAdditionChain_of_ne_zero`). -/
abbrev AscAdditionChain (n : ℕ) : Type := {s : List ℕ // IsAscAddChain n s}

/-- **A003313 in the entry's own convention**: the least `r` for which there is
a strictly increasing addition chain `1 = s 0 < ⋯ < s r = n`, as the
subtype-indexed infimum `⨅ s : AscAdditionChain n, chainSteps s.val` in `ℕ`.

Degenerate value: `AscAdditionChain 0` is empty, so `lAsc 0 = 0` is the junk
value of the empty infimum, matching the junk `l 0 = 0` — see `lAsc_zero`.  The
entry has offset `1`, so `a(0)` is not defined there either. -/
noncomputable def lAsc (n : ℕ) : ℕ :=
  ⨅ s : AscAdditionChain n, chainSteps s.val

/-- Any ascending chain for `n` bounds `lAsc n` from above. -/
theorem lAsc_le_chainSteps {n : ℕ} (s : AscAdditionChain n) : lAsc n ≤ chainSteps s.val :=
  Nat.sInf_le (Set.mem_range_self s)

/-- No ascending chain reaches `0`: reversed it would be a permissive chain with
head `0`, and all chain members are positive. -/
instance instIsEmptyAscAdditionChainZero : IsEmpty (AscAdditionChain 0) :=
  ⟨fun s => by
    have hchain := s.property.isAddChain_reverse
    have hhead := s.property.head?_reverse
    obtain ⟨y, t, heq⟩ := List.exists_cons_of_ne_nil hchain.ne_nil
    rw [heq, List.head?_cons, Option.some_inj] at hhead
    have h1 : 1 ≤ (0 : ℕ) :=
      hchain.one_le_of_mem 0 (by rw [heq, ← hhead]; exact List.mem_cons_self)
    omega⟩

/-- Degenerate value, pinned: `lAsc 0 = 0` is the junk value of the infimum over
the empty type `AscAdditionChain 0`, exactly as for `l_zero`. -/
@[simp] theorem lAsc_zero : lAsc 0 = 0 :=
  Nat.iInf_of_empty _

/-- Every `n ≠ 0` has an ascending chain: normalize the staircase chain. -/
theorem nonempty_ascAdditionChain_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Nonempty (AscAdditionChain n) := by
  obtain ⟨c⟩ := nonempty_additionChain_of_ne_zero hn
  exact ⟨⟨ascNormalize c.val n, isAscAddChain_ascNormalize c.property.1 c.head_mem⟩⟩

/-- For `n ≠ 0` the infimum defining `lAsc n` is attained. -/
theorem exists_chainSteps_eq_lAsc {n : ℕ} (hn : n ≠ 0) :
    ∃ s : AscAdditionChain n, chainSteps s.val = lAsc n := by
  haveI hne : Nonempty (AscAdditionChain n) := nonempty_ascAdditionChain_of_ne_zero hn
  have hmem : lAsc n ∈ Set.range fun s : AscAdditionChain n => chainSteps s.val :=
    Nat.sInf_mem (Set.range_nonempty _)
  rwa [Set.mem_range] at hmem

/-- **The two conventions agree**: the permissive minimum `l` of this file and
the ascending minimum `lAsc` of the OEIS A003313 comment are the same function
of `n`, for every `n` (including the junk value at `n = 0`, where both infima
are empty).

`l n ≤ lAsc n` because an optimal ascending chain, reversed, is a permissive
chain with the same number of additions; `lAsc n ≤ l n` because an optimal
permissive chain normalizes (`ascNormalize`) to an ascending chain with no more
additions. -/
theorem l_eq_lAsc (n : ℕ) : l n = lAsc n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [l_zero, lAsc_zero]
  · have hn : n ≠ 0 := hpos.ne'
    refine le_antisymm ?_ ?_
    · obtain ⟨s, hs⟩ := exists_chainSteps_eq_lAsc hn
      rw [← hs]
      exact l_le_of_isAddChain s.val.reverse s.property.isAddChain_reverse
        s.property.head?_reverse (le_of_eq (chainSteps_reverse s.val))
    · obtain ⟨c, hc⟩ := exists_chainSteps_eq_l hn
      calc lAsc n ≤ chainSteps (ascNormalize c.val n) :=
            lAsc_le_chainSteps ⟨_, isAscAddChain_ascNormalize c.property.1 c.head_mem⟩
        _ ≤ chainSteps c.val := chainSteps_ascNormalize_le c.property.1 c.head_mem
        _ = l n := hc

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

/-! ## Ground checks for the ascending convention

An explicit optimal *ascending* chain for each `1 ≤ n ≤ 8`, certified by kernel
`decide` against `IsAscAddChain`, together with the resulting values of `lAsc`.
The values are transported from `l` by `l_eq_lAsc`; independently, each chain
below has exactly `a(n)` additions, so the two computations agree pointwise.
This is the first verification of that agreement in this repository: an INDEX
claim that it had been "computationally verified to n = 24" cited a review file
that does not exist and is unsourced. -/

example : IsAscAddChain 1 [1] := by decide                    -- a(1) = 0
example : IsAscAddChain 2 [1, 2] := by decide                 -- a(2) = 1
example : IsAscAddChain 3 [1, 2, 3] := by decide              -- a(3) = 2
example : IsAscAddChain 4 [1, 2, 4] := by decide              -- a(4) = 2
example : IsAscAddChain 5 [1, 2, 4, 5] := by decide           -- a(5) = 3
example : IsAscAddChain 6 [1, 2, 4, 6] := by decide           -- a(6) = 3
example : IsAscAddChain 7 [1, 2, 4, 6, 7] := by decide        -- a(7) = 4
example : IsAscAddChain 8 [1, 2, 4, 8] := by decide           -- a(8) = 3

/-- Agreement of the ascending minimum with the A003313 terms
`a(1), …, a(8) = 0, 1, 2, 2, 3, 3, 4, 3`.  Upper bounds are the explicit chains
displayed above (through `l_le_of_isAddChain` on their reversals, or through
`l_two_pow` at `4` and `8`); lower bounds are kernel-`decide` exhaustions of all
shorter chains through `decidableLLe`. -/
theorem lAsc_eq_A003313_of_le_eight :
    lAsc 1 = 0 ∧ lAsc 2 = 1 ∧ lAsc 3 = 2 ∧ lAsc 4 = 2 ∧ lAsc 5 = 3 ∧ lAsc 6 = 3 ∧
      lAsc 7 = 4 ∧ lAsc 8 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← l_eq_lAsc]
  · exact l_one
  · exact l_two
  · have hub : l 3 ≤ 2 := l_le_of_isAddChain [3, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 3 ≤ 1 := by decide
    omega
  · have h := l_two_pow 2
    norm_num at h
    exact h
  · have hub : l 5 ≤ 3 := l_le_of_isAddChain [5, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 5 ≤ 2 := by decide
    omega
  · have hub : l 6 ≤ 3 := l_le_of_isAddChain [6, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 6 ≤ 2 := by decide
    omega
  · have hub : l 7 ≤ 4 := l_le_of_isAddChain [7, 6, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 7 ≤ 3 := by decide
    omega
  · have h := l_two_pow 3
    norm_num at h
    exact h

example : lAsc 0 = 0 := lAsc_zero      -- junk value, documented at `lAsc`
example : lAsc 15 = 5 := by            -- a(15) = 5, matching the `l 15 = 5` check
  rw [← l_eq_lAsc]
  have hub : l 15 ≤ 5 := l_le_of_isAddChain [15, 12, 6, 3, 2, 1] (by decide) rfl (by decide)
  -- `+kernel` as in the `l 15 = 5` check above: the 576-chain enumeration is
  -- evaluated by kernel reduction only.  This is NOT `native_decide`; the trust
  -- surface is unchanged.
  have hlb : ¬l 15 ≤ 4 := by decide +kernel
  omega

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

-- and for the ascending layer: `isAscAddChain_ascNormalize` and
-- `chainSteps_ascNormalize_le` at the overshooting chain `[3, 4, 2, 1]` for
-- `n = 3`, the `IsAscAddChain.*` lemmas at `[1, 2, 3, 6, 12, 15]`, and
-- `exists_chainSteps_eq_lAsc` / `lAsc_le_chainSteps` at `n = 5`:
example : IsAscAddChain 3 (ascNormalize [3, 4, 2, 1] 3) :=
  isAscAddChain_ascNormalize (by decide) (by decide)
example : chainSteps (ascNormalize [3, 4, 2, 1] 3) ≤ chainSteps [3, 4, 2, 1] :=
  chainSteps_ascNormalize_le (by decide) (by decide)
example : IsAddChain ([1, 2, 3, 6, 12, 15] : List ℕ).reverse :=
  (show IsAscAddChain 15 [1, 2, 3, 6, 12, 15] by decide).isAddChain_reverse
example : ([1, 2, 3, 6, 12, 15] : List ℕ).reverse.head? = some 15 :=
  (show IsAscAddChain 15 [1, 2, 3, 6, 12, 15] by decide).head?_reverse
example : ∃ s : AscAdditionChain 5, chainSteps s.val = lAsc 5 :=
  exists_chainSteps_eq_lAsc (by norm_num)
example : lAsc 5 ≤ chainSteps ([1, 2, 4, 5] : List ℕ) :=
  lAsc_le_chainSteps ⟨[1, 2, 4, 5], by decide⟩
example : ([1, 2, 3] : List ℕ).head? = some 1 :=
  head?_eq_of_sortedLT (by decide) (by decide) (by decide)
example : ([1, 2, 3] : List ℕ).getLast? = some 3 :=
  getLast?_eq_of_sortedLT (by decide) (by decide) (by decide)
example : ∃ a ∈ [15, 12, 6, 3, 2, 1], ∃ b ∈ [15, 12, 6, 3, 2, 1],
    a < 15 ∧ b < 15 ∧ (15 : ℕ) = a + b :=
  (show IsAddChain [15, 12, 6, 3, 2, 1] by decide).exists_lt_add_of_mem 15
    (by decide) (by decide)

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
#print axioms lAsc
#print axioms l_eq_lAsc
#print axioms lAsc_zero
#print axioms lAsc_eq_A003313_of_le_eight
#print axioms lAsc_le_chainSteps
#print axioms exists_chainSteps_eq_lAsc
#print axioms nonempty_ascAdditionChain_of_ne_zero
#print axioms instIsEmptyAscAdditionChainZero
#print axioms isAscAddChain_iff
#print axioms instDecidableIsAscAddChain
#print axioms isAscAddChain_ascNormalize
#print axioms chainSteps_ascNormalize_le
#print axioms mem_ascNormalize
#print axioms sortedLT_ascNormalize
#print axioms length_ascNormalize_le
#print axioms IsAscAddChain.ne_nil
#print axioms IsAscAddChain.isAddChain_reverse_take
#print axioms IsAscAddChain.isAddChain_reverse
#print axioms IsAscAddChain.head?_reverse
#print axioms IsAddChain.exists_lt_add_of_mem
#print axioms chainSteps_reverse
#print axioms head?_eq_of_sortedLT
#print axioms getLast?_eq_of_sortedLT

end NumberComplexity
