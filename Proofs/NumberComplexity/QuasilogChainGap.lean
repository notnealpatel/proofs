import Mathlib
import NumberComplexity.AdditionChain
import NumberComplexity.Quasilog

/-!
# OEIS A076142: the gap between the quasi-logarithm and the shortest chain

A076142 is `a(n) = A064097(n) - A003313(n)`: the amount by which the completely
additive quasi-logarithm `quasilog` (A064097, `NumberComplexity/Quasilog.lean`)
overshoots the true shortest-addition-chain length `l` (A003313,
`NumberComplexity/AdditionChain.lean`).

**Why the gap is nonnegative.** The `quasilog` recursion is exactly a
*chain-building scheme*: at a prime `p` it spends one addition to descend from
`p` to `p - 1` (the step `x ↦ x + 1`, legal because `1` belongs to every
addition chain), and at a composite `n = m * k` it spends `a m + a k`
additions by the *factor method* — scale a chain for `k` by `m` and append a
chain for `m`.  So `quasilog n` is the cost of one particular chain for `n`,
while `l n` minimises over *all* chains; hence `l n ≤ quasilog n`, i.e.
`a(n) = A064097(n) - A003313(n) ≥ 0`, the content of the entry's `nonn`
keyword.  This is the theorem `NumberComplexity.l_le_quasilog`, and it is the
wiring that links the two committed definition layers.

## Novelty status (literature sweep 2026-07-30, `.tasks/main/docs/novelty-QuasilogChainGap.md`)

LIKELY-KNOWN.  The inequality follows by strong induction from two classical
facts: the factor-method subadditivity `l (m * n) ≤ l m + l n`, posed by Scholz
(Aufgabe 253, Jahresbericht d. DMV 47 (1937), 41–42) and proved by Brauer (On
addition chains, Bull. AMS 45 (1939), 736–739 — whose p. 737 construction is
exactly `factorChain` below), and the trivial successor bound
`l (n + 1) ≤ l n + 1`.  Knuth (TAOCP Vol. 2, 3rd ed., §4.6.3) covers the factor
method.  No prior statement of the specific comparison to A064097 was found;
the formalization here appears to be its first recorded proof.  Not a novel
result — the ingredients are Scholz–Brauer.

Main declarations:

* `NumberComplexity.factorChain` — the factor-method composite chain: scale a
  chain by `x`, drop its final `1` (whose scaled copy `x` is the head of the
  chain being appended), and append a chain for `x`;
* `NumberComplexity.isAddChain_factorChain`, `NumberComplexity.mem_factorChain`,
  `NumberComplexity.head?_factorChain` — its chain property, membership, head;
* `NumberComplexity.l_mul_le` — **subadditivity on products**,
  `l (m * n) ≤ l m + l n` for `0 < m`, `0 < n` (the factor method);
* `NumberComplexity.l_add_one_le` — `l (n + 1) ≤ l n + 1` for `0 < n` (extend a
  shortest chain for `n` by the sum of its head `n` and its member `1`);
* `NumberComplexity.l_le_quasilog` — **tier 1, proved**: `l n ≤ quasilog n` for
  `0 < n`;
* `NumberComplexity.log_two_le_l_le_quasilog` — the sandwich
  `⌊log₂ n⌋ ≤ l n ≤ quasilog n`, joining the two files' bounds;
* `NumberComplexity.gap` — A076142 itself, as an integer difference (cast
  before subtracting, so no `ℕ` truncation is hidden in the statement);
* `NumberComplexity.gap_nonneg` — `0 ≤ gap n` for `0 < n`;
* `NumberComplexity.gap_23_eq_one`, `NumberComplexity.gap_33_eq_one`,
  `NumberComplexity.l_lt_quasilog_23` — the entry's first two nonzero terms,
  certified; in particular the tier-1 inequality is somewhere strict, so
  A076142 is not the zero sequence;
* `NumberComplexity.gapSum` — the partial sums `∑_{k ≤ n} a(k)` of the entry's
  formula, with `NumberComplexity.gapSum_nonneg` and
  `NumberComplexity.one_le_gapSum` (`1 ≤ gapSum n` for `23 ≤ n`);
* `NumberComplexity.gapSum_mul_log_div_sq_nonneg`,
  `NumberComplexity.eventually_log_pos_and_sq_pos` — sign and junk-value guards
  for the conjectured limit;
* `NumberComplexity.exists_tendsto_gapSum_mul_log_div_sq` — **tier 2, open**:
  the entry's unattributed "it seems" formula
  `(∑_{k ≤ n} a(k)) * log n / n² → c` with `0.006 < c < 0.01`.  Carried as an
  intended `sorry` (statement archive), guarded and instantiated as described
  in its section below.

**Degenerate values.** At `n = 0` both `l 0 = 0` (empty infimum: no chain
reaches `0`) and `quasilog 0 = 0` (junk input) are junk, so `gap 0 = 0` is a
junk-derived zero.  Every statement about a single `l n` or `gap n` therefore
carries the guard `0 < n`; the partial sums start their index at `k = 1`; and
the `Real.log` and division of the tier-2 statement are guarded structurally by
`eventually_log_pos_and_sq_pos`.

Ground truth: `oeis show A076142`, pulled live 2026-07-30. Name
`a(n) = A064097(n) - A003313(n)`, keyword `nonn`, terms (offset 1) begin with
twenty-two zeros, `a(23) = 1`, `a(33) = 1`, `a(43) = 1`, `a(46) = a(47) = 1`,
… `a(129) = 2`; the entry's comment (Antti Karttunen, Aug 18 2017) records the
first occurrences of `0, 1, 2, …` at `n = 1, 23, 129, 517, …`.  Checked below.

Card: `Formalize/A076142-quasilog-chain-gap.md`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## The factor method: `l` is subadditive on products -/

/-- The factor-method composite chain.  If `c` is an addition chain for `m` and
`d` is an addition chain for `x`, then `factorChain x c d` is an addition chain
for `x * m`: every element of `c` except its final `1` is scaled by `x` (the
scaled copy of that final `1` is `x`, which is already the head of `d`), and
`d` is appended below.  In the reversed representation
`[x * m, …, x * a₁, x, …, 1]`. -/
def factorChain (x : ℕ) (c d : List ℕ) : List ℕ :=
  c.dropLast.map (x * ·) ++ d

/-- Scaling sends members of `c` to members of `factorChain x c d`: a member
lying in `c.dropLast` goes into the scaled part, and the final member `1` of a
chain goes to `x`, a member of `d`. -/
theorem mem_factorChain {c d : List ℕ} (hc : IsAddChain c) {x a : ℕ} (hx : x ∈ d)
    (ha : a ∈ c) : x * a ∈ factorChain x c d := by
  have hne : c ≠ [] := hc.ne_nil
  have hlast : c.getLast hne = 1 := by
    have hlast? := hc.getLast?_eq_one
    rw [List.getLast?_eq_some_getLast hne] at hlast?
    exact Option.some_inj.mp hlast?
  have hsplit : c.dropLast ++ [c.getLast hne] = c := List.dropLast_append_getLast hne
  rw [← hsplit, List.mem_append, List.mem_singleton] at ha
  rcases ha with hdrop | hone
  · exact List.mem_append_left _ (List.mem_map_of_mem hdrop)
  · rw [hone, hlast, Nat.mul_one]
    exact List.mem_append_right _ hx

/-- `factorChain x c d` is an addition chain: each scaled step
`x * (a + b) = x * a + x * b` has both summands present by `mem_factorChain`,
and the bottom of the list is the chain `d`. -/
theorem isAddChain_factorChain {c d : List ℕ} (hc : IsAddChain c) (hd : IsAddChain d)
    {x : ℕ} (hx : x ∈ d) : IsAddChain (factorChain x c d) := by
  induction hc with
  | one => simpa [factorChain] using hd
  | @add c a b ha hb hc ih =>
    have hne : c ≠ [] := hc.ne_nil
    have hstep : factorChain x ((a + b) :: c) d = (x * a + x * b) :: factorChain x c d := by
      simp only [factorChain, List.dropLast_cons_of_ne_nil hne, List.map_cons, List.cons_append,
        Nat.mul_add]
    rw [hstep]
    exact .add (mem_factorChain hc hx ha) (mem_factorChain hc hx hb) ih

/-- The head of the composite chain is `x * m`, where `m` heads `c` and `x`
heads `d` (for the one-element chain `c = [1]` the composite is `d` itself and
`x * 1 = x` is still its head). -/
theorem head?_factorChain {c d : List ℕ} (hc : IsAddChain c) {m x : ℕ}
    (hcm : c.head? = some m) (hdx : d.head? = some x) :
    (factorChain x c d).head? = some (x * m) := by
  rcases c with _ | ⟨y, t⟩
  · exact absurd rfl hc.ne_nil
  · rw [List.head?_cons, Option.some_inj] at hcm
    subst hcm
    rcases t with _ | ⟨z, t⟩
    · have hy : y = 1 := isAddChain_singleton_iff.mp hc
      subst hy
      simpa [factorChain] using hdx
    · simp only [factorChain, List.dropLast_cons_of_ne_nil (List.cons_ne_nil z t), List.map_cons,
        List.cons_append, List.head?_cons]

/-- The composite chain performs the sum of the two chains' additions:
`length = (c.length - 1) + d.length`, stated subtraction-free. -/
theorem length_factorChain_add_one (x : ℕ) {c d : List ℕ} (hc : c ≠ []) :
    (factorChain x c d).length + 1 = c.length + d.length := by
  have hpos : 0 < c.length := List.length_pos_of_ne_nil hc
  have hdrop : c.dropLast.length = c.length - 1 := List.length_dropLast
  simp only [factorChain, List.length_append, List.length_map]
  omega

/-- **The factor method**: `l (m * n) ≤ l m + l n` for `0 < m`, `0 < n`.  Both
guards are needed to keep `l` off its junk value at `0`. -/
theorem l_mul_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : l (m * n) ≤ l m + l n := by
  obtain ⟨c, hcsteps⟩ := exists_chainSteps_eq_l hm.ne'
  obtain ⟨d, hdsteps⟩ := exists_chainSteps_eq_l hn.ne'
  obtain ⟨hcchain, hchead⟩ := c.property
  obtain ⟨hdchain, hdhead⟩ := d.property
  have hnmem : n ∈ d.val := d.head_mem
  have hchain : IsAddChain (factorChain n c.val d.val) :=
    isAddChain_factorChain hcchain hdchain hnmem
  refine l_le_of_isAddChain (factorChain n c.val d.val) hchain ?_ ?_
  · rw [head?_factorChain hcchain hchead hdhead, Nat.mul_comm]
  · have hlen : (factorChain n c.val d.val).length + 1 = c.val.length + d.val.length :=
      length_factorChain_add_one n hcchain.ne_nil
    have hc1 : c.val.length = chainSteps c.val + 1 := hcchain.length_eq_chainSteps_add_one
    have hd1 : d.val.length = chainSteps d.val + 1 := hdchain.length_eq_chainSteps_add_one
    have hf1 : (factorChain n c.val d.val).length
        = chainSteps (factorChain n c.val d.val) + 1 := hchain.length_eq_chainSteps_add_one
    omega

/-- One extra addition suffices to step up by one: `l (n + 1) ≤ l n + 1` for
`0 < n`, since `1` is a member of every addition chain
(`IsAddChain.one_mem`). -/
theorem l_add_one_le {n : ℕ} (hn : 0 < n) : l (n + 1) ≤ l n + 1 := by
  obtain ⟨c, hcsteps⟩ := exists_chainSteps_eq_l hn.ne'
  obtain ⟨hchain, hhead⟩ := c.property
  have hsteps : chainSteps ((n + 1) :: c.val) = l n + 1 := by
    rw [chainSteps_cons, hchain.length_eq_chainSteps_add_one, hcsteps]
  exact l_le_of_isAddChain ((n + 1) :: c.val) (.add c.head_mem hchain.one_mem hchain)
    (by rw [List.head?_cons]) hsteps.le

/-! ## Tier 1: the quasi-logarithm dominates the shortest chain -/

/-- **Nonnegativity of OEIS A076142** in its primitive form: the shortest
addition chain is never longer than the quasi-logarithmic factor-method bound,
`l n ≤ quasilog n` for `0 < n` (A003313(n) ≤ A064097(n)).  The `quasilog`
recursion is a chain-building scheme: `+1` at a prime step (`l_add_one_le`)
and the factor method at a composite step (`l_mul_le`). -/
theorem l_le_quasilog (n : ℕ) (hn : 0 < n) : l n ≤ quasilog n := by
  -- strong induction on `n`, phrased as plain induction on an upper bound `N`
  suffices H : ∀ N n : ℕ, n ≤ N → 0 < n → l n ≤ quasilog n by
    exact H n n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro n hle hn
    exact absurd hle (Nat.not_le.mpr hn)
  | succ N ih =>
    intro n hle hn
    by_cases h1 : n = 1
    · subst h1
      rw [l_one, quasilog_one]
    have h2 : 2 ≤ n := by omega
    by_cases hp : n.Prime
    · -- prime step: one addition `x ↦ x + 1` on top of a chain for `n - 1`
      have hIH : l (n - 1) ≤ quasilog (n - 1) := ih (n - 1) (by omega) (by omega)
      have hstep : l n ≤ l (n - 1) + 1 := by
        have hle1 := l_add_one_le (show 0 < n - 1 by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hle1
      rw [quasilog_of_prime hp]
      omega
    · -- composite step: the factor method at the least prime factor
      have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega : n ≠ 1)
      have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hple : n.minFac ≤ n := Nat.minFac_le (by omega)
      have hplt : n.minFac < n := lt_of_le_of_ne hple (fun h => hp (h ▸ hpp))
      have hqpos : 0 < n / n.minFac := Nat.div_pos hple hpp.pos
      have hqlt : n / n.minFac < n := Nat.div_lt_self (by omega) hpp.one_lt
      have hIH1 : l n.minFac ≤ quasilog n.minFac := ih n.minFac (by omega) hpp.pos
      have hIH2 : l (n / n.minFac) ≤ quasilog (n / n.minFac) :=
        ih (n / n.minFac) (by omega) hqpos
      have hfac : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hpdvd
      have hmul : l (n.minFac * (n / n.minFac)) ≤ l n.minFac + l (n / n.minFac) :=
        l_mul_le hpp.pos hqpos
      rw [hfac] at hmul
      rw [quasilog_of_not_prime h2 hp]
      omega

/-- The two committed layers, sandwiched: `⌊log₂ n⌋ ≤ l n ≤ quasilog n` for
`0 < n`.  The left half is the doubling bound of `AdditionChain.lean`, the right
half is `l_le_quasilog`; together they re-derive Wilson's lower bound
`log_two_le_quasilog` of `Quasilog.lean` along a different route, so the two
files' independently proved bounds are consistent. -/
theorem log_two_le_l_le_quasilog (n : ℕ) (hn : 0 < n) :
    Nat.log 2 n ≤ l n ∧ l n ≤ quasilog n :=
  ⟨log_two_le_l n hn, l_le_quasilog n hn⟩

/-! ## A076142 itself -/

/-- **OEIS A076142**: `a(n) = A064097(n) - A003313(n)`, the gap between the
quasi-logarithm and the shortest-addition-chain length.  Both casts precede the
subtraction, so the difference is taken in `ℤ` and no `ℕ` truncation is hidden
in the statement; `gap_nonneg` shows the value is nonnegative for `0 < n`
(the entry's `nonn` keyword).  At `n = 0` the value `0` is junk-derived, both
inputs being junk. -/
noncomputable def gap (n : ℕ) : ℤ := (quasilog n : ℤ) - (l n : ℤ)

/-- **A076142 is nonnegative** (the entry's `nonn` keyword) for `0 < n`. -/
theorem gap_nonneg (n : ℕ) (hn : 0 < n) : 0 ≤ gap n := by
  have hle : l n ≤ quasilog n := l_le_quasilog n hn
  have hcast : (l n : ℤ) ≤ (quasilog n : ℤ) := by exact_mod_cast hle
  unfold gap
  omega

/-- Partial sums `∑_{k = 1}^{n} a(k)` of A076142, the object of the entry's
formula.  The index set `Finset.Icc 1 n` excludes the junk input `0`. -/
noncomputable def gapSum (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, gap k

/-- The partial sums are nonnegative. -/
theorem gapSum_nonneg (n : ℕ) : 0 ≤ gapSum n :=
  Finset.sum_nonneg fun k hk => gap_nonneg k (Finset.mem_Icc.mp hk).1

/-! ## Ground checks against `oeis show A076142` (pulled live 2026-07-30)

Each value `gap n = v` below is certified from its two components: `quasilog n`
by the conditional defining equations of `NumberComplexity/Quasilog.lean`, and
`l n` by an explicit optimal chain (upper bound, `l_le_of_isAddChain`) together
with exhaustion of all chains of `v - 1` additions (lower bound, the
`Decidable (l n ≤ k)` instance of `NumberComplexity/AdditionChain.lean`).

**Trust.** No `native_decide` anywhere: `decide +kernel` checks the same
certificate by kernel reduction, and the `maxRecDepth` bump only raises the
kernel's recursion limit for the 14400-element enumeration `chainsOfLength 5`.
The next entry `a(43) = 1` would need `chainsOfLength 6` (518400 chains) and is
omitted on cost grounds.

Terms checked: `a(1) … a(8) = 0`, `a(15) = a(16) = a(22) = a(32) = 0`, and the
first two nonzero terms `a(23) = a(33) = 1` — consistent with the entry's
comment (Antti Karttunen, Aug 18 2017) that the value `1` first occurs at
`n = 23`.  Every value agrees both with the entry's DATA section (129 terms)
and with an independent recomputation of A003313 (exhaustive iterative-
deepening chain search) and A064097 over `n ≤ 130`. -/

/-- Ground-check helper: assemble `gap n` from its two component values. -/
theorem gap_eq_sub {n p q : ℕ} (hq : quasilog n = p) (hl : l n = q) :
    gap n = (p : ℤ) - (q : ℤ) := by
  unfold gap
  rw [hq, hl]

example : gap 1 = 0 := by                         -- a(1) = 0
  rw [gap_eq_sub quasilog_one l_one]
  norm_num

example : gap 2 = 0 := by                         -- a(2) = 0
  have hq : quasilog 2 = 1 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  rw [gap_eq_sub hq l_two]
  norm_num

example : gap 3 = 0 := by                         -- a(3) = 0
  have hq : quasilog 3 = 2 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 3 = 2 := by
    have hub : l 3 ≤ 2 := l_le_of_isAddChain [3, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 3 ≤ 1 := by decide
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 4 = 0 := by                         -- a(4) = 0
  have hq : quasilog 4 = 2 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 4 = 2 := by
    have hpow := l_two_pow 2
    norm_num at hpow
    exact hpow
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 5 = 0 := by                         -- a(5) = 0
  have hq : quasilog 5 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 5 = 3 := by
    have hub : l 5 ≤ 3 := l_le_of_isAddChain [5, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 5 ≤ 2 := by decide
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 6 = 0 := by                         -- a(6) = 0
  have hq : quasilog 6 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 6 = 3 := by
    have hub : l 6 ≤ 3 := l_le_of_isAddChain [6, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 6 ≤ 2 := by decide
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 7 = 0 := by                         -- a(7) = 0
  have hq : quasilog 7 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 7 = 4 := by
    have hub : l 7 ≤ 4 := l_le_of_isAddChain [7, 6, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 7 ≤ 3 := by decide
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 8 = 0 := by                         -- a(8) = 0
  have hq : quasilog 8 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 8 = 3 := by
    have hpow := l_two_pow 3
    norm_num at hpow
    exact hpow
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 15 = 0 := by                        -- a(15) = 0 (binary method beaten: l 15 = 5)
  have hq : quasilog 15 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 15 = 5 := by
    have hub : l 15 ≤ 5 :=
      l_le_of_isAddChain [15, 12, 6, 3, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 15 ≤ 4 := by decide +kernel
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 16 = 0 := by                        -- a(16) = 0
  have hq : quasilog 16 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 16 = 4 := by
    have hpow := l_two_pow 4
    norm_num at hpow
    exact hpow
  rw [gap_eq_sub hq hl]
  norm_num

set_option maxRecDepth 40000 in
example : gap 22 = 0 := by                        -- a(22) = 0, the last zero before n = 23
  have hq : quasilog 22 = 6 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 22 = 6 := by
    have hub : l 22 ≤ 6 :=
      l_le_of_isAddChain [22, 11, 10, 5, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 22 ≤ 5 := by decide +kernel
    omega
  rw [gap_eq_sub hq hl]
  norm_num

example : gap 32 = 0 := by                        -- a(32) = 0
  have hq : quasilog 32 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 32 = 5 := by
    have hpow := l_two_pow 5
    norm_num at hpow
    exact hpow
  rw [gap_eq_sub hq hl]
  norm_num

set_option maxRecDepth 40000 in
/-- **`a(23) = 1`**: the first nonzero term of A076142.  The quasi-logarithm
pays `quasilog 23 = 7` (the prime chain `23 → 22 = 2 · 11 → 11 → 10 = 2 · 5 →
5 → 4`), while the true shortest chain has `l 23 = 6` additions
(`1, 2, 4, 5, 9, 18, 23`).  The lower bound `¬l 23 ≤ 5` is kernel exhaustion of
all 14400 addition chains with five additions. -/
theorem gap_23_eq_one : gap 23 = 1 := by
  have hq : quasilog 23 = 7 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 23 = 6 := by
    have hub : l 23 ≤ 6 :=
      l_le_of_isAddChain [23, 18, 9, 5, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 23 ≤ 5 := by decide +kernel
    omega
  rw [gap_eq_sub hq hl]
  norm_num

set_option maxRecDepth 40000 in
/-- **`a(33) = 1`**: the second nonzero term of A076142.  Here
`quasilog 33 = quasilog 3 + quasilog 11 = 2 + 5 = 7` while `l 33 = 6` (five
doublings and one addition: `1, 2, 4, 8, 16, 32, 33`). -/
theorem gap_33_eq_one : gap 33 = 1 := by
  have hq : quasilog 33 = 7 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
  have hl : l 33 = 6 := by
    have hub : l 33 ≤ 6 :=
      l_le_of_isAddChain [33, 32, 16, 8, 4, 2, 1] (by decide) rfl (by decide)
    have hlb : ¬l 33 ≤ 5 := by decide +kernel
    omega
  rw [gap_eq_sub hq hl]
  norm_num

-- ground checks for `gapSum`: it starts at `0`, and jumps by exactly one at the
-- entry's first nonzero term `a(23) = 1`
example : gapSum 1 = 0 := by
  unfold gapSum
  rw [Finset.Icc_self, Finset.sum_singleton, gap_eq_sub quasilog_one l_one]
  norm_num

example : gapSum (22 + 1) = gapSum 22 + 1 := by
  have h23 : gap (22 + 1) = 1 := gap_23_eq_one
  unfold gapSum
  rw [Finset.sum_Icc_succ_top (by norm_num : (1 : ℕ) ≤ 22 + 1) gap, h23]

/-! ## Satisfiability of hypotheses at concrete models

Every hypothesis-bearing declaration above is jointly instantiated at an
explicit model: the `factorChain` lemmas at `c = [3, 2, 1]` (a chain for `3`),
`d = [2, 1]` (a chain for `2`) and `x = 2`, whose composite is the chain
`[6, 4, 2, 1]` for `6`; the two upper-bound lemmas and tier 1 at small `n`; and
the tier-1 inequality is shown to be *strict* somewhere (`n = 23`), so it is not
an equality in disguise. -/

example : factorChain 2 [3, 2, 1] [2, 1] = [6, 4, 2, 1] := rfl

example : (2 : ℕ) * 3 ∈ factorChain 2 [3, 2, 1] [2, 1] :=
  mem_factorChain (by decide) (by decide) (by decide)

example : IsAddChain (factorChain 2 [3, 2, 1] [2, 1]) :=
  isAddChain_factorChain (by decide) (by decide) (by decide)

example : (factorChain 2 [3, 2, 1] [2, 1]).head? = some (2 * 3) :=
  head?_factorChain (by decide) rfl rfl

example : (factorChain 2 [3, 2, 1] [2, 1]).length + 1 = [3, 2, 1].length + [2, 1].length :=
  length_factorChain_add_one 2 (by decide)

example : l (3 * 2) ≤ l 3 + l 2 := l_mul_le (by norm_num) (by norm_num)  -- 3 ≤ 2 + 1
example : l 5 ≤ l 4 + 1 := l_add_one_le (by norm_num)              -- 3 ≤ 2 + 1, tight
example : l 15 ≤ quasilog 15 := l_le_quasilog 15 (by norm_num)     -- 5 ≤ 5, tight
example : 0 ≤ gap 23 := gap_nonneg 23 (by norm_num)
example : Nat.log 2 23 ≤ l 23 ∧ l 23 ≤ quasilog 23 :=
  log_two_le_l_le_quasilog 23 (by norm_num)

/-- The tier-1 bound is strict somewhere — at `n = 23` the quasi-logarithm
overshoots the shortest chain — so `l_le_quasilog` is not an equality in
disguise and A076142 is not the zero sequence. -/
theorem l_lt_quasilog_23 : l 23 < quasilog 23 := by
  have hgap := gap_23_eq_one
  unfold gap at hgap
  omega

/-! ## Tier 2: the entry's "it seems" formula (OPEN, intended `sorry`) -/

/-- The gap sequence is not eventually zero on the range of the conjecture:
`gap 23 = 1` gives `1 ≤ gapSum n` for every `23 ≤ n`.  This is the
nontriviality check for the conjecture below — were every gap zero, the ratio
would be identically `0` and its limit `0`, outside the entry's window
`0.006 < c < 0.01`. -/
theorem one_le_gapSum {n : ℕ} (hn : 23 ≤ n) : 1 ≤ gapSum n := by
  have hmem : (23 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by norm_num, hn⟩
  have hle : gap 23 ≤ gapSum n :=
    Finset.single_le_sum (f := gap) (fun k hk => gap_nonneg k (Finset.mem_Icc.mp hk).1) hmem
  rw [gap_23_eq_one] at hle
  exact hle

example : 1 ≤ gapSum 23 := one_le_gapSum (by norm_num)
example : 1 ≤ gapSum 100 := one_le_gapSum (by norm_num)

/-- The sequence whose limit the conjecture asserts is nonnegative at every `n`
(including the junk points `n ≤ 1`, where it is `0`), so any limit is `≥ 0` —
consistent with the entry's window `0.006 < c < 0.01`. -/
theorem gapSum_mul_log_div_sq_nonneg (n : ℕ) :
    0 ≤ (gapSum n : ℝ) * Real.log n / (n : ℝ) ^ 2 := by
  have hsum : (0 : ℝ) ≤ (gapSum n : ℝ) := by exact_mod_cast gapSum_nonneg n
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  exact div_nonneg (mul_nonneg hsum hlog) (sq_nonneg _)

/-- Junk-value guard for the conjecture below: on the eventual domain of
`Filter.atTop` the totalized operators of the statement are off their junk
values — `2 ≤ n` gives `0 < Real.log n` (junk at `n = 0`, zero at `n = 1`) and
`0 < (n : ℝ) ^ 2`, so the ratio is a genuine quotient there. -/
theorem eventually_log_pos_and_sq_pos :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < Real.log n ∧ 0 < (n : ℝ) ^ 2 := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by linarith
  exact ⟨Real.log_pos hn1, pow_pos (by linarith : (0 : ℝ) < (n : ℝ)) 2⟩

/-- **OEIS A076142, formula section** (unattributed: "It seems that
`sum(k = 1, n, a(k)) * log(n)/n^2 -> c` with `0.006 < c < 0.01`") — OPEN,
intended `sorry`.

Equivalently the average gap grows like `c' * n / log n`.  The statement is a
`Filter.Tendsto` over `ℕ → ℝ` along `Filter.atTop`, so the junk values of
`Real.log` and of division at `n ≤ 1` are irrelevant to its truth
(`eventually_log_pos_and_sq_pos`).  The constant is existentially quantified
and pinned only by the entry's strict numeric window, so it is not a free
parameter fixed by a hypothesis. -/
theorem exists_tendsto_gapSum_mul_log_div_sq :
    ∃ c : ℝ, 0.006 < c ∧ c < 0.01 ∧
      Filter.Tendsto (fun n : ℕ => (gapSum n : ℝ) * Real.log n / (n : ℝ) ^ 2)
        Filter.atTop (nhds c) := by
  -- intended sorry: open ("it seems") conjecture, card A076142-quasilog-chain-gap
  sorry

-- the constant window of the conjecture is a nonempty interval, so the `∃ c`
-- is not quantified over an empty domain
example : ∃ c : ℝ, 0.006 < c ∧ c < 0.01 := ⟨0.008, by norm_num, by norm_num⟩

/-! ## Axiom audit (sorry-free declarations only) -/

#print axioms factorChain
#print axioms mem_factorChain
#print axioms isAddChain_factorChain
#print axioms head?_factorChain
#print axioms length_factorChain_add_one
#print axioms l_mul_le
#print axioms l_add_one_le
#print axioms l_le_quasilog
#print axioms log_two_le_l_le_quasilog
#print axioms gap
#print axioms gap_eq_sub
#print axioms gap_nonneg
#print axioms gap_23_eq_one
#print axioms gap_33_eq_one
#print axioms l_lt_quasilog_23
#print axioms gapSum
#print axioms gapSum_nonneg
#print axioms one_le_gapSum
#print axioms gapSum_mul_log_div_sq_nonneg
#print axioms eventually_log_pos_and_sq_pos

end NumberComplexity
