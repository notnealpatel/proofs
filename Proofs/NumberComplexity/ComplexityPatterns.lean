/-
  NumberComplexity/ComplexityPatterns — record values of integer
  complexity (OEIS A005520): `a(n)` = the smallest number whose
  Mahler–Popken complexity (A005245, `NumberComplexity.complexity`)
  equals `n`, and the two patterns asserted in the A005520 entry.

    · `exists_le_complexityRec_eq` / `exists_complexityRec_eq` /
      `exists_pos_complexity_eq`
        — discrete intermediate-value property of the norm (it steps
          up by at most one, `‖m+1‖ ≤ ‖m‖ + 1`, and is unbounded,
          `2·m ≤ 2^‖m‖`), hence surjectivity: every `n` is a
          complexity value, so the record `smallestOfComplexity n`
          is well defined via `Nat.find`.
    · `smallestOfComplexity n`
        — A005520: least `m` with `complexityRec m = n` (equivalently
          `complexity m = n` by the master theorem of IntComplexity).
          JUNK VALUE: `smallestOfComplexity 0 = 0` (pinned), inherited
          from `complexity 0 = 0`.
    · order/spec API — `complexityRec_smallestOfComplexity`,
      `smallestOfComplexity_le`, `smallestOfComplexity_eq_iff`,
      `le_smallestOfComplexity` (`n ≤ a(n)`),
      `smallestOfComplexity_le_of_le_complexityRec`,
      `smallestOfComplexity_injective`,
      `smallestOfComplexity_strictMono` (the record sequence is
      strictly increasing),
      `smallestOfComplexity_eq_self_iff` (`a(n) = n ↔ n ≤ 5`).
    · packed table `tblData` / `tbl` (private)
        — kernel-checkable table `‖0‖ … ‖719‖` packed into a single
          natural number, one byte per value; the A005245 recurrence
          is re-derived for every row inside the kernel by four
          `decide +kernel` chunk checks, and
          `smallestOfComplexity_eq_of_tbl` turns one scan into a
          record certificate. No `native_decide` anywhere: the
          trusted base stays the kernel. (A `List ℕ` table is
          infeasible here: `O(N³)` kernel reduction blows a 12 GB
          memory budget at table size ~167.)
    · record certificates — `smallestOfComplexity_one` …
      `smallestOfComplexity_twentyThree`, kernel-checked against the
      live OEIS A005520 data (`oeis show A005520` and b-file
      b005520.txt, pulled 2026-07-30): a(1..23) = 1, 2, 3, 4, 5, 7,
      10, 11, 17, 22, 23, 41, 47, 59, 89, 107, 167, 179, 263, 347,
      467, 683, 719.
    · `smallestOfComplexity_prime` — the certified-range restriction
      of the prime pattern: `a(n)` is prime for `2 ≤ n ≤ 23` outside
      the composite records `a(4) = 4`, `a(7) = 10`, `a(10) = 22`.
    · the two OPEN pattern claims of the entry, stated exactly and
      left as INTENDED, DISCLOSED sorries:
        (i)  after 1438 = 2·719, all terms through 8206559 = a(53)
             are prime (J. V. Post 2006);
        (ii) all known terms a(45) = 590399 … a(89) = 872573642639
             are ≡ −1 (mod 120) (E. Pegg Jr 2001 / A. Karttunen 2015).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib
import NumberComplexity.IntComplexity

set_option autoImplicit false
-- the packed table `tbl` reads bytes via `256 ^ i` for `i < 720`;
-- raise the elaborator's exponent-folding threshold accordingly
-- (GMP-cheap; kernel reduction has no such threshold)
set_option exponentiation.threshold 800

namespace NumberComplexity

/-! ## 1. Every natural number is a complexity value

The A005520 record `a(n)` exists because the complexity norm takes
every value `n`: it starts at `‖1‖ = 1`, moves up by at most `1` at
each step (`‖m+1‖ ≤ ‖m‖ + 1`), and is unbounded (`2·m ≤ 2^‖m‖`).

The growth and step lemmas are `private`: sharp versions belong to the
Hamilton–Ballinger bounds layer (see the sibling file), and only these
weak forms are needed here. -/

/-- Growth of value against cost: every `{1,+,×}`-expression satisfies
`2 · e.eval ≤ 2 ^ e.cost`. (A weak, self-contained form of the upper
half of the Hamilton–Ballinger bounds — private to this file.) -/
private theorem two_mul_eval_le_two_pow_cost (e : Expr) :
    2 * e.eval ≤ 2 ^ e.cost := by
  induction e with
  | one => decide
  | add a b iha ihb =>
      have h2a : 2 ≤ 2 ^ a.cost := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ a.cost := Nat.pow_le_pow_right (by omega) a.one_le_cost
      have h2b : 2 ≤ 2 ^ b.cost := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ b.cost := Nat.pow_le_pow_right (by omega) b.one_le_cost
      have hmul : 2 ^ a.cost + 2 ^ b.cost ≤ 2 ^ a.cost * 2 ^ b.cost :=
        Nat.add_le_mul h2a h2b
      simp only [Expr.eval, Expr.cost]
      rw [pow_add]
      omega
  | mul a b iha ihb =>
      have heb : b.eval ≤ 2 ^ b.cost := by omega
      simp only [Expr.eval, Expr.cost]
      rw [pow_add, ← Nat.mul_assoc]
      exact Nat.mul_le_mul iha heb

/-- The norm grows at least logarithmically: `2 · n ≤ 2 ^ ‖n‖` for
`1 ≤ n` (stated for the computable `complexityRec` via the master
theorem). Private: only unboundedness is needed here. -/
private theorem two_mul_le_two_pow_complexityRec {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ 2 ^ complexityRec n := by
  obtain ⟨e, he, hc⟩ := exists_cost_eq_complexity hn
  have h := two_mul_eval_le_two_pow_cost e
  rw [he, hc, complexity_eq_complexityRec] at h
  exact h

/-- Unboundedness witness: `n < ‖2 ^ n‖`. Private. -/
private theorem lt_complexityRec_two_pow (n : ℕ) :
    n < complexityRec (2 ^ n) := by
  have h := two_mul_le_two_pow_complexityRec
    (n := 2 ^ n) (Nat.one_le_pow n 2 (by omega))
  have h2 : (2 : ℕ) ^ (n + 1) ≤ 2 ^ complexityRec (2 ^ n) := by
    calc (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 ^ complexityRec (2 ^ n) := h
  have h3 : n + 1 ≤ complexityRec (2 ^ n) :=
    (Nat.pow_le_pow_iff_right (by omega)).mp h2
  omega

/-- Step bound: `‖n + 1‖ ≤ ‖n‖ + 1` for `1 ≤ n` (split off one `+1`).
Private: it is a special case of subadditivity. -/
private theorem complexityRec_succ_le {n : ℕ} (hn : 1 ≤ n) :
    complexityRec (n + 1) ≤ complexityRec n + 1 := by
  have h := complexityRec_add_le hn (le_refl 1)
  rw [complexityRec_one] at h
  exact h

/-- Discrete intermediate-value property of the norm: every value
`1 ≤ n ≤ ‖M‖` is attained at or below `M`. Walking `1, 2, …, M` the
norm starts at `‖1‖ = 1` and steps up by at most one
(`complexityRec_succ_le`), so on the way to `‖M‖` it cannot skip `n`.
(The witness is the least `m` with `n ≤ ‖m‖`.) -/
theorem exists_le_complexityRec_eq {M n : ℕ} (hn : 1 ≤ n)
    (hnM : n ≤ complexityRec M) : ∃ m : ℕ, m ≤ M ∧ complexityRec m = n := by
  have hex : ∃ m : ℕ, n ≤ complexityRec m := ⟨M, hnM⟩
  refine ⟨Nat.find hex, Nat.find_le hnM, le_antisymm ?_ (Nat.find_spec hex)⟩
  rcases Nat.lt_or_ge (Nat.find hex) 2 with hlt | hge
  · have h1 : 1 ≤ Nat.find hex := by
      by_contra h0
      have hz : Nat.find hex = 0 := by omega
      have hspec := Nat.find_spec hex
      rw [hz, complexityRec_zero] at hspec
      omega
    have he : Nat.find hex = 1 := by omega
    rw [he, complexityRec_one]
    exact hn
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
    have hmin : ¬ n ≤ complexityRec (k + 1) := Nat.find_min hex (by omega)
    have hstep : complexityRec (k + 2) ≤ complexityRec (k + 1) + 1 :=
      complexityRec_succ_le (by omega)
    rw [hk]
    omega

/-- Surjectivity of the (computable) complexity norm: every `n : ℕ` is
`‖m‖` for some `m` — at `n = 0` by the junk value `‖0‖ = 0`, and for
`1 ≤ n` by the intermediate-value property below the unboundedness
witness `n < ‖2 ^ n‖`. This is the well-definedness of the A005520
record. -/
theorem exists_complexityRec_eq (n : ℕ) : ∃ m : ℕ, complexityRec m = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, rfl⟩
  · obtain ⟨m, _, hm⟩ :=
      exists_le_complexityRec_eq hn (le_of_lt (lt_complexityRec_two_pow n))
    exact ⟨m, hm⟩

/-- Surjectivity onto the positive values, for the noncomputable norm:
for `1 ≤ n` some `1 ≤ m` has `complexity m = n` (the guard `1 ≤ m`
keeps the witness off the junk value `complexity 0 = 0`). -/
theorem exists_pos_complexity_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ complexity m = n := by
  obtain ⟨m, hm⟩ := exists_complexityRec_eq n
  refine ⟨m, ?_, by rw [complexity_eq_complexityRec, hm]⟩
  by_contra h
  have hm0 : m = 0 := by omega
  rw [hm0, complexityRec_zero] at hm
  omega

/-! ## 2. The record sequence A005520 -/

/-- A005520: `smallestOfComplexity n` is the smallest number of
integer complexity `n` — the least `m` with `complexityRec m = n`,
equivalently (master theorem) with `complexity m = n`.

JUNK VALUE: `smallestOfComplexity 0 = 0`, inherited from the junk
value `complexity 0 = 0` of the norm (`smallestOfComplexity_zero`
pins it). The OEIS sequence starts at `n = 1`. -/
def smallestOfComplexity (n : ℕ) : ℕ := Nat.find (exists_complexityRec_eq n)

/-- The record has the complexity it records: `‖a(n)‖ = n` (computable
form). -/
theorem complexityRec_smallestOfComplexity (n : ℕ) :
    complexityRec (smallestOfComplexity n) = n :=
  Nat.find_spec (exists_complexityRec_eq n)

/-- The record has the complexity it records: `complexity (a(n)) = n`. -/
theorem complexity_smallestOfComplexity (n : ℕ) :
    complexity (smallestOfComplexity n) = n := by
  rw [complexity_eq_complexityRec]
  exact complexityRec_smallestOfComplexity n

/-- Minimality, upper-bound direction: any `m` with `‖m‖ = n` bounds
the record, `a(n) ≤ m`. -/
theorem smallestOfComplexity_le {n m : ℕ} (h : complexityRec m = n) :
    smallestOfComplexity n ≤ m := Nat.find_le h

/-- Minimality, lower-bound direction: numbers below the record do not
have complexity `n`. -/
theorem complexityRec_ne_of_lt_smallestOfComplexity {n k : ℕ}
    (h : k < smallestOfComplexity n) : complexityRec k ≠ n :=
  Nat.find_min (exists_complexityRec_eq n) h

/-- Characterization of the record — the `decide` workhorse:
`a(n) = m` iff `‖m‖ = n` and no `k < m` has `‖k‖ = n`. (`Nat.find` is
opaque to kernel reduction, so concrete record values are certified
through this equivalence, never by evaluating `Nat.find`.) -/
theorem smallestOfComplexity_eq_iff {n m : ℕ} :
    smallestOfComplexity n = m ↔
      complexityRec m = n ∧ ∀ k < m, complexityRec k ≠ n :=
  Nat.find_eq_iff (exists_complexityRec_eq n)

/-- JUNK-VALUE PIN: `smallestOfComplexity 0 = 0`, by the junk value
`complexityRec 0 = 0` — convention, not content. -/
theorem smallestOfComplexity_zero : smallestOfComplexity 0 = 0 := by
  rw [smallestOfComplexity_eq_iff]
  exact ⟨complexityRec_zero, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- Records of positive complexity are positive. -/
theorem one_le_smallestOfComplexity {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ smallestOfComplexity n := by
  rcases Nat.eq_zero_or_pos (smallestOfComplexity n) with h0 | h1
  · have h := complexityRec_smallestOfComplexity n
    rw [h0, complexityRec_zero] at h
    omega
  · exact h1

/-- `n ≤ a(n)`: a number of complexity `n` is at least `n`, because
`‖m‖ ≤ m`. (Unguarded: at `n = 0` it reads `0 ≤ 0`.) -/
theorem le_smallestOfComplexity (n : ℕ) : n ≤ smallestOfComplexity n := by
  have h := complexityRec_smallestOfComplexity n
  have hle := complexityRec_le_self (smallestOfComplexity n)
  omega

/-- The record sequence is injective (distinct complexities have
distinct smallest witnesses): `a` is a right inverse of `‖·‖`. -/
theorem smallestOfComplexity_injective :
    Function.Injective smallestOfComplexity := by
  intro n₁ n₂ h
  have h₁ := complexityRec_smallestOfComplexity n₁
  have h₂ := complexityRec_smallestOfComplexity n₂
  rw [← h₁, ← h₂, h]

/-- `a(‖m‖) ≤ m`: the record for the complexity of `m` is at most
`m`. -/
theorem smallestOfComplexity_complexityRec_le (m : ℕ) :
    smallestOfComplexity (complexityRec m) ≤ m :=
  smallestOfComplexity_le rfl

/-- Record minimality against the norm: for `1 ≤ n`, `a(n) ≤ M` as
soon as `n ≤ ‖M‖` — by the intermediate-value property a witness of
complexity exactly `n` already sits at or below `M`. -/
theorem smallestOfComplexity_le_of_le_complexityRec {M n : ℕ} (hn : 1 ≤ n)
    (h : n ≤ complexityRec M) : smallestOfComplexity n ≤ M := by
  obtain ⟨m, hmM, hm⟩ := exists_le_complexityRec_eq hn h
  exact le_trans (smallestOfComplexity_le hm) hmM

/-- The record sequence A005520 is strictly increasing (so listing it
by complexity, as the OEIS does, lists it in increasing order). For
`0 < n₁ < n₂` the intermediate-value property places a witness of
complexity `n₁` at or below `a(n₂)`, and that witness is not `a(n₂)`
itself since `‖a(n₂)‖ = n₂ ≠ n₁`; the base case `a(0) = 0 < a(n₂)` is
the junk pin plus positivity of records. -/
theorem smallestOfComplexity_strictMono : StrictMono smallestOfComplexity := by
  intro n₁ n₂ hlt
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn₁
  · rw [smallestOfComplexity_zero]
    exact one_le_smallestOfComplexity (by omega)
  · have h2 := complexityRec_smallestOfComplexity n₂
    obtain ⟨m, hmM, hm⟩ :=
      exists_le_complexityRec_eq (M := smallestOfComplexity n₂) hn₁ (by omega)
    have hne : m ≠ smallestOfComplexity n₂ := by
      intro he
      rw [he, h2] at hm
      omega
    exact lt_of_le_of_lt (smallestOfComplexity_le hm) (lt_of_le_of_ne hmM hne)

/-! ## 3. A kernel-checkable table of complexity values

`complexityRec` recomputes subvalues exponentially often, so kernel
`decide` cannot reach record values beyond ~23 through it, and a
memoized `List ℕ` table is no better: `getD` lookups cost `O(i)`
kernel steps, the recurrence check costs `O(N³)`, and at `N = 167`
that already exceeds a 12 GB memory budget (measured).

The table below is instead packed into a single natural number
`tblData` = `Σ_i ‖i‖ · 256^i` (one byte per value; `‖i‖ ≤ 23 < 256`
on the range). A lookup `tbl i = tblData / 256^i % 256` costs `O(1)`
GMP-accelerated kernel operations, so checking the full A005245
recurrence against `tbl` over all rows `i < 720` is cheap. The check
is split into four row ranges (`tblOk_chunk0`–`tblOk_chunk3`) to
bound the kernel's per-declaration memory; `tbl_eq_complexityRec`
then proves the table correct against `complexityRec` by strong
induction, and `smallestOfComplexity_eq_of_tbl` converts one scan
(`noneBelow`) plus one lookup into a record certificate.

The literal `tblData` needs no external trust: the chunk theorems
re-derive every byte from the recurrence inside the kernel. TRUST
NOTE: the chunk theorems use `decide +kernel` — checked by direct
kernel reduction, skipping the elaborator's slower duplicate
evaluation; the trusted base is unchanged (no `native_decide`
anywhere). All `private`: downstream users should use the
certificates, not the table. -/

/-- The packed table: byte `i` (base 256) is `‖i‖` for `i < 720`, as
certified against the A005245 recurrence by `tblOk_chunk0`–`3` and
`tbl_eq_complexityRec`. Generated from the recurrence and
cross-checked against the OEIS A005245 b-file (pulled 2026-07-30). -/
private def tblData : ℕ := 77248245877566447747355580917438836639432741300811594162281645065299698660707358750222912309260157300445630256101551935515580740608122828177750378776703934947068711200326571282043798497165761248084192258447696657131790768058977569092481019028089491740888040528587688985031594310277590665712847210236351579210654059049095405841443801904587044061099624927486569772376028056987821787286522878612241205906829125207101342355565190836036676376286787603092534289778807452877824749293971629328633430376787956369800841433386137076969706320150331374039095066249904088238955812677386293096145147674660486024713699520603824910953281865095206263952827056960771599132222531201875097917173635442161291570877091840991109550813026052142239544806242262834770706713937146323787440870265157756669722126006696937299731394750153336101962556267651821600189901713623954558238005825158983183000982641351518865200523920357780641915952641021643998705031513722822399910130767970298412802988898520961840062059121106640123658659552734217541099391287038854362194076292428594923686008186041834153582658497881972500247879480578445831668706467230279576292810036963828296172852190340773696082307685310702133186480682110682235498925215273340361068589943061101832111789422186375479788411510578235815546219282182173490396757952156486851618147468173427659865480562262861710915365574865824829376266793409429096257249681856251573985358313027994192737734937779937304158835118794232815910550110824695159836363346261149487667895936158215694026627809864952118276067452217512203037327752641645998763248271209440094453862260371612114867475084983752375013800664960570789838849318573180793082710321316199282190362090893641357100897176559539601633918157671121913326678765925986074880

/-- Table lookup: byte `i` of `tblData`. Values beyond the packed
range are the junk value `0` (harmless: every use is guarded by
`i < 720`). -/
private def tbl (i : ℕ) : ℕ := tblData / 256 ^ i % 256

-- ground checks for the lookup, against A005245 values and the junk
-- value out of range
example : tbl 0 = 0 := by decide
example : tbl 1 = 1 := by decide
example : tbl 6 = 5 := by decide
example : tbl 11 = 8 := by decide
example : tbl 12 = 7 := by decide
set_option maxRecDepth 8192 in
example : tbl 719 = 23 := by decide
set_option maxRecDepth 8192 in
example : tbl 720 = 0 := by decide   -- out-of-range junk

/-- Row `i` of the A005245 recurrence, checked against the packed
table with `tbl` itself as the oracle for smaller indices. -/
private def tblRule (i : ℕ) : Bool :=
  tbl i == if i = 0 then 0 else if i = 1 then 1 else minSplit tbl i (i / 2)

/-- Conjunction of `tblRule` over the row range `[lo, lo + len)`. -/
private def tblRuleRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => tblRuleRange lo len && tblRule (lo + len)

/-- `noneBelow n m = true` iff no table entry below index `m` equals
`n` — the minimality scan of a record certificate. -/
private def noneBelow (n : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => noneBelow n k && !(tbl k == n)

-- Ground checks for the three predicates (vacuity audit), positive AND
-- negative for each — the negatives prove none of them is constantly
-- `true`; in particular `tblRule 720 = false` shows the recurrence test
-- discriminates and that the packed table genuinely ends at row 719.
example : tblRule 5 = true := by decide
set_option maxRecDepth 8192 in
example : tblRule 719 = true := by decide +kernel
set_option maxRecDepth 8192 in
example : tblRule 720 = false := by decide +kernel
set_option maxRecDepth 8192 in
example : tblRuleRange 717 3 = true := by decide
set_option maxRecDepth 8192 in
example : tblRuleRange 718 3 = false := by decide
set_option maxRecDepth 8192 in
example : noneBelow 23 719 = true := by decide
set_option maxRecDepth 8192 in
example : noneBelow 23 720 = false := by decide
example : noneBelow 5 5 = true := by decide
example : noneBelow 5 6 = false := by decide

/-- Extraction: a true `tblRuleRange` check yields `tblRule i` for
every row in its range. -/
private theorem tblRule_of_tblRuleRange {lo len : ℕ}
    (h : tblRuleRange lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → tblRule i = true := by
  induction len with
  | zero =>
      intro i h1 h2
      omega
  | succ len ih =>
      intro i h1 h2
      simp only [tblRuleRange, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge i (lo + len) with hlt | hge
      · exact ih h.1 i h1 hlt
      · have hie : i = lo + len := by omega
        rw [hie]
        exact h.2

/-- Extraction: a true `noneBelow` scan means no entry below `m` is
`n`. -/
private theorem tbl_ne_of_noneBelow {n : ℕ} :
    ∀ {m : ℕ}, noneBelow n m = true → ∀ k, k < m → tbl k ≠ n := by
  intro m
  induction m with
  | zero =>
      intro _ k hk
      omega
  | succ m ih =>
      intro h k hk
      simp only [noneBelow, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at h
      rcases Nat.lt_or_ge k m with hlt | hge
      · exact ih h.1 k hlt
      · have hke : k = m := by omega
        rw [hke]
        exact h.2

/-- Rows `0..179` of the recurrence check. TRUST NOTE: `decide
+kernel` (kernel reduction only; trusted base unchanged). -/
private theorem tblOk_chunk0 : tblRuleRange 0 180 = true := by decide +kernel

/-- Rows `180..359` of the recurrence check (kernel reduction). -/
private theorem tblOk_chunk1 : tblRuleRange 180 180 = true := by decide +kernel

/-- Rows `360..539` of the recurrence check (kernel reduction). -/
private theorem tblOk_chunk2 : tblRuleRange 360 180 = true := by decide +kernel

/-- Rows `540..719` of the recurrence check (kernel reduction). -/
private theorem tblOk_chunk3 : tblRuleRange 540 180 = true := by decide +kernel

/-- Every row `i < 720` of the packed table satisfies the A005245
recurrence (the four chunk checks glued together). -/
private theorem tblRule_all : ∀ i, i < 720 → tblRule i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 180 with h0 | h0
  · exact tblRule_of_tblRuleRange tblOk_chunk0 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 360 with h1 | h1
  · exact tblRule_of_tblRuleRange tblOk_chunk1 i h0 (by omega)
  rcases Nat.lt_or_ge i 540 with h2 | h2
  · exact tblRule_of_tblRuleRange tblOk_chunk2 i h1 (by omega)
  · exact tblRule_of_tblRuleRange tblOk_chunk3 i h2 (by omega)

/-- Correctness of the packed table: `tbl i = ‖i‖` for `i < 720`, by
strong induction along the recurrence (`minSplit_congr` swaps the
`tbl` oracle for `complexityRec` below `i`). -/
private theorem tbl_eq_complexityRec : ∀ i, i < 720 → tbl i = complexityRec i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hrule := tblRule_all i hi
    simp only [tblRule, beq_iff_eq] at hrule
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · rw [if_pos rfl] at hrule
        rw [hrule, complexityRec_zero]
      · rw [if_neg (by omega), if_pos rfl] at hrule
        rw [hrule, complexityRec_one]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
      rw [if_neg (by omega), if_neg (by omega)] at hrule
      have hcongr : minSplit tbl (m + 2) ((m + 2) / 2)
          = minSplit complexityRec (m + 2) ((m + 2) / 2) :=
        minSplit_congr (fun j hj => ih j hj (by omega)) (by omega)
      rw [hrule, hcongr, ← complexityRec_eq_minSplit (by omega)]

/-- CERTIFICATE EXTRACTOR: if the scan below `m < 720` finds no entry
`n` and entry `m` is `n`, then `smallestOfComplexity n = m`.
(`Nat.find` is opaque to kernel reduction, so concrete record values
are certified through `smallestOfComplexity_eq_iff` and the table,
never by evaluating `Nat.find`.) -/
private theorem smallestOfComplexity_eq_of_tbl {n m : ℕ} (hm : m < 720)
    (hnone : noneBelow n m = true) (hval : tbl m = n) :
    smallestOfComplexity n = m := by
  rw [smallestOfComplexity_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [← tbl_eq_complexityRec m hm]
    exact hval
  · intro k hk
    rw [← tbl_eq_complexityRec k (by omega)]
    exact tbl_ne_of_noneBelow hnone k hk

/-! ## 4. Record certificates

GROUND TRUTH (`oeis show A005520` and b-file `b005520.txt`, both
pulled live 2026-07-30): a(1..23) = 1, 2, 3, 4, 5, 7, 10, 11, 17,
22, 23, 41, 47, 59, 89, 107, 167, 179, 263, 347, 467, 683, 719.
Every certificate below is a kernel-checked scan of the packed table
— no `native_decide`, the trusted base stays the kernel.
(`maxRecDepth`: the scan recursion nests with depth ~m in the
elaborator; the kernel re-checks either way.) -/

/-- A005520(1) = 1. -/
theorem smallestOfComplexity_one : smallestOfComplexity 1 = 1 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(2) = 2. -/
theorem smallestOfComplexity_two : smallestOfComplexity 2 = 2 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(3) = 3. -/
theorem smallestOfComplexity_three : smallestOfComplexity 3 = 3 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(4) = 4. -/
theorem smallestOfComplexity_four : smallestOfComplexity 4 = 4 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(5) = 5. -/
theorem smallestOfComplexity_five : smallestOfComplexity 5 = 5 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(6) = 7: the first record exceeding its index (‖6‖ = 5
already, so no number of complexity 6 exists below 7). -/
theorem smallestOfComplexity_six : smallestOfComplexity 6 = 7 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(7) = 10 — composite, one of the four known composite
records. -/
theorem smallestOfComplexity_seven : smallestOfComplexity 7 = 10 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(8) = 11. -/
theorem smallestOfComplexity_eight : smallestOfComplexity 8 = 11 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(9) = 17. -/
theorem smallestOfComplexity_nine : smallestOfComplexity 9 = 17 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(10) = 22 — composite, one of the four known composite
records. -/
theorem smallestOfComplexity_ten : smallestOfComplexity 10 = 22 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(11) = 23. -/
theorem smallestOfComplexity_eleven : smallestOfComplexity 11 = 23 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(12) = 41. -/
theorem smallestOfComplexity_twelve : smallestOfComplexity 12 = 41 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(13) = 47. -/
theorem smallestOfComplexity_thirteen : smallestOfComplexity 13 = 47 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(14) = 59. -/
theorem smallestOfComplexity_fourteen : smallestOfComplexity 14 = 59 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(15) = 89. -/
theorem smallestOfComplexity_fifteen : smallestOfComplexity 15 = 89 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-- A005520(16) = 107. -/
theorem smallestOfComplexity_sixteen : smallestOfComplexity 16 = 107 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(17) = 167. -/
theorem smallestOfComplexity_seventeen : smallestOfComplexity 17 = 167 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(18) = 179. -/
theorem smallestOfComplexity_eighteen : smallestOfComplexity 18 = 179 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(19) = 263. -/
theorem smallestOfComplexity_nineteen : smallestOfComplexity 19 = 263 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(20) = 347. -/
theorem smallestOfComplexity_twenty : smallestOfComplexity 20 = 347 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(21) = 467. -/
theorem smallestOfComplexity_twentyOne : smallestOfComplexity 21 = 467 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(22) = 683. -/
theorem smallestOfComplexity_twentyTwo : smallestOfComplexity 22 = 683 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- A005520(23) = 719 — the last record CERTIFIED here (the table ends at
row 719; a(24) = 1223, prime, and the composite record 1438 = 2 · 719
that opens the prime window of claim (i) both lie beyond it); itself
≡ −1 (mod 120), an early sporadic instance of the Pegg pattern of
claim (ii). -/
theorem smallestOfComplexity_twentyThree : smallestOfComplexity 23 = 719 :=
  smallestOfComplexity_eq_of_tbl (by omega) (by decide) (by decide)

/-! ## 5. Structural patterns over the certified range -/

/-- For `6 ≤ n` the norm drops strictly below `n` (`‖6‖ = 5` and the
step bound). Private: a sharp version belongs to the bounds layer. -/
private theorem complexityRec_lt_self {n : ℕ} (hn : 6 ≤ n) :
    complexityRec n < n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have hstep := complexityRec_succ_le (n := n) (by omega)
      omega

/-- The record equals its index exactly on the initial segment:
`a(n) = n ↔ n ≤ 5` (for `1 ≤ n`; the degenerate `a(0) = 0` is junk).
Forward: `‖n‖ < n` for `6 ≤ n`. Backward: the certified records
a(1)..a(5). -/
theorem smallestOfComplexity_eq_self_iff {n : ℕ} (hn : 1 ≤ n) :
    smallestOfComplexity n = n ↔ n ≤ 5 := by
  constructor
  · intro h
    by_contra hgt
    have h6 : 6 ≤ n := by omega
    have hv := complexityRec_smallestOfComplexity n
    rw [h] at hv
    have hlt := complexityRec_lt_self h6
    omega
  · intro h5
    interval_cases n
    · exact smallestOfComplexity_one
    · exact smallestOfComplexity_two
    · exact smallestOfComplexity_three
    · exact smallestOfComplexity_four
    · exact smallestOfComplexity_five

/-- Prime pattern over the kernel-certified range: except for
`a(4) = 4`, `a(7) = 10`, and `a(10) = 22`, every certified record
`a(2), …, a(23)` is prime — the restriction to the certified range of
the Post 2006 comment on A005520 ("except for a(4) = 4, a(7) = 10,
a(10) = 22 and a(25) = 1438, we have a(1) through a(53) are all
primes"; the comment's inclusion of the unit `a(1) = 1` among the
primes is corrected here by the guard `2 ≤ n`). -/
theorem smallestOfComplexity_prime {n : ℕ} (h2 : 2 ≤ n) (h23 : n ≤ 23)
    (h4 : n ≠ 4) (h7 : n ≠ 7) (h10 : n ≠ 10) :
    Nat.Prime (smallestOfComplexity n) := by
  rcases (show n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9 ∨ n = 11 ∨
      n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨
      n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [smallestOfComplexity_two]; norm_num
  · rw [smallestOfComplexity_three]; norm_num
  · rw [smallestOfComplexity_five]; norm_num
  · rw [smallestOfComplexity_six]; norm_num
  · rw [smallestOfComplexity_eight]; norm_num
  · rw [smallestOfComplexity_nine]; norm_num
  · rw [smallestOfComplexity_eleven]; norm_num
  · rw [smallestOfComplexity_twelve]; norm_num
  · rw [smallestOfComplexity_thirteen]; norm_num
  · rw [smallestOfComplexity_fourteen]; norm_num
  · rw [smallestOfComplexity_fifteen]; norm_num
  · rw [smallestOfComplexity_sixteen]; norm_num
  · rw [smallestOfComplexity_seventeen]; norm_num
  · rw [smallestOfComplexity_eighteen]; norm_num
  · rw [smallestOfComplexity_nineteen]; norm_num
  · rw [smallestOfComplexity_twenty]; norm_num
  · rw [smallestOfComplexity_twentyOne]; norm_num
  · rw [smallestOfComplexity_twentyTwo]; norm_num
  · rw [smallestOfComplexity_twentyThree]; norm_num

/-- Certified early instance of the Pegg residue pattern (card claim
(ii) concerns `a(45)` onward; sporadic earlier terms already satisfy
it): `a(23) = 719 ≡ −1 (mod 120)`. -/
theorem smallestOfComplexity_twentyThree_mod_120 :
    smallestOfComplexity 23 % 120 = 119 := by
  rw [smallestOfComplexity_twentyThree]

/-! ## 6. The open pattern claims of the A005520 entry

Both claims below are the card's claims (i) and (ii), stated exactly
as the OEIS entry asserts them. Each is a FINITE, decidable-in-
principle statement about record values that have been computed in
the literature (Pegg 2001, Post 2006, Iraids 2011 b-file) but lie far
beyond kernel `decide` reach (the window of claim (i) starts at
a(26) = 1439 and runs to a(53) = 8206559; claim (ii) runs to
a(89) = 872573642639). No structural explanation is known for either
pattern. The `sorry`s are INTENDED and disclosed; they are the open
content of the card. -/

/-- OPEN — card claim (i), OEIS A005520 (J. V. Post, Apr 07 2006):
"After 1438 = 2·719, all elements through 8206559 are primes." Every
record value in the window `(1438, 8206559]` is prime. Per the
b-file (pulled 2026-07-30) the terms in this window are
a(26) = 1439 … a(53) = 8206559, so the hypotheses are jointly
satisfiable (at `n = 26`, per data — itself beyond kernel reach).
The claim is finite: `n ≤ a(n)` (`le_smallestOfComplexity`) bounds
the indices concerned by `n ≤ 8206559`. -/
theorem smallestOfComplexity_prime_of_1438_lt {n : ℕ}
    (h1 : 1438 < smallestOfComplexity n)
    (h2 : smallestOfComplexity n ≤ 8206559) :
    Nat.Prime (smallestOfComplexity n) := by
  sorry

/-- OPEN — card claim (ii), OEIS A005520 (E. Pegg Jr, Apr 10 2001;
range clarified by A. Karttunen, Dec 14 2015): all known terms
a(45) = 590399 through a(89) = 872573642639 are ≡ −1 (mod 120).
The index domain `45 ≤ n ≤ 89` is nonempty, and the pattern genuinely
starts at 45: a(44) = 540539 ≡ 59 (mod 120) per the b-file (pulled
2026-07-30). -/
theorem smallestOfComplexity_mod_120 {n : ℕ} (h45 : 45 ≤ n) (h89 : n ≤ 89) :
    smallestOfComplexity n % 120 = 119 := by
  sorry

/-! ## Satisfiability of the guarded statements

Every hypothesis-bearing, sorry-free theorem above is instantiated
jointly at a concrete model. -/

example : ∃ m : ℕ, m ≤ 7 ∧ complexityRec m = 3 :=
  exists_le_complexityRec_eq (by omega) (by decide)
example : ∃ m : ℕ, 1 ≤ m ∧ complexity m = 3 := exists_pos_complexity_eq (by omega)
example : 1 ≤ smallestOfComplexity 6 := one_le_smallestOfComplexity (by omega)
example : smallestOfComplexity 6 ≤ 7 :=
  smallestOfComplexity_le (n := 6) (m := 7) (by decide)
example : smallestOfComplexity 6 ≤ 7 :=
  smallestOfComplexity_le_of_le_complexityRec (by omega) (by decide)
example : smallestOfComplexity 3 < smallestOfComplexity 7 :=
  smallestOfComplexity_strictMono (by omega)
example : complexityRec 5 ≠ 6 :=
  complexityRec_ne_of_lt_smallestOfComplexity (n := 6) (k := 5)
    (by rw [smallestOfComplexity_six]; omega)
example : smallestOfComplexity 5 = 5 ↔ 5 ≤ 5 :=
  smallestOfComplexity_eq_self_iff (by omega)
example : ¬ smallestOfComplexity 6 = 6 := by
  have h := (smallestOfComplexity_eq_self_iff (n := 6) (by omega))
  omega
example : smallestOfComplexity 8 ≠ smallestOfComplexity 3 := by
  intro h
  have h83 : (8 : ℕ) = 3 := smallestOfComplexity_injective h
  omega
example : Nat.Prime (smallestOfComplexity 23) :=
  smallestOfComplexity_prime (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-! ## Axiom audit (sorry-free declarations only)

Expected: every entry reports a subset of
`{propext, Classical.choice, Quot.sound}`. The sweep covers every
sorry-free declaration of this file, `private` helpers and `def`s
included. The two OPEN claims `smallestOfComplexity_prime_of_1438_lt`
and `smallestOfComplexity_mod_120` are intentionally `sorry`ed (card
status: open) and are excluded from the audit. -/

#print axioms two_mul_eval_le_two_pow_cost
#print axioms two_mul_le_two_pow_complexityRec
#print axioms lt_complexityRec_two_pow
#print axioms complexityRec_succ_le
#print axioms exists_le_complexityRec_eq
#print axioms exists_complexityRec_eq
#print axioms exists_pos_complexity_eq
#print axioms smallestOfComplexity
#print axioms complexityRec_smallestOfComplexity
#print axioms complexity_smallestOfComplexity
#print axioms smallestOfComplexity_le
#print axioms complexityRec_ne_of_lt_smallestOfComplexity
#print axioms smallestOfComplexity_eq_iff
#print axioms smallestOfComplexity_zero
#print axioms one_le_smallestOfComplexity
#print axioms le_smallestOfComplexity
#print axioms smallestOfComplexity_injective
#print axioms smallestOfComplexity_complexityRec_le
#print axioms smallestOfComplexity_le_of_le_complexityRec
#print axioms smallestOfComplexity_strictMono
#print axioms tblData
#print axioms tbl
#print axioms tblRule
#print axioms tblRuleRange
#print axioms noneBelow
#print axioms tblRule_of_tblRuleRange
#print axioms tbl_ne_of_noneBelow
#print axioms tblOk_chunk0
#print axioms tblOk_chunk1
#print axioms tblOk_chunk2
#print axioms tblOk_chunk3
#print axioms tblRule_all
#print axioms tbl_eq_complexityRec
#print axioms smallestOfComplexity_eq_of_tbl
#print axioms smallestOfComplexity_one
#print axioms smallestOfComplexity_two
#print axioms smallestOfComplexity_three
#print axioms smallestOfComplexity_four
#print axioms smallestOfComplexity_five
#print axioms smallestOfComplexity_six
#print axioms smallestOfComplexity_seven
#print axioms smallestOfComplexity_eight
#print axioms smallestOfComplexity_nine
#print axioms smallestOfComplexity_ten
#print axioms smallestOfComplexity_eleven
#print axioms smallestOfComplexity_twelve
#print axioms smallestOfComplexity_thirteen
#print axioms smallestOfComplexity_fourteen
#print axioms smallestOfComplexity_fifteen
#print axioms smallestOfComplexity_sixteen
#print axioms smallestOfComplexity_seventeen
#print axioms smallestOfComplexity_eighteen
#print axioms smallestOfComplexity_nineteen
#print axioms smallestOfComplexity_twenty
#print axioms smallestOfComplexity_twentyOne
#print axioms smallestOfComplexity_twentyTwo
#print axioms smallestOfComplexity_twentyThree
#print axioms complexityRec_lt_self
#print axioms smallestOfComplexity_eq_self_iff
#print axioms smallestOfComplexity_prime
#print axioms smallestOfComplexity_twentyThree_mod_120

end NumberComplexity
