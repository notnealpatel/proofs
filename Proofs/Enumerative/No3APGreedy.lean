import Enumerative.StanleyDigits

/-!
# OEIS A092482: the greedy 3-AP-free sequence seeded by `1, 2, 3`

**OEIS A092482**, "Sequence contains no 3-term arithmetic progression, other than its
initial terms 1, 2, 3."  Pinned verbatim from `goof oeis show A092482` (2026-08-05).

*Definition* (OEIS comment, verbatim):

> a(1)=1, a(2)=2, a(3)=3; a(n) is least k such that no three terms of a(1), a(2), ...,
> a(n-1), k form an arithmetic progression, except for the first triple (1,2,3).

*Data* (OEIS `terms`, verbatim):

> 1,2,3,6,7,14,15,17,18,36,37,39,40,45,46,48,49,98,99,101,102,107,108,110,111,125,126,
> 128,129,134,135,137,138,276,277,279,280,285,286,288,289,303,304,306,307,312,313,315,
> 316,357,358,360,361,366,367,369,370

*Formula* (OEIS `formulas`, verbatim):

> For n > 2, a(n+2) = 1 + 2^floor(log_2(n)) + Sum_{k=1..n} (3^A007814(n) + 1)/2 =
1 + A053644(n) + A005836(n) (conjectured and checked up to n=512).

*Mathematica* (OEIS `programs`, verbatim, the unambiguous rendering of the formula):

> (* Comparing with data from conjectured formula: *)
> b[n_] := If[n < 4, n, 1 + 2^(Length[id = IntegerDigits[n - 2, 2]] - 1) +
>   FromDigits[id, 3]];
> Table[b[n], {n, 1, 512}] (* _Jean-François Alcover_, Jan 15 2019 *)

**This file proves that formula** — it is no longer a conjecture.  The main theorem is
`greedySeq_eq_closedForm`: the greedy sequence `greedySeq`, defined from the OEIS rule
via `Nat.find`, equals `closedForm`.  Everything here is 0-indexed, so
`greedySeq n = A092482(n+1)` and the formula reads
`greedySeq (m + 2) = 1 + 2 ^ ⌊log₂ (m+1)⌋ + binToTernary (m+1)` (`greedySeq_add_two`),
where `binToTernary` — the base-2 expansion of `j` read in base 3, i.e. A005836 at
offset `0` — is imported from `Proofs/Enumerative/StanleyDigits.lean`.

Two textual notes on the pinned formula, neither affecting the statement proved here:

* `Sum_{k=1..n} (3^A007814(n) + 1)/2` has a typo in the OEIS entry: the summand index
  must be `k`, not `n`.  Read literally the sum is `n·(3^A007814(n)+1)/2`, which at
  `n = 3` gives `3` and hence `a(5) = 1 + 2 + 3 = 6`, whereas the `terms` field has
  `a(5) = 7`.  With `k` the sum is `binToTernary n`; we prove that reading as a theorem
  (`two_mul_binToTernary_eq_sum`, stated division-free by doubling), alongside the
  `A053644`/`A005836` form (`greedySeq_add_two`).
* `A053644(n)` and `A005836(n)` must be read as *0-indexed* lookups into the printed
  term lists (`A053644 = 0,1,2,2,4,4,4,4,8,…` so `A053644(n) = 2^⌊log₂ n⌋`;
  `A005836 = 0,1,3,4,9,10,12,13,27,…` so `A005836(n) = binToTernary n`).  Reading
  `A005836` 1-indexed (its declared OEIS offset) gives `A005836(3) = 3` and hence
  `a(5) = 1 + 2 + 3 = 6 ≠ 7`; reading `A053644` 1-indexed gives `A053644(4) = 2` and
  hence `a(6) = 1 + 2 + 9 = 12 ≠ 14`.

## Structure of the proof

Write `V` for the set of terms.  With `C L = 2^L + 3^L + 1` and `T L = A005836 ∩ [0,3^L)`,

  `V = {1, 2} ∪ ⋃_{L ≥ 0} (C L + T L)`,

i.e. `V` is a disjoint union of *blocks*, the `L`-th being a translate of the first `2^L`
terms of the Stanley sequence A003278.  The key identity is

  `2 · max (block L) = C (L+1)`   (`two_mul_le_blockStart_succ` is its inequality form),

a squeeze, not a coincidence: a reflection `2y - x` off terms `x < y ≤ max` reaches at
most `2 · max - 1`, so `2 · max` is always a legal extension and the greedy jump cannot
pass it; `q_covering` blocks everything strictly between, so it cannot stop short.  The
jump out of block `L` therefore lands exactly on the first integer that *cannot* be
blocked.  Three ingredients:

* `noThreeAPExceptSeed_Vset` — `V` carries no 3-term AP other than `(1,2,3)`.  An AP
  forces all three terms into one block, where 3-AP-freeness is the A003278 statement.
* `exists_blocking` — every integer `> 2` outside `V` completes an AP with two smaller
  members of `V`.  Inside the span `[C L, C L + 3 ^ L)` (any offset with a ternary digit
  `2`, including those above the top term) this is the classical `keepOnes`/`capDigits`
  witness pair; across the addressless gap `[C L + 3 ^ L, C (L+1))` it is `q_covering`,
  an induction whose four cases exactly tile the gap.
* the greedy scaffolding, `Nat.find` over `IsGoodStep`, as in `StanleyDigits.lean`.

The seed is *derived*, not assumed: the greedy recursion here starts from `{1}` and the
`(1,2,3)` exemption forces `1, 2, 3` (`prefixSet_two`), so this formalization agrees with
the OEIS definition, which stipulates `a(1)=1, a(2)=2, a(3)=3`.

## Provenance (literature sweep 2026-08-05)

The OEIS entry labels the formula "conjectured and checked up to n=512"
(Jean-François Alcover, Jan 15 2019).  We found no published proof.  The companion array
**A093682** collects greedy 3-AP-free sequences with conjectured closed forms and states
verbatim, in its comments:

> The nonarithmetic-3-progression sequences starting with a(1)=1, a(2)=1+3^m or 1+2*3^m,
> m >= 0, seem to have especially simple 'closed' forms. None of these formulas have been
> proved, however.

A092482 is **not** a row of that array: A093682's rows are seeded `1, 1+3^m` or
`1, 1+2·3^m` (rows 0–6 are A003278, A004793, A033157, A093678–A093681 per its `xrefs`),
and its conjectured closed forms have a *P-periodic* correction term
(`T(m, n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with f(n) a P-periodic
function`), whereas the correction here, `2^floor(log_2 n)`, is unbounded.  A093682 cross-references
A092482 under `Cf.` (A092482 does not reference A093682).

A092482 is also **not** a Stanley sequence in the sense of Odlyzko–Stanley (*Some curious
sequences constructed with the greedy algorithm*, Bell Labs memorandum, 1978) or
Erdős–Lev–Rauzy–Sándor–Sárközy (*Greedy algorithm, arithmetic progressions, subset sums
and divisibility*, Discrete Math. 200 (1999) 119–135): a Stanley sequence `S(A)` requires
its seed `A` to be 3-AP-free, and `{1,2,3}` is not (`not_threeAPFree_seed`).  For the same
reason the classification machinery of D. Rolnick, *On the classification of Stanley
sequences* (European J. Combin. 59 (2017) 51–70) and R. A. Moy–D. Rolnick, *Novel
structures in Stanley sequences* (Discrete Math. 339 (2016) 689–698) does not apply: a
"regular"/Type-1 Stanley sequence has a *constant* character, whereas the correction term
here doubles at every power of two.

The proof below is, as far as we can determine, the first proof of this closed form; we
make no claim of deep novelty — the mechanism is the standard base-2/base-3 greedy
argument of A003278, applied blockwise.
-/

set_option autoImplicit false

namespace A092482

/-! ## Extra arithmetic of `binToTernary`

`binToTernary` (from `Proofs/Enumerative/StanleyDigits.lean`) reads the base-2 expansion
of `n` as a base-3 expansion; its range is A005836.  We need how it interacts with the
leading binary digit. -/

/-- `binToTernary` sends `2 ^ L` to `3 ^ L`: a leading binary `1` becomes a leading
ternary `1`. -/
theorem binToTernary_pow_two (L : ℕ) : binToTernary (2 ^ L) = 3 ^ L := by
  induction L with
  | zero => simpa using binToTernary_one
  | succ L ih =>
    have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    rw [h2, binToTernary_two_mul, ih]
    ring

/-- Splitting off the leading binary digit: for `r < 2 ^ L` the value of `2 ^ L + r`
is `3 ^ L` plus the value of `r`. -/
theorem binToTernary_add_pow_two :
    ∀ L r : ℕ, r < 2 ^ L → binToTernary (2 ^ L + r) = 3 ^ L + binToTernary r := by
  intro L
  induction L with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simpa [binToTernary_zero] using binToTernary_one
  | succ L ih =>
    intro r hr
    obtain ⟨r', b, hb, hreq, hTr⟩ := binToTernary_bit r
    have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have h3 : (3 : ℕ) ^ (L + 1) = 3 * 3 ^ L := by ring
    have hr' : r' < 2 ^ L := by omega
    have hstep := ih r' hr'
    have hkey : 2 ^ (L + 1) + r = 2 * (2 ^ L + r') + b := by omega
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rw [hkey, Nat.add_zero, binToTernary_two_mul, hstep]
      omega
    · rw [hkey, binToTernary_two_mul_add_one, hstep]
      omega

/-- Doubling bound: base-3 digits in `{0,1}` below `3 ^ L` double to digits in `{0,2}`,
still below `3 ^ L`.  Equivalently `binToTernary r ≤ (3^L - 1)/2` for `r < 2 ^ L`. -/
theorem two_mul_binToTernary_lt :
    ∀ L r : ℕ, r < 2 ^ L → 2 * binToTernary r < 3 ^ L := by
  intro L
  induction L with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simpa using binToTernary_zero
  | succ L ih =>
    intro r hr
    obtain ⟨r', b, hb, hreq, hTr⟩ := binToTernary_bit r
    have h3 : (3 : ℕ) ^ (L + 1) = 3 * 3 ^ L := by ring
    have hr' : r' < 2 ^ L := by omega
    have hstep := ih r' hr'
    omega

/-- `binToTernary r < 3 ^ L` exactly when `r < 2 ^ L`. -/
theorem binToTernary_lt_pow_iff (L r : ℕ) : binToTernary r < 3 ^ L ↔ r < 2 ^ L := by
  rw [← binToTernary_pow_two L]
  exact binToTernary_strictMono.lt_iff_lt

/-! ## Blocks

`blockStart L = 2 ^ L + 3 ^ L + 1` and `Tset L` is `A005836 ∩ [0, 3 ^ L)`; the `L`-th
block of the sequence is `blockStart L + Tset L`. -/

/-- First term of the `L`-th block: `3, 6, 14, 36, 98, 276, …`. -/
def blockStart (L : ℕ) : ℕ := 2 ^ L + 3 ^ L + 1

/-- The base-3-digits-in-`{0,1}` numbers below `3 ^ L` (the first `2 ^ L` terms of
A005836); the `L`-th block of A092482 is `blockStart L + Tset L`. -/
def Tset (L : ℕ) : Set ℕ := {t | t ∈ Set.range binToTernary ∧ t < 3 ^ L}

/-- `Tset` in terms of an index: `t ∈ Tset L` iff `t = binToTernary r` for some
`r < 2 ^ L`. -/
theorem mem_Tset_iff {L t : ℕ} : t ∈ Tset L ↔ ∃ r, r < 2 ^ L ∧ binToTernary r = t := by
  constructor
  · rintro ⟨⟨r, rfl⟩, hlt⟩
    exact ⟨r, (binToTernary_lt_pow_iff L r).mp hlt, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, rfl⟩, (binToTernary_lt_pow_iff L r).mpr hr⟩

/-- Blocks nest: `Tset L ⊆ Tset (L+1)`. -/
theorem Tset_subset_succ (L : ℕ) : Tset L ⊆ Tset (L + 1) := by
  rintro t ⟨hr, hlt⟩
  exact ⟨hr, hlt.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self L))⟩

/-- Prefixing a ternary digit `1`: `3 ^ L + Tset L ⊆ Tset (L+1)`. -/
theorem mem_Tset_succ_of_mem {L t : ℕ} (ht : t ∈ Tset L) : 3 ^ L + t ∈ Tset (L + 1) := by
  obtain ⟨r, hr, rfl⟩ := mem_Tset_iff.mp ht
  refine mem_Tset_iff.mpr ⟨2 ^ L + r, ?_, binToTernary_add_pow_two L r hr⟩
  have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  omega

/-- The doubling bound on a block: `2 t < 3 ^ L` for `t ∈ Tset L`. -/
theorem two_mul_lt_of_mem_Tset {L t : ℕ} (ht : t ∈ Tset L) : 2 * t < 3 ^ L := by
  obtain ⟨r, hr, rfl⟩ := mem_Tset_iff.mp ht
  exact two_mul_binToTernary_lt L r hr

/-- The greedy prefix through block `L - 1`: `Pre 0 = {1,2}` (the terms before the first
block) and `Pre (L+1) = Pre L ∪ (blockStart L + Tset L)`. -/
def Pre : ℕ → Set ℕ
  | 0 => {1, 2}
  | L + 1 => Pre L ∪ {m | ∃ t ∈ Tset L, m = blockStart L + t}

/-- **The set of terms of A092482**: `1`, `2`, and the blocks. -/
def Vset : Set ℕ := {1, 2} ∪ {m | ∃ L, ∃ t ∈ Tset L, m = blockStart L + t}

/-- Block starts increase strictly: `3 < 6 < 14 < 36 < …`. -/
theorem blockStart_strictMono : StrictMono blockStart := by
  intro a b hab
  have h2 : (2 : ℕ) ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab.le
  have h3 : (3 : ℕ) ^ a < 3 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  simp only [blockStart]
  omega

/-- Every block starts at or above `3`, the third term. -/
theorem three_le_blockStart (L : ℕ) : 3 ≤ blockStart L := by
  have h2 : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  have h3 : 1 ≤ (3 : ℕ) ^ L := Nat.one_le_pow _ _ (by norm_num)
  simp only [blockStart]
  omega

/-- A block sits strictly below the start of the next block. -/
theorem blockStart_add_lt_succ {L t : ℕ} (ht : t ∈ Tset L) :
    blockStart L + t < blockStart (L + 1) := by
  have h := two_mul_lt_of_mem_Tset ht
  have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have h3 : (3 : ℕ) ^ (L + 1) = 3 * 3 ^ L := by ring
  have h2p : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  simp only [blockStart]
  omega

/-- Prefixes nest. -/
theorem Pre_subset_succ (L : ℕ) : Pre L ⊆ Pre (L + 1) := fun _ hp => Or.inl hp

/-- Every prefix consists of terms. -/
theorem Pre_subset_Vset : ∀ L : ℕ, Pre L ⊆ Vset := by
  intro L
  induction L with
  | zero => intro p hp; exact Or.inl hp
  | succ L ih =>
    rintro p (hp | ⟨t, ht, rfl⟩)
    · exact ih hp
    · exact Or.inr ⟨L, t, ht, rfl⟩

/-- Every element of the prefix `Pre L` lies below the start of block `L`. -/
theorem Pre_lt_blockStart : ∀ L p : ℕ, p ∈ Pre L → p < blockStart L := by
  intro L
  induction L with
  | zero =>
    intro p hp
    have h : blockStart 0 = 3 := by norm_num [blockStart]
    rcases hp with rfl | rfl <;> omega
  | succ L ih =>
    rintro p (hp | ⟨t, ht, rfl⟩)
    · exact (ih p hp).trans (blockStart_strictMono (Nat.lt_succ_self L))
    · exact blockStart_add_lt_succ ht

/-- **The tightness of the block structure**: doubling the prefix through block `L`
never exceeds the start of block `L+1`.  Equality is attained at the top of block `L`,
which is why the greedy sequence jumps to exactly `blockStart (L+1)`. -/
theorem two_mul_le_blockStart_succ :
    ∀ L p : ℕ, p ∈ Pre (L + 1) → 2 * p ≤ blockStart (L + 1) := by
  intro L
  induction L with
  | zero =>
    rintro p (hp | ⟨t, ht, rfl⟩)
    · rcases hp with rfl | rfl <;> norm_num [blockStart]
    · have h := two_mul_lt_of_mem_Tset ht
      norm_num [blockStart] at h ⊢
      omega
  | succ L ih =>
    rintro p (hp | ⟨t, ht, rfl⟩)
    · exact (ih p hp).trans (blockStart_strictMono (Nat.lt_succ_self (L + 1))).le
    · have h := two_mul_lt_of_mem_Tset ht
      have h2 : (2 : ℕ) ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
      have h3 : (3 : ℕ) ^ (L + 2) = 3 * 3 ^ (L + 1) := by ring
      simp only [blockStart]
      omega

/-- Every member of `Vset` below `blockStart L` already lies in the prefix `Pre L`. -/
theorem mem_Pre_of_lt_blockStart :
    ∀ L v : ℕ, v ∈ Vset → v < blockStart L → v ∈ Pre L := by
  intro L
  induction L with
  | zero =>
    intro v hv hlt
    have h0 : blockStart 0 = 3 := by norm_num [blockStart]
    rcases hv with hv | ⟨L', t, ht, rfl⟩
    · exact hv
    · exact absurd (three_le_blockStart L') (by omega)
  | succ L ih =>
    intro v hv hlt
    rcases Nat.lt_or_ge v (blockStart L) with h | h
    · exact Pre_subset_succ L (ih v hv h)
    · -- `v` lies in block `L`
      rcases hv with hv | ⟨L', t, ht, rfl⟩
      · exact absurd (three_le_blockStart L) (by rcases hv with rfl | rfl <;> omega)
      · have hLL : L' = L := by
          by_contra hne
          rcases Nat.lt_or_ge L' L with hlt' | hge'
          · have hb := blockStart_add_lt_succ ht
            have hm : blockStart (L' + 1) ≤ blockStart L :=
              blockStart_strictMono.monotone (by omega)
            omega
          · have hm : blockStart (L + 1) ≤ blockStart L' :=
              blockStart_strictMono.monotone (by omega)
            omega
        subst hLL
        exact Or.inr ⟨t, ht, rfl⟩

/-- Members of `Vset` in the range of block `L` are exactly the block. -/
theorem mem_Tset_of_mem_Vset {L v : ℕ} (hv : v ∈ Vset) (h1 : blockStart L ≤ v)
    (h2 : v < blockStart (L + 1)) : ∃ t ∈ Tset L, v = blockStart L + t := by
  rcases hv with hv | ⟨L', t, ht, rfl⟩
  · exact absurd (three_le_blockStart L) (by rcases hv with rfl | rfl <;> omega)
  · have hLL : L' = L := by
      by_contra hne
      rcases Nat.lt_or_ge L' L with hlt' | hge'
      · have hb := blockStart_add_lt_succ ht
        have hm : blockStart (L' + 1) ≤ blockStart L :=
          blockStart_strictMono.monotone (by omega)
        omega
      · have hm : blockStart (L + 1) ≤ blockStart L' :=
          blockStart_strictMono.monotone (by omega)
        omega
    subst hLL
    exact ⟨t, ht, rfl⟩

/-- Every integer `≥ 3` sits in a unique block range `[blockStart L, blockStart (L+1))`. -/
theorem exists_block_index {m : ℕ} (hm : 3 ≤ m) :
    ∃ L, blockStart L ≤ m ∧ m < blockStart (L + 1) := by
  have hex : ∃ L, m < blockStart (L + 1) := by
    refine ⟨m, ?_⟩
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ (3 : ℕ) ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [blockStart]
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    have h0 : blockStart 0 = 3 := by norm_num [blockStart]
    omega
  · obtain ⟨L, hL⟩ : ∃ L, Nat.find hex = L + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (m := L) (by omega)
    rw [hL]
    omega

/-- The first term `1` lies in every prefix. -/
theorem one_mem_Pre (L : ℕ) : 1 ∈ Pre L := by
  induction L with
  | zero => exact Or.inl rfl
  | succ L ih => exact Or.inl ih

/-- The second term `2` lies in every prefix. -/
theorem two_mem_Pre (L : ℕ) : 2 ∈ Pre L := by
  induction L with
  | zero => exact Or.inr rfl
  | succ L ih => exact Or.inl ih

/-- Terms are positive; `1` is the least. -/
theorem one_le_of_mem_Vset {v : ℕ} (hv : v ∈ Vset) : 1 ≤ v := by
  rcases hv with hv | ⟨L, t, _, rfl⟩
  · rcases hv with rfl | rfl <;> omega
  · have := three_le_blockStart L
    omega

/-! ## The two covering lemmas

`exists_ap_witness` is the classical A003278 fact: every `u < 3 ^ L` is `2t - t'` for a
pair from `Tset L` (take `t = t' = u` if `u` itself has no ternary digit `2`, otherwise the
`capDigits`/`keepOnes` pair).  `q_covering` is the induction that covers the gap between
consecutive blocks; its four cases tile the target range exactly. -/

/-- **Classical A003278 covering**: every `u < 3 ^ L` is an endpoint reflection `2t - t'`
of a pair in `Tset L`.  Stated additively as `u + t' = 2 * t`. -/
theorem exists_ap_witness (L u : ℕ) (hu : u < 3 ^ L) :
    ∃ t ∈ Tset L, ∃ t' ∈ Tset L, u + t' = 2 * t := by
  by_cases hmem : u ∈ Set.range binToTernary
  · exact ⟨u, ⟨hmem, hu⟩, u, ⟨hmem, hu⟩, by omega⟩
  · have hcap := capDigits_le u
    have hkeep := keepOnes_le u
    refine ⟨capDigits u, ⟨capDigits_mem_range u, by omega⟩,
      keepOnes u, ⟨keepOnes_mem_range u, by omega⟩, ?_⟩
    have h := keepOnes_add_self u
    omega

/-- **The gap-covering induction.**  For every `μ < 3 ^ L + 2 ^ L` there is `t` in block
`L` and `p` in the prefix below block `L` with `μ + p = 2 t + 2 ^ L + 1`.  Translating by
`2 · blockStart L` this says exactly that every integer in `[blockStart L + 3 ^ L,
blockStart (L+1))` — the run above the *span* of block `L`, where no block-`L` offset
exists — completes an arithmetic progression with two earlier terms.  Non-terms inside
the span (offset has a ternary digit `2`) are not covered here; `exists_blocking`
dispatches them via the `keepOnes`/`capDigits` witnesses instead. -/
theorem q_covering : ∀ L μ : ℕ, μ < 3 ^ L + 2 ^ L →
    ∃ t ∈ Tset L, ∃ p ∈ Pre L, μ + p = 2 * t + 2 ^ L + 1 := by
  intro L
  induction L with
  | zero =>
    intro μ hμ
    have hμ2 : μ < 2 := by simpa using hμ
    have ht : (0 : ℕ) ∈ Tset 0 := ⟨⟨0, binToTernary_zero⟩, by norm_num⟩
    interval_cases μ
    · exact ⟨0, ht, 2, two_mem_Pre 0, by norm_num⟩
    · exact ⟨0, ht, 1, one_mem_Pre 0, by norm_num⟩
  | succ L ih =>
    intro μ hμ
    have hpow2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow3 : (3 : ℕ) ^ (L + 1) = 3 * 3 ^ L := by ring
    have h23 : (2 : ℕ) ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by norm_num) L
    rcases Nat.lt_or_ge μ (2 ^ L) with hA | hA
    · -- Case A: reflect a low block-`L` element off block `L`.
      obtain ⟨u, hu⟩ : ∃ u, u + 2 ^ L = μ + 3 ^ L := ⟨μ + 3 ^ L - 2 ^ L, by omega⟩
      have hulr : u < 3 ^ L := by omega
      obtain ⟨t, ht, t', ht', heq⟩ := exists_ap_witness L u hulr
      refine ⟨t, Tset_subset_succ L ht, blockStart L + t', Or.inr ⟨t', ht', rfl⟩, ?_⟩
      simp only [blockStart]
      omega
    rcases Nat.lt_or_ge μ (2 ^ L + 3 ^ L) with hB | hB
    · -- Case B: the induction hypothesis, shifted by `2 ^ L`.
      obtain ⟨μ', hμ'⟩ : ∃ μ', μ' + 2 ^ L = μ := ⟨μ - 2 ^ L, by omega⟩
      have hlt : μ' < 3 ^ L + 2 ^ L := by omega
      obtain ⟨t, ht, p, hp, heq⟩ := ih μ' hlt
      exact ⟨t, Tset_subset_succ L ht, p, Pre_subset_succ L hp, by omega⟩
    rcases Nat.lt_or_ge μ (2 ^ L + 2 * 3 ^ L) with hC | hC
    · -- Case C: reflect off block `L` into the top half of block `L+1`.
      obtain ⟨u, hu⟩ : ∃ u, u + 2 ^ L + 3 ^ L = μ := ⟨μ - 2 ^ L - 3 ^ L, by omega⟩
      have hulr : u < 3 ^ L := by omega
      obtain ⟨t, ht, t', ht', heq⟩ := exists_ap_witness L u hulr
      refine ⟨3 ^ L + t, mem_Tset_succ_of_mem ht, blockStart L + t',
        Or.inr ⟨t', ht', rfl⟩, ?_⟩
      simp only [blockStart]
      omega
    · -- Case D: the induction hypothesis, shifted into the top half of block `L+1`.
      obtain ⟨μ', hμ'⟩ : ∃ μ', μ' + 2 * 3 ^ L + 2 ^ L = μ :=
        ⟨μ - 2 * 3 ^ L - 2 ^ L, by omega⟩
      have hlt : μ' < 3 ^ L + 2 ^ L := by omega
      obtain ⟨t, ht, p, hp, heq⟩ := ih μ' hlt
      exact ⟨3 ^ L + t, mem_Tset_succ_of_mem ht, p, Pre_subset_succ L hp, by omega⟩

/-- **Every non-term above `2` is blocked**: if `m > 2` is not a term of A092482 then `m`
completes a 3-term arithmetic progression with two strictly smaller terms.  This is the
minimality half of the greedy characterization. -/
theorem exists_blocking {m : ℕ} (hm : 2 < m) (hV : m ∉ Vset) :
    ∃ x y, x ∈ Vset ∧ y ∈ Vset ∧ x < m ∧ y < m ∧ m + x = 2 * y := by
  obtain ⟨L, h1, h2⟩ := exists_block_index (show 3 ≤ m by omega)
  rcases Nat.lt_or_ge m (blockStart L + 3 ^ L) with hi | hii
  · -- `m` lies inside the span of block `L`: the classical digit witnesses.
    obtain ⟨u, hu⟩ : ∃ u, blockStart L + u = m := ⟨m - blockStart L, by omega⟩
    have hulr : u < 3 ^ L := by omega
    have hnot : u ∉ Set.range binToTernary := fun hmem =>
      hV (Or.inr ⟨L, u, ⟨hmem, hulr⟩, hu.symm⟩)
    have hcap := capDigits_lt_of_not_mem_range hnot
    have hkeep := keepOnes_le u
    have hsum := keepOnes_add_self u
    exact ⟨blockStart L + keepOnes u, blockStart L + capDigits u,
      Or.inr ⟨L, keepOnes u, ⟨keepOnes_mem_range u, by omega⟩, rfl⟩,
      Or.inr ⟨L, capDigits u, ⟨capDigits_mem_range u, by omega⟩, rfl⟩,
      by omega, by omega, by omega⟩
  · -- `m` lies in the gap above block `L`: the covering induction.
    obtain ⟨μ, hμ⟩ : ∃ μ, blockStart L + 3 ^ L + μ = m :=
      ⟨m - blockStart L - 3 ^ L, by omega⟩
    have hpow2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow3 : (3 : ℕ) ^ (L + 1) = 3 * 3 ^ L := by ring
    have hμlt : μ < 3 ^ L + 2 ^ L := by
      simp only [blockStart] at hμ h2
      omega
    obtain ⟨t, ht, p, hp, heq⟩ := q_covering L μ hμlt
    have hplt : p < blockStart L := Pre_lt_blockStart L p hp
    have htlt : t < 3 ^ L := ht.2
    refine ⟨p, blockStart L + t, Pre_subset_Vset L hp, Or.inr ⟨L, t, ht, rfl⟩,
      by omega, by omega, ?_⟩
    simp only [blockStart] at hμ ⊢
    omega

/-! ## `Vset` carries no arithmetic progression but the exempted `(1,2,3)` -/

/-- The OEIS rule for A092482: a set of naturals contains no three terms in arithmetic
progression, *except* for the exempted initial triple `(1, 2, 3)`. -/
def NoThreeAPExceptSeed (s : Set ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → a + c = 2 * b → a = 1 ∧ b = 2 ∧ c = 3

/-- Monotonicity of the rule under subsets. -/
theorem NoThreeAPExceptSeed.mono {s t : Set ℕ} (hst : s ⊆ t)
    (h : NoThreeAPExceptSeed t) : NoThreeAPExceptSeed s :=
  fun a ha b hb c hc => h a (hst ha) b (hst hb) c (hst hc)

/-- The rule is a weakening of Mathlib's `ThreeAPFree`: every 3-AP-free set obeys it. -/
theorem noThreeAPExceptSeed_of_threeAPFree {s : Set ℕ} (h : ThreeAPFree s) :
    NoThreeAPExceptSeed s := by
  intro a ha b hb c hc hab hbc habc
  exact absurd (h ha hb hc (show a + c = b + b by omega)) (by omega)

/-- …and a *strict* weakening: the seed `{1,2,3}` obeys the rule. -/
theorem noThreeAPExceptSeed_seed : NoThreeAPExceptSeed ({1, 2, 3} : Set ℕ) := by
  intro a ha b hb c hc hab hbc habc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  omega

/-- …but is not 3-AP-free.  So the exemption clause carries real content: without it the
greedy sequence would be the Stanley sequence A003278. -/
theorem not_threeAPFree_seed : ¬ ThreeAPFree ({1, 2, 3} : Set ℕ) := by
  intro h
  have h1 : (1 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := Or.inl rfl
  have h2 : (2 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := Or.inr (Or.inl rfl)
  have h3 : (3 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := Or.inr (Or.inr rfl)
  have := h h1 h2 h3 (show (1 : ℕ) + 3 = 2 + 2 by norm_num)
  omega

/-- **The admissibility half**: the term set of A092482 has no 3-term arithmetic
progression other than `(1, 2, 3)`.  An AP forces all three terms into a single block,
where the claim is 3-AP-freeness of A003278. -/
theorem noThreeAPExceptSeed_Vset : NoThreeAPExceptSeed Vset := by
  intro a ha b hb c hc hab hbc habc
  have h1a : 1 ≤ a := one_le_of_mem_Vset ha
  obtain ⟨L, hL1, hL2⟩ := exists_block_index (show 3 ≤ c by omega)
  obtain ⟨tc, htc, hceq⟩ := mem_Tset_of_mem_Vset hc hL1 hL2
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · -- the only block-`0` term is `3`, and the AP is forced to be `(1,2,3)`
    have htc0 : tc = 0 := by
      have := htc.2
      simpa using this
    have hb0 : blockStart 0 = 3 := by norm_num [blockStart]
    have hbP : b ∈ Pre 0 := mem_Pre_of_lt_blockStart 0 b hb (by omega)
    rcases hbP with rfl | rfl
    · omega
    · exact ⟨by omega, rfl, by omega⟩
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hbge : blockStart (L' + 1) ≤ b := by
      by_contra hlt
      have hbP : b ∈ Pre (L' + 1) := mem_Pre_of_lt_blockStart _ b hb (by omega)
      have := two_mul_le_blockStart_succ L' b hbP
      omega
    obtain ⟨tb, htb, hbeq⟩ := mem_Tset_of_mem_Vset hb hbge (by omega)
    have htclt : 2 * tc < 3 ^ (L' + 1) := two_mul_lt_of_mem_Tset htc
    have hbs : blockStart (L' + 1) = 2 * 2 ^ L' + 3 * 3 ^ L' + 1 := by
      simp only [blockStart]; ring
    have hage : blockStart (L' + 1) ≤ a := by
      by_contra hlt
      have haP : a ∈ Pre (L' + 1) := mem_Pre_of_lt_blockStart _ a ha (by omega)
      have h2a := two_mul_le_blockStart_succ L' a haP
      have h3 : (3 : ℕ) ^ (L' + 1) = 3 * 3 ^ L' := by ring
      omega
    obtain ⟨ta, hta, haeq⟩ := mem_Tset_of_mem_Vset ha hage (by omega)
    -- all three sit in block `L'+1`: reduce to 3-AP-freeness of A003278
    obtain ⟨pa, hpa⟩ := hta.1
    obtain ⟨pb, hpb⟩ := htb.1
    obtain ⟨pc, hpc⟩ := htc.1
    have hkey : binToTernary pa + binToTernary pc = 2 * binToTernary pb := by
      rw [hpa, hpb, hpc]
      omega
    obtain ⟨hab', -⟩ := binToTernary_add_eq_two_mul hkey
    exfalso
    rw [hab'] at hpa
    omega

/-! ## The closed form

`closedForm n = A092482(n+1)` (0-indexed).  For `n ≥ 2` this is the OEIS formula
`1 + A053644(n-1) + A005836(n-1)` with both cross-references read at offset `0`. -/

/-- **The closed form of A092482** (0-indexed, so `closedForm n = A092482(n+1)`):
`1`, `2`, and then `1 + 2 ^ ⌊log₂ j⌋ + binToTernary j` for `j = 1, 2, 3, …`. -/
def closedForm : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 ^ Nat.log 2 (n + 1) + binToTernary (n + 1) + 1

/-- The closed form at index 0 is the first seed value. -/
@[simp] theorem closedForm_zero : closedForm 0 = 1 := rfl

/-- The closed form at index 1 is the second seed value. -/
@[simp] theorem closedForm_one : closedForm 1 = 2 := rfl

/-- Defining equation of `closedForm` past the first two terms. -/
theorem closedForm_add_two (n : ℕ) :
    closedForm (n + 2) = 2 ^ Nat.log 2 (n + 1) + binToTernary (n + 1) + 1 := rfl

/-- `A092482(3) = 3`, the third seed value. -/
theorem closedForm_two : closedForm 2 = 3 := by
  have h := closedForm_add_two 0
  norm_num [binToTernary_one] at h
  exact h

/-- Base-2 decomposition of a positive index into its leading power of two and remainder. -/
theorem exists_log_decomposition {j : ℕ} (hj : 1 ≤ j) :
    ∃ r, r < 2 ^ Nat.log 2 j ∧ j = 2 ^ Nat.log 2 j + r := by
  have hlow : 2 ^ Nat.log 2 j ≤ j := Nat.pow_log_le_self 2 (by omega)
  have hhigh : j < 2 ^ (Nat.log 2 j + 1) := Nat.lt_pow_succ_log_self (by norm_num) j
  have h2 : (2 : ℕ) ^ (Nat.log 2 j + 1) = 2 * 2 ^ Nat.log 2 j := by ring
  exact ⟨j - 2 ^ Nat.log 2 j, by omega, by omega⟩

/-- The closed form in block coordinates: index `2 ^ L + r + 1` (0-indexed) sits at
position `r` of block `L`. -/
theorem closedForm_eq_block {m L r : ℕ} (hL : Nat.log 2 (m + 1) = L)
    (hr : m + 1 = 2 ^ L + r) (hrlt : r < 2 ^ L) :
    closedForm (m + 2) = blockStart L + binToTernary r := by
  rw [closedForm_add_two, hL, hr, binToTernary_add_pow_two L r hrlt]
  simp only [blockStart]
  ring

/-- The closed form is strictly increasing, so it enumerates its range in order. -/
theorem closedForm_strictMono : StrictMono closedForm := by
  apply strictMono_nat_of_lt_succ
  intro n
  match n with
  | 0 => norm_num
  | 1 => rw [closedForm_one, show (1 : ℕ) + 1 = 2 from rfl, closedForm_two]; norm_num
  | m + 2 =>
    rw [closedForm_add_two m, show m + 2 + 1 = (m + 1) + 2 from rfl, closedForm_add_two (m + 1)]
    have hlog : Nat.log 2 (m + 1) ≤ Nat.log 2 (m + 1 + 1) := Nat.log_mono_right (by omega)
    have hpow : (2 : ℕ) ^ Nat.log 2 (m + 1) ≤ 2 ^ Nat.log 2 (m + 1 + 1) :=
      Nat.pow_le_pow_right (by norm_num) hlog
    have hb : binToTernary (m + 1) < binToTernary (m + 1 + 1) :=
      binToTernary_strictMono (by omega)
    omega

/-- Every closed-form value is a term. -/
theorem closedForm_mem_Vset (n : ℕ) : closedForm n ∈ Vset := by
  match n with
  | 0 => exact Or.inl (Or.inl rfl)
  | 1 => exact Or.inl (Or.inr rfl)
  | m + 2 =>
    obtain ⟨r, hrlt, hr⟩ := exists_log_decomposition (show 1 ≤ m + 1 by omega)
    refine Or.inr ⟨Nat.log 2 (m + 1), binToTernary r,
      ⟨⟨r, rfl⟩, (binToTernary_lt_pow_iff _ r).mpr hrlt⟩, ?_⟩
    exact closedForm_eq_block rfl hr hrlt

/-- Every term is a closed-form value. -/
theorem exists_closedForm_eq : ∀ v : ℕ, v ∈ Vset → ∃ n, closedForm n = v := by
  rintro v (hv | ⟨L, t, ht, rfl⟩)
  · rcases hv with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨r, hr, rfl⟩ := mem_Tset_iff.mp ht
    have h1 : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 ^ L + r := ⟨2 ^ L + r - 1, by omega⟩
    have hlog : Nat.log 2 (m + 1) = L := by
      rw [hm]
      refine Nat.log_eq_of_pow_le_of_lt_pow (by omega) ?_
      have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
      omega
    exact ⟨m + 2, closedForm_eq_block hlog hm hr⟩

/-- The values of the closed form are exactly `Vset`. -/
theorem range_closedForm : Set.range closedForm = Vset := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    exact closedForm_mem_Vset n
  · intro hv
    exact exists_closedForm_eq v hv

/-! ## The greedy recursion

Exactly the scaffolding of `Proofs/Enumerative/StanleyDigits.lean`, with `ThreeAPFree`
replaced by `NoThreeAPExceptSeed`.  The seed is *not* assumed: the recursion starts from
`{1}` and the `(1,2,3)` exemption forces `1, 2, 3` (see `prefixSet_two`). -/

/-- The rule is decidable on a finite set, so the greedy step is computable. -/
instance decidableNoThreeAPExceptSeed (s : Finset ℕ) :
    Decidable (NoThreeAPExceptSeed (↑s : Set ℕ)) :=
  decidable_of_iff
    (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → a + c = 2 * b → a = 1 ∧ b = 2 ∧ c = 3)
    (by simp only [NoThreeAPExceptSeed, Finset.mem_coe])

/-- `k` is a legal greedy extension of the finite set `s`: it exceeds every element of `s`
and inserting it preserves the OEIS rule. -/
def IsGoodStep (s : Finset ℕ) (k : ℕ) : Prop :=
  (∀ a ∈ s, a < k) ∧ NoThreeAPExceptSeed (↑(insert k s) : Set ℕ)

/-- Legality of a greedy extension is decidable, so `Nat.find` applies. -/
instance (s : Finset ℕ) : DecidablePred (IsGoodStep s) := fun k =>
  inferInstanceAs (Decidable ((∀ a ∈ s, a < k) ∧
    NoThreeAPExceptSeed (↑(insert k s) : Set ℕ)))

/-- The greedy step never gets stuck: `2 · max + 1` is always legal. -/
theorem exists_isGoodStep {s : Finset ℕ} (hs : NoThreeAPExceptSeed (↑s : Set ℕ)) :
    ∃ k, IsGoodStep s k := by
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

/-- Base of the greedy recursion: the singleton `{1}` obeys the rule. -/
theorem noThreeAPExceptSeed_singleton :
    NoThreeAPExceptSeed (↑({1} : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc hab hbc habc
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb hc
  omega

/-- The greedy step: the least legal extension. -/
def nextGreedy (s : Finset ℕ) (hs : NoThreeAPExceptSeed (↑s : Set ℕ)) : ℕ :=
  Nat.find (exists_isGoodStep hs)

/-- The greedy prefix sets bundled with the invariant. -/
def greedyAux : ℕ → {s : Finset ℕ // NoThreeAPExceptSeed (↑s : Set ℕ)}
  | 0 => ⟨{1}, noThreeAPExceptSeed_singleton⟩
  | n + 1 =>
    ⟨insert (nextGreedy (greedyAux n).1 (greedyAux n).2) (greedyAux n).1,
      (Nat.find_spec (exists_isGoodStep (greedyAux n).2)).2⟩

/-- The greedy prefix `{a(1), …, a(n+1)}`. -/
def prefixSet (n : ℕ) : Finset ℕ := (greedyAux n).1

/-- Invariant: every greedy prefix obeys the rule. -/
theorem prefixSet_noThreeAPExceptSeed (n : ℕ) :
    NoThreeAPExceptSeed (↑(prefixSet n) : Set ℕ) := (greedyAux n).2

/-- **The greedy sequence of OEIS A092482** (0-indexed: `greedySeq n = A092482(n+1)`):
it starts at `1`, and each next term is the least number exceeding all previous terms
whose insertion creates no 3-term arithmetic progression other than `(1,2,3)`. -/
def greedySeq : ℕ → ℕ
  | 0 => 1
  | n + 1 => nextGreedy (prefixSet n) (prefixSet_noThreeAPExceptSeed n)

/-- `A092482(1) = 1`, the starting value of the recursion. -/
theorem greedySeq_zero : greedySeq 0 = 1 := rfl

/-- The greedy recursion starts from `{1}` alone. -/
theorem prefixSet_zero : prefixSet 0 = {1} := rfl

/-- Each greedy step inserts exactly the next term. -/
theorem prefixSet_succ (n : ℕ) :
    prefixSet (n + 1) = insert (greedySeq (n + 1)) (prefixSet n) := rfl

/-- Greediness, packaged. -/
theorem isLeast_greedySeq_succ (n : ℕ) :
    IsLeast {k | (∀ a ∈ prefixSet n, a < k) ∧
      NoThreeAPExceptSeed (↑(insert k (prefixSet n)) : Set ℕ)} (greedySeq (n + 1)) :=
  ⟨Nat.find_spec (exists_isGoodStep (prefixSet_noThreeAPExceptSeed n)),
    fun _ hk => Nat.find_min' _ hk⟩

/-! ## The main theorem: greedy = closed form -/

/-- **Key step**: on the prefix `{closedForm 0, …, closedForm n}` the greedy choice is
`closedForm (n+1)`.  Admissibility is `noThreeAPExceptSeed_Vset`; minimality is
`exists_blocking`. -/
theorem nextGreedy_key {n : ℕ} {s : Finset ℕ} (hs : NoThreeAPExceptSeed (↑s : Set ℕ))
    (hset : s = (Finset.range (n + 1)).image closedForm) :
    nextGreedy s hs = closedForm (n + 1) := by
  subst hset
  simp only [nextGreedy]
  rw [Nat.find_eq_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact closedForm_strictMono (Finset.mem_range.mp hi)
  · refine NoThreeAPExceptSeed.mono ?_ noThreeAPExceptSeed_Vset
    intro z hz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_image] at hz
    rcases hz with rfl | ⟨i, -, rfl⟩
    · exact closedForm_mem_Vset (n + 1)
    · exact closedForm_mem_Vset i
  · intro k hk hgood
    obtain ⟨hlt, hfree⟩ := hgood
    have hnmem : closedForm n ∈ (Finset.range (n + 1)).image closedForm :=
      Finset.mem_image_of_mem _ (Finset.self_mem_range_succ n)
    have hkn : closedForm n < k := hlt _ hnmem
    -- for `n ≤ 1` the interval `(closedForm n, closedForm (n+1))` is empty
    have hk3 : 3 < k := by
      match n with
      | 0 => rw [closedForm_zero] at hkn; rw [show (0 : ℕ) + 1 = 1 from rfl,
               closedForm_one] at hk; omega
      | 1 => rw [closedForm_one] at hkn; rw [show (1 : ℕ) + 1 = 2 from rfl,
               closedForm_two] at hk; omega
      | m + 2 =>
        have h : closedForm 2 ≤ closedForm (m + 2) :=
          closedForm_strictMono.monotone (by omega)
        rw [closedForm_two] at h
        omega
    have hknot : k ∉ Vset := by
      rw [← range_closedForm]
      rintro ⟨i, rfl⟩
      have h1 : n < i := closedForm_strictMono.lt_iff_lt.mp hkn
      have h2 : i < n + 1 := closedForm_strictMono.lt_iff_lt.mp hk
      omega
    obtain ⟨x, y, hx, hy, hxk, hyk, hxy⟩ := exists_blocking (by omega) hknot
    obtain ⟨i, hi⟩ := exists_closedForm_eq x hx
    obtain ⟨j, hj⟩ := exists_closedForm_eq y hy
    have hiN : i < n + 1 := closedForm_strictMono.lt_iff_lt.mp (by omega)
    have hjN : j < n + 1 := closedForm_strictMono.lt_iff_lt.mp (by omega)
    have hmemx : x ∈ (↑(insert k ((Finset.range (n + 1)).image closedForm)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (hi ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr hiN))
    have hmemy : y ∈ (↑(insert k ((Finset.range (n + 1)).image closedForm)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (hj ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr hjN))
    have hmemk : k ∈ (↑(insert k ((Finset.range (n + 1)).image closedForm)) : Set ℕ) := by
      rw [Finset.coe_insert]
      exact Set.mem_insert _ _
    obtain ⟨-, -, hk3'⟩ :=
      hfree x hmemx y hmemy k hmemk (by omega) hyk (by omega)
    omega

/-- The greedy prefix sets are the initial segments of the closed form. -/
theorem prefixSet_eq_image :
    ∀ n : ℕ, prefixSet n = (Finset.range (n + 1)).image closedForm := by
  intro n
  induction n with
  | zero =>
    rw [Finset.range_one, Finset.image_singleton, closedForm_zero]
    exact prefixSet_zero
  | succ n ih =>
    rw [prefixSet_succ, show greedySeq (n + 1) =
        nextGreedy (prefixSet n) (prefixSet_noThreeAPExceptSeed n) from rfl,
      nextGreedy_key (prefixSet_noThreeAPExceptSeed n) ih, ih]
    conv_rhs => rw [Finset.range_add_one, Finset.image_insert]

/-- Pointwise form of the main theorem. -/
theorem greedySeq_apply (n : ℕ) : greedySeq n = closedForm n := by
  cases n with
  | zero => rfl
  | succ n => exact nextGreedy_key (prefixSet_noThreeAPExceptSeed n) (prefixSet_eq_image n)

/-- **Main theorem (OEIS A092482)**: the greedy 3-AP-avoiding sequence with the `(1,2,3)`
exemption equals the conjectured closed form. -/
theorem greedySeq_eq_closedForm : greedySeq = closedForm := funext greedySeq_apply

/-! ## Consequences -/

/-- The OEIS formula in its published shape (stated there for `n > 2`; proved here for all `n ≥ 1`):
`A092482(n+2) = 1 + A053644(n) + A005836(n)`, both cross-references read at offset `0`.
0-indexed here, `A092482(n+2) = greedySeq (n+1)`, so with `n = m + 1` this reads
`greedySeq (m + 2) = 1 + 2 ^ ⌊log₂ (m+1)⌋ + binToTernary (m+1)`. -/
theorem greedySeq_add_two (m : ℕ) :
    greedySeq (m + 2) = 1 + 2 ^ Nat.log 2 (m + 1) + binToTernary (m + 1) := by
  rw [greedySeq_apply, closedForm_add_two]
  ring

/-- The seed is *derived*, not assumed: `A092482(2) = 2`. -/
theorem greedySeq_one : greedySeq 1 = 2 := by rw [greedySeq_apply, closedForm_one]

/-- The seed is *derived*, not assumed: `A092482(3) = 3`, the exempted third term. -/
theorem greedySeq_two : greedySeq 2 = 3 := by rw [greedySeq_apply, closedForm_two]

/-- **Agreement with the OEIS definition's stipulated seed**: the greedy recursion started
from `{1}` reproduces `a(1)=1, a(2)=2, a(3)=3`, so seeding the recursion with `{1,2,3}`
instead (as the OEIS comment does) gives the same sequence. -/
theorem prefixSet_two : prefixSet 2 = {1, 2, 3} := by
  rw [prefixSet_eq_image 2]
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl closedForm_zero
    · exact Or.inr (Or.inl closedForm_one)
    · exact Or.inr (Or.inr closedForm_two)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by omega, closedForm_zero⟩
    · exact ⟨1, by omega, closedForm_one⟩
    · exact ⟨2, by omega, closedForm_two⟩

/-- The greedy sequence is strictly increasing. -/
theorem greedySeq_strictMono : StrictMono greedySeq := by
  rw [greedySeq_eq_closedForm]
  exact closedForm_strictMono

/-- The term set of the greedy sequence is the block union `Vset`. -/
theorem range_greedySeq : Set.range greedySeq = Vset := by
  rw [greedySeq_eq_closedForm]
  exact range_closedForm

/-- Set form of the block characterization: `m` is a term of A092482 iff `m ∈ {1,2}` or
`m = 2^L + 3^L + 1 + t` for some `L` and some `t` in A005836 with `t < 3^L`. -/
theorem exists_greedySeq_eq_iff {m : ℕ} :
    (∃ n, greedySeq n = m) ↔ m ∈ ({1, 2} : Set ℕ) ∪ {m | ∃ L, ∃ t ∈ Tset L,
      m = 2 ^ L + 3 ^ L + 1 + t} := by
  have h : m ∈ Set.range greedySeq ↔ m ∈ Vset := by rw [range_greedySeq]
  simpa only [Set.mem_range, Vset, blockStart] using h

/-- The greedy sequence's term set carries no 3-term arithmetic progression except the
exempted `(1, 2, 3)`. -/
theorem noThreeAPExceptSeed_range_greedySeq :
    NoThreeAPExceptSeed (Set.range greedySeq) := by
  rw [range_greedySeq]
  exact noThreeAPExceptSeed_Vset

/-! ## The `A007814` summation form of the OEIS formula

The pinned OEIS formula also gives `A005836(n)` as `Sum_{k=1..n} (3^A007814(k) + 1)/2`
(printed with a typo, `A007814(n)` for `A007814(k)`; see the file header).  We state it
division-free, doubled. -/

/-- One step of the summation form: `2·A005836(n+1) − 2·A005836(n) = 3^A007814(n+1) + 1`,
stated subtraction-free. -/
theorem two_mul_binToTernary_succ (n : ℕ) :
    2 * binToTernary (n + 1) = 2 * binToTernary n + 3 ^ padicValNat 2 (n + 1) + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · subst hm
      rw [binToTernary_two_mul_add_one, binToTernary_two_mul,
        padicValNat.eq_zero_of_not_dvd (show ¬(2 ∣ 2 * m + 1) by omega)]
      ring
    · subst hm
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring, binToTernary_two_mul,
        binToTernary_two_mul_add_one,
        padicValNat_base_mul (by norm_num) (show m + 1 ≠ 0 by omega)]
      have hih := ih m (by omega)
      have hp : (3 : ℕ) ^ (padicValNat 2 (m + 1) + 1) = 3 * 3 ^ padicValNat 2 (m + 1) := by
        ring
      omega

/-- **The `A007814` summation form**, division-free:
`2 · A005836(n) = ∑_{k=1}^{n} (3^A007814(k) + 1)`, i.e. the OEIS formula's
`Sum_{k=1..n} (3^A007814(k) + 1)/2` equals `A005836(n)` at offset `0`. -/
theorem two_mul_binToTernary_eq_sum (n : ℕ) :
    2 * binToTernary n = ∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1) := by
  induction n with
  | zero => simp [binToTernary_zero]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, two_mul_binToTernary_succ n]
    ring

/-! ## Ground checks against the OEIS data

The list below is transcribed verbatim from the `terms` field of `oeis show A092482`
(fetched 2026-08-05).  Everything is kernel-checked: `norm_num` evaluates `Nat.log` and
`Nat.digits`/`Nat.ofDigits`, and no `native_decide` is used anywhere in this file. -/

/-- **Ground check**: the first 57 terms of the greedy sequence are exactly the OEIS
`terms` field of A092482. -/
theorem greedySeq_ground :
    (List.range 57).map greedySeq =
      [1, 2, 3, 6, 7, 14, 15, 17, 18, 36, 37, 39, 40, 45, 46, 48, 49, 98, 99, 101, 102,
       107, 108, 110, 111, 125, 126, 128, 129, 134, 135, 137, 138, 276, 277, 279, 280,
       285, 286, 288, 289, 303, 304, 306, 307, 312, 313, 315, 316, 357, 358, 360, 361,
       366, 367, 369, 370] := by
  rw [greedySeq_eq_closedForm]
  norm_num [closedForm, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil, List.range_succ]

/- **Independent cross-check of the greedy definition itself.**  `greedySeq_ground` above
is a kernel-checked theorem, but it routes through `greedySeq_eq_closedForm`; if
`greedySeq` had been mis-formalized, both sides would be wrong together.  The `#eval`
below instead *runs* the greedy recursion — `Nat.find` over `IsGoodStep`, i.e. the literal
OEIS rule with no reference to the closed form — and prints

  `[1, 2, 3, 6, 7, 14, 15, 17, 18, 36, 37, 39, 40, 45, 46, 48, 49, 98, 99, 101]`,

the first 20 entries of the OEIS `terms` field.  This is a diagnostic, not a proof, and
contributes no axioms. -/
#eval (List.range 20).map greedySeq

/-- Ground check for `blockStart`: block starts are the OEIS terms `3, 6, 14, 36, 98,
276` at positions `3, 4, 6, 10, 18, 34`. -/
theorem blockStart_ground :
    blockStart 0 = 3 ∧ blockStart 1 = 6 ∧ blockStart 2 = 14 ∧ blockStart 3 = 36 ∧
      blockStart 4 = 98 ∧ blockStart 5 = 276 := by
  norm_num [blockStart]

/-- Ground check for `binToTernary` at the block widths used above (A005836). -/
theorem binToTernary_ground :
    (List.range 8).map binToTernary = [0, 1, 3, 4, 9, 10, 12, 13] := by
  norm_num [binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil, List.range_succ]

/-- Ground check for `Tset`: `Tset 2 = {0, 1, 3, 4}`, and `2` is excluded (its ternary
expansion has a digit `2`). -/
theorem Tset_two_ground :
    (0 : ℕ) ∈ Tset 2 ∧ (1 : ℕ) ∈ Tset 2 ∧ (3 : ℕ) ∈ Tset 2 ∧ (4 : ℕ) ∈ Tset 2 ∧
      (2 : ℕ) ∉ Tset 2 := by
  refine ⟨⟨⟨0, binToTernary_zero⟩, by norm_num⟩, ⟨⟨1, binToTernary_one⟩, by norm_num⟩,
    ⟨⟨2, ?_⟩, by norm_num⟩, ⟨⟨3, ?_⟩, by norm_num⟩, ?_⟩
  · norm_num [binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  · norm_num [binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  · exact fun h => two_not_mem_range_binToTernary h.1

/-- Ground check for `Vset` / `Pre`: `4` is the first non-term above the seed. -/
theorem four_not_mem_Vset : (4 : ℕ) ∉ Vset := by
  rintro (hv | ⟨L, t, ht, hEq⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    omega
  · have h1 := three_le_blockStart L
    have h2 : t < 3 ^ L := ht.2
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · norm_num [blockStart] at hEq h2
      omega
    · have hmono : blockStart 1 ≤ blockStart L := blockStart_strictMono.monotone (by omega)
      have hb1 : blockStart 1 = 6 := by norm_num [blockStart]
      omega

/-- Ground check for `Pre`: `4` is not in the prefix `Pre 2 = {1,2,3,6,7}`. -/
theorem four_not_mem_Pre_two : (4 : ℕ) ∉ Pre 2 :=
  fun h => four_not_mem_Vset (Pre_subset_Vset 2 h)

/-! ## Satisfiability of the hypotheses

Each nontrivial hypothesis set below is instantiated jointly at a concrete point, so no
statement above is vacuous. -/

/-- The exempted triple genuinely occurs in `Vset`: `1 < 2 < 3` are terms and
`1 + 3 = 2 · 2`.  Hence the exemption clause of `NoThreeAPExceptSeed` is *not* vacuous,
and the conclusion `a = 1 ∧ b = 2 ∧ c = 3` of `noThreeAPExceptSeed_Vset` is attained. -/
theorem seed_ap_mem_Vset :
    (1 : ℕ) ∈ Vset ∧ (2 : ℕ) ∈ Vset ∧ (3 : ℕ) ∈ Vset ∧ (1 : ℕ) + 3 = 2 * 2 :=
  ⟨Or.inl (Or.inl rfl), Or.inl (Or.inr rfl),
    Or.inr ⟨0, 0, ⟨⟨0, binToTernary_zero⟩, by norm_num⟩, by norm_num [blockStart]⟩, by
      norm_num⟩

/-- Joint instantiation of every hypothesis of `noThreeAPExceptSeed_Vset` at the exempted
triple; the conclusion fires. -/
example : (1 : ℕ) = 1 ∧ (2 : ℕ) = 2 ∧ (3 : ℕ) = 3 :=
  noThreeAPExceptSeed_Vset 1 seed_ap_mem_Vset.1 2 seed_ap_mem_Vset.2.1 3
    seed_ap_mem_Vset.2.2.1 (by norm_num) (by norm_num) (by norm_num)

/-- Joint instantiation of the hypotheses of `exists_blocking` at `m = 4`: the witnesses
are `2` and `3` (the progression `2, 3, 4`). -/
example : ∃ x y, x ∈ Vset ∧ y ∈ Vset ∧ x < 4 ∧ y < 4 ∧ 4 + x = 2 * y :=
  exists_blocking (by norm_num) four_not_mem_Vset

/-- Joint instantiation of the hypotheses of `q_covering` at `L = 2, μ = 3`. -/
example : ∃ t ∈ Tset 2, ∃ p ∈ Pre 2, 3 + p = 2 * t + 2 ^ 2 + 1 :=
  q_covering 2 3 (by norm_num)

/-- Joint instantiation of the hypotheses of `exists_ap_witness` at `L = 2, u = 5`
(ternary `12`, so the `capDigits`/`keepOnes` branch is taken). -/
example : ∃ t ∈ Tset 2, ∃ t' ∈ Tset 2, 5 + t' = 2 * t :=
  exists_ap_witness 2 5 (by norm_num)

/-- Joint instantiation of the hypotheses of `exists_isGoodStep` at the base prefix. -/
example : ∃ k, IsGoodStep {1} k := exists_isGoodStep noThreeAPExceptSeed_singleton

/-- Joint instantiation of the hypotheses of `nextGreedy_key` at `n = 0`. -/
example : nextGreedy (prefixSet 0) (prefixSet_noThreeAPExceptSeed 0) = closedForm 1 :=
  nextGreedy_key (prefixSet_noThreeAPExceptSeed 0) (prefixSet_eq_image 0)

/-- Joint instantiation of the hypotheses of `mem_Tset_of_mem_Vset` at `L = 1, v = 7`. -/
example : ∃ t ∈ Tset 1, (7 : ℕ) = blockStart 1 + t :=
  mem_Tset_of_mem_Vset
    (Or.inr ⟨1, 1, ⟨⟨1, binToTernary_one⟩, by norm_num⟩, by norm_num [blockStart]⟩)
    (by norm_num [blockStart]) (by norm_num [blockStart])

/-- `NoThreeAPExceptSeed` is not vacuously true of every set: `{2, 3, 4}` violates it. -/
example : ¬ NoThreeAPExceptSeed ({2, 3, 4} : Set ℕ) := by
  intro h
  have := h 2 (Or.inl rfl) 3 (Or.inr (Or.inl rfl)) 4 (Or.inr (Or.inr rfl))
    (by norm_num) (by norm_num) (by norm_num)
  omega

/-- Ground check of the summation form at `n = 4`: `2 · A005836(4) = 2 · 9 = 18`. -/
example : 2 * binToTernary 4 = ∑ k ∈ Finset.Icc 1 4, (3 ^ padicValNat 2 k + 1) :=
  two_mul_binToTernary_eq_sum 4

/-- **The exemption is load-bearing**: A092482 is not the Stanley sequence A003278.  With
the `(1,2,3)` triple forbidden rather than exempted the greedy from `1` is
`stanleyGreedy = 1, 2, 4, 5, 10, …`, whose third term is `4`, not `3`. -/
theorem greedySeq_ne_stanleyGreedy : greedySeq ≠ stanleyGreedy := by
  intro h
  have h2 : greedySeq 2 = stanleyGreedy 2 := by rw [h]
  rw [greedySeq_two, stanleyGreedy_apply] at h2
  simp only [stanleyDigits] at h2
  norm_num [binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil] at h2

/-- **The seed-exemption defect is exactly `2 ^ L`**: the `L`-th block of A092482 starts
`2 ^ L` above the Stanley term at the same position, i.e.
`greedySeq (2 ^ L + 1) = stanleyGreedy (2 ^ L) + 2 ^ L` (0-indexed; block `L` starts at
index `2 ^ L + 1`).  The one exempted term `3` shifts the first block start by `1`, and the
greedy doubling dynamics (`blockStart (L+1) = 2 · max (block L)`) double that defect once
per block, forever — the source of the unbounded `2 ^ ⌊log₂ n⌋` correction in the closed
form. -/
theorem greedySeq_defect (L : ℕ) :
    greedySeq (2 ^ L + 1) = stanleyGreedy (2 ^ L) + 2 ^ L := by
  have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hidx : 2 ^ L + 1 = (2 ^ L - 1) + 2 := by omega
  have hsucc : 2 ^ L - 1 + 1 = 2 ^ L := by omega
  have hstanley : stanleyGreedy (2 ^ L) = 3 ^ L + 1 := by
    rw [stanleyGreedy_eq]
    exact congrArg (· + 1) (binToTernary_pow_two L)
  rw [hidx, greedySeq_add_two, hsucc, Nat.log_pow (by norm_num),
    binToTernary_pow_two, hstanley]
  ring

/-- Ground check of `greedySeq_defect` at `L = 2`: block `2` starts at `a(6) = 14`
(0-indexed `greedySeq 5`), the Stanley term is `A003278(5) = 10`, and `14 = 10 + 4`. -/
example : greedySeq 5 = 14 ∧ stanleyGreedy 4 = 10 := by
  refine ⟨?_, ?_⟩
  · rw [greedySeq_apply]
    norm_num [closedForm, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  · rw [stanleyGreedy_eq]
    norm_num [Nat.ofDigits_cons, Nat.ofDigits_nil]

end A092482

/-! ## Axiom audit -/

#print axioms A092482.greedySeq_eq_closedForm
#print axioms A092482.greedySeq_apply
#print axioms A092482.greedySeq_add_two
#print axioms A092482.greedySeq_ground
#print axioms A092482.noThreeAPExceptSeed_Vset
#print axioms A092482.exists_blocking
#print axioms A092482.q_covering
#print axioms A092482.range_greedySeq
#print axioms A092482.prefixSet_two
#print axioms A092482.two_mul_binToTernary_eq_sum
#print axioms A092482.noThreeAPExceptSeed_range_greedySeq
#print axioms A092482.exists_greedySeq_eq_iff
#print axioms A092482.greedySeq_ne_stanleyGreedy
#print axioms A092482.greedySeq_defect
#print axioms A092482.not_threeAPFree_seed
