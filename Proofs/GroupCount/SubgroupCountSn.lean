import Mathlib

/-!
# A005432: subgroups of `Sₙ`, and Pyber's claim that the lower bound is the truth

`GroupCount.numSubgroupsSymm n = Fintype.card (Subgroup (Equiv.Perm (Fin n)))` is OEIS
**A005432**, the number of subgroups of the symmetric group `Sₙ` with conjugates counted as
distinct.  This file archives the *statement* that the lower end of Pyber's window is the
true growth rate; that statement is the file's single `sorry`.

## The source, verbatim

Re-pulled with `oeis show A005432` on 2026-08-05.  Quoted fields, verbatim:

> **id** `A005432`
>
> **name** `Number of permutation groups of degree n (or, number of distinct subgroups of
> symmetric group S_n, counting conjugates as distinct).`
>
> **terms** `1,1,2,6,30,156,1455,11300,151221,1694723,29594446,404126228,10594925360,`
> `175238308453,5651774693595,117053117995400,5320744503742316,125889331236297288,`
> `7598016157515302757`
>
> **comments**
> * `Labeled version of A000638.`
> * `L. Pyber shows c^(n^2(1+o(1))) <= a(n) <= d^(n^2(1+o(1))), c=2^(1/16), d=24^(1/6);`
>   `conjectures lower bound is accurate.`
>
> **formulas** `Exponential transform of A116655. Binomial transform of A116693. -
> _Christian G. Bower_, Feb 23 2006`
>
> **xrefs** `Cf. A000001, A000019, A000638.`
>
> **keywords** `nonn,hard,more,nice`
>
> **programs**
> * `(Magma) n := 5; &+[ Length(s):s in SubgroupLattice(Sym(n)) ];`
> * `(GAP) List([0..5],n->Sum( List( ConjugacyClassesSubgroups( SymmetricGroup(n)),
>   Size))); # _Alexander Hulpke_, Dec 03 2004`

The GAP program `List([0..5], …)` fixes the **offset at 0**: the listed terms are
`a(0), a(1), …`.  Cross-checked by an independent enumeration of the subgroup lattices of
`S₀ … S₅` (breadth-first closure over `Sₙ`), which reproduces `1, 1, 2, 6, 30, 156`, and
inside Lean by `numSubgroupsSymm_zero`, `numSubgroupsSymm_one`, `numSubgroupsSymm_two`.

## The OEIS comment is stale: the conjecture is a theorem

**The OEIS comment above still calls the lower bound a conjecture; it has since been
proved.**  Roney-Dougal and Tracey, *Subgroups of symmetric groups: enumeration and
asymptotic properties* (arXiv:2503.05416, fetched to `References/arXiv-2503-05416/`),
open their abstract with, verbatim:

> `In this paper, we prove that the symmetric group $\Sn_n$ has $2^{n^2/16+o(n^2)}$`
> `subgroups, settling a conjecture of Pyber from 1993.`

Their introduction records the attribution and the conjecture, verbatim:

> `Pyber proved in 1993 \cite{PybAnnals}  that for a positive integer $n$, the number`
> `$|\Sub(\Sn_n)|$ of subgroups of $\Sn_n$ is at most $2^{\xi n^2+o(n^2)}$ where`
> `$\xi=\frac{1}{6}\log{24}$ (our logarithms  are to the base $2$).`
> `Pyber conjectured, however, that $|\Sub(\Sn_n)|= 2^{n^2/16+o(n^2)}$.`
> `In this paper, we prove a strong form of Pyber's conjecture.`

and their Theorem 1, verbatim:

> `There exist absolute constants $\alpha > 0$ and $\beta$ such that for all integers`
> `$n > 1$ \[2^{n^2/16+\alpha n\log{n}}  \le |\Sub(\Sn_n)| \le 2^{n^2/16 + \beta n^{3/2}}.\]`

Two notes on the attribution.  (i) `24^(n²/6) = 2^(ξn²)` with `ξ = (log₂ 24)/6`, so the
OEIS `d = 24^(1/6)` and Roney-Dougal–Tracey's `ξ` are the same bound.  (ii) OEIS credits
Pyber with *both* displayed bounds; Roney-Dougal–Tracey credit him only with the upper one
(from the *Annals* paper, not the DIMACS one), the lower bound `2^(n²/16)` being the
elementary count of subgroups of an elementary abelian `2`-subgroup of rank `⌊n/2⌋`.

## What this file asserts, and what it does not

| claim | status in the literature | status in this file |
|---|---|---|
| `c^(n²(1+o(1))) ≤ a(n)`, `c = 2^(1/16)` | proved (elementary) | `PyberLowerBound`, a `Prop`; **not** asserted |
| `a(n) ≤ d^(n²(1+o(1)))`, `d = 24^(1/6)` | proved (Pyber 1993) | `PyberUpperBound`, a `Prop`; **not** asserted |
| `a(n) = c^(n²(1+o(1)))` ("lower bound is accurate") | proved (Roney-Dougal–Tracey 2025) | `pyber_conjecture`, the one `sorry` |
| `2^(n²/16+αn log n) ≤ a(n) ≤ 2^(n²/16+βn^(3/2))` | proved (Roney-Dougal–Tracey 2025, Thm 1) | `RoneyDougalTraceyBound`, a `Prop`; **not** asserted |

Nothing in this file is proved from the literature: the four claims above appear only as
named `Prop`s, and the single `sorry` — `GroupCount.pyber_conjecture` — marks the third of
them as *archived, not formalized*.  It is **not** an open problem; it is a 2025 theorem
that this file does not carry a proof of.  What the file *does* prove, `sorry`-free, is the
reduction `GroupCount.PyberConjecture.of_roneyDougalTracey`: the strong Theorem 1 shape
implies the archived statement.  That is exactly the gap the `sorry` stands for.

## Reading the `o(1)`

`c^(n²(1+o(1))) ≤ a(n)` is rendered as `GroupCount.GrowsAtLeastPow`: there is a function
`e =o[atTop] 1` with `c ^ (n² * (1 + e n)) ≤ a n` eventually — the literal transcription of
the source.  `GroupCount.growsLikePow_iff_isLittleO_log` proves that the two-sided version
`GrowsLikePow b A` is *equivalent* to `log (A n) = n² · log b + o(n²)`, so at `b = c` the
archived statement is exactly `log₂ a(n) = (1/16 + o(1)) · n²`
(`GroupCount.pyberConjecture_iff_isLittleO_log`) — the form Roney-Dougal–Tracey use.  That
equivalence is the statement audit: it is proved here, with no `sorry`, and it pins down
what the `∃ e` encoding means.

## Main definitions

* `GroupCount.numSubgroupsSymm` — A005432, as `Fintype.card (Subgroup (Equiv.Perm (Fin n)))`.
* `GroupCount.pyberC`, `GroupCount.pyberD` — the bases `2^(1/16)` and `24^(1/6)`, pinned by
  `pyberC ^ 16 = 2` and `pyberD ^ 6 = 24`.
* `GroupCount.GrowsAtLeastPow`, `GrowsAtMostPow`, `GrowsLikePow` — the three
  `b^(n²(1+o(1)))` shapes.
* `GroupCount.PyberLowerBound`, `PyberUpperBound`, `PyberConjecture` — the three claims of
  the OEIS comment, as `Prop`s.
* `GroupCount.RoneyDougalTraceyShape`, `RoneyDougalTraceyBound` — Theorem 1 of
  arXiv:2503.05416, as a `Prop` (`n^(3/2)` written `n * √n`, `log` base `2`).

## Main results

* `GroupCount.pyber_conjecture` — **the archived statement; the file's only `sorry`.**
* `GroupCount.PyberConjecture.of_roneyDougalTracey` — the 2025 Theorem 1 shape implies the
  archived statement, so the `sorry` is exactly "Theorem 1 is not formalized here";
  `sorry`-free.
* `GroupCount.exists_roneyDougalTraceyShape` — the Theorem 1 shape is satisfiable (a
  concrete `A` meeting both bounds), so the reduction above is not vacuous; `sorry`-free.
* `GroupCount.growsLikePow_iff_isLittleO_log` — the growth predicate is equivalent to the
  logarithmic form; `sorry`-free.
* `GroupCount.pyberConjecture_iff_isLittleO_log` — its specialization: the archived
  statement says `log a(n) − n²·(log 2)/16 = o(n²)`; `sorry`-free.
* `GroupCount.PyberConjecture.lowerBound`, `.upperBound` — it implies both of the OEIS
  comment's displayed bounds; `sorry`-free.
* `GroupCount.growsLikePow_unique_base` — a sequence cannot grow like two different bases,
  so the archived statement is *not* a consequence of Pyber's window: it singles out `c`;
  `sorry`-free.
* `GroupCount.numSubgroupsSymm_zero/_one/_two`, `numSubgroupsSymm_mono`,
  `numSubgroupsSymm_pos` — the ground-truth and monotonicity layer.

## References

* OEIS A005432 (`oeis show A005432`), quoted verbatim above.
* C. M. Roney-Dougal and G. Tracey, *Subgroups of symmetric groups: enumeration and
  asymptotic properties*, arXiv:2503.05416 — quoted verbatim above from
  `References/arXiv-2503-05416/paper.tex`.  Settles the archived statement.
* L. Pyber, *Enumerating finite groups of a given order*, Ann. of Math. (2) **137** (1993)
  203–220 — cited by Roney-Dougal–Tracey as `[PybAnnals]`, the source of the upper bound.
* L. Pyber, *Asymptotic results for permutation groups*, Groups and Computation, DIMACS
  Ser. Discrete Math. Theoret. Computer Sci. **11** (ed. Finkelstein, L. and Kantor, W. M.,
  Amer. Math. Soc., Providence, 1993) 197–219 — cited by Roney-Dougal–Tracey as `[Pyber]`.

No part of any of these papers is formalized here.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace GroupCount

/-! ## The counting function `numSubgroupsSymm` (A005432) -/

/-- **A005432**: the number of subgroups of the symmetric group `Sₙ`, conjugates counted as
distinct.  `Subgroup G` is the type of *all* subgroups of `G`, so its cardinality counts
distinct subgroups, exactly as the OEIS name asks.  `noncomputable` because the only
`Fintype (Subgroup G)` instance Mathlib carries (`SetLike.instFintype`) is noncomputable;
the *value* is instance-independent, `Fintype` being a subsingleton. -/
noncomputable def numSubgroupsSymm (n : ℕ) : ℕ :=
  Fintype.card (Subgroup (Equiv.Perm (Fin n)))

/-- The count is never zero: `⊥` is a subgroup of every group.  This is what keeps the
logarithmic form of the growth statements off the junk value `Real.log 0 = 0`. -/
theorem numSubgroupsSymm_pos (n : ℕ) : 0 < numSubgroupsSymm n :=
  Fintype.card_pos_iff.mpr ⟨⊥⟩

/-- `a(n) = 1` for `n ≤ 1`: `S₀` and `S₁` are trivial (`0! = 1! = 1`), so `⊥ = ⊤` is the only
subgroup.  Phrased with the hypothesis `n ≤ 1` rather than
`Subsingleton (Equiv.Perm (Fin n))` on purpose: the latter is a class, hence a local
instance, and it makes Lean synthesize `Unique.fintype` for `Fintype (Subgroup Sₙ)` where the
definition of `numSubgroupsSymm` uses `SetLike.instFintype` — propositionally the same
instance, but not one that unifies. -/
theorem numSubgroupsSymm_of_le_one {n : ℕ} (hn : n ≤ 1) : numSubgroupsSymm n = 1 := by
  rw [numSubgroupsSymm, Fintype.card_eq_one_iff]
  haveI : Subsingleton (Equiv.Perm (Fin n)) := by
    refine Fintype.card_le_one_iff_subsingleton.mp ?_
    rw [Fintype.card_perm, Fintype.card_fin]
    interval_cases n <;> decide
  exact ⟨⊥, fun H => Subsingleton.elim H ⊥⟩

/-- A group of order two has exactly two subgroups, `⊥` and `⊤`: a subgroup has order
dividing `2` by Lagrange, order `1` forces `⊥` and order `2` forces `⊤`. -/
theorem card_subgroup_of_card_eq_two {G : Type*} [Group G] [Fintype G] [Fintype (Subgroup G)]
    (h : Fintype.card G = 2) : Fintype.card (Subgroup G) = 2 := by
  classical
  have hnat : Nat.card G = 2 := by rw [Nat.card_eq_fintype_card, h]
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : IsSimpleOrder (Subgroup G) := by
    refine ⟨fun H => ?_⟩
    have hdvd : Nat.card H ∣ 2 := hnat ▸ H.card_subgroup_dvd_card
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact Or.inl (Subgroup.card_eq_one.mp h1)
    · exact Or.inr (Subgroup.eq_top_of_card_eq H (by rw [h2, hnat]))
  exact (Fintype.card_congr (IsSimpleOrder.equivBool (α := Subgroup G))).trans Fintype.card_bool

/-- `a(0) = 1` — `S₀` is trivial, so `⊥ = ⊤` is its only subgroup. -/
theorem numSubgroupsSymm_zero : numSubgroupsSymm 0 = 1 := numSubgroupsSymm_of_le_one (by omega)

/-- `a(1) = 1` — `S₁` is trivial. -/
theorem numSubgroupsSymm_one : numSubgroupsSymm 1 = 1 := numSubgroupsSymm_of_le_one (by omega)

/-- `a(2) = 2` — `S₂` has order `2`, hence exactly the two subgroups `⊥` and `⊤`.  This is
the first *nondegenerate* term: it is not the collapsed value `1`. -/
theorem numSubgroupsSymm_two : numSubgroupsSymm 2 = 2 := by
  rw [numSubgroupsSymm]
  exact card_subgroup_of_card_eq_two (by rw [Fintype.card_perm, Fintype.card_fin]; decide)

/-- **A005432 is monotone.**  For `m ≤ n` the embedding `Fin m ↪ Fin n` induces an injective
homomorphism `Sₘ →* Sₙ` (`Equiv.Perm.viaEmbeddingHom`), and pushing subgroups forward along
an injective homomorphism is injective on subgroups. -/
theorem numSubgroupsSymm_mono : Monotone numSubgroupsSymm := fun _ _ hmn =>
  Fintype.card_le_of_injective (Subgroup.map (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hmn)))
    (Subgroup.map_injective (Equiv.Perm.viaEmbeddingHom_injective _))

/-! ## The two bases of Pyber's window -/

/-- Pyber's lower-bound base `c = 2^(1/16)`, pinned by `pyberC ^ 16 = 2`. -/
noncomputable def pyberC : ℝ := (2 : ℝ) ^ (1 / 16 : ℝ)

/-- Pyber's upper-bound base `d = 24^(1/6)`, pinned by `pyberD ^ 6 = 24`. -/
noncomputable def pyberD : ℝ := (24 : ℝ) ^ (1 / 6 : ℝ)

/-- Ground truth for `pyberC`: it is the real sixteenth root of `2`. -/
theorem pyberC_pow_sixteen : pyberC ^ (16 : ℕ) = 2 := by
  rw [pyberC, ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 16 : ℝ)) 16,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Ground truth for `pyberD`: it is the real sixth root of `24`. -/
theorem pyberD_pow_six : pyberD ^ (6 : ℕ) = 24 := by
  rw [pyberD, ← Real.rpow_natCast ((24 : ℝ) ^ (1 / 6 : ℝ)) 6,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
  norm_num

/-- `0 < c`. -/
theorem pyberC_pos : 0 < pyberC := Real.rpow_pos_of_pos (by norm_num) _

/-- `0 < d`. -/
theorem pyberD_pos : 0 < pyberD := Real.rpow_pos_of_pos (by norm_num) _

/-- `1 < c`: the window's lower base is a genuine growth rate, not a collapse to `1`. -/
theorem one_lt_pyberC : 1 < pyberC :=
  Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by norm_num⟩)

/-- `1 < d`. -/
theorem one_lt_pyberD : 1 < pyberD :=
  Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by norm_num⟩)

/-- **Pyber's window is not degenerate**: `c < d`, so his lower and upper bounds are
genuinely different growth rates and "the lower bound is accurate" has content. -/
theorem pyberC_lt_pyberD : pyberC < pyberD := by
  have h1 : (2 : ℝ) ^ (1 / 16 : ℝ) < (2 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr (by norm_num)
  have h2 : (2 : ℝ) ^ (1 / 6 : ℝ) < (24 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  exact lt_trans h1 h2

/-! ## The `b ^ (n² (1 + o(1)))` growth shapes

These transcribe the source's `c^(n^2(1+o(1))) <= a(n) <= d^(n^2(1+o(1)))` literally: the
`o(1)` is an existentially quantified `e =o[atTop] 1` sitting inside the exponent, and the
inequality holds eventually.  `GroupCount.growsLikePow_iff_isLittleO_log` certifies that the
encoding means what it should. -/

/-- `A n` is eventually at least `b ^ (n² (1 + o(1)))`.  Equivalently (for `1 < b` and
eventually positive `A`) `log b ≤ liminf (log (A n) / n²)`. -/
def GrowsAtLeastPow (b : ℝ) (A : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ, e =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, b ^ ((n : ℝ) ^ 2 * (1 + e n)) ≤ A n

/-- `A n` is eventually at most `b ^ (n² (1 + o(1)))`. -/
def GrowsAtMostPow (b : ℝ) (A : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ, e =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, A n ≤ b ^ ((n : ℝ) ^ 2 * (1 + e n))

/-- `A n = b ^ (n² (1 + o(1)))`: the two-sided version, i.e. `b` is exactly the growth rate.
This is the shape of the OEIS phrase "conjectures lower bound is accurate". -/
def GrowsLikePow (b : ℝ) (A : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ, e =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, A n = b ^ ((n : ℝ) ^ 2 * (1 + e n))

/-- Growing exactly like `b` is in particular growing at least like `b`. -/
theorem GrowsLikePow.growsAtLeastPow {b : ℝ} {A : ℕ → ℝ} (h : GrowsLikePow b A) :
    GrowsAtLeastPow b A := by
  obtain ⟨e, he, hev⟩ := h
  exact ⟨e, he, hev.mono fun _ hn => le_of_eq hn.symm⟩

/-- Growing exactly like `b` is in particular growing at most like `b`. -/
theorem GrowsLikePow.growsAtMostPow {b : ℝ} {A : ℕ → ℝ} (h : GrowsLikePow b A) :
    GrowsAtMostPow b A := by
  obtain ⟨e, he, hev⟩ := h
  exact ⟨e, he, hev.mono fun _ hn => le_of_eq hn⟩

/-- A larger base gives a weaker upper bound: growing at most like `b` implies growing at
most like any `b' ≥ b`.  (This is what makes Pyber's upper bound a consequence of his
conjecture, since `pyberC < pyberD`.) -/
theorem GrowsAtMostPow.mono_base {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') {A : ℕ → ℝ}
    (h : GrowsAtMostPow b A) : GrowsAtMostPow b' A := by
  obtain ⟨e, he, hev⟩ := h
  refine ⟨e, he, ?_⟩
  have hpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ 1 + e n := by
    have htend : Tendsto e atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp he
    filter_upwards [htend.eventually_const_lt (show (-1 : ℝ) < 0 by norm_num)] with n hn
    linarith
  filter_upwards [hev, hpos] with n hn hn'
  exact hn.trans (Real.rpow_le_rpow hb hbb (mul_nonneg (by positivity) hn'))

/-! ## The statement audit: the growth shape is the logarithmic one -/

/-- **`GrowsLikePow` says what it looks like it says.**  For a base `1 < b` and an eventually
positive `A`, `A n = b ^ (n² (1 + o(1)))` is *equivalent* to `log (A n) = n² · log b + o(n²)`.

This is the file's statement audit: it fixes the meaning of the `∃ e =o[atTop] 1` encoding,
and it is proved here with no `sorry`. -/
theorem growsLikePow_iff_isLittleO_log {b : ℝ} (hb : 1 < b) {A : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, 0 < A n) :
    GrowsLikePow b A ↔
      (fun n : ℕ => Real.log (A n) - (n : ℝ) ^ 2 * Real.log b) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hlogb : 0 < Real.log b := Real.log_pos hb
  constructor
  · rintro ⟨e, he, hev⟩
    have hbig : (fun n : ℕ => Real.log b * (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ => (n : ℝ) ^ 2) :=
      (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).const_mul_left (Real.log b)
    have hmul := hbig.mul_isLittleO he
    have hsimp : (fun n : ℕ => Real.log b * (n : ℝ) ^ 2 * e n) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) := by
      refine hmul.congr' (Filter.EventuallyEq.refl _ _) ?_
      filter_upwards with n
      exact mul_one _
    refine hsimp.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hev] with n hn
    rw [hn, Real.log_rpow hb0]
    ring
  · intro hlittle
    refine ⟨fun n => (Real.log (A n) - (n : ℝ) ^ 2 * Real.log b) / (n : ℝ) ^ 2 / Real.log b,
      ?_, ?_⟩
    · refine (Asymptotics.isLittleO_one_iff ℝ).mpr ?_
      have hdiv : Tendsto
          (fun n : ℕ => (Real.log (A n) - (n : ℝ) ^ 2 * Real.log b) / (n : ℝ) ^ 2)
          atTop (𝓝 0) := hlittle.tendsto_div_nhds_zero
      simpa using hdiv.div_const (Real.log b)
    · filter_upwards [hA, eventually_ge_atTop 1] with n hAn hn1
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hne : ((n : ℝ) ^ 2) ≠ 0 := by positivity
      have hkey : Real.log b * ((n : ℝ) ^ 2 *
          (1 + (Real.log (A n) - (n : ℝ) ^ 2 * Real.log b) / (n : ℝ) ^ 2 / Real.log b)) =
          Real.log (A n) := by
        field_simp
        ring
      rw [Real.rpow_def_of_pos hb0, hkey, Real.exp_log hAn]

/-! ## The three claims of the OEIS comment -/

/-- **The OEIS comment's lower bound**, `c^(n²(1+o(1))) ≤ a(n)` with `c = 2^(1/16)`.
A theorem of the literature (the elementary count of subgroups of an elementary abelian
`2`-subgroup of rank `⌊n/2⌋`); *not* proved in this file, which asserts nothing about it. -/
def PyberLowerBound : Prop :=
  GrowsAtLeastPow pyberC (fun n => (numSubgroupsSymm n : ℝ))

/-- **Pyber's upper bound**, `a(n) ≤ d^(n²(1+o(1)))` with `d = 24^(1/6)`, i.e.
`2^(ξn² + o(n²))` with `ξ = (log₂ 24)/6`.  A theorem of the literature (Pyber 1993); *not*
proved in this file, which asserts nothing about it. -/
def PyberUpperBound : Prop :=
  GrowsAtMostPow pyberD (fun n => (numSubgroupsSymm n : ℝ))

/-- **"Conjectures lower bound is accurate"**: `a(n) = c^(n²(1+o(1)))` with `c = 2^(1/16)`;
equivalently `log₂ a(n) = (1/16 + o(1)) n²`
(`GroupCount.pyberConjecture_iff_isLittleO_log`).  Conjectured by Pyber in 1993 and
**proved** by Roney-Dougal and Tracey in 2025; not formalized here. -/
def PyberConjecture : Prop :=
  GrowsLikePow pyberC (fun n => (numSubgroupsSymm n : ℝ))

/-- The logarithm of `pyberC` is `(log 2)/16`. -/
theorem log_pyberC : Real.log pyberC = Real.log 2 / 16 := by
  rw [pyberC, Real.log_rpow (by norm_num)]
  ring

/-- **The archived statement, in logarithmic form.**  `PyberConjecture` is exactly
`log a(n) − n²·(log 2)/16 = o(n²)`, i.e. `log₂ a(n) = (1/16 + o(1)) · n²` — the form used in
the literature.  `sorry`-free: this is the audit of the archived statement, not part of it. -/
theorem pyberConjecture_iff_isLittleO_log :
    PyberConjecture ↔
      (fun n : ℕ => Real.log (numSubgroupsSymm n) - (n : ℝ) ^ 2 * (Real.log 2 / 16))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  have hpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (numSubgroupsSymm n : ℝ) :=
    Filter.Eventually.of_forall fun n => by exact_mod_cast numSubgroupsSymm_pos n
  rw [PyberConjecture, growsLikePow_iff_isLittleO_log one_lt_pyberC hpos, log_pyberC]

/-! ## The archived statement -/

/-- **The A005432 growth rate — archived, not proved here.**  The OEIS comment reads

> `L. Pyber shows c^(n^2(1+o(1))) <= a(n) <= d^(n^2(1+o(1))), c=2^(1/16), d=24^(1/6);`
> `conjectures lower bound is accurate.`

and this declaration archives the last clause: the number of subgroups of `Sₙ` is
`2^((1/16 + o(1)) n²)`.  **This is not an open problem.**  Pyber conjectured it in 1993;
Roney-Dougal and Tracey proved it in 2025 (arXiv:2503.05416, Theorem 1), in the stronger
form recorded as `GroupCount.RoneyDougalTraceyBound`.  The `sorry` records that their proof
is not formalized here — and `GroupCount.PyberConjecture.of_roneyDougalTracey` shows that
formalizing Theorem 1 would discharge it.  This is the only `sorry` in the file. -/
theorem pyber_conjecture : PyberConjecture := by
  sorry

/-- The archived statement implies the OEIS comment's lower bound: it is a genuine
strengthening of it, not a restatement. -/
theorem PyberConjecture.lowerBound (h : PyberConjecture) : PyberLowerBound :=
  GrowsLikePow.growsAtLeastPow h

/-- The archived statement implies Pyber's upper bound as well, because `pyberC < pyberD`.
So it is consistent with the whole of the quoted comment. -/
theorem PyberConjecture.upperBound (h : PyberConjecture) : PyberUpperBound :=
  GrowsAtMostPow.mono_base pyberC_pos.le pyberC_lt_pyberD.le (GrowsLikePow.growsAtMostPow h)

/-! ## The 2025 resolution, and the reduction it supplies

Theorem 1 of Roney-Dougal–Tracey is transcribed as `RoneyDougalTraceyShape` (with `n^(3/2)`
written `n * √n` and `log` at base `2`, as their convention states).  It is not proved here,
but the reduction from it to the archived statement *is*, together with a satisfiability
witness for its shape so that the reduction is demonstrably not vacuous. -/

/-- `n · √n = o(n²)`, the reason the Theorem 1 error term is absorbed by `o(n²)`. -/
theorem isLittleO_mul_sqrt_sq :
    (fun n : ℕ => (n : ℝ) * Real.sqrt n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine (Asymptotics.isLittleO_iff_tendsto ?_).mpr ?_
  · intro n hn
    have hz : (n : ℝ) = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hn
    rw [hz, zero_mul]
  · refine Filter.Tendsto.congr' ?_ hsqrt.inv_tendsto_atTop
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by linarith)
    simp only [Pi.inv_apply]
    field_simp
    nlinarith [hsq]

/-- `log x ≤ 2√x`, from `log t ≤ t − 1` at `t = √x`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h1
  linarith

/-- `log₂ x ≤ 4√x`; the constant is slack (`2/log 2 ≈ 2.89`) and only has to be explicit. -/
theorem logb_le_four_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 4 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmain : Real.log x ≤ 2 * Real.sqrt x := log_le_two_mul_sqrt hx
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- **Theorem 1 of arXiv:2503.05416**, as a shape for an arbitrary counting function:
there are absolute constants `α > 0` and `β` with
`2^(n²/16 + α n log₂ n) ≤ A n ≤ 2^(n²/16 + β n^(3/2))` for every `n > 1`.  Here `n^(3/2)` is
written `n * √n`, and `log` is base `2` as the paper's convention states. -/
def RoneyDougalTraceyShape (A : ℕ → ℕ) : Prop :=
  ∃ α β : ℝ, 0 < α ∧ ∀ n : ℕ, 1 < n →
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) ≤ (A n : ℝ) ∧
      (A n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + β * n * Real.sqrt n)

/-- **Theorem 1 of arXiv:2503.05416** at A005432 itself.  A theorem of the literature; *not*
proved in this file, which asserts nothing about it. -/
def RoneyDougalTraceyBound : Prop := RoneyDougalTraceyShape numSubgroupsSymm

/-- **Satisfiability of the Theorem 1 shape** (STYLE.md).  Both hypotheses of
`GroupCount.isLittleO_log_of_roneyDougalTraceyShape` — positivity and the shape — hold
jointly at the concrete model `A n = 2 ^ ⌈n²/16 + n√n⌉`, with `α = 1/4` and `β = 2`.  So the
reduction below is not an implication out of a contradiction. -/
theorem exists_roneyDougalTraceyShape :
    ∃ A : ℕ → ℕ, (∀ n, 0 < A n) ∧ RoneyDougalTraceyShape A := by
  refine ⟨fun n => 2 ^ ⌈(n : ℝ) ^ 2 / 16 + (n : ℝ) * Real.sqrt n⌉₊,
    fun _ => pow_pos (by norm_num) _, 1 / 4, 2, by norm_num, fun n hn => ?_⟩
  set m : ℕ := ⌈(n : ℝ) ^ 2 / 16 + (n : ℝ) * Real.sqrt n⌉₊ with hm
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ ((m : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 16 + (n : ℝ) * Real.sqrt n := by positivity
  have hlow : (n : ℝ) ^ 2 / 16 + (n : ℝ) * Real.sqrt n ≤ (m : ℝ) := Nat.le_ceil _
  have hhigh : (m : ℝ) < (n : ℝ) ^ 2 / 16 + (n : ℝ) * Real.sqrt n + 1 := Nat.ceil_lt_add_one hx0
  have hlogb : Real.logb 2 (n : ℝ) ≤ 4 * Real.sqrt n := logb_le_four_mul_sqrt hn0
  refine ⟨?_, ?_⟩
  · rw [hcast, Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    nlinarith
  · rw [hcast, Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    nlinarith

/-- **The Theorem 1 shape gives the `o(n²)` logarithmic form.**  Both error terms
`α n log₂ n` and `β n^(3/2)` are `o(n²)`, so `log (A n) − n²·(log 2)/16 = o(n²)`. -/
theorem isLittleO_log_of_roneyDougalTraceyShape {A : ℕ → ℕ} (hApos : ∀ n, 0 < A n)
    (h : RoneyDougalTraceyShape A) :
    (fun n : ℕ => Real.log (A n) - (n : ℝ) ^ 2 * (Real.log 2 / 16)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2) := by
  obtain ⟨α, β, hα, hb⟩ := h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Asymptotics.IsBigO.trans_isLittleO ?_ isLittleO_mul_sqrt_sq
  refine Asymptotics.IsBigO.of_bound |β * Real.log 2| ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨hlo, hhi⟩ := hb n (by omega)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAR : (0 : ℝ) < (A n : ℝ) := by exact_mod_cast hApos n
  have hlogb : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
  have hL : ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) * Real.log 2 ≤ Real.log (A n) := by
    have hstep := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hlo
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hstep
  have hU : Real.log (A n) ≤ ((n : ℝ) ^ 2 / 16 + β * n * Real.sqrt n) * Real.log 2 := by
    have hstep := Real.log_le_log hAR hhi
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hstep
  have hexpL : ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) * Real.log 2
      = (n : ℝ) ^ 2 * (Real.log 2 / 16) + (α * n * Real.logb 2 n) * Real.log 2 := by ring
  have hexpU : ((n : ℝ) ^ 2 / 16 + β * n * Real.sqrt n) * Real.log 2
      = (n : ℝ) ^ 2 * (Real.log 2 / 16) + (β * Real.log 2) * ((n : ℝ) * Real.sqrt n) := by ring
  rw [hexpL] at hL
  rw [hexpU] at hU
  have hprod : 0 ≤ (α * n * Real.logb 2 n) * Real.log 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hα.le (by positivity)) hlogb) hlog2.le
  have hgnn : 0 ≤ Real.log (A n) - (n : ℝ) ^ 2 * (Real.log 2 / 16) := by linarith
  have hns : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgnn, abs_of_nonneg hns]
  calc Real.log (A n) - (n : ℝ) ^ 2 * (Real.log 2 / 16)
      ≤ (β * Real.log 2) * ((n : ℝ) * Real.sqrt n) := by linarith
    _ ≤ |β * Real.log 2| * ((n : ℝ) * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hns

/-- **The 2025 theorem discharges the archived statement.**  This is the precise content of
the `sorry` in `GroupCount.pyber_conjecture`: formalizing Theorem 1 of arXiv:2503.05416
would remove it.  `sorry`-free. -/
theorem PyberConjecture.of_roneyDougalTracey (h : RoneyDougalTraceyBound) : PyberConjecture :=
  pyberConjecture_iff_isLittleO_log.mpr
    (isLittleO_log_of_roneyDougalTraceyShape numSubgroupsSymm_pos h)

/-! ## Non-degeneracy of the archived statement

Three checks that `PyberConjecture` is neither vacuous nor free: the shape is satisfiable at
a concrete model, it is refutable at another, and it pins the base — so it does **not**
follow from Pyber's window. -/

/-- The exact power `b ^ (n²)` grows like `b`, with the `o(1)` witnessed by the zero function.
This is the seed of the satisfiability witnesses below. -/
theorem growsLikePow_rpow_sq (b : ℝ) :
    GrowsLikePow b (fun n : ℕ => b ^ ((n : ℝ) ^ 2)) :=
  ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _,
    Filter.Eventually.of_forall fun n => by rw [add_zero, mul_one]⟩

/-- **Joint satisfiability** (STYLE.md): at the single concrete model `A n = c^(n²)`, all
three claims of the OEIS comment hold simultaneously.  So the triple of statements is not
contradictory, and neither is the archived statement in the presence of the two bounds. -/
theorem exists_model_of_pyber_shape :
    ∃ A : ℕ → ℝ, GrowsAtLeastPow pyberC A ∧ GrowsAtMostPow pyberD A ∧ GrowsLikePow pyberC A := by
  refine ⟨fun n : ℕ => pyberC ^ ((n : ℝ) ^ 2), ?_, ?_, growsLikePow_rpow_sq pyberC⟩
  · exact GrowsLikePow.growsAtLeastPow (growsLikePow_rpow_sq pyberC)
  · exact GrowsAtMostPow.mono_base pyberC_pos.le pyberC_lt_pyberD.le
      (GrowsLikePow.growsAtMostPow (growsLikePow_rpow_sq pyberC))

/-- **The growth shape is refutable**: a bounded sequence does not grow at least like any
base `1 < b`.  So `GrowsAtLeastPow` — and hence `PyberConjecture`, which implies it — is not
satisfied by everything. -/
theorem not_growsAtLeastPow_const {b : ℝ} (hb : 1 < b) (c : ℝ) (hc : c ≤ 1) :
    ¬ GrowsAtLeastPow b (fun _ => c) := by
  rintro ⟨e, he, hev⟩
  have htend : Tendsto e atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp he
  obtain ⟨n, ⟨hn, hen⟩, hn2⟩ :=
    ((hev.and (htend.eventually_const_lt (show (-1 : ℝ) / 2 < 0 by norm_num))).and
      (eventually_ge_atTop 2)).exists
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 + e n := by linarith
  have hlt : (1 : ℝ) < b ^ ((n : ℝ) ^ 2 * (1 + e n)) :=
    Real.one_lt_rpow_iff_of_pos (lt_trans zero_lt_one hb) |>.mpr
      (Or.inl ⟨hb, mul_pos hsq hpos⟩)
  linarith

/-- **The base is pinned**: an eventually positive sequence cannot grow like two different
bases.  Consequently `PyberConjecture` does *not* follow from Pyber's two bounds — those
leave the whole window `[c, d]` open, while the archived statement selects `c`. -/
theorem growsLikePow_unique_base {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b') {A : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, 0 < A n) (h : GrowsLikePow b A) (h' : GrowsLikePow b' A) : b = b' := by
  -- The logarithmic form says `log (A n) / n² → log β`; a limit is unique.
  have key : ∀ β : ℝ,
      (fun n : ℕ => Real.log (A n) - (n : ℝ) ^ 2 * Real.log β) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) →
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ) ^ 2) atTop (𝓝 (Real.log β)) := by
    intro β hlo
    have h0 : Tendsto
        (fun n : ℕ => (Real.log (A n) - (n : ℝ) ^ 2 * Real.log β) / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      hlo.tendsto_div_nhds_zero
    have h1 := h0.add_const (Real.log β)
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hne : ((n : ℝ) ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hlog : Real.log b = Real.log b' :=
    tendsto_nhds_unique (key b ((growsLikePow_iff_isLittleO_log hb hA).mp h))
      (key b' ((growsLikePow_iff_isLittleO_log hb' hA).mp h'))
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (lt_trans zero_lt_one hb))
    (Set.mem_Ioi.mpr (lt_trans zero_lt_one hb')) hlog

/-! ## Axiom audit

Every declaration in this file rests only on `{propext, Classical.choice, Quot.sound}` with
exactly one exception: `GroupCount.pyber_conjecture`, which also carries `sorryAx`.  That is
the archived statement, and it is the only `sorry` here.  Nothing else consumes it —
`PyberConjecture.lowerBound`, `.upperBound` and `.of_roneyDougalTracey` take the statement as
a *hypothesis*, so they stay `sorryAx`-free.  There is no `native_decide` in this file. -/

#print axioms numSubgroupsSymm
#print axioms numSubgroupsSymm_pos
#print axioms numSubgroupsSymm_of_le_one
#print axioms card_subgroup_of_card_eq_two
#print axioms numSubgroupsSymm_zero
#print axioms numSubgroupsSymm_one
#print axioms numSubgroupsSymm_two
#print axioms numSubgroupsSymm_mono
#print axioms pyberC
#print axioms pyberD
#print axioms pyberC_pow_sixteen
#print axioms pyberD_pow_six
#print axioms pyberC_pos
#print axioms pyberD_pos
#print axioms one_lt_pyberC
#print axioms one_lt_pyberD
#print axioms pyberC_lt_pyberD
#print axioms GrowsAtLeastPow
#print axioms GrowsAtMostPow
#print axioms GrowsLikePow
#print axioms GrowsLikePow.growsAtLeastPow
#print axioms GrowsLikePow.growsAtMostPow
#print axioms GrowsAtMostPow.mono_base
#print axioms growsLikePow_iff_isLittleO_log
#print axioms PyberLowerBound
#print axioms PyberUpperBound
#print axioms PyberConjecture
#print axioms log_pyberC
#print axioms pyberConjecture_iff_isLittleO_log
#print axioms pyber_conjecture
#print axioms PyberConjecture.lowerBound
#print axioms PyberConjecture.upperBound
#print axioms isLittleO_mul_sqrt_sq
#print axioms log_le_two_mul_sqrt
#print axioms logb_le_four_mul_sqrt
#print axioms RoneyDougalTraceyShape
#print axioms RoneyDougalTraceyBound
#print axioms exists_roneyDougalTraceyShape
#print axioms isLittleO_log_of_roneyDougalTraceyShape
#print axioms PyberConjecture.of_roneyDougalTracey
#print axioms growsLikePow_rpow_sq
#print axioms exists_model_of_pyber_shape
#print axioms not_growsAtLeastPow_const
#print axioms growsLikePow_unique_base

end GroupCount
