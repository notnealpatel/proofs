/-
  Erdős Problem #688 — sieving [1, n] by congruences with large prime
  moduli.
  Status: open.  Tier UC lemma mine (interval-covering certificates).

  Verbatim statement (`goof erdos fetch 688`, pulled 2026-08-05):

    "Define $\epsilon_n$ to be maximal such that there exists some
    choice of congruence class $a_p$ for all primes
    $n^{\epsilon_n}<p\leq n$ such that every integer in $[1,n]$
    satisfies at least one of the congruences $\equiv a_p\pmod{p}$.

    Estimate $\epsilon_n$ - in particular is it true that
    $\epsilon_n=o(1)?$"

  DB remarks: Erdős: ε_n ≫ log log log n / log log n.  Cluster with
  #687, #689, #1200.

  Formalization: the real-exponent threshold `n^ε` is clumsy in ℕ;
  we parametrize by the integer cutoff `T` instead — `CoversWith n T`
  says the primes in `(T, n]` admit residues covering `[1, n]` — and
  express ε_n-statements through the least admissible `T`.

  Repo adjacency: same verification shape as `Erdos.Covering`
  (interval coverage instead of full residue coverage) — certified
  lower-bound data points are the lane.

  Mathlib inventory: `Nat.ModEq`, `Finset.filter Nat.Prime`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E688

/-- `CoversWith n T`: there is a choice of residue `a p` for each
    prime `p ∈ (T, n]` such that every `m ∈ [1, n]` satisfies
    `m ≡ a p (mod p)` for some such prime. -/
def CoversWith (n T : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
    ∃ p ∈ (Finset.Icc (T + 1) n).filter Nat.Prime, m % p = a p % p

/-- The interval `[1, 12]` is covered by the primes `2, 3, 5, 7, 11`,
    with residues `0, 0, 1, 0, 5` respectively. The witnesses for
    `m = 1, …, 12` are `5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2`. -/
theorem coversWith_twelve_one : CoversWith 12 1 := by
  let a : ℕ → ℕ := fun p => if p = 5 then 1 else if p = 11 then 5 else 0
  have hpool : (Finset.Icc (1 + 1) 12).filter Nat.Prime =
      ({2, 3, 5, 7, 11} : Finset ℕ) := by decide
  have hcert : ∀ m : Fin 13, 1 ≤ m.val →
      ∃ p : Fin 13, p.val ∈ ({2, 3, 5, 7, 11} : Finset ℕ) ∧
        m.val % p.val = a p.val % p.val := by decide
  refine ⟨a, ?_⟩
  intro m hm
  rcases Finset.mem_Icc.mp hm with ⟨hmLower, hmUpper⟩
  let mFin : Fin 13 := ⟨m, Nat.lt_succ_of_le hmUpper⟩
  rcases hcert mFin hmLower with ⟨p, hp, heq⟩
  refine ⟨p.val, ?_, heq⟩
  rw [hpool]
  exact hp

/-- Ground truth probe shape: with `T = 1` (all primes `≤ n`
    available, including 2 and 3) covering `[1, 12]` is easy —
    e.g. a₂ = 0 (evens), a₃ = 1 ({1,4,7,10}), a₅ = 3 ({3}), a₇ = 5
    ({5}), a₁₁ = 9 ({9}), leaving 11 ← a₁₁… probe carefully; recorded
    as the satisfiability stub.  -- PROVABLE (decide once a concrete
    residue table is pinned; the table above needs re-checking —
    that is exactly what the stub is for). -/
example : CoversWith 12 1 := by
  exact coversWith_twelve_one

/-- Monotonicity in `T` (smaller cutoff = more primes = easier):
    `CoversWith n T'` implies `CoversWith n T` for `T ≤ T'`.
    -- PROVABLE (weaken the prime pool; effort S). -/
theorem coversWith_mono (n T T' : ℕ) (hTT : T ≤ T')
    (h : CoversWith n T') : CoversWith n T := by
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro m hm
  rcases ha m hm with ⟨p, hp, heq⟩
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hpLower, hpUpper⟩
  have hpLower' : T + 1 ≤ p :=
    (Nat.add_le_add_right hTT 1).trans hpLower
  exact ⟨p, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpLower', hpUpper⟩, hpPrime⟩, heq⟩

/-- `minCutoff n`: the largest admissible cutoff — we track
    `sSup {T | CoversWith n T}`; `ε_n = log(minCutoff n)/log n` in
    the problem's normalization.  (T = 0 always works for n ≥ 1?
    No — coverage with all primes ≤ n is itself nontrivial for the
    m = 1 case… 1 % p = a p % p requires choosing a p ≡ 1 for some p;
    fine.  sSup honesty: the set is bounded by n.) -/
noncomputable def maxCutoff (n : ℕ) : ℕ := sSup {T : ℕ | CoversWith n T}

/-- **Erdős's lower bound** (DB): ε_n ≫ log log log n / log log n —
    in cutoff form: `maxCutoff n ≥ n^{c·lll n/ll n}` for some
    `c > 0` and large n.  Archived (the construction is a
    Rankin-style sieve). -/
theorem erdos_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (c * Real.log (Real.log (Real.log n)) /
        Real.log (Real.log n)) ≤ (maxCutoff n : ℝ) := by
  sorry

/-- **Erdős #688, headline (OPEN)**: `ε_n = o(1)` — in cutoff form:
    for every `δ > 0`, eventually `maxCutoff n < n^δ` — every
    covering must use some prime below `n^δ`. -/
theorem erdos_688 (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (maxCutoff n : ℝ) < (n : ℝ) ^ δ := by
  sorry

/-! ### Refutation of the `[1, 30]` certificate lane

Original (false) declaration, retained for the record:

```
/-- Certificate lane: a concrete covering of `[1, 30]` using only
    primes in `(2, 30]` (no modulus 2) — a genuinely nontrivial
    interval-covering certificate; probe with sage for the residue
    table, then `decide`.  Yields the data point
    `maxCutoff 30 ≥ 2`.  -- PROVABLE-in-principle (decide). -/
theorem cutoff_30_ge_2 : CoversWith 30 2 := by
  sorry
```

The claim is false.  Kernel-checked argument (`search` below): every
residue class mod `3` meets `[1, 30]` in exactly `10` points, so
whichever class `a₃` is chosen, `20` points remain for the primes
`5, 7, …, 29`.  In each of the three cases the largest class of each
remaining prime meets those `20` points in at most
`4, 4, 2, 2, 2, 2, 2, 1` (for `a₃ ≡ 0, 1`) or `4, 3, 2, 2, 2, 2, 2, 2`
(for `a₃ ≡ 2`) points, i.e. `19 < 20` in total. -/

/-- `classCount U p r`: the number of entries `x` of `U` with
    `x % p = r`. -/
def classCount (U : List ℕ) (p r : ℕ) : ℕ := U.countP fun x => x % p == r

example : classCount [1, 2, 3, 4, 5] 2 1 = 3 := rfl
example : classCount [1, 2, 3, 4, 5] 3 0 = 1 := rfl

/-- `maxClass U p`: the largest number of entries of `U` lying in a
    single residue class mod `p` (`0` when `U` is empty). -/
def maxClass (U : List ℕ) (p : ℕ) : ℕ :=
  (U.map fun x => classCount U p (x % p)).foldr max 0

example : maxClass [1, 2, 3, 4, 5] 2 = 3 := rfl
example : maxClass [1, 2, 3, 4, 5] 7 = 1 := rfl
example : maxClass [] 7 = 0 := rfl

/-- `capSum U ps`: the sum over `p ∈ ps` of `maxClass U p`, an upper
    bound on how many entries of `U` one class per prime can cover. -/
def capSum (U ps : List ℕ) : ℕ := (ps.map (maxClass U)).sum

example : capSum [1, 2, 3, 4, 5] [2, 3] = 5 := rfl

/-- `search ps U`: a branch-and-bound test returning `true` whenever one
    residue class per modulus in `ps` can cover every entry of `U`
    (completeness is `search_complete`).  At each modulus `p` it prunes
    when `U.length > capSum U (p :: ps)`, and otherwise branches over
    leaving `U` unchanged or removing the class of some `x ∈ U`. -/
def search : List ℕ → List ℕ → Bool
  | [], U => U.isEmpty
  | p :: ps, U =>
    decide (U.length ≤ capSum U (p :: ps)) &&
      (search ps U || (U.map (· % p)).any fun r =>
        search ps (U.filter fun x => x % p != r))

example : search [2, 3] [1, 2, 3, 5] = true := by decide
example : search [2, 3] [1, 2, 3, 4] = false := by decide
example : search [3] [1, 2] = false := by decide

/-- Every entry of a list of naturals is at most its `foldr max 0`. -/
theorem le_foldr_max {l : List ℕ} {y : ℕ} (hy : y ∈ l) : y ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hy
  | cons z l ih =>
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

/-- A residue class mod `p` contains at most `maxClass U p` entries
    of `U`. -/
theorem countP_le_maxClass (U : List ℕ) (p c : ℕ) :
    U.countP (fun x => x % p == c % p) ≤ maxClass U p := by
  by_cases hx : ∃ x ∈ U, x % p = c % p
  · obtain ⟨x, hxU, hxc⟩ := hx
    have hcount : U.countP (fun y => y % p == c % p) = classCount U p (x % p) := by
      rw [classCount, hxc]
    rw [hcount]
    exact le_foldr_max (List.mem_map_of_mem hxU)
  · have hzero : U.countP (fun y => y % p == c % p) = 0 := by
      rw [List.countP_eq_zero]
      intro y hy hyc
      exact hx ⟨y, hy, by simpa using hyc⟩
    rw [hzero]
    exact Nat.zero_le _

/-- Union bound: if every entry of a sublist `V` of `U` lies in the
    chosen class `a p` mod some `p ∈ ps`, then `V.length` is at most the
    total number of entries of `U` in the chosen classes. -/
theorem length_le_sum_countP (a : ℕ → ℕ) (U : List ℕ) :
    ∀ (ps V : List ℕ), V.Sublist U → (∀ x ∈ V, ∃ p ∈ ps, x % p = a p % p) →
      V.length ≤ (ps.map fun p => U.countP fun x => x % p == a p % p).sum := by
  intro ps
  induction ps with
  | nil =>
    intro V _ hcov
    cases V with
    | nil => simp
    | cons x V => simpa using hcov x List.mem_cons_self
  | cons p ps ih =>
    intro V hsub hcov
    rw [List.map_cons, List.sum_cons,
      List.length_eq_countP_add_countP (fun x => x % p == a p % p)]
    have hfirst : V.countP (fun x => x % p == a p % p) ≤
        U.countP (fun x => x % p == a p % p) := hsub.countP_le
    have hrest : V.countP (fun x => ¬(x % p == a p % p)) ≤
        (ps.map fun q => U.countP fun x => x % q == a q % q).sum := by
      rw [List.countP_eq_length_filter]
      apply ih
      · exact List.filter_sublist.trans hsub
      · intro x hx
        rcases List.mem_filter.mp hx with ⟨hxV, hxp⟩
        obtain ⟨q, hq, hxq⟩ := hcov x hxV
        rcases List.mem_cons.mp hq with rfl | hqps
        · simp [hxq] at hxp
        · exact ⟨q, hqps, hxq⟩
    omega

/-- If one class `a p` per `p ∈ ps` covers `U`, then
    `U.length ≤ capSum U ps`. -/
theorem length_le_capSum (a : ℕ → ℕ) (ps U : List ℕ)
    (hcov : ∀ x ∈ U, ∃ p ∈ ps, x % p = a p % p) : U.length ≤ capSum U ps := by
  refine (length_le_sum_countP a U ps U (List.Sublist.refl U) hcov).trans ?_
  unfold capSum
  apply List.sum_le_sum
  intro p _
  exact countP_le_maxClass U p (a p)

/-- Completeness of `search`: if one class `a p` per modulus `p ∈ ps`
    covers every entry of `U`, then `search ps U = true`. -/
theorem search_complete (a : ℕ → ℕ) (ps : List ℕ) :
    ∀ U : List ℕ, (∀ x ∈ U, ∃ p ∈ ps, x % p = a p % p) → search ps U = true := by
  induction ps with
  | nil =>
    intro U hcov
    cases U with
    | nil => rfl
    | cons x U => simpa using hcov x List.mem_cons_self
  | cons p ps ih =>
    intro U hcov
    have hcap := length_le_capSum a (p :: ps) U hcov
    simp only [search, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      List.any_eq_true]
    refine ⟨hcap, ?_⟩
    by_cases hx : ∃ x ∈ U, x % p = a p % p
    · obtain ⟨x, hxU, hxa⟩ := hx
      right
      refine ⟨x % p, List.mem_map_of_mem hxU, ih _ ?_⟩
      intro y hy
      rcases List.mem_filter.mp hy with ⟨hyU, hyp⟩
      obtain ⟨q, hq, hyq⟩ := hcov y hyU
      rcases List.mem_cons.mp hq with rfl | hqps
      · simp [hyq, hxa] at hyp
      · exact ⟨q, hqps, hyq⟩
    · left
      apply ih
      intro y hyU
      obtain ⟨q, hq, hyq⟩ := hcov y hyU
      rcases List.mem_cons.mp hq with rfl | hqps
      · exact absurd ⟨y, hyU, hyq⟩ hx
      · exact ⟨q, hqps, hyq⟩

/-- The finite check: `[1, 30]` admits no covering by one class per
    prime `3, 5, …, 29` (evaluated by `decide`). -/
theorem search_primes_three_to_29 :
    search [3, 5, 7, 11, 13, 17, 19, 23, 29] (List.range' 1 30) = false := by
  decide

/-- **Refutation of `cutoff_30_ge_2`.**  The removed claim was
    "`CoversWith 30 2`: a concrete covering of `[1, 30]` using only
    primes in `(2, 30]` (no modulus 2) … yields the data point
    `maxCutoff 30 ≥ 2`".  It is false: for every choice of residues
    `a₃, a₅, …, a₂₉`, some `m ∈ [1, 30]` is missed.  Counterexample
    certificate: after any class mod `3` (always `10` points of
    `[1, 30]`), the `20` survivors meet at most `19` points of the
    best classes mod `5, …, 29` (see the section note above).  The
    discrepancy is with the repository's own certificate-lane guess, not
    with Erdős #688, which makes no claim about `n = 30`; the correct
    data point is `maxCutoff 30 = 1` (`maxCutoff_thirty`). -/
theorem cutoff_30_ge_2_false : ¬ CoversWith 30 2 := by
  rintro ⟨a, ha⟩
  have hpool : (Finset.Icc (2 + 1) 30).filter Nat.Prime =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by decide
  have hcov : ∀ x ∈ List.range' 1 30,
      ∃ p ∈ [3, 5, 7, 11, 13, 17, 19, 23, 29], x % p = a p % p := by
    intro x hx
    rw [List.mem_range'_1] at hx
    have hxIcc : x ∈ Finset.Icc 1 30 := Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
    obtain ⟨p, hp, hxp⟩ := ha x hxIcc
    rw [hpool] at hp
    exact ⟨p, by simpa using hp, hxp⟩
  have htrue := search_complete a _ _ hcov
  rw [search_primes_three_to_29] at htrue
  exact Bool.false_ne_true htrue

/-- No cutoff `T ≥ 2` admits a covering of `[1, 30]`: by
    `coversWith_mono`, such a covering would give `CoversWith 30 2`. -/
theorem not_coversWith_thirty_of_two_le (T : ℕ) (hT : 2 ≤ T) :
    ¬ CoversWith 30 T := fun h =>
  cutoff_30_ge_2_false (coversWith_mono 30 2 T hT h)

/-- Corrected certificate: `[1, 30]` is covered by the primes
    `2, 3, …, 29` with residues
    `a₂ = 1, a₃ = 2, a₅ = 4, a₇ = 3, a₁₁ = 6, a₁₃ = 12, a₁₇ = 16,
    a₁₉ = 18, a₂₃ = 22, a₂₉ = 1`. -/
theorem coversWith_thirty_one : CoversWith 30 1 := by
  let a : ℕ → ℕ := fun p =>
    if p = 2 then 1 else if p = 3 then 2 else if p = 5 then 4 else
    if p = 7 then 3 else if p = 11 then 6 else if p = 13 then 12 else
    if p = 17 then 16 else if p = 19 then 18 else if p = 23 then 22 else
    if p = 29 then 1 else 0
  have hpool : (Finset.Icc (1 + 1) 30).filter Nat.Prime =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by decide
  have hcert : ∀ m : Fin 31, 1 ≤ m.val →
      ∃ p : Fin 31, p.val ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) ∧
        m.val % p.val = a p.val % p.val := by decide
  refine ⟨a, ?_⟩
  intro m hm
  rcases Finset.mem_Icc.mp hm with ⟨hmLower, hmUpper⟩
  let mFin : Fin 31 := ⟨m, Nat.lt_succ_of_le hmUpper⟩
  rcases hcert mFin hmLower with ⟨p, hp, heq⟩
  refine ⟨p.val, ?_, heq⟩
  rw [hpool]
  exact hp

/-- The corrected data point: `maxCutoff 30 = 1`, i.e. the largest
    cutoff `T` for which the primes in `(T, 30]` can cover `[1, 30]` is
    `T = 1` (so modulus `2` is indispensable at `n = 30`). -/
theorem maxCutoff_thirty : maxCutoff 30 = 1 := by
  have hmem : 1 ∈ {T : ℕ | CoversWith 30 T} := coversWith_thirty_one
  have hbound : ∀ T ∈ {T : ℕ | CoversWith 30 T}, T ≤ 1 := by
    intro T hT
    by_contra hlt
    exact not_coversWith_thirty_of_two_le T (by omega) hT
  apply le_antisymm
  · exact csSup_le ⟨1, hmem⟩ hbound
  · exact le_csSup ⟨1, hbound⟩ hmem

end ErdosCandidates.E688

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch exactly.
   - Re-parametrization from real exponent n^epsilon to integer cutoff T is
     faithful: CoversWith n T uses primes in (T, n], and maxCutoff = sSup
     recovers epsilon_n = log(maxCutoff n)/log n.
   - Monotonicity direction is correct: T <= T' and CoversWith n T' (fewer
     primes) implies CoversWith n T (more primes) by extending the witness.
   - sSup honesty: set is bounded by n (T = n gives empty prime pool) and
     nonempty (T = 0 gives all primes <= n, sufficient for n >= 2).
   - Erdos lower bound lll/ll faithfully translates DB remark.
   - Headline epsilon_n = o(1) correctly encoded as maxCutoff n < n^delta.
-/
