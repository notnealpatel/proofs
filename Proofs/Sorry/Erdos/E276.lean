/-
  Erdős Problem #276 — all-composite Lucas sequences without a covering
  obstruction.
  Status: open.  Historical Tier UA attack target (certificate slice);
  this archive does not activate a dispatch lane.

  Verbatim statement (`goof erdos fetch 276`, pulled 2026-08-05):

    "Is there an infinite Lucas sequence $a_0,a_1,\ldots$ where
    $a_{n+2}=a_{n+1}+a_n$ for $n\geq 0$ such that all $a_k$ are
    composite, and yet no integer has a common factor with every term of
    the sequence?"

  DB remarks: Graham [Gr64] produced an all-composite Lucas sequence via
  covering systems (33-digit seeds); Vsemirnov holds the record seeds
  a₀ = 106276436867, a₁ = 35256392432.  Wilf's example is OEIS A083216
  (the historical campaign's C6 target).  Ismailescu–Son [IsSo14]
  'conjecturally solved' the problem: with p = 1, q a 129-digit number,
  a₀ = p² + q², a₁ = 2pq + q², the even-indexed terms are composite by a
  covering system and the odd-indexed terms factor algebraically as
  a_{2n+1} = (pFₙ + qF_{n+1})(pLₙ + qL_{n+1}) (F = Fibonacci,
  L = Lucas); no covering system appears responsible for the odd terms,
  but non-responsibility is unproved.

  Mathlib inventory (leandoc 2026-08-05): `Nat.fib` exists; general
  two-seed Lucas sequences do not (only `LucasLehmer`,
  `LinearRecurrence` — leandoc search "lucas sequence recurrence").
  Fresh def below.
-/
import Mathlib
import Erdos.Covering.RankOfApparition

set_option autoImplicit false

namespace ErdosCandidates.E276

/-- The Lucas (Fibonacci-like) sequence with seeds `a₀, a₁`:
    `lucasSeq a₀ a₁ (n+2) = lucasSeq a₀ a₁ (n+1) + lucasSeq a₀ a₁ n`. -/
def lucasSeq (a₀ a₁ : ℕ) : ℕ → ℕ
  | 0 => a₀
  | 1 => a₁
  | n + 2 => lucasSeq a₀ a₁ (n + 1) + lucasSeq a₀ a₁ n

/-- Ground truth: seeds (0, 1) give Fibonacci.
    -- PROVABLE (rfl / induction against `Nat.fib`). -/
theorem lucas_fib_ten : lucasSeq 0 1 10 = 55 := by
  decide

/-- `AllComposite a₀ a₁`: every term of the sequence is composite
    (neither 0, 1, nor prime — we require `2 ≤ aₖ ∧ ¬ prime`, pinning
    the degenerate small values out per STYLE.md). -/
def AllComposite (a₀ a₁ : ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ lucasSeq a₀ a₁ k ∧ ¬ (lucasSeq a₀ a₁ k).Prime

/-- `NoCommonFactor a₀ a₁`: no integer `m ≥ 2` shares a factor with
    every term — the "no covering obstruction of gcd type" condition of
    the problem. -/
def NoCommonFactor (a₀ a₁ : ℕ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, Nat.Coprime m (lucasSeq a₀ a₁ k)

/-- **Erdős #276 (OPEN)**: is there an all-composite Lucas sequence with
    no common-factor obstruction?

    Source text: "Is there an infinite Lucas sequence ... such that all
    $a_k$ are composite, and yet no integer has a common factor with
    every term of the sequence?"

    Note on fidelity: "no integer has a common factor with every term"
    is the literal negative condition; the deeper intended question
    (whether a covering system is 'responsible') is informal — the DB
    itself only formalizes the gcd version, which is what
    `NoCommonFactor` states.  Ismailescu–Son give a candidate believed
    to satisfy both conjuncts. -/
theorem erdos_276 :
    ∃ a₀ a₁ : ℕ, AllComposite a₀ a₁ ∧ NoCommonFactor a₀ a₁ := by
  sorry

/-- Vsemirnov covering certificate: triples `(p, r, z)` such that the
    prime `p` has Fibonacci rank of apparition dividing `r` and divides
    the Vsemirnov sequence at index `z`, hence at every index `≡ z (mod r)`. -/
private def vCover : List (ℕ × ℕ × ℕ) :=
  [(2, 3, 1), (3, 4, 3), (5, 5, 4), (7, 8, 5), (11, 10, 6), (17, 9, 2), (19, 18, 14),
   (23, 24, 17), (31, 30, 0), (41, 20, 18), (47, 16, 9), (61, 15, 12), (107, 36, 8),
   (181, 90, 80), (541, 90, 62), (769, 96, 91), (1103, 48, 33), (2521, 60, 48)]

/-- The classes `z (mod r)` of `vCover` cover every residue modulo `1440`. -/
private theorem vCover_covers :
    (List.range 1440).all (fun n => vCover.any (fun t => n % t.2.1 == t.2.2)) = true := by
  decide +kernel

/-- Certificate condition on a triple `(p, r, z)`: `2 ≤ p` is below the
    sequence's lower bound, `p ∣ F r`, `r ∣ 1440`, `z < r`, and `p`
    divides the Vsemirnov term of index `z`. -/
private def VCertTriple (t : ℕ × ℕ × ℕ) : Prop :=
  2 ≤ t.1 ∧ t.1 < 35256392432 ∧ t.1 ∣ Nat.fib t.2.1 ∧ t.2.1 ∣ 1440 ∧ t.2.2 < t.2.1 ∧
    t.1 ∣ lucasSeq 106276436867 35256392432 t.2.2

/-- Every triple of `vCover` satisfies the certificate condition
    (checked by kernel evaluation). -/
private theorem vCover_cert : ∀ t ∈ vCover, VCertTriple t := by
  unfold VCertTriple
  decide +kernel

/-- Every Vsemirnov term is at least the smaller seed `35256392432`. -/
private theorem vsemirnov_ge (n : ℕ) :
    35256392432 ≤ lucasSeq 106276436867 35256392432 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [lucasSeq]
    | 1, _ => simp [lucasSeq]
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      rw [lucasSeq]
      omega

/-- **Graham/Vsemirnov certificate slice (the Tier-UA target)**: the
    Vsemirnov seeds generate an all-composite Lucas sequence.  This is
    the covering-system half only (the sequence does have a common
    factor structure — it is the classical construction).

    Suggested infrastructure: the `IsFibonacciLike` machinery in
    `Proofs/Erdos/Covering/RankOfApparition.lean`, used in the historical
    A083216/Wilf lane; this is not a certificate for the displayed seeds.
    The covering system must assign to each residue class of indices a
    prime dividing the corresponding terms (via `lucasSeq` mod p
    periodicity — Pisano periods).  Mathlib: `Nat.ModEq`, periodicity
    of linear recurrences mod p is elementary induction.
    Historical effort estimate M, conditional on the certificate infrastructure. -/
theorem vsemirnov_all_composite :
    AllComposite 106276436867 35256392432 := by
  intro n
  have hge := vsemirnov_ge n
  refine ⟨by omega, ?_⟩
  -- the residue `n % 1440` lies in some class `z (mod r)` of the covering
  have hcov := vCover_covers
  rw [List.all_eq_true] at hcov
  have hrange : n % 1440 ∈ List.range 1440 :=
    List.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  have hany := hcov _ hrange
  rw [List.any_eq_true] at hany
  obtain ⟨⟨p, r, z⟩, hmem, hmod⟩ := hany
  obtain ⟨hp2, hplt, hfib, hr, hzr, hz⟩ := vCover_cert _ hmem
  simp only [beq_iff_eq] at hmod
  have hs : Erdos.Covering.IsFibonacciLike
      (fun k => (lucasSeq 106276436867 35256392432 k : ℤ)) := fun k => by
    simp [lucasSeq]
  have hrank : Erdos.Covering.rankOfApparition p ∣ r :=
    (Erdos.Covering.dvd_fib_iff_rankOfApparition_dvd (by omega) r).mp hfib
  have hn : n % r = z % r := by
    rw [← Nat.mod_mod_of_dvd n hr, hmod, Nat.mod_eq_of_lt hzr]
  have hdvd : (p : ℤ) ∣ (lucasSeq 106276436867 35256392432 n : ℤ) :=
    hs.dvd_of_mod_eq (by omega) hrank (Int.natCast_dvd_natCast.mpr hz) hn
  exact Nat.not_prime_of_dvd_of_lt (Int.natCast_dvd_natCast.mp hdvd) hp2 (by omega)

/-- Sanity: the Vsemirnov seeds themselves are composite, and the
    recurrence's first terms are as expected.
    -- PROVABLE (decide / norm_num primality certificates). -/
theorem vsemirnov_seed_sanity :
    ¬ (106276436867 : ℕ).Prime ∧ ¬ (35256392432 : ℕ).Prime ∧
    lucasSeq 106276436867 35256392432 2 = 141532829299 := by
  have hdiv₀ : 31 ∣ (106276436867 : ℕ) := by
    norm_num
  have hdiv₁ : 2 ∣ (35256392432 : ℕ) := by
    norm_num
  constructor
  · exact Nat.not_prime_of_dvd_of_lt hdiv₀ (by norm_num) (by norm_num)
  · constructor
    · exact Nat.not_prime_of_dvd_of_lt hdiv₁ (by norm_num) (by norm_num)
    · norm_num [lucasSeq]

/-- Non-degeneracy of `NoCommonFactor`: the Fibonacci sequence (seeds
    1, 1) satisfies it — consecutive Fibonacci numbers are coprime, so
    no `m ≥ 2` divides every term (indeed `fib` hits 1).  But Fibonacci
    has prime terms, so it fails `AllComposite`: the two conjuncts of
    the problem are jointly nontrivial.  -- PROVABLE. -/
theorem fibonacci_seed_nontrivial : NoCommonFactor 1 1 ∧ ¬ AllComposite 1 1 := by
  constructor
  · intro m hm
    exact ⟨0, Nat.coprime_one_right m⟩
  · intro h
    have hsmall : 2 ≤ 1 := (h 0).1
    omega

end ErdosCandidates.E276

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - lucasSeq def is correct (ℕ → ℕ, additive recurrence, two seeds).  ℕ codomain is
     safe: the problem requires all terms composite (hence positive), and additive
     recurrence over ℕ seeds produces only ℕ values.
   - AllComposite: requires 2 ≤ a_k ∧ ¬ prime — correct reading of "composite" that
     excludes 0 and 1.
   - NoCommonFactor: ∀ m ≥ 2, ∃ k, Coprime m (a_k).  Faithful to "no integer has a
     common factor with every term" (m=0 trivially shares factors, m=1 trivially doesn't,
     negatives symmetric — restricting to m ≥ 2 is the standard reading).
   - Vsemirnov seeds (106276436867, 35256392432): verified both composite; sum
     106276436867 + 35256392432 = 141532829299 matches the file's example.
   - DB attribution chain (Graham [Gr64], Vsemirnov record, Ismailescu-Son [IsSo14])
     matches the file header and theorem docstrings.
   - Ismailescu-Son factorization a_{2n+1} = (pF_n + qF_{n+1})(pL_n + qL_{n+1}) is
     from the DB comment (Woett, Nov 2025); file correctly attributes.
-/
