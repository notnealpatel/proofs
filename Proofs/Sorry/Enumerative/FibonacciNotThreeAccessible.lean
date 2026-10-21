/-
# The Fibonacci numbers are not 3-accessible (Wesley)

## Source

William J. Wesley, "The Fibonacci numbers are not 3-accessible",
arXiv:2609.33744.  Section 2 ("Proof of Theorem 1"): Theorem 1 (`MainThm`),
Lemma 2 (`LemmaRecur`), Lemma 3 (`LemmaS`).  Recorded 2026-10-21.

Verbatim informal claim (Theorem 1):

> There exists a 3-coloring of $\mathbb{Z}^+$ that does not contain
> monochromatic 19-term $F$-diffsequences. In particular,
> $\operatorname{doa}(F) = 2$.

Definitions (Section 1): a *$D$-diffsequence* is a sequence of integers
$x_1 < \dots < x_k$ with $x_{i+1} - x_i \in D$; $D$ is *$r$-accessible* if
every $r$-coloring of the positive integers contains arbitrarily long
monochromatic $D$-diffsequences.  $F = \{f_n : n \ge 1\} = \{1, 2, 3, 5, 8, \dots\}$.

The paper's coloring: $m = 232$, $\alpha = 184 + 8\phi$,
$\rho(n) = \lfloor \alpha n \rfloor \bmod m$, $\chi(n) = C(\rho(n))$ with the
explicit 3-coloring $C = (C_1, C_2, C_3)$ of $\mathbb{Z}_m$.

## Status

Proved in the paper.  The "not 3-accessible" half (`doa(F) ≤ 2`) is the new
result of the paper; the lower bound `doa(F) ≥ 2` is Landman–Robertson (2007)
and is only cited, so it is not formalized here.

## What is formalized (all proved, no `sorry`)

* `lemma_2`  — Lemma 2 of the paper, over `ℝ`.
* `floor_alpha_mul` — exact integer form `⌊α n⌋ = 188 n + ⌊√(80 n²)⌋`.
* `lemma_3`  — Lemma 3 of the paper: `ρ(x + f) - ρ(x) ∈ S (mod 232)` for `f ∈ F`.
* `paperColoring_not_monochromatic_twenty` — the paper's coloring `χ` has no
  monochromatic 20-term `F`-diffsequence (finite height certificate on the
  Cayley digraph, checked by `decide`).
* `thm_1` — Theorem 1 as stated: some 3-coloring has no monochromatic
  19-term `F`-diffsequence.
* `not_isAccessible_fibSet_three` — `F` is not 3-accessible.

## Discrepancy note (off by one in the paper)

The paper's own graph argument shows the longest paths in `G[C_i]` have 19,
18, 14 vertices, hence a monochromatic diffsequence of `χ` has *at most 19*
terms; this excludes 20-term sequences, not 19-term ones.  The paper's
coloring is therefore certified here only for 20 terms
(`paperColoring_not_monochromatic_twenty`).  Theorem 1 (19 terms) is proved
with a different coloring `improvedC` of `ℤ/232` (same `α` and `m`, found by
simulated annealing during triage) whose monochromatic Cayley-digraph paths
have at most 16 vertices, so it has no monochromatic 17-term diffsequence
(`improvedColoring_not_monochromatic_seventeen`).  Theorem 1 is existential
in the coloring, so this proves the statement exactly as written.
Brute force (triage, not a proof) finds the paper's coloring's actual longest
monochromatic `F`-diffsequence up to 200000 to be 14 terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FibonacciNotThreeAccessible

open Real

/-! ## Definitions mirroring Section 1 -/

/-- The Fibonacci set `F = {f_n : n ≥ 1} = {1, 2, 3, 5, 8, …}`. -/
def fibSet : Set ℕ := {d | ∃ n, 0 < n ∧ Nat.fib n = d}

/-- `x 0 < x 1 < ⋯ < x (k-1)` is a `D`-diffsequence: consecutive terms increase and
their difference lies in `D`. -/
def IsDiffseq (D : Set ℕ) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ i, i + 1 < k → x i < x (i + 1) ∧ x (i + 1) - x i ∈ D

/-- The first `k` terms of `x` all receive the same color under `χ`. -/
def IsMonochromatic {r : ℕ} (χ : ℕ → Fin r) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ i < k, χ (x i) = χ (x 0)

/-- `D` is `r`-accessible: every `r`-coloring of the positive integers contains
arbitrarily long monochromatic `D`-diffsequences of positive integers.  (A coloring
of `ℤ⁺` is modelled as a coloring of `ℕ` whose value at `0` is irrelevant.) -/
def IsAccessible (D : Set ℕ) (r : ℕ) : Prop :=
  ∀ χ : ℕ → Fin r, ∀ k, ∃ x : ℕ → ℕ,
    (∀ i < k, 0 < x i) ∧ IsDiffseq D k x ∧ IsMonochromatic χ k x

example : 1 ∈ fibSet := ⟨1, by decide, by decide⟩
example : 8 ∈ fibSet := ⟨6, by decide, by decide⟩
example : 0 ∉ fibSet := fun ⟨_, hn, h⟩ => (Nat.fib_pos.mpr hn).ne' h
/-- Non-vacuity of the diffsequence hypothesis: `0, 1, …, 18` is an `F`-diffsequence. -/
example : IsDiffseq fibSet 19 id := fun i _ => ⟨by simp, 1, by decide, by simp⟩

/-! ## Section 2: the constants `α`, `ρ` and Lemma 2 -/

/-- The paper's rotation number `α = 184 + 8φ` (`= 188 + 4√5`). -/
noncomputable def alpha : ℝ := 184 + 8 * goldenRatio

/-- The paper's `ρ(n) = ⌊α n⌋ mod 232`, as a natural number in `[0, 232)`. -/
noncomputable def rho (n : ℕ) : ℕ := ⌊alpha * n⌋₊ % 232

/-- Lemma 2 (`LemmaRecur`): `(a + bφ) f_n = a f_n + b f_{n+1} - b ψ^n` for integers
`a, b` and all `n ≥ 0`. -/
theorem lemma_2 (a b : ℤ) (n : ℕ) :
    ((a : ℝ) + b * goldenRatio) * Nat.fib n =
      a * Nat.fib n + b * Nat.fib (n + 1) - b * goldenConj ^ n := by
  rw [Real.coe_fib_eq, Real.coe_fib_eq]
  have hs : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hdiff : goldenRatio = goldenConj + √5 := by
    rw [goldenRatio, goldenConj]; ring
  rw [pow_succ, pow_succ]
  field_simp
  rw [hdiff]
  ring

/-- `⌊√(80 n²)⌋ = ⌊4√5 · n⌋`, computed with the integer square root. -/
def sqrtPart (n : ℕ) : ℕ := Nat.sqrt (80 * n ^ 2)

example : sqrtPart 1 = 8 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num
example : sqrtPart 2 = 17 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num

/-- Exact integer form of the paper's floor: `⌊α n⌋ = 188 n + ⌊√(80 n²)⌋`. -/
theorem floor_alpha_mul (n : ℕ) : ⌊alpha * n⌋₊ = 188 * n + sqrtPart n := by
  have hsq : √((80 * n ^ 2 : ℕ) : ℝ) = 4 * √5 * n := by
    have h : ((80 * n ^ 2 : ℕ) : ℝ) = (4 * √5 * n) * (4 * √5 * n) := by
      have h5 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
      push_cast
      nlinarith [h5]
    rw [h, Real.sqrt_mul_self (by positivity)]
  have hα : alpha * n = √((80 * n ^ 2 : ℕ) : ℝ) + ((188 * n : ℕ) : ℝ) := by
    rw [hsq, alpha, goldenRatio]; push_cast; ring
  rw [hα, Nat.floor_add_natCast (Real.sqrt_nonneg _), Real.nat_floor_real_sqrt_eq_nat_sqrt,
    sqrtPart]
  ring

/-- `ρ` in integer form. -/
theorem rho_eq (n : ℕ) : rho n = (188 * n + sqrtPart n) % 232 := by
  rw [rho, floor_alpha_mul]

/-- Ground truth: `⌊α⌋ = 196` and `⌊2α⌋ = 393` (so `ρ(1) = 196`, `ρ(2) = 161`). -/
example : ⌊alpha * (1 : ℕ)⌋₊ = 196 ∧ ⌊alpha * (2 : ℕ)⌋₊ = 393 := by
  rw [floor_alpha_mul, floor_alpha_mul, sqrtPart, sqrtPart]
  constructor
  · rw [show 188 * 1 + Nat.sqrt (80 * 1 ^ 2) = 188 + Nat.sqrt 80 by norm_num,
      show Nat.sqrt 80 = 8 by rw [eq_comm, Nat.eq_sqrt]; norm_num]
  · rw [show 188 * 2 + Nat.sqrt (80 * 2 ^ 2) = 376 + Nat.sqrt 320 by norm_num,
      show Nat.sqrt 320 = 17 by rw [eq_comm, Nat.eq_sqrt]; norm_num]

/-! ## The floor of a sum -/

/-- `⌊c(x+f)⌋ - ⌊cx⌋ ∈ {⌊cf⌋, ⌊cf⌋ + 1}` for `c = √80`, in integer form. -/
theorem sqrtPart_add (x f : ℕ) :
    sqrtPart x + sqrtPart f ≤ sqrtPart (x + f) ∧
      sqrtPart (x + f) ≤ sqrtPart x + sqrtPart f + 1 := by
  unfold sqrtPart
  set p := Nat.sqrt (80 * x ^ 2)
  set q := Nat.sqrt (80 * f ^ 2)
  have hp1 : p * p ≤ 80 * x ^ 2 := Nat.sqrt_le _
  have hp2 : 80 * x ^ 2 < (p + 1) * (p + 1) := Nat.lt_succ_sqrt _
  have hq1 : q * q ≤ 80 * f ^ 2 := Nat.sqrt_le _
  have hq2 : 80 * f ^ 2 < (q + 1) * (q + 1) := Nat.lt_succ_sqrt _
  have hpq : p * q ≤ 80 * x * f := by
    have h : (p * q) * (p * q) ≤ (80 * x * f) * (80 * x * f) := by
      calc (p * q) * (p * q) = (p * p) * (q * q) := by ring
        _ ≤ (80 * x ^ 2) * (80 * f ^ 2) := Nat.mul_le_mul hp1 hq1
        _ = (80 * x * f) * (80 * x * f) := by ring
    exact Nat.mul_self_le_mul_self_iff.mp h
  have hpq' : 80 * x * f < (p + 1) * (q + 1) := by
    have h : (80 * x * f) * (80 * x * f) < ((p + 1) * (q + 1)) * ((p + 1) * (q + 1)) := by
      calc (80 * x * f) * (80 * x * f) = (80 * x ^ 2) * (80 * f ^ 2) := by ring
        _ < ((p + 1) * (p + 1)) * ((q + 1) * (q + 1)) :=
          Nat.mul_lt_mul_of_lt_of_lt hp2 hq2
        _ = ((p + 1) * (q + 1)) * ((p + 1) * (q + 1)) := by ring
    exact Nat.mul_self_lt_mul_self_iff.mp h
  constructor
  · rw [Nat.le_sqrt]
    nlinarith
  · rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
    nlinarith

/-! ## `⌊α f_n⌋` modulo 232 -/

/-- Cassini's identity in the form `f_{n+1}² - f_{n+1} f_n - f_n² = (-1)^n`. -/
theorem cassini (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n - (Nat.fib n : ℤ) ^ 2) =
      (-1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by ring, Nat.fib_add_two, pow_succ]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-- For `n ≥ 5`, `⌊4√5 f_n⌋ ∈ {4L_n - 1, 4L_n}` with `4 L_n = 8 f_{n+1} - 4 f_n`,
stated without subtraction (this is `|8ψ^n| < 1` in integer form). -/
theorem sqrtPart_fib (m : ℕ) :
    sqrtPart (Nat.fib (m + 5)) + 4 * Nat.fib (m + 5) ≤ 8 * Nat.fib (m + 6) ∧
      8 * Nat.fib (m + 6) ≤ sqrtPart (Nat.fib (m + 5)) + 4 * Nat.fib (m + 5) + 1 := by
  unfold sqrtPart
  set F := Nat.fib (m + 5)
  set E := Nat.fib (m + 4)
  have hG : Nat.fib (m + 6) = E + F := Nat.fib_add_two
  have hF : 5 ≤ F := by
    calc 5 = Nat.fib 5 := by decide
      _ ≤ F := Nat.fib_mono (show 5 ≤ m + 5 by omega)
  have hE : 3 ≤ E := by
    calc 3 = Nat.fib 4 := by decide
      _ ≤ E := Nat.fib_mono (show 4 ≤ m + 4 by omega)
  have hc := cassini (m + 5)
  rw [show m + 5 + 1 = m + 6 by ring, hG] at hc
  have hc' : ((E + F : ℕ) : ℤ) ^ 2 - (E + F : ℕ) * (F : ℤ) - (F : ℤ) ^ 2 = 1 ∨
      ((E + F : ℕ) : ℤ) ^ 2 - (E + F : ℕ) * (F : ℤ) - (F : ℤ) ^ 2 = -1 := by
    rw [hc]; exact neg_one_pow_eq_or ℤ (m + 5)
  set q := Nat.sqrt (80 * F ^ 2)
  have hq1 : q * q ≤ 80 * F ^ 2 := Nat.sqrt_le _
  have hq2 : 80 * F ^ 2 < (q + 1) * (q + 1) := Nat.lt_succ_sqrt _
  rw [hG]
  have hq1' : (q : ℤ) * q ≤ 80 * (F : ℤ) ^ 2 := by exact_mod_cast hq1
  have hq2' : 80 * (F : ℤ) ^ 2 < ((q : ℤ) + 1) * ((q : ℤ) + 1) := by exact_mod_cast hq2
  have hE' : (3 : ℤ) ≤ E := by exact_mod_cast hE
  have hF' : (5 : ℤ) ≤ F := by exact_mod_cast hF
  push_cast at hc'
  constructor
  · by_contra hcon
    replace hcon := Nat.lt_of_not_le hcon
    have hlt : (8 * ((E : ℤ) + F)) < q + 4 * F := by exact_mod_cast hcon
    rcases hc' with h | h <;> nlinarith
  · by_contra hcon
    replace hcon := Nat.lt_of_not_le hcon
    have hlt : (q : ℤ) + 4 * F + 1 < 8 * ((E : ℤ) + F) := by exact_mod_cast hcon
    rcases hc' with h | h <;> nlinarith

/-- The paper's sequence `a_n = 184 f_n + 8 f_{n+1}`. -/
def orbitSeq (n : ℕ) : ℕ := 184 * Nat.fib n + 8 * Nat.fib (n + 1)

/-- The consecutive pairs `(a_n, a_{n+1}) mod 232`; the orbit
`𝒪 = {8, 56, 128, 160, 184, 192, 200}` of period 7. -/
def orbitPairs : List (ℕ × ℕ) :=
  [(8, 192), (192, 200), (200, 160), (160, 128), (128, 56), (56, 184), (184, 8)]

/-- `a_n` satisfies the Fibonacci recurrence. -/
theorem orbitSeq_add_two (n : ℕ) : orbitSeq (n + 2) = orbitSeq n + orbitSeq (n + 1) := by
  unfold orbitSeq
  rw [Nat.fib_add_two (n := n), show n + 2 + 1 = (n + 1) + 2 by ring,
    Nat.fib_add_two (n := n + 1), Nat.fib_add_two (n := n)]
  ring

/-- `a_n mod 232` is periodic of period 7 with orbit `𝒪`. -/
theorem orbit_pair (n : ℕ) : (orbitSeq n % 232, orbitSeq (n + 1) % 232) ∈ orbitPairs := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hclosed : ∀ p ∈ orbitPairs, (p.2, (p.1 + p.2) % 232) ∈ orbitPairs := by decide
    rw [show k + 1 + 1 = k + 2 by ring, orbitSeq_add_two, Nat.add_mod]
    exact hclosed _ ih

/-- The possible values of `⌊α f⌋ mod 232`, `f ∈ F`:
`{126, 161, 196} ∪ 𝒪 ∪ (𝒪 - 1)`. -/
def baseList : List ℕ := [126, 161, 196, 8, 56, 128, 160, 184, 192, 200,
  7, 55, 127, 159, 183, 191, 199]

/-- The paper's set `S` (verbatim). -/
def stepList : List ℕ := [7, 8, 9, 55, 56, 57, 126, 127, 128, 129, 159, 160, 161, 162,
  183, 184, 185, 191, 192, 193, 196, 197, 199, 200, 201]

/-- `S = {126,161,196} ∪ {127,162,197} ∪ 𝒪 ∪ (𝒪+1) ∪ (𝒪-1)` contains `d` and `d + 1`
for every `d ∈ baseList`. -/
theorem baseList_step : ∀ d ∈ baseList, d ∈ stepList ∧ d + 1 ∈ stepList := by decide

/-- `⌊α f_n⌋ mod 232 ∈ {126,161,196} ∪ 𝒪 ∪ (𝒪 - 1)` for `n ≥ 1`. -/
theorem floor_fib_mod (n : ℕ) (hn : 0 < n) :
    (188 * Nat.fib n + sqrtPart (Nat.fib n)) % 232 ∈ baseList := by
  obtain h1 | h2 | h3 | h4 | ⟨m, rfl⟩ : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ ∃ m, n = m + 5 := by
    rcases n with _ | _ | _ | _ | _ | m
    · omega
    all_goals simp_all
  · have hs : sqrtPart 1 = 8 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num
    subst h1; rw [Nat.fib_one, hs]; decide
  · have hs : sqrtPart 1 = 8 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num
    subst h2; rw [Nat.fib_two, hs]; decide
  · have hs : sqrtPart 2 = 17 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num
    subst h3; rw [show Nat.fib 3 = 2 by decide, hs]; decide
  · have hs : sqrtPart 3 = 26 := by rw [sqrtPart, eq_comm, Nat.eq_sqrt]; norm_num
    subst h4; rw [show Nat.fib 4 = 3 by decide, hs]; decide
  · obtain ⟨hlo, hhi⟩ := sqrtPart_fib m
    have ho := orbit_pair (m + 5)
    unfold orbitSeq at ho
    have hrec : Nat.fib (m + 5 + 1) = Nat.fib (m + 6) := rfl
    rw [hrec] at ho
    simp only [orbitPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ho
    simp only [baseList, List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- Lemma 3, integer form: translating by a Fibonacci number changes
`(188 x + ⌊√(80x²)⌋) mod 232` by an element of `S`. -/
theorem rhoNat_add_fib (x n : ℕ) (hn : 0 < n) : ∃ s ∈ stepList,
    (188 * (x + Nat.fib n) + sqrtPart (x + Nat.fib n)) % 232 =
      ((188 * x + sqrtPart x) % 232 + s) % 232 := by
  have hb := floor_fib_mod n hn
  obtain ⟨hs0, hs1⟩ := baseList_step _ hb
  obtain ⟨hlo, hhi⟩ := sqrtPart_add x (Nat.fib n)
  rcases Nat.lt_or_ge (sqrtPart (x + Nat.fib n)) (sqrtPart x + sqrtPart (Nat.fib n) + 1)
    with h | h
  · refine ⟨_, hs0, ?_⟩
    have he : sqrtPart (x + Nat.fib n) = sqrtPart x + sqrtPart (Nat.fib n) := by omega
    rw [he]; omega
  · refine ⟨_, hs1, ?_⟩
    have he : sqrtPart (x + Nat.fib n) = sqrtPart x + sqrtPart (Nat.fib n) + 1 := by omega
    rw [he]; omega

/-- Lemma 3 (`LemmaS`): for all `f ∈ F`, `ρ(x + f) - ρ(x) ∈ S` in `ℤ/232`, i.e.
`ρ(x + f) = (ρ(x) + s) mod 232` for some `s ∈ S`. -/
theorem lemma_3 (x f : ℕ) (hf : f ∈ fibSet) : ∃ s ∈ stepList, rho (x + f) = (rho x + s) % 232 := by
  obtain ⟨n, hn, rfl⟩ := hf
  simpa only [rho_eq] using rhoNat_add_fib x n hn

/-! ## Height certificates on the Cayley digraph `G[C_i]` -/

/-- The `u`-th base-32 digit of `H`: the height table entry `h(u)`. -/
def heightOf (H u : ℕ) : ℕ := (H >>> (5 * u)) % 32

/-- Certificate check: for all `u ∈ ℤ/232` and `s ∈ S`, if `u` and `u + s` have the same
color under `C`, then `h(u + s) < h(u)`.  (So `G[C_i]` is acyclic for each color and
`h` bounds path lengths.) -/
def certOK (C : ℕ → Fin 3) (H : ℕ) : Bool :=
  (List.range 232).all fun u => stepList.all fun s =>
    !(decide (C u = C ((u + s) % 232))) || decide (heightOf H ((u + s) % 232) < heightOf H u)

/-- All heights are `< K`. -/
def boundOK (H K : ℕ) : Bool := (List.range 232).all fun u => decide (heightOf H u < K)

/-- Generic height argument: if `C` admits a height certificate bounded by `K`, then the
coloring `n ↦ C(ρ n)` has no monochromatic `(K+1)`-term `F`-diffsequence. -/
theorem not_monochromatic_of_cert (C : ℕ → Fin 3) (H K : ℕ) (hcert : certOK C H = true)
    (hbound : boundOK H K = true) (x : ℕ → ℕ) (hx : IsDiffseq fibSet (K + 1) x) :
    ¬ IsMonochromatic (fun n => C (rho n)) (K + 1) x := by
  intro hmono
  have hc : ∀ u < 232, ∀ s ∈ stepList, C u = C ((u + s) % 232) →
      heightOf H ((u + s) % 232) < heightOf H u := by
    intro u hu s hs hC
    simp only [certOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hcert
    rcases hcert u hu s hs with h | h
    · exact absurd hC h
    · exact h
  have hb : ∀ u < 232, heightOf H u < K := by
    intro u hu
    simp only [boundOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hbound
    exact hbound u hu
  have hdesc : ∀ i, i < K + 1 → heightOf H (rho (x i)) + i ≤ heightOf H (rho (x 0)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      obtain ⟨-, hd⟩ := hx j hj
      obtain ⟨s, hs, hrho⟩ := lemma_3 (x j) (x (j + 1) - x j) hd
      have hxj : x j + (x (j + 1) - x j) = x (j + 1) := by
        have := (hx j hj).1; omega
      rw [hxj] at hrho
      have hcol : C (rho (x j)) = C ((rho (x j) + s) % 232) := by
        have hmj : C (rho (x j)) = C (rho (x 0)) := hmono j (by omega)
        have hmj1 : C (rho (x (j + 1))) = C (rho (x 0)) := hmono (j + 1) hj
        rw [← hrho, hmj, hmj1]
      have hlt := hc (rho (x j)) (Nat.mod_lt _ (by norm_num)) s hs hcol
      rw [← hrho] at hlt
      omega
  have hK := hdesc K (by omega)
  have hlt := hb (rho (x 0)) (Nat.mod_lt _ (by norm_num))
  omega

/-! ## The paper's coloring `C` of `ℤ/232` -/

/-- Membership in the paper's color class
`C₁ = [0,24] ∪ {68} ∪ [87,98] ∪ [125,126] ∪ [148,155] ∪ [187,196] ∪ [200,217] ∪ {231}`. -/
def inC1 (u : ℕ) : Bool :=
  u ≤ 24 || u == 68 || (87 ≤ u && u ≤ 98) || (125 ≤ u && u ≤ 126) || (148 ≤ u && u ≤ 155) ||
    (187 ≤ u && u ≤ 196) || (200 ≤ u && u ≤ 217) || u == 231

/-- Membership in `C₂ = [41,55] ∪ [117,124] ∪ [127,143] ∪ [156,186] ∪ [218,224]`. -/
def inC2 (u : ℕ) : Bool :=
  (41 ≤ u && u ≤ 55) || (117 ≤ u && u ≤ 124) || (127 ≤ u && u ≤ 143) ||
    (156 ≤ u && u ≤ 186) || (218 ≤ u && u ≤ 224)

/-- Membership in `C₃ = [25,40] ∪ [56,67] ∪ [69,86] ∪ [99,116] ∪ [144,147] ∪ [197,199] ∪
[225,230]`. -/
def inC3 (u : ℕ) : Bool :=
  (25 ≤ u && u ≤ 40) || (56 ≤ u && u ≤ 67) || (69 ≤ u && u ≤ 86) || (99 ≤ u && u ≤ 116) ||
    (144 ≤ u && u ≤ 147) || (197 ≤ u && u ≤ 199) || (225 ≤ u && u ≤ 230)

/-- The paper's coloring `C` of `ℤ/232`, with the paper's colors `1, 2, 3` written
`0, 1, 2`. -/
def paperC (u : ℕ) : Fin 3 := if inC1 u then 0 else if inC2 u then 1 else 2

set_option maxRecDepth 100000 in
/-- Ground truth: `C₁, C₂, C₃` partition `{0, …, 231}` (each residue lies in exactly one
class). -/
example : (List.range 232).all (fun u =>
    (if inC1 u then 1 else 0) + (if inC2 u then 1 else 0) + (if inC3 u then 1 else 0) == 1) =
      true := by decide

set_option maxRecDepth 100000 in
/-- Ground truth: `paperC` agrees with the class `C₃` on `{0, …, 231}`. -/
example : (List.range 232).all (fun u => (paperC u == 2) == inC3 u) = true := by decide

/-- The paper's 3-coloring `χ(n) = C(ρ(n))` of the positive integers. -/
noncomputable def paperColoring (n : ℕ) : Fin 3 := paperC (rho n)

/-- Height table for `paperC`: `h(u) + 1` is the number of vertices on the longest
monochromatic path from `u` in the Cayley digraph (max 19 vertices). -/
def paperHeight : ℕ :=
  8824601084478421337089433220089021505880875094362635220708834266993159645407467416692712386436177664153574818157779381317298489394153471718618389317776035335998755423166906331360910341223700703481290405107104536487830604416341672508629473086934219546731139802053539421025991318383215465750271115379265015860759741179460092772498632498541550863173106

set_option maxRecDepth 100000 in
/-- Kernel-checked certificate that every `G[C_i]` is acyclic with heights from
`paperHeight`. -/
theorem paper_cert : certOK paperC paperHeight = true := by decide

/-- Heights for `paperC` are at most 18 (longest path: 19 vertices, as in the paper). -/
theorem paper_bound : boundOK paperHeight 19 = true := by decide

/-- The paper's coloring `χ` has no monochromatic 20-term `F`-diffsequence.  (This is
exactly what the paper's path-length bound "at most 19" yields.) -/
theorem paperColoring_not_monochromatic_twenty (x : ℕ → ℕ) (hx : IsDiffseq fibSet 20 x) :
    ¬ IsMonochromatic paperColoring 20 x :=
  not_monochromatic_of_cert paperC paperHeight 19 paper_cert paper_bound x hx

/-! ## An improved coloring of `ℤ/232` (same `α`, `m`) -/

/-- A piecewise-constant coloring of `{0, …, 231}` from a list of
(right endpoint, color) breakpoints. -/
def pieceColor : List (ℕ × Fin 3) → ℕ → Fin 3
  | [], _ => 0
  | (b, c) :: rest, u => if u ≤ b then c else pieceColor rest u

/-- A second coloring of `ℤ/232` (found by simulated annealing during triage) whose
monochromatic Cayley-digraph paths have at most 16 vertices. -/
def improvedC (u : ℕ) : Fin 3 :=
  pieceColor [(23, 0), (40, 2), (55, 1), (86, 2), (97, 0), (118, 2), (143, 1), (148, 2),
    (156, 0), (175, 1), (177, 2), (187, 1), (197, 0), (198, 2), (218, 0), (226, 1), (228, 2),
    (231, 0)] u

example : improvedC 0 = 0 ∧ improvedC 24 = 2 ∧ improvedC 231 = 0 := by decide

/-- The coloring `n ↦ improvedC(ρ(n))` of the positive integers. -/
noncomputable def improvedColoring (n : ℕ) : Fin 3 := improvedC (rho n)

/-- Height table for `improvedC` (max height 15). -/
def improvedHeight : ℕ :=
  7577244309918845883565583878863006884372876191757011813835308550215279086456822356693316627798961626885182668585608396289213445306611155288856080384123302564838532805479843490355348993759388483460781250524282428155291985718838742189657979910277331704502941298265359705176648837841080108175320895992654814640794153799980748580876757226566767028452847

set_option maxRecDepth 100000 in
/-- Kernel-checked certificate for `improvedC`. -/
theorem improved_cert : certOK improvedC improvedHeight = true := by decide

/-- Heights for `improvedC` are at most 15. -/
theorem improved_bound : boundOK improvedHeight 16 = true := by decide

/-- `improvedColoring` has no monochromatic 17-term `F`-diffsequence. -/
theorem improvedColoring_not_monochromatic_seventeen (x : ℕ → ℕ)
    (hx : IsDiffseq fibSet 17 x) : ¬ IsMonochromatic improvedColoring 17 x :=
  not_monochromatic_of_cert improvedC improvedHeight 16 improved_cert improved_bound x hx

/-! ## Theorem 1 -/

/-- **Theorem 1** (Wesley, arXiv:2609.33744): there exists a 3-coloring of the positive
integers with no monochromatic 19-term `F`-diffsequence.  (Stated for colorings of `ℕ`
and sequences in `ℕ`, which is at least as strong.) -/
theorem thm_1 : ∃ χ : ℕ → Fin 3, ∀ x : ℕ → ℕ,
    IsDiffseq fibSet 19 x → ¬ IsMonochromatic χ 19 x := by
  refine ⟨improvedColoring, fun x hx hmono => ?_⟩
  exact improvedColoring_not_monochromatic_seventeen x (fun i hi => hx i (by omega))
    (fun i hi => hmono i (by omega))

/-- **Theorem 1, accessibility form**: the Fibonacci numbers are not 3-accessible,
i.e. `doa(F) ≤ 2`. -/
theorem not_isAccessible_fibSet_three : ¬ IsAccessible fibSet 3 := by
  intro hacc
  obtain ⟨χ, hχ⟩ := thm_1
  obtain ⟨x, -, hx, hmono⟩ := hacc χ 19
  exact hχ x hx hmono

end Candidates.FibonacciNotThreeAccessible
