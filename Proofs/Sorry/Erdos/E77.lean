/-
  Erdős Problem #77 — growth of diagonal Ramsey numbers.
  Status: open.  Prize: $100 for existence of the limit ([Er61]),
  $10000 offered in [Er88] for non-existence ("as a joke"); the DB
  list endpoint reports $250 but this appears to conflate with prizes
  on related Ramsey problems — primary-source prize is $100.
  Tier C infrastructure target: R(k) is not in Mathlib; defining it
  unlocks #781-adjacent and #112 work.

  Verbatim statement (`goof erdos fetch 77`, pulled 2026-08-05):

    "If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such
    that every $2$-colouring of the edges of $K_n$ contains a
    monochromatic copy of $K_k$, then find the value of
    \[\lim_{k\to \infty}R(k)^{1/k}.\]"

  DB remarks: Erdős proved √2 ≤ liminf ≤ limsup ≤ 4; upper bound
  4 − 1/128 (Campos–Griffiths–Morris–Sahasrabudhe [CGMS23]), then
  3.7992… (Gupta–Ndiaye–Norin–Wei [GNNW24]); simpler 4 − c proof
  [BBCGHMST24].  Erdős: "perhaps it is 2 but we have no real
  evidence".  Recorded as C₁₇ in Tao's optimization-problems repo
  (comment).  OEIS anchor: A059442 (diagonal Ramsey: 1, 2, 6, 18;
  R(5) unknown, 43–46).

  Mathlib inventory (leandoc 2026-08-05): NO Ramsey numbers in Mathlib
  (search "ramsey number graph" returns only extremal/Turán API).
  A 2-coloring of E(K_n) is encoded as a graph G on Fin n (color 1 =
  G-edges, color 2 = non-edges); "monochromatic K_k" = ¬CliqueFree in
  G or in Gᶜ.  `SimpleGraph.CliqueFree` exists.
-/
import Mathlib
import Sorry.Erdos.Erdos77.ClassicalBounds
import Sorry.Erdos.RamseySmallNumbers
import Sorry.Erdos.RamseyProbabilisticLowerBound

set_option autoImplicit false

namespace ErdosCandidates.E77

open SimpleGraph

/-- The pentagon on five vertices and its complement both have no three-clique.
The certificate checks only the 32 vertex subsets, not an enumeration of graphs. -/
private theorem pentagon_cliqueFree_pair :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by
  let G : SimpleGraph (Fin 5) := SimpleGraph.fromRel
    (fun a b => (a.val + 1) % 5 = b.val)
  have hfinite : ∀ t ∈ (Finset.univ : Finset (Fin 5)).powerset,
      ¬G.IsNClique 3 t ∧ ¬Gᶜ.IsNClique 3 t := by
    decide
  refine ⟨G, ?_, ?_⟩
  · intro t
    exact (hfinite t (Finset.mem_powerset.mpr (Finset.subset_univ t))).1
  · intro t
    exact (hfinite t (Finset.mem_powerset.mpr (Finset.subset_univ t))).2

/-- Ground truth, small values (A059442 / classical): `R 1 = 1`,
    `R 2 = 2`, `R 3 = 6`.  `R 3 = 6`: the pentagon 2-coloring shows
    5 < R 3 (C₅ and its complement are triangle-free), and every
    graph on 6 vertices has a monochromatic triangle (the classical
    pigeonhole).  -- PROVABLE (R 3 via native_decide over 2^15 graphs
    on 6 vertices, or the pigeonhole argument by hand; the C₅ witness
    by decide).  Effort S–M. -/
theorem R_three : R 3 = 6 := by
  have hupper : R 3 ≤ 6 := by
    have hchoose : Nat.choose 4 2 = 6 := by decide
    simpa only [show 2 * 3 - 2 = 4 from rfl, show 3 - 1 = 2 from rfl,
      hchoose] using R_le_choose 3 (by decide)
  have hnot : ¬R 3 ≤ 5 := by
    intro hle
    obtain ⟨G, hG, hGc⟩ := pentagon_cliqueFree_pair
    rcases (R_le_iff 5 3).mp hle G with h | h
    · exact h hG
    · exact h hGc
  have hlower : 6 ≤ R 3 := by omega
  exact Nat.le_antisymm hupper hlower

/-- `R 4 = 18` (Greenwood–Gleason), the boundary of feasible
    verification: 2^{C(17,2)} colorings is far beyond brute force, but
    the classical proof (R(4) ≤ R(3)+R(4,3)-ish recursions plus the
    Paley graph on 17 vertices as witness) is a bounded combinatorial
    argument.  Recorded as the stretch certificate target. -/
theorem R_four : R 4 = 18 :=
  ErdosCandidates.RamseySmallNumbers.R_four

/-- **Erdős #77 (OPEN, $100)**: the limit `lim R(k)^{1/k}` exists.
    (Determining its value is the full problem; existence alone was
    the $100 prize.)  Stated via `Filter.Tendsto` to a positive real. -/
theorem erdos_77_limit_exists :
    ∃ L : ℝ, 1 < L ∧
      Filter.Tendsto (fun k : ℕ => (R k : ℝ) ^ ((1 : ℝ) / k))
        Filter.atTop (nhds L) := by
  sorry

/-- **Erdős's classical bounds**, the two genuinely formalizable
    theorems of this lane:
    (a) upper: `R k ≤ 4^k` (Erdős–Szekeres pigeonhole double
        induction);
    (b) lower: `√2^k ≤ R k` for large k — the probabilistic/counting
        bound `2^{k/2} ≤ R(k)` (finite union bound over cliques;
        rational arithmetic, no measure theory needed).
    Effort M each. -/
theorem R_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (R k : ℝ) :=
  ErdosCandidates.RamseyProbabilisticLowerBound.R_lower_bound k hk

/-- **CGMS 2023 / GNNW 2024**, archived: `limsup R(k)^{1/k} ≤ 3.7993`
    (the current record 3.7992…, rounded up to keep the constant
    honest).  Way beyond current formalization reach (container-style
    book arguments); archived for the record. -/
theorem gnnw_upper :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (R k : ℝ) ^ ((1 : ℝ) / k) ≤ 3.7993 := by
  sorry

end ErdosCandidates.E77

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 77` exactly.
   - Prize: DB list endpoint reports $250, but primary source is $100 for existence
     ([Er61]); $10000 for non-existence (joke, [Er88]). Corrected to $100.
   - HasRamseyProperty encoding (G vs complement, CliqueFree) is faithful to the 2-coloring
     definition. No Ramsey number def in Mathlib (grep confirmed: only Hindman/HalesJewett).
   - R(3)=6 and C5 witness: C5 and its complement (also C5) are both triangle-free; correct.
   - R(4)=18 Greenwood-Gleason: standard, correctly attributed.
   - Erdos bounds sqrt(2) <= liminf, limsup <= 4: matches DB.
   - CGMS 4-1/128 and GNNW 3.7992: matches DB. File rounds to 3.7993 (safe upper bound).
   - BBCGHMST24 simpler proof: mentioned in DB, file header.
   - Tao C17 comment: matches DB comment by TerenceTao.
   - OEIS A059442 mentioned; DB does not mention it but file marks it as an anchor (acceptable).
-/
