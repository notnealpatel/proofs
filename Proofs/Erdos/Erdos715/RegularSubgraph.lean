/-
  Erdős Problem #715 — every 4-regular multigraph plus an edge contains a
  3-regular subgraph (Alon–Friedland–Kalai), via Chevalley–Warning over F₃.

  PROVENANCE. erdosproblems.com/715: "Does every regular graph of degree 4
  contain a regular subgraph of degree 3?" — a problem of Berge (or
  Berge–Sauer). The answer for simple graphs is yes (Tashkinov, "Regular
  subgraphs of regular graphs", Soviet Math. Dokl. 26 (1982), 37–38 — NOT
  formalized here; that proof is elementary-combinatorial and much harder).
  Alon–Friedland–Kalai proved the companion result that this file formalizes:

    every 4-regular (loopless) MULTIGRAPH plus an edge contains a
    3-regular subgraph,

  [AFK84a] N. Alon, S. Friedland, G. Kalai, "Regular subgraphs of almost
    regular graphs", J. Combin. Theory Ser. B 37 (1984), 79–91 (Theorem 4.1
    at q = 3: every loopless multigraph of type (4,5) has a 3-regular
    subgraph; statement (1.1) there is the "plus an edge" form);
  [AFK84b] N. Alon, S. Friedland, G. Kalai, "Every 4-regular graph plus an
    edge contains a 3-regular subgraph", J. Combin. Theory Ser. B 37 (1984),
    92–93 (the note cited by erdosproblems.com/715).

  EXACT CLAIM BOUNDARY. The symbolic prime theorem
  `exists_prime_regular_submultiset` formalizes [AFK84a] Theorem 2.1
  with d_j = 1 and the divisible-subgraph threshold of Theorem 3.1,
  followed by degree pinning: maximum degree ≤ 2p−1 and m > (p−1)n
  yield a nonempty submultigraph with all degrees zero or p. This is
  not an identification with Theorem 4.1, which is a type-(k,k+1) result.
  The original p = 3 consumers and polynomial APIs are retained.

  We also formalize the Chevalley–Warning core of the AFK
  argument for the prime q = 3 (their §2–§3 route, [AFK84a] Theorem 3.1
  specialized to p = 3, d = 1), in the strongest local form:

    `exists_three_regular_submultiset`:
      every loopless multigraph with all degrees ≤ 5 and  m > 2n  edges
      (n = #vertices, m = #edges with multiplicity) contains a nonempty
      sub-multigraph in which every vertex has degree 0 or 3.

  This implies the headline (`four_regular_plus_edge`): a 4-regular loopless
  multigraph E has m = 2n by the handshake lemma (`sum_deg`), so E plus any
  extra non-loop edge — parallel edges allowed — has max degree ≤ 5 and
  m = 2n + 1 > 2n. A restatement for `SimpleGraph` plus one (possibly
  parallel) edge is `simpleGraph_four_regular_plus_edge`. Degrees ≤ 5
  arbitrary is formally more general than AFK's type-(4,5) hypothesis
  (degrees ∈ {4,5}, one vertex of degree 5), which forces
  2m = Σ_v deg(v) ≥ 4n + 1, i.e. m > 2n.

  The "plus an edge" hypothesis is essential in the multigraph setting:
  [AFK84a] remark that doubling every edge of an odd cycle gives a 4-regular
  multigraph with no 3-regular subgraph. The smallest instance, the doubled
  triangle, is machine-checked below (`doubledTriangle_no_three_regular`,
  by `decide`), so the m > 2n threshold in the main theorem is sharp.

  METHOD ([AFK84a] §2–§3, exposited in Alon, "Combinatorial Nullstellensatz",
  Combin. Probab. Comput. 8 (1999), §6). Work over F₃ with one variable x_e
  per edge (parallel edges get distinct variables; the multiset of edges is
  enumerated by a list). For each vertex v set  f_v = Σ_{e ∋ v} x_e².  Then
  deg f_v = 2, so Σ_v deg f_v ≤ 2n < m, and the Chevalley–Warning theorem
  (Mathlib: `char_dvd_card_solutions_of_fintype_sum_lt`) makes the number of
  common zeros divisible by 3; since x = 0 is a zero, a common zero x ≠ 0
  exists. On its support S := {e : x_e ≠ 0} every square x_e² equals 1, so
  deg_S(v) ≡ 0 (mod 3) for every v; deg_S(v) ≤ deg_E(v) ≤ 5 pins
  deg_S(v) ∈ {0, 3}.

  CARRIER. A multigraph on a finite vertex type `V` is a
  `Multiset (Sym2 V)` all of whose members are non-diagonal (loopless;
  parallel edges = multiplicity). `deg E v` counts, with multiplicity, the
  edges containing `v` — for loopless edge multisets this is the
  graph-theoretic vertex degree. A "3-regular subgraph" is a sub-multiset
  `S ≤ E`, `S ≠ 0`, with `deg S v ∈ {0, 3}` for every `v` — i.e. a
  3-regular multigraph on the vertices it touches. Note the algebraic core
  (`exists_support_list`) does not need looplessness; the hypothesis enters
  only to make `deg` the honest degree and to make `S` a genuine loopless
  multigraph.

  Axiom audit (2026-07-11, `#print axioms` via `lake env lean`): every
  theorem below — `exists_three_regular_submultiset`,
  `four_regular_plus_edge`, `simpleGraph_four_regular_plus_edge`,
  `doubledTriangle_no_three_regular`, `sum_deg` — depends on exactly
  [propext, Classical.choice, Quot.sound]. No `sorryAx`, no
  `native_decide`: the two `decide` certificates (the doubled-triangle
  scan over all 64 sub-multisets and the F₃ square fact
  `sq_eq_one_of_ne_zero`) reduce in the kernel.
-/

import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

open Finset MvPolynomial

namespace Erdos715

variable {V : Type*} [DecidableEq V]

-- ════════════════════════════════════════════════════════════════════
-- §1 DEGREE IN AN EDGE MULTISET
-- ════════════════════════════════════════════════════════════════════

/-- The degree of a vertex `v` in a multiset `E` of edges: the number of
edges of `E`, counted with multiplicity, that contain `v`. For loopless
`E` (no member is diagonal) this is the graph-theoretic vertex degree. -/
def deg (E : Multiset (Sym2 V)) (v : V) : ℕ :=
  E.countP (v ∈ ·)

@[simp] lemma deg_zero (v : V) : deg (0 : Multiset (Sym2 V)) v = 0 :=
  Multiset.countP_zero _

lemma deg_cons (e : Sym2 V) (E : Multiset (Sym2 V)) (v : V) :
    deg (e ::ₘ E) v = deg E v + if v ∈ e then 1 else 0 :=
  Multiset.countP_cons _ _ _

lemma deg_mono {S E : Multiset (Sym2 V)} (h : S ≤ E) (v : V) :
    deg S v ≤ deg E v :=
  Multiset.countP_le_of_le _ h

/-- A loopless edge has exactly two endpoints. -/
lemma card_filter_mem_eq_two [Fintype V] {e : Sym2 V} (he : ¬ e.IsDiag) :
    #{v | v ∈ e} = 2 := by
  induction e with
  | h a b =>
    rw [Sym2.mk_isDiag_iff] at he
    have hab : ({v | v ∈ (s(a, b) : Sym2 V)} : Finset V) = {a, b} := by
      ext c
      simp [Sym2.mem_iff]
    rw [hab, Finset.card_pair he]

/-- Handshake lemma for loopless edge multisets:
the degrees sum to twice the number of edges. -/
lemma sum_deg [Fintype V] (E : Multiset (Sym2 V)) :
    (∀ e ∈ E, ¬ e.IsDiag) → ∑ v, deg E v = 2 * Multiset.card E := by
  induction E using Multiset.induction_on with
  | empty => intro _; simp
  | cons e E ih =>
    intro hE
    have he : ¬ e.IsDiag := hE e (Multiset.mem_cons_self e E)
    have hE' : ∀ f ∈ E, ¬ f.IsDiag := fun f hf => hE f (Multiset.mem_cons_of_mem hf)
    simp only [deg_cons, Finset.sum_add_distrib, ih hE', Finset.sum_boole,
      Nat.cast_id, card_filter_mem_eq_two he, Multiset.card_cons]
    ring

-- ════════════════════════════════════════════════════════════════════
-- §2 THE CHEVALLEY–WARNING VERTEX POLYNOMIALS OVER F₃
-- ════════════════════════════════════════════════════════════════════

/-- The vertex polynomial of `v` for an edge list `l`, over `F₃`:
`f_v = Σ_{i : v ∈ l[i]} X_i ^ 2`, one variable per list position, so
parallel edges get distinct variables. -/
noncomputable def vertexPoly (l : List (Sym2 V)) (v : V) :
    MvPolynomial (Fin l.length) (ZMod 3) :=
  ∑ i ∈ {j | v ∈ l.get j}, X i ^ 2

lemma eval_vertexPoly (l : List (Sym2 V)) (x : Fin l.length → ZMod 3) (v : V) :
    eval x (vertexPoly l v) = ∑ i ∈ {j | v ∈ l.get j}, x i ^ 2 := by
  simp [vertexPoly]

lemma totalDegree_vertexPoly (l : List (Sym2 V)) (v : V) :
    (vertexPoly l v).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun _ _ => le_of_eq (totalDegree_X_pow _ _)

/-- The nonzero squares of `F₃`. -/
lemma sq_eq_one_of_ne_zero : ∀ a : ZMod 3, a ≠ 0 → a ^ 2 = 1 := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 THE CORE ARGUMENT
-- ════════════════════════════════════════════════════════════════════

/-- Vertex polynomial over the prime field, with one variable per edge occurrence. -/
noncomputable def primeVertexPoly (p : ℕ) (l : List (Sym2 V)) (v : V) :
    MvPolynomial (Fin l.length) (ZMod p) :=
  ∑ i ∈ {j | v ∈ l.get j}, X i ^ (p - 1)

/-- Evaluation of the prime vertex polynomial is the sum of incident powers. -/
lemma eval_primeVertexPoly (p : ℕ) (l : List (Sym2 V))
    (x : Fin l.length → ZMod p) (v : V) :
    eval x (primeVertexPoly p l v) = ∑ i ∈ {j | v ∈ l.get j}, x i ^ (p - 1) := by
  simp [primeVertexPoly]

/-- Each prime vertex polynomial has total degree at most `p - 1`. -/
lemma totalDegree_primeVertexPoly (p : ℕ) (hp : Nat.Prime p)
    (l : List (Sym2 V)) (v : V) :
    (primeVertexPoly p l v).totalDegree ≤ p - 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact totalDegree_finsetSum_le fun _ _ => le_of_eq (totalDegree_X_pow _ _)

/-- The new polynomial agrees with the original polynomial at prime three. -/
example (l : List (Sym2 V)) (v : V) : primeVertexPoly 3 l v = vertexPoly l v := rfl

/-- At prime two each incident variable occurs to the first power. -/
example (l : List (Sym2 V)) (v : V) :
    primeVertexPoly 2 l v = ∑ i ∈ {j | v ∈ l.get j}, X i := by
  simp [primeVertexPoly]

/-- Fermat's identity in the prime field for a nonzero element. -/
lemma prime_pow_eq_one (p : ℕ) (hp : Nat.Prime p) (x : ZMod p) (hx : x ≠ 0) :
    x ^ (p - 1) = 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  simpa only [ZMod.card] using FiniteField.pow_card_sub_one_eq_one x hx

/-- A multiple of a prime below twice that prime is zero or the prime itself. -/
lemma prime_degree_pinning (p : ℕ) (hp : Nat.Prime p) (d : ℕ)
    (hd : p ∣ d) (hb : d ≤ 2 * p - 1) : d = 0 ∨ d = p := by
  have hp2 := hp.two_le
  obtain ⟨k, rfl⟩ := hd
  have hk : k < 2 := by
    by_contra hn
    have hmul : p * 2 ≤ p * k := Nat.mul_le_mul_left p (by omega)
    omega
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl <;> simp

/-- AFK's prime Chevalley–Warning core on an occurrence-indexed edge list:
more than `(p - 1) * #V` edges and degrees at most `2*p - 1` yield a
nonempty submultiset with degrees zero or `p`. Looplessness is not needed here. -/
lemma exists_prime_support_list [Fintype V] (p : ℕ) (hp : Nat.Prime p) (l : List (Sym2 V))
    (hdeg : ∀ v, deg (l : Multiset (Sym2 V)) v ≤ 2 * p - 1)
    (hcard : (p - 1) * Fintype.card V < l.length) :
    ∃ S ≤ (l : Multiset (Sym2 V)), S ≠ 0 ∧ ∀ v, deg S v = 0 ∨ deg S v = p := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hexp : p - 1 ≠ 0 := by omega
  -- Chevalley–Warning over the prime field: sum of degrees is less than the variable count.
  have hsum : (∑ v : V, (primeVertexPoly p l v).totalDegree) < Fintype.card (Fin l.length) := by
    calc ∑ v : V, (primeVertexPoly p l v).totalDegree
        ≤ ∑ _v : V, (p - 1) := Finset.sum_le_sum fun v _ => totalDegree_primeVertexPoly p hp l v
      _ = (p - 1) * Fintype.card V := by simp [Finset.sum_const, mul_comm]
      _ < l.length := hcard
      _ = Fintype.card (Fin l.length) := (Fintype.card_fin _).symm
  have hdvd : p ∣ Fintype.card
      {x : Fin l.length → ZMod p // ∀ v, eval x (primeVertexPoly p l v) = 0} :=
    char_dvd_card_solutions_of_fintype_sum_lt p hsum
  -- Zero is a common zero, but a prime cannot divide one.
  have h0 : ∀ v, eval (0 : Fin l.length → ZMod p) (primeVertexPoly p l v) = 0 := by
    intro v
    rw [eval_primeVertexPoly]
    simp [hexp]
  obtain ⟨x, hxsol, hxne⟩ :
      ∃ x : Fin l.length → ZMod p, (∀ v, eval x (primeVertexPoly p l v) = 0) ∧ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hone : Fintype.card
        {x : Fin l.length → ZMod p // ∀ v, eval x (primeVertexPoly p l v) = 0} = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨0, h0⟩, fun y => Subtype.ext (hcon y.1 y.2)⟩
    rw [hone] at hdvd
    exact hp.not_dvd_one hdvd
  -- the support of x, as a sub-multiset of the edge multiset
  set T : Finset (Fin l.length) := {i | x i ≠ 0} with hT
  have hSle : T.val.map l.get ≤ (l : Multiset (Sym2 V)) := by
    calc T.val.map l.get
        ≤ (Finset.univ.val : Multiset (Fin l.length)).map l.get :=
          Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ T))
      _ = (l : Multiset (Sym2 V)) := by
          rw [Finset.val_univ_fin, Multiset.map_coe, List.map_get_finRange]
  refine ⟨T.val.map l.get, hSle, ?_, ?_⟩
  · -- nonemptiness: x has support
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxne
    intro hS0
    have hiT : i ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hi
    have : l.get i ∈ T.val.map l.get :=
      Multiset.mem_map_of_mem _ (Finset.mem_val.mpr hiT)
    rw [hS0] at this
    exact Multiset.notMem_zero _ this
  · -- Divisibility and the strict twice-prime bound pin each support degree.
    intro v
    have hdvdp : p ∣ deg (T.val.map l.get) v := by
      have hcount : deg (T.val.map l.get) v = #(T.filter (fun i => v ∈ l.get i)) := by
        rw [deg, Multiset.countP_map]
        rfl
      rw [← ZMod.natCast_eq_zero_iff _ p, hcount]
      have hfilter : T.filter (fun i => v ∈ l.get i)
          = ({i | v ∈ l.get i} : Finset (Fin l.length)).filter (fun i => x i ≠ 0) := by
        rw [hT, Finset.filter_comm]
      rw [hfilter]
      calc (#(({i | v ∈ l.get i} : Finset (Fin l.length)).filter (fun i => x i ≠ 0)) : ZMod p)
          = ∑ i ∈ ({i | v ∈ l.get i} : Finset (Fin l.length)).filter (fun i => x i ≠ 0),
              (1 : ZMod p) := by simp
        _ = ∑ i ∈ ({i | v ∈ l.get i} : Finset (Fin l.length)).filter (fun i => x i ≠ 0),
              x i ^ (p - 1) :=
            Finset.sum_congr rfl fun i hi =>
              (prime_pow_eq_one p hp _ (Finset.mem_filter.mp hi).2).symm
        _ = ∑ i ∈ ({i | v ∈ l.get i} : Finset (Fin l.length)), x i ^ (p - 1) :=
            Finset.sum_filter_of_ne fun i _ h hxi => h (by rw [hxi]; exact zero_pow hexp)
        _ = eval x (primeVertexPoly p l v) := (eval_primeVertexPoly p l x v).symm
        _ = 0 := hxsol v
    have hbound : deg (T.val.map l.get) v ≤ 2 * p - 1 := (deg_mono hSle v).trans (hdeg v)
    exact prime_degree_pinning p hp _ hdvdp hbound

/-- Core of the AFK theorem at prime three, preserving the original list API. -/
lemma exists_support_list [Fintype V] (l : List (Sym2 V))
    (hdeg : ∀ v, deg (l : Multiset (Sym2 V)) v ≤ 5)
    (hcard : 2 * Fintype.card V < l.length) :
    ∃ S ≤ (l : Multiset (Sym2 V)), S ≠ 0 ∧ ∀ v, deg S v = 0 ∨ deg S v = 3 := by
  exact exists_prime_support_list 3 (by decide) l hdeg hcard

/-- AFK's prime regular-subgraph theorem: a loopless multigraph with degrees
at most `2*p - 1` and more than `(p - 1) * #V` edges contains a nonempty
loopless submultigraph whose touched vertices all have degree `p`.
This is the prime case of AFK1984 §2–§3 (Theorems 2.1 and 3.1), with degree pinning. -/
theorem exists_prime_regular_submultiset [Fintype V] (p : ℕ) (hp : Nat.Prime p)
    (E : Multiset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (hdeg : ∀ v, deg E v ≤ 2 * p - 1)
    (hcard : (p - 1) * Fintype.card V < Multiset.card E) :
    ∃ S ≤ E, S ≠ 0 ∧ (∀ e ∈ S, ¬ e.IsDiag) ∧ ∀ v, deg S v = 0 ∨ deg S v = p := by
  obtain ⟨l, rfl⟩ : ∃ l : List (Sym2 V), (l : Multiset (Sym2 V)) = E :=
    ⟨E.toList, E.coe_toList⟩
  obtain ⟨S, hSle, hSne, hSdeg⟩ :=
    exists_prime_support_list p hp l hdeg (by simpa using hcard)
  exact ⟨S, hSle, hSne, fun e he => hE e (Multiset.mem_of_le hSle he), hSdeg⟩

/-- Prime two is jointly satisfiable on three parallel non-loop edges. -/
example : Nat.Prime 2 ∧
    (∀ e ∈ ({s(0, 1), s(0, 1), s(0, 1)} : Multiset (Sym2 (Fin 2))), ¬ e.IsDiag) ∧
    (∀ v, deg ({s(0, 1), s(0, 1), s(0, 1)} : Multiset (Sym2 (Fin 2))) v ≤ 2 * 2 - 1) ∧
    (2 - 1) * Fintype.card (Fin 2) <
      ({s(0, 1), s(0, 1), s(0, 1)} : Multiset (Sym2 (Fin 2))).card := by decide

/-- Prime three is jointly satisfiable on five parallel non-loop edges. -/
example : Nat.Prime 3 ∧
    (∀ e ∈ ({s(0, 1), s(0, 1), s(0, 1), s(0, 1), s(0, 1)} :
      Multiset (Sym2 (Fin 2))), ¬ e.IsDiag) ∧
    (∀ v, deg ({s(0, 1), s(0, 1), s(0, 1), s(0, 1), s(0, 1)} :
      Multiset (Sym2 (Fin 2))) v ≤ 2 * 3 - 1) ∧
    (3 - 1) * Fintype.card (Fin 2) <
      ({s(0, 1), s(0, 1), s(0, 1), s(0, 1), s(0, 1)} :
        Multiset (Sym2 (Fin 2))).card := by decide

-- ════════════════════════════════════════════════════════════════════
-- §4 MAIN THEOREM AND THE 4-REGULAR-PLUS-EDGE COROLLARIES
-- ════════════════════════════════════════════════════════════════════

/-- **Alon–Friedland–Kalai, Chevalley–Warning core at q = 3** ([AFK84a]
Theorem 3.1 for p = 3 plus the degree pinning of §4): every loopless
multigraph with maximum degree at most 5 and more than `2 * #V` edges
contains a nonempty (loopless) sub-multigraph in which every vertex has
degree 0 or 3 — a 3-regular subgraph on the vertices it touches. -/
theorem exists_three_regular_submultiset [Fintype V]
    (E : Multiset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (hdeg : ∀ v, deg E v ≤ 5) (hcard : 2 * Fintype.card V < Multiset.card E) :
    ∃ S ≤ E, S ≠ 0 ∧ (∀ e ∈ S, ¬ e.IsDiag) ∧ ∀ v, deg S v = 0 ∨ deg S v = 3 := by
  obtain ⟨l, rfl⟩ : ∃ l : List (Sym2 V), (l : Multiset (Sym2 V)) = E :=
    ⟨E.toList, E.coe_toList⟩
  obtain ⟨S, hSle, hSne, hSdeg⟩ := exists_support_list l hdeg (by simpa using hcard)
  exact ⟨S, hSle, hSne, fun e he => hE e (Multiset.mem_of_le hSle he), hSdeg⟩

/-- **Erdős #715, multigraph form (Alon–Friedland–Kalai [AFK84b])**: every
4-regular loopless multigraph plus one extra edge — parallel to an existing
edge or not — contains a 3-regular subgraph. -/
theorem four_regular_plus_edge [Fintype V]
    (E : Multiset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (hreg : ∀ v, deg E v = 4) (e : Sym2 V) (he : ¬ e.IsDiag) :
    ∃ S ≤ e ::ₘ E, S ≠ 0 ∧ (∀ f ∈ S, ¬ f.IsDiag) ∧ ∀ v, deg S v = 0 ∨ deg S v = 3 := by
  apply exists_three_regular_submultiset
  · intro f hf
    rcases Multiset.mem_cons.mp hf with rfl | hf
    exacts [he, hE f hf]
  · intro v
    rw [deg_cons]
    have := hreg v
    split_ifs <;> omega
  · -- handshake: 4-regularity forces exactly 2·#V edges, so now 2·#V + 1
    have hhs : ∑ v, deg E v = 2 * Multiset.card E := sum_deg E hE
    have hsum : ∑ v, deg E v = 4 * Fintype.card V := by
      simp [hreg, Finset.sum_const, Finset.card_univ, mul_comm]
    rw [Multiset.card_cons]
    omega

/-- **Erdős #715 for a `SimpleGraph` (Alon–Friedland–Kalai)**: the edge
multiset of a 4-regular simple graph, plus one extra non-loop edge (possibly
parallel to an existing edge), contains a 3-regular subgraph. -/
theorem simpleGraph_four_regular_plus_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree 4)
    (e : Sym2 V) (he : ¬ e.IsDiag) :
    ∃ S ≤ e ::ₘ G.edgeFinset.val, S ≠ 0 ∧ (∀ f ∈ S, ¬ f.IsDiag) ∧
      ∀ v, deg S v = 0 ∨ deg S v = 3 := by
  apply four_regular_plus_edge _ _ _ _ he
  · intro f hf
    exact G.not_isDiag_of_mem_edgeSet
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_val.mp hf))
  · intro v
    rw [deg, Multiset.countP_eq_card_filter, ← Finset.filter_val,
      ← SimpleGraph.incidenceFinset_eq_filter]
    exact Eq.trans (SimpleGraph.card_incidenceFinset_eq_degree G v) (hreg v)

-- ════════════════════════════════════════════════════════════════════
-- §5 SHARPNESS: THE DOUBLED TRIANGLE
-- ════════════════════════════════════════════════════════════════════

/-- The doubled triangle: three vertices, each pair joined by two parallel
edges — the smallest doubled odd cycle, [AFK84a]'s counterexample family. -/
def doubledTriangle : Multiset (Sym2 (Fin 3)) :=
  {s(0, 1), s(0, 1), s(1, 2), s(1, 2), s(0, 2), s(0, 2)}

/-- The doubled triangle is a loopless 4-regular multigraph (with
`2 * #V = 6` edges, exactly at the threshold of the main theorem). -/
example : (∀ e ∈ doubledTriangle, ¬ e.IsDiag) ∧
    (∀ v, deg doubledTriangle v = 4) ∧ Multiset.card doubledTriangle = 6 := by
  decide

/-- The 4-regular doubled triangle has NO 3-regular subgraph: the extra
edge in `four_regular_plus_edge` is essential for multigraphs (for simple
graphs it is not — Tashkinov 1982, not formalized here). -/
theorem doubledTriangle_no_three_regular :
    ¬ ∃ S ≤ doubledTriangle, S ≠ 0 ∧ ∀ v, deg S v = 0 ∨ deg S v = 3 := by
  have key : ∀ S ∈ doubledTriangle.powerset,
      S = 0 ∨ ¬ (∀ v, deg S v = 0 ∨ deg S v = 3) := by decide
  rintro ⟨S, hle, hne, hdeg⟩
  rcases key S (Multiset.mem_powerset.mpr hle) with h | h
  · exact hne h
  · exact h hdeg

end Erdos715
