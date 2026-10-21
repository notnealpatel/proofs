/- Historical/source claims below are retained verbatim, not independently paper-audited.
   A fresh `erdos fetch 86` matched the current statement and reported literature bounds;
   that source check does not establish primary-paper verification. -/
/-
  Erdős Problem #86 — C₄-free subgraphs of the hypercube.
  Status: open; $100.  Tier B archive target with certificate layer.

  Verbatim statement (`goof erdos fetch 86`, pulled 2026-08-05):

    "Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has
    $2^n$ vertices and $n2^{n-1}$ edges). Is it true that every subgraph
    of $Q_n$ with
    \[\geq \left(\frac{1}{2}+o(1)\right)n2^{n-1}\]
    many edges contains a $C_4$?"

  DB remarks: with f(n) = max C₄-free edge count, the conjecture is
  f(n) ≤ (1/2 + o(1))·n·2^{n-1}.  Erdős [Er91]: f(n) ≥ (1/2 + c/n)·n·2^{n-1};
  Brass–Harborth–Nienborg [BHN95]: f(n) ≥ (1/2 + c/√n)·n·2^{n-1}.
  Balogh–Hu–Lidický–Liu [BHLL14]: f(n) ≤ 0.6068·n·2^{n-1}; Baber
  [Ba12b]: f(n) ≤ 0.60318·n·2^{n-1}.  Comment (rafalwrona, May 2026,
  comment-sourced): explicit C₄-free edge-list certificates for Q₉–Q₁₅
  (e.g. Q₉: 1505 edges), verified by exhaustive 4-cycle enumeration.

  OEIS anchor: A245762.

  Mathlib inventory (leandoc 2026-08-05): no hypercube graph
  (leandoc miss "hypercube"); `SimpleGraph.cycleGraph`,
  `SimpleGraph.Free` (`¬ A ⊑ B`, Copy.lean) for C₄-containment;
  `SimpleGraph.edgeFinset.card` for edge counts.  Q_n defined fresh
  below on `Fin n → Bool`.
-/
import Combinatorics.HypercubeGraph

set_option autoImplicit false

namespace ErdosCandidates.E86

open SimpleGraph

/-- The `n`-dimensional hypercube graph on `Fin n → Bool`: adjacent iff
    the points differ in exactly one coordinate.  (Fresh def; leandoc
    confirms no Mathlib hypercube graph.  `Finset.filter` over `univ`
    keeps it decidable.) -/
abbrev hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) := HypercubeGraph.hypercube n

/-- Ground truth: `Q_n` has `2^n` vertices and `n·2^{n-1}` edges (the
    DB's own parenthetical).  -- PROVABLE (double counting; or decide
    for n ≤ 3). -/
theorem hypercube_card_verts (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n :=
  HypercubeGraph.hypercube_card_verts n

/-- The finite hypercube edge count, now proved in the production unit. -/
theorem hypercube_card_edges (n : ℕ) [DecidableRel (hypercube n).Adj] :
    (hypercube n).edgeFinset.card = n * 2 ^ (n - 1) :=
  HypercubeGraph.hypercube_card_edges n

/-- `C4Free H`: `H` contains no 4-cycle, via Mathlib's `Free`
    (no copy of `cycleGraph 4`). -/
abbrev C4Free {V : Type*} (H : SimpleGraph V) : Prop := HypercubeGraph.C4Free H

/-- Sanity: `Q_2` is itself a 4-cycle, so `Q_2` is NOT C₄-free, and
    deleting any edge of `Q_2` leaves a C₄-free graph with 3 edges.
    -- PROVABLE (decide-scale). -/
example : ¬ C4Free (hypercube 2) := HypercubeGraph.not_c4Free_hypercube_two

/-- `maxC4FreeEdges n`: the extremal count `f(n)` — the largest number
    of edges of a C₄-free subgraph of `Q_n`.  Encoded as a sup over
    subgraphs `H ≤ hypercube n` (classical choice for the filter). -/
noncomputable abbrev maxC4FreeEdges (n : ℕ) : ℕ := HypercubeGraph.maxC4FreeEdges n

/-- **Erdős #86 (OPEN, $100)**: `f(n) ≤ (1/2 + o(1))·n·2^{n-1}` —
    every subgraph of `Q_n` with `(1/2 + ε)·n·2^{n-1}` edges contains a
    C₄, for every `ε > 0` and `n` large.

    Source text: "Is it true that every subgraph of $Q_n$ with
    $\geq (\frac{1}{2}+o(1))n2^{n-1}$ many edges contains a $C_4$?"

    Best known: `f(n) ≤ 0.60318·n·2^{n-1}` (Baber, flag algebras) —
    the flag-algebra certificate is a large SDP, an interesting but
    heavy verification target.  Archived. -/
theorem erdos_86 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (maxC4FreeEdges n : ℝ) ≤ (1 / 2 + ε) * n * 2 ^ (n - 1) := by
  sorry

/-- **BHN lower bound** (BHN95), archived: for some `c > 0` and all
    large `n`, `(1/2 + c/√n)·n·2^{n-1} ≤ f(n)`.  The construction is
    explicit (layered edge selection); a fully explicit finite slice is
    the certificate layer below. -/
theorem bhn_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 / 2 + c / Real.sqrt n) * n * 2 ^ (n - 1) ≤ (maxC4FreeEdges n : ℝ) := by
  sorry

/-- Edge mask of the external `Q₉` certificate (rafalwronapl/erdos86-hypercube-c4,
    file `q9_edges_repair_from1503_iter2.json`, SHA-256
    `0994be825ec39d115b65eb1436eace7c1be324448a6ec116d69c8a7e2a75d338`).
    Vertices are 9-bit codes; bit `9 * v + i` is set iff the cube edge
    `{v, v ^^^ 2 ^ i}` with `v` the lower endpoint is kept.  The data are
    only an input: everything about them is re-checked by the kernel below. -/
private def q9Mask : ℕ := 53625940114794791898547238123772173927778824148353718391191652569537396831705837568129685992853219037855387006417194327744853574459011507232850021110428242845249456022601287397774277637960470965511076711527819685932114054484518269462137044496603958211017405800682248365431056206235173509103595981221474363376642976966913710824796152629692633530426764311170308324474949893922746883171617305608054622155901252081697176124944712039603192101823424278305111674629628329886193976603796847897938582460536186723319169979064423577419681986959988141529969914916136651719476621245636754036819590014915974330271554367696859214691245205835854820457684878079532098891130306955628685915174690776115499688972440982220533745535703107538605501068146554108552610914270309650448284532031398575068257177220943231279916655913446697166067677887925248158302565551147449071070916997131665446181173098351046552136442216436925903640843655442343276672246906109735475309000562789320061154353528815240497159377020536213022505446224946299170577972247916918559658338090888528416044633123461279243620351022307821006616797364899189088678983507988937793484090648088644293605201417422165231403722720666582967639614543949968154844985998109324043180327112665737680633940780282285939593671406065470291358741261654351522615660031644324214894216380345513466086772879776211724926063632523048207071183653137826537136558667207

/-- `q9Keep a b`: the codes `a`, `b` differ in exactly one bit `i < 9`, and the
    corresponding edge is in the certificate mask. -/
private def q9Keep (a b : ℕ) : Bool :=
  (List.range 9).any fun i => a ^^^ b == 2 ^ i && q9Mask.testBit (9 * min a b + i)

/-- The edge-membership test is symmetric. -/
private theorem q9Keep_comm (a b : ℕ) : q9Keep a b = q9Keep b a := by
  unfold q9Keep
  rw [Nat.xor_comm, min_comm]

/-- Boolean check that no 2-face `{v, v⊕eᵢ, v⊕eⱼ, v⊕eᵢ⊕eⱼ}` of `Q₉` has all four
    edges in the certificate. -/
private def q9CheckFaces : Bool :=
  (List.range 512).all fun v => (List.range 9).all fun i => (List.range 9).all fun j =>
    i == j || !(q9Keep v (v ^^^ 2 ^ i) && q9Keep v (v ^^^ 2 ^ j) &&
      q9Keep (v ^^^ 2 ^ i) (v ^^^ 2 ^ i ^^^ 2 ^ j) && q9Keep (v ^^^ 2 ^ j) (v ^^^ 2 ^ i ^^^ 2 ^ j))

/-- Kernel evaluation of the 2-face check (about 30 s; no `native_decide`). -/
private theorem q9CheckFaces_eq : q9CheckFaces = true := by decide +kernel

/-- Unpacked 2-face check: if three edges of a 2-face are kept, the fourth is not. -/
private theorem q9_face {v i j : ℕ} (hv : v < 512) (hi : i < 9) (hj : j < 9) (hij : i ≠ j)
    (h1 : q9Keep v (v ^^^ 2 ^ i) = true) (h2 : q9Keep v (v ^^^ 2 ^ j) = true)
    (h3 : q9Keep (v ^^^ 2 ^ i) (v ^^^ 2 ^ i ^^^ 2 ^ j) = true) :
    q9Keep (v ^^^ 2 ^ j) (v ^^^ 2 ^ i ^^^ 2 ^ j) = false := by
  have h := q9CheckFaces_eq
  simp only [q9CheckFaces, List.all_eq_true, List.mem_range] at h
  have hv' := h v hv i hi j hj
  simpa [hij, h1, h2, h3] using hv'

/-- Kept edges, indexed by lower endpoint code and direction. -/
private def q9EdgeCodes : Finset (ℕ × Fin 9) :=
  (Finset.range 512 ×ˢ Finset.univ).filter
    (fun p => p.1.testBit p.2 = false ∧ q9Keep p.1 (p.1 ^^^ 2 ^ (p.2 : ℕ)) = true)

/-- The certificate has exactly 1505 edges (kernel count). -/
private theorem q9EdgeCodes_card : q9EdgeCodes.card = 1505 := by decide +kernel

/-- Flip coordinate `i` of a Boolean vector. -/
private def flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !(x j) else x j

/-- Flipping the same coordinate twice is the identity. -/
private theorem flipAt_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipAt (flipAt x i) i = x := by
  funext j
  by_cases hj : j = i <;> simp [flipAt, hj]

/-- A one-coordinate flip is a hypercube neighbour. -/
private theorem flipAt_adj {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (hypercube n).Adj x (flipAt x i) := by
  change (Finset.univ.filter (fun j => x j ≠ flipAt x i j)).card = 1
  have h : Finset.univ.filter (fun j => x j ≠ flipAt x i j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j; simp [flipAt]
    · simp [flipAt, hj]
  rw [h]
  simp

/-- Distinct coordinates give distinct flips. -/
private theorem flipAt_injective {n : ℕ} (x : Fin n → Bool) :
    Function.Injective (flipAt x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [flipAt, hij] at hi

/-- Every hypercube neighbour is a one-coordinate flip. -/
private theorem eq_flipAt_of_adj {n : ℕ} (x y : Fin n → Bool)
    (h : (hypercube n).Adj x y) : ∃ i, flipAt x i = y := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hdiff : ∀ j, x j ≠ y j ↔ j = i := by
    intro j
    have hm := congrArg (fun s : Finset (Fin n) => j ∈ s) hi
    simpa using hm
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    have hn : x i ≠ y i := (hdiff i).mpr rfl
    simp only [flipAt]
    cases hx : x i <;> cases hy : y i <;> simp_all
  · have he : x j = y j := not_ne_iff.mp (fun hn => hj ((hdiff j).mp hn))
    simp [flipAt, hj, he]

/-- In codes, flipping coordinate `i` is xor with `2 ^ i`. -/
private theorem ofBits_flipAt (x : Fin 9 → Bool) (i : Fin 9) :
    Nat.ofBits (flipAt x i) = Nat.ofBits x ^^^ 2 ^ (i : ℕ) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_ofBits, Nat.testBit_ofBits]
  by_cases hk : k < 9
  · by_cases hki : (i : ℕ) = k
    · subst hki
      simp [flipAt]
    · have hne : (⟨k, hk⟩ : Fin 9) ≠ i := fun h => hki (by rw [← h])
      simp [hk, flipAt, hne, hki]
  · have hki : (i : ℕ) ≠ k := by omega
    simp [hk, hki]

/-- Decode a 9-bit code into a Boolean vector. -/
private def bitsOf (v : ℕ) : Fin 9 → Bool := fun i => v.testBit i

/-- Decoding then encoding is the identity on codes below `2 ^ 9`. -/
private theorem ofBits_bitsOf {v : ℕ} (hv : v < 512) : Nat.ofBits (bitsOf v) = v := by
  change Nat.ofBits (fun i : Fin 9 => v.testBit i) = v
  rw [Nat.ofBits_testBit]
  exact Nat.mod_eq_of_lt hv

/-- Encoding then decoding is the identity on Boolean vectors. -/
private theorem bitsOf_ofBits (x : Fin 9 → Bool) : bitsOf (Nat.ofBits x) = x := by
  funext i
  simp [bitsOf]

/-- The certificate graph: hypercube edges whose code pair is kept by the mask. -/
private def certGraph : SimpleGraph (Fin 9 → Bool) where
  Adj x y := (hypercube 9).Adj x y ∧ q9Keep (Nat.ofBits x) (Nat.ofBits y) = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [q9Keep_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- Unfolding lemma for certificate adjacency. -/
private theorem certGraph_adj {x y : Fin 9 → Bool} :
    certGraph.Adj x y ↔
      (hypercube 9).Adj x y ∧ q9Keep (Nat.ofBits x) (Nat.ofBits y) = true := Iff.rfl

private instance : DecidableRel certGraph.Adj :=
  fun _ _ => decidable_of_iff _ certGraph_adj.symm

/-- The certificate is a subgraph of `Q₉`. -/
private theorem certGraph_le : certGraph ≤ hypercube 9 :=
  fun _ _ h => (certGraph_adj.mp h).1

/-- A hypercube 4-cycle `a, a⊕eᵢ, c, a⊕eⱼ` closes as a 2-face: `i ≠ j` and
    `c = a⊕eᵢ⊕eⱼ`. -/
private theorem square_eq (a : Fin 9 → Bool) (i j k l : Fin 9)
    (hac : a ≠ flipAt (flipAt a i) k) (hbd : flipAt a i ≠ flipAt a j)
    (h : flipAt (flipAt a i) k = flipAt (flipAt a j) l) : i ≠ j ∧ k = j := by
  have hij : i ≠ j := fun hij => hbd (by rw [hij])
  refine ⟨hij, ?_⟩
  by_contra hkj
  have hj := congrFun h j
  by_cases hlj : l = j
  · subst hlj
    exact hac (by rw [h, flipAt_flipAt])
  · have hji : j ≠ i := fun e => hij e.symm
    have hjk : j ≠ k := fun e => hkj e.symm
    have hjl : j ≠ l := fun e => hlj e.symm
    simp [flipAt, hji, hjk, hjl] at hj

/-- The certificate graph contains no 4-cycle. -/
private theorem certGraph_c4Free : C4Free certGraph := by
  rintro ⟨f⟩
  have hab : certGraph.Adj (f 0) (f 1) := f.toHom.map_rel (by decide)
  have hbc : certGraph.Adj (f 1) (f 2) := f.toHom.map_rel (by decide)
  have hdc : certGraph.Adj (f 3) (f 2) := f.toHom.map_rel (by decide)
  have had : certGraph.Adj (f 0) (f 3) := f.toHom.map_rel (by decide)
  have hac : f 0 ≠ f 2 := f.injective.ne (by decide)
  have hbd : f 1 ≠ f 3 := f.injective.ne (by decide)
  rw [certGraph_adj] at hab hbc hdc had
  obtain ⟨i, hi⟩ := eq_flipAt_of_adj _ _ hab.1
  obtain ⟨j, hj⟩ := eq_flipAt_of_adj _ _ had.1
  obtain ⟨k, hk⟩ := eq_flipAt_of_adj _ _ hbc.1
  obtain ⟨l, hl⟩ := eq_flipAt_of_adj _ _ hdc.1
  rw [← hi] at hk hbd
  rw [← hj] at hl hbd
  rw [← hk] at hac
  obtain ⟨hij, hkj⟩ := square_eq (f 0) i j k l hac hbd (hk.trans hl.symm)
  subst hkj
  set v := Nat.ofBits (f 0) with hv
  have hvlt : v < 512 := Nat.ofBits_lt_two_pow (f 0)
  have hijN : (i : ℕ) ≠ (k : ℕ) := fun e => hij (Fin.ext e)
  have h1 : q9Keep v (v ^^^ 2 ^ (i : ℕ)) = true := by
    have h := hab.2
    rwa [← hi, ofBits_flipAt] at h
  have h2 : q9Keep v (v ^^^ 2 ^ (k : ℕ)) = true := by
    have h := had.2
    rwa [← hj, ofBits_flipAt] at h
  have h3 : q9Keep (v ^^^ 2 ^ (i : ℕ)) (v ^^^ 2 ^ (i : ℕ) ^^^ 2 ^ (k : ℕ)) = true := by
    have h := hbc.2
    rw [← hi, ← hk] at h
    simpa only [ofBits_flipAt] using h
  have h4 : q9Keep (v ^^^ 2 ^ (k : ℕ)) (v ^^^ 2 ^ (i : ℕ) ^^^ 2 ^ (k : ℕ)) = true := by
    have h := hdc.2
    rw [← hj, ← hk] at h
    simpa only [ofBits_flipAt] using h
  have h4' := q9_face hvlt i.isLt k.isLt hijN h1 h2 h3
  rw [h4] at h4'
  exact Bool.noConfusion h4'

-- The `constructorNameAsVariable` linter exceeds its recursion limit on this proof.
set_option linter.constructorNameAsVariable false in
/-- The certificate graph has exactly 1505 edges, via the bijection
    `(v, i) ↦ s(v, v⊕eᵢ)` from lower-endpoint codes. -/
private theorem certGraph_card : certGraph.edgeFinset.card = 1505 := by
  rw [← q9EdgeCodes_card]
  symm
  refine Finset.card_bij (fun p _ => s(bitsOf p.1, flipAt (bitsOf p.1) p.2)) ?_ ?_ ?_
  · rintro ⟨v, i⟩ hp
    simp only [q9EdgeCodes, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true] at hp
    obtain ⟨hv, -, hkeep⟩ := hp
    rw [mem_edgeFinset, mem_edgeSet, certGraph_adj, ofBits_flipAt, ofBits_bitsOf hv]
    exact ⟨flipAt_adj _ _, hkeep⟩
  · rintro ⟨v, i⟩ hp ⟨w, j⟩ hq h
    simp only [q9EdgeCodes, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true] at hp hq
    obtain ⟨hv, hvi, -⟩ := hp
    obtain ⟨hw, hwj, -⟩ := hq
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hvw : v = w := by
        rw [← ofBits_bitsOf hv, ← ofBits_bitsOf hw, h1]
      subst hvw
      have hij : i = j := flipAt_injective _ h2
      rw [hij]
    · exfalso
      have e1 := congrFun h1 i
      have e2 := congrFun h2 i
      simp only [bitsOf, flipAt] at e1 e2
      rw [hvi] at e2
      by_cases hij : i = j
      · subst hij
        rw [hwj] at e2
        simp at e2
      · rw [if_neg hij, hvi] at e1
        rw [← e1] at e2
        simp at e2
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet, certGraph_adj] at he
      obtain ⟨hxy, hkeep⟩ := he
      obtain ⟨i, rfl⟩ := eq_flipAt_of_adj _ _ hxy
      cases hxi : x i
      · refine ⟨(Nat.ofBits x, i), ?_, ?_⟩
        · simp only [q9EdgeCodes, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            Finset.mem_univ, and_true]
          refine ⟨Nat.ofBits_lt_two_pow x, ?_, ?_⟩
          · rw [Nat.testBit_ofBits_lt _ _ i.isLt]
            exact hxi
          · rw [← ofBits_flipAt]
            exact hkeep
        · simp only [bitsOf_ofBits]
      · refine ⟨(Nat.ofBits (flipAt x i), i), ?_, ?_⟩
        · simp only [q9EdgeCodes, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            Finset.mem_univ, and_true]
          refine ⟨Nat.ofBits_lt_two_pow _, ?_, ?_⟩
          · rw [Nat.testBit_ofBits_lt _ _ i.isLt]
            simp [flipAt, hxi]
          · rw [← ofBits_flipAt, flipAt_flipAt, q9Keep_comm]
            exact hkeep
        · simp only [bitsOf_ofBits, flipAt_flipAt]
          exact Sym2.eq_swap

/-- **Certificate layer (the repo lane)**: `f(9) ≥ 1505` — an explicit
    C₄-free subgraph of `Q₉` with 1505 edges exists (rafalwrona's
    edge-list certificate, comment-sourced; SHA-pinned JSON in the
    linked repo).  Verification = C₄-freeness of an explicit edge list:
    `native_decide` territory (4608 potential C₄s in Q₉ per the
    comment's table).  Fetch the edge list before attempting.
    -- PROVABLE-in-principle (native_decide). -/
theorem certificate_q9 : 1505 ≤ maxC4FreeEdges 9 := by
  have h := HypercubeGraph.card_edges_le_maxC4FreeEdges 9 certGraph certGraph_le
    certGraph_c4Free
  rwa [certGraph_card] at h

/-- Small exact value sanity: `f(2) = 3` (drop any edge of the single
    4-cycle).  -- PROVABLE (decide over subgraphs of Q₂, 2⁴ edge
    subsets).  Pins `maxC4FreeEdges` against off-by-one in the sup
    encoding. -/
theorem maxC4FreeEdges_two : maxC4FreeEdges 2 = 3 := HypercubeGraph.maxC4FreeEdges_two

end ErdosCandidates.E86

/- Historical source review follows; its claims are not an independent primary-paper audit. -/

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB exactly.
   - Hypercube graph fresh def confirmed necessary: Mathlib has no
     SimpleGraph hypercube (grep hit only HalesJewett combinatorial
     hypercubes, not graph-theoretic).
   - Q_n vertex count 2^n and edge count n*2^(n-1) match DB parenthetical.
   - C4Free uses (cycleGraph 4).Free H, which expands to !(cycleGraph 4 <= H)
     i.e. "H does not contain a copy of C4" -- correct direction confirmed
     from Copy.lean:372.
   - f(2) = 3: Q2 is C4 itself (4 edges); deleting any edge gives 3 C4-free
     edges.  Correct.
   - Q9 certificate 1505 edges matches rafalwrona comment table exactly.
   - rafalwrona comment correctly flagged as comment-sourced (May 2026).
   - Upper bounds: Baber 0.60318 and BHLL 0.6068 match DB and comment.
   - Lower bounds: Erdos c/n and BHN c/sqrt(n) match DB section text.
   - OEIS A245762 anchor noted.
-/
