/-
  Erdős Problem #834 — a 3-critical 3-uniform hypergraph of minimum
  degree 7.
  Status: solved (Li 2025) — YES under chromatic criticality, NO under
  transversal criticality.  Tier C target (seeds a hypergraph lane).

  Verbatim statement (`goof erdos fetch 834`, pulled 2026-08-05):

    "Does there exist a $3$-critical $3$-uniform hypergraph in which
    every vertex has degree $\geq 7$?"

  DB remarks (Erdős–Lovász [ErLo75]): "3-critical" was not specified.
  Two readings: (a) transversal-critical (τ = 3, every edge-deleted
  subhypergraph has a 2-transversal) — Raphael Steiner observed such
  hypergraphs have bounded size, making the problem finite;
  (b) chromatic-critical (χ = 3, deleting any edge or vertex drops χ
  to 2) — the reading endorsed by AlexisOlson's comment (source paper
  context, Abbott–Hare terminology, non-triviality).  Li [Li25,
  arXiv:2512.24850] resolved BOTH: transversal-critical forces a
  vertex of degree ≤ 6; chromatic-critical admits an explicit
  9-vertex construction with min degree 7.

  Repo adjacency: `Proofs/Erdos/CoveringNumber.lean` (`IsTransversal`,
  `coveringNumber`) covers the transversal-side vocabulary;
  `ErdosLovasz.lean` is the same paper's other problem.

  Mathlib inventory: no hypergraph type; `Finset (Finset (Fin 9))`
  convention.  3^9 = 19683 colorings × ≤ C(9,3) edges: criticality
  checking is `decide`/`native_decide` sized once Li's edge list is
  transcribed (it is explicit in [Li25]; fetch before proving).
-/
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ErdosCandidates.E834

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `ProperColoring H c`: no edge of `H` is monochromatic under `c`. -/
def ProperColoring {k : ℕ} (H : Finset (Finset V)) (c : V → Fin k) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `ChromaticallyThreeCritical H`: χ(H) = 3 (3-colorable, not
    2-colorable) and every proper edge- or vertex-deletion is
    2-colorable.  Vertex deletion = restrict to edges avoiding `v`. -/
def ChromaticallyThreeCritical (H : Finset (Finset V)) : Prop :=
  (∃ c : V → Fin 3, ProperColoring H c) ∧
  (¬ ∃ c : V → Fin 2, ProperColoring H c) ∧
  (∀ e ∈ H, ∃ c : V → Fin 2, ProperColoring (H.erase e) c) ∧
  (∀ v : V, ∃ c : V → Fin 2,
    ProperColoring (H.filter (fun e => v ∉ e)) c)

/-- `degree H v`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- The seven specified lines of the Fano plane on `Fin 7`. -/
def fano : Finset (Finset (Fin 7)) :=
  {{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}}

example : fano =
    ({{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6},
      {2,4,5}} : Finset (Finset (Fin 7))) := rfl

/-- The explicit three-coloring: point zero has color two, points one and
    two have color one, and the other four points have color zero. -/
def fanoThreeColor (v : Fin 7) : Fin 3 :=
  if v = 0 then 2 else if v = 1 ∨ v = 2 then 1 else 0

example : (fanoThreeColor 0, fanoThreeColor 1, fanoThreeColor 2,
    fanoThreeColor 3, fanoThreeColor 4, fanoThreeColor 5, fanoThreeColor 6) =
    (2, 1, 1, 0, 0, 0, 0) := by decide

/-- Checking the seven lines proves that the explicit three-coloring is proper. -/
theorem fano_three_color_proper : ProperColoring fano fanoThreeColor := by
  unfold ProperColoring
  decide

/-- Every binary assignment has a monochromatic Fano line. This kernel
    certificate checks only the 128 binary assignments and the seven lines. -/
theorem fano_binary_certificate :
    ∀ c : Fin 7 → Fin 2, ∃ e ∈ fano, ∀ x ∈ e, ∀ y ∈ e, c x = c y := by
  decide

/-- No binary coloring of the Fano plane is proper. -/
theorem fano_not_two_colorable : ¬ ∃ c : Fin 7 → Fin 2, ProperColoring fano c := by
  rintro ⟨c, hc⟩
  obtain ⟨e, he, hmono⟩ := fano_binary_certificate c
  obtain ⟨x, hx, y, hy, hxy⟩ := hc e he
  exact hxy (hmono x hx y hy)

/-- Distinct Fano lines meet in exactly one point, and each has a point
    inside and a point outside the other. Only the seven-by-seven pairs are checked. -/
theorem fano_line_pair_certificate :
    ∀ e ∈ fano, ∀ f ∈ fano, f ≠ e →
      (f ∩ e).card = 1 ∧ ∃ x ∈ f, ∃ y ∈ f, x ∈ e ∧ y ∉ e := by
  decide

/-- Every point is on a Fano line. -/
theorem fano_incident_line : ∀ v : Fin 7, ∃ e ∈ fano, v ∈ e := by
  decide

/-- Every Fano line is nonempty, including those through the boundary points. -/
theorem fano_lines_nonempty : ∀ e ∈ fano, e.Nonempty := by
  decide

omit [DecidableEq V] [Fintype V] in
/-- Proper colorings remain proper when lines are removed. -/
theorem properColoring_mono {k : ℕ} {H K : Finset (Finset V)}
    {c : V → Fin k} (hKH : K ⊆ H) (hc : ProperColoring H c) :
    ProperColoring K c := by
  intro e he
  exact hc e (hKH he)

/-- Coloring a deleted line one and its complement zero properly colors
    every retained Fano line. -/
theorem fano_edge_color_proper (e : Finset (Fin 7)) (he : e ∈ fano) :
    ProperColoring (fano.erase e) (fun v => if v ∈ e then (1 : Fin 2) else 0) := by
  intro f hf
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hf
  obtain ⟨_, x, hx, y, hy, hxe, hye⟩ := fano_line_pair_certificate e he f hmem hne
  refine ⟨x, hx, y, hy, ?_⟩
  simp [hxe, hye]

/-- Deleting any Fano line leaves a binary-colorable hypergraph. -/
theorem fano_edge_two_colorable :
    ∀ e ∈ fano, ∃ c : Fin 7 → Fin 2, ProperColoring (fano.erase e) c := by
  intro e he
  exact ⟨_, fano_edge_color_proper e he⟩

/-- Deleting a point removes an incident line, so the coloring for deletion
    of that line also colors all lines avoiding the point. -/
theorem fano_vertex_two_colorable :
    ∀ v : Fin 7, ∃ c : Fin 7 → Fin 2,
      ProperColoring (fano.filter (fun e => v ∉ e)) c := by
  intro v
  obtain ⟨e, he, hve⟩ := fano_incident_line v
  refine ⟨(fun w => if w ∈ e then 1 else 0),
    properColoring_mono ?_ (fano_edge_color_proper e he)⟩
  intro f hf
  obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfH⟩
  intro hfe
  exact hvf (hfe ▸ hve)

/-- The specified Fano plane satisfies all four clauses of chromatic
    three-criticality, with explicit coloring and deletion witnesses. -/
theorem fano_chromatically_three_critical : ChromaticallyThreeCritical fano := by
  exact ⟨⟨fanoThreeColor, fano_three_color_proper⟩, fano_not_two_colorable,
    fano_edge_two_colorable, fano_vertex_two_colorable⟩

example : (0 : Fin 7) ≠ 6 := by decide
example : degree fano 0 = 3 ∧ degree fano 6 = 3 := by decide
example : ∃ c : Fin 7 → Fin 3, ProperColoring fano c :=
  ⟨fanoThreeColor, fano_three_color_proper⟩
example : ∃ c : Fin 7 → Fin 2, ProperColoring (fano.erase {0,1,2}) c := by
  apply fano_edge_two_colorable
  decide
example : ∃ c : Fin 7 → Fin 2,
    ProperColoring (fano.filter (fun e => (6 : Fin 7) ∉ e)) c :=
  fano_vertex_two_colorable 6

/-- Ground truth for the degree def: in the Fano plane every point has
    degree 3.  -- PROVABLE (decide). -/
example :
    degree ({{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6},
      {2,4,5}} : Finset (Finset (Fin 7))) 0 = 3 := by
  decide

/-- Li's 22 edges ([Li25], eq. (H-edges)), shifted from vertices `1..9`
    to `Fin 9` by subtracting one and indexed in the paper's order. -/
def liEdge : Fin 22 → Finset (Fin 9) :=
  ![{0,1,2}, {0,1,8}, {0,2,7}, {0,3,5}, {0,3,7}, {0,3,8},
    {0,4,6}, {0,4,7}, {0,4,8}, {0,5,6}, {1,2,5}, {1,2,6},
    {1,3,8}, {1,4,8}, {1,5,6}, {2,3,7}, {2,4,7}, {2,5,6},
    {3,5,7}, {3,5,8}, {4,6,7}, {4,6,8}]

example : liEdge 0 = {0,1,2} ∧ liEdge 21 = {4,6,8} := ⟨rfl, rfl⟩

/-- Li's hypergraph: the set of the 22 tabulated edges. -/
def liH : Finset (Finset (Fin 9)) :=
  Finset.univ.image liEdge

/-- Membership in Li's hypergraph means being one of the tabulated edges. -/
theorem mem_liH {e : Finset (Fin 9)} : e ∈ liH ↔ ∃ i, liEdge i = e := by
  simp [liH]

/-- The 22 tabulated edges are pairwise distinct. -/
theorem liEdge_injective : Function.Injective liEdge := by
  decide

/-- Li's hypergraph has exactly 22 edges. -/
theorem liH_card : liH.card = 22 := by
  rw [liH, Finset.card_image_of_injective _ liEdge_injective, Finset.card_univ,
    Fintype.card_fin]

/-- Every tabulated edge has exactly three vertices. -/
theorem liEdge_card : ∀ i, (liEdge i).card = 3 := by
  decide

/-- Every edge of Li's hypergraph has exactly three vertices. -/
theorem liH_uniform : ∀ e ∈ liH, e.card = 3 := by
  intro e he
  obtain ⟨i, rfl⟩ := mem_liH.mp he
  exact liEdge_card i

/-- Every vertex lies on at least seven tabulated edges. -/
theorem liEdge_degree : ∀ v : Fin 9,
    7 ≤ (Finset.univ.filter (fun i : Fin 22 => v ∈ liEdge i)).card := by
  decide

/-- Every vertex of Li's hypergraph has degree at least seven. -/
theorem liH_degree : ∀ v : Fin 9, 7 ≤ degree liH v := by
  intro v
  have hdeg : degree liH v = (Finset.univ.filter (fun i : Fin 22 => v ∈ liEdge i)).card := by
    rw [degree, liH, Finset.filter_image,
      Finset.card_image_of_injective _ liEdge_injective]
  rw [hdeg]
  exact liEdge_degree v

example : degree liH 0 = 10 ∧ degree liH 8 = 7 := by
  rw [degree, degree, liH]
  decide

/-- Li's three-coloring `ψ` shifted to `Fin 9`: vertex six has color two,
    vertices two, five, seven and eight have color one, the rest color zero. -/
def liThreeColor (v : Fin 9) : Fin 3 :=
  if v = 6 then 2 else if v = 2 ∨ v = 5 ∨ v = 7 ∨ v = 8 then 1 else 0

example : (liThreeColor 0, liThreeColor 2, liThreeColor 6) = (0, 1, 2) := by decide

/-- No tabulated edge is monochromatic under Li's three-coloring. -/
theorem liEdge_three_color : ∀ i, ∃ x ∈ liEdge i, ∃ y ∈ liEdge i,
    liThreeColor x ≠ liThreeColor y := by
  decide

/-- Li's three-coloring is proper. -/
theorem liH_three_color_proper : ProperColoring liH liThreeColor := by
  intro e he
  obtain ⟨i, rfl⟩ := mem_liH.mp he
  exact liEdge_three_color i

/-- Every binary assignment on `Fin 9` has a monochromatic tabulated edge:
    a kernel sweep over the 512 assignments. -/
theorem liEdge_binary_certificate :
    ∀ c : Fin 9 → Fin 2, ∃ i, ∀ x ∈ liEdge i, ∀ y ∈ liEdge i, c x = c y := by
  decide

/-- Li's hypergraph has no proper binary coloring. -/
theorem liH_not_two_colorable : ¬ ∃ c : Fin 9 → Fin 2, ProperColoring liH c := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hmono⟩ := liEdge_binary_certificate c
  obtain ⟨x, hx, y, hy, hxy⟩ := hc (liEdge i) (mem_liH.mpr ⟨i, rfl⟩)
  exact hxy (hmono x hx y hy)

/-- The blue sets of Li's edge-deletion table ([Li25], Table B.1), shifted
    to `Fin 9`; entry `i` belongs to edge `liEdge i`. -/
def liBlue : Fin 22 → Finset (Fin 9) :=
  ![{5,6,7,8}, {2,3,4,5}, {1,3,4,5}, {1,6,7,8}, {2,4,5,8}, {1,4,5,7},
    {1,5,7,8}, {2,3,6,8}, {1,3,6,7}, {1,2,3,4}, {0,6,7,8}, {0,5,7,8},
    {0,2,4,5}, {0,2,3,6}, {0,2,3,4}, {0,1,4,5}, {0,1,3,6}, {0,1,3,4},
    {0,2,6,8}, {0,1,6,7}, {0,2,5,8}, {0,1,5,7}]

example : liBlue 0 = {5,6,7,8} ∧ liBlue 21 = {0,1,5,7} := ⟨rfl, rfl⟩

/-- Table B.1 is valid: under the indicator coloring of `liBlue i`, every
    tabulated edge other than edge `i` has two differently colored vertices. -/
theorem liBlue_certificate : ∀ i j : Fin 22, i ≠ j →
    ∃ x ∈ liEdge j, ∃ y ∈ liEdge j,
      (if x ∈ liBlue i then (1 : Fin 2) else 0) ≠ (if y ∈ liBlue i then (1 : Fin 2) else 0) := by
  decide

/-- Deleting edge `i` of Li's hypergraph leaves it properly colored by the
    indicator of `liBlue i`. -/
theorem liBlue_proper (i : Fin 22) :
    ProperColoring (liH.erase (liEdge i))
      (fun v => if v ∈ liBlue i then (1 : Fin 2) else 0) := by
  intro f hf
  obtain ⟨hne, hfH⟩ := Finset.mem_erase.mp hf
  obtain ⟨j, rfl⟩ := mem_liH.mp hfH
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  exact liBlue_certificate i j hij

/-- Deleting any edge of Li's hypergraph leaves a binary-colorable hypergraph. -/
theorem liH_edge_two_colorable :
    ∀ e ∈ liH, ∃ c : Fin 9 → Fin 2, ProperColoring (liH.erase e) c := by
  intro e he
  obtain ⟨i, rfl⟩ := mem_liH.mp he
  exact ⟨_, liBlue_proper i⟩

/-- Every vertex lies on some tabulated edge. -/
theorem liEdge_incident : ∀ v : Fin 9, ∃ i, v ∈ liEdge i := by
  decide

/-- Deleting a vertex removes an incident edge, so the binary coloring for
    deletion of that edge colors every edge avoiding the vertex. -/
theorem liH_vertex_two_colorable :
    ∀ v : Fin 9, ∃ c : Fin 9 → Fin 2,
      ProperColoring (liH.filter (fun e => v ∉ e)) c := by
  intro v
  obtain ⟨i, hvi⟩ := liEdge_incident v
  refine ⟨_, properColoring_mono ?_ (liBlue_proper i)⟩
  intro f hf
  obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfH⟩
  intro hfe
  exact hvf (hfe ▸ hvi)

/-- **Erdős #834, chromatic reading — Li's construction** ([Li25]):
    there is a 3-uniform, chromatically 3-critical hypergraph on 9
    vertices with every vertex of degree ≥ 7.

    Source: "Does there exist a $3$-critical $3$-uniform hypergraph in
    which every vertex has degree $\geq 7$?"  Answer YES (chromatic
    criticality).

    Attack: transcribe Li's explicit 9-vertex edge list from
    arXiv:2512.24850 (`goof fetch` the paper into References first),
    then every conjunct is a finite check: uniformity and degrees by
    `decide`; 2-uncolorability is 2⁹ = 512 colorings; 3-colorability
    exhibits one witness; criticality is |H| + 9 more 512-sweeps.
    `native_decide` comfortably; kernel `decide` plausibly.  Effort M
    (transcription + instance wrangling), and it seeds the repo's
    hypergraph lane. -/
theorem li_construction :
    ∃ H : Finset (Finset (Fin 9)),
      (∀ e ∈ H, e.card = 3) ∧
      ChromaticallyThreeCritical H ∧
      ∀ v : Fin 9, 7 ≤ degree H v := by
  exact ⟨liH, liH_uniform,
    ⟨⟨liThreeColor, liH_three_color_proper⟩, liH_not_two_colorable,
      liH_edge_two_colorable, liH_vertex_two_colorable⟩, liH_degree⟩

section Bollobas

/-! Bollobás's set-pairs inequality, reproduced privately from the
sorry-free module `Proofs/Sorry/Combinatorics/BollobasSetPairs.lean` (the
`Sorry` library may not be imported here).  Li's transversal bound is its
`(3, 2)` case. -/

open Finset

/-- Pascal-type identity `(c+1) · C(a+c+1, a) = (a+c+1) · C(a+c, a)`, i.e.
`b · C(a+b, a) = (a+b) · C(a+b-1, a)` for `b = c + 1 ≥ 1`. -/
private theorem succ_mul_choose_add_succ (a c : ℕ) :
    (c + 1) * (a + (c + 1)).choose a = (a + (c + 1)) * (a + c).choose a := by
  have h1 : (a + (c + 1)).choose a = (a + c + 1).choose (c + 1) := by
    rw [Nat.choose_symm_add, ← add_assoc]
  have h2 : (a + c).choose a = (a + c).choose c := Nat.choose_symm_add
  rw [h1, h2, ← add_assoc, Nat.add_one_mul_choose_eq]
  ring

/-- Double-counting weight identity for one pair: if `A, B ⊆ X` are disjoint and
`B` is nonempty, then summing `1 / C(|A| + |B \ {x}|, |A|)` over `x ∈ X \ A`
gives `|X| / C(|A| + |B|, |A|)`. -/
private theorem sum_inv_choose_erase_eq {α : Type*} [DecidableEq α] (X A B : Finset α)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hAB : Disjoint A B) (hB : B.Nonempty) :
    ∑ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℕ) : ℚ)⁻¹ =
      (#X : ℚ) * (((#A + #B).choose #A : ℕ) : ℚ)⁻¹ := by
  obtain ⟨c, hc⟩ : ∃ c, #B = c + 1 := ⟨#B - 1, by have := hB.card_pos; omega⟩
  have hsplit : ∀ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℕ) : ℚ)⁻¹ =
      if x ∈ B then (((#A + c).choose #A : ℕ) : ℚ)⁻¹
      else (((#A + (c + 1)).choose #A : ℕ) : ℚ)⁻¹ := by
    intro x _
    split_ifs with hx
    · rw [card_erase_of_mem hx, hc, Nat.add_sub_cancel]
    · rw [erase_eq_of_notMem hx, hc]
  rw [sum_congr rfl hsplit, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hfilt : {x ∈ X \ A | x ∈ B} = B := by
    ext x
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨_, hxB⟩
      exact hxB
    · intro hxB
      exact ⟨⟨hBX hxB, disjoint_right.1 hAB hxB⟩, hxB⟩
  have hcardXA : #(X \ A) + #A = #X := card_sdiff_add_card_eq_card hAX
  have hcardsplit := card_filter_add_card_filter_not (s := X \ A) (fun x => x ∈ B)
  rw [hfilt] at hcardsplit
  have hrest : (#{x ∈ X \ A | x ∉ B} : ℚ) = #X - #A - (c + 1) := by
    have hnat : #{x ∈ X \ A | x ∉ B} + (c + 1) + #A = #X := by omega
    have hq : (#{x ∈ X \ A | x ∉ B} : ℚ) + (c + 1) + #A = #X := by exact_mod_cast hnat
    linarith
  rw [hfilt, hrest, hc]
  have hid : ((c + 1 : ℕ) : ℚ) * ((#A + (c + 1)).choose #A : ℕ) =
      ((#A + (c + 1) : ℕ) : ℚ) * ((#A + c).choose #A : ℕ) := by
    exact_mod_cast succ_mul_choose_add_succ #A c
  have hpos1 : (0 : ℚ) < ((#A + c).choose #A : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hpos2 : (0 : ℚ) < ((#A + (c + 1)).choose #A : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  push_cast at hid ⊢
  field_simp
  linear_combination hid

/-- Bollobás's inequality relative to a ground set `X`: if every `A i`, `B i`
(`i ∈ s`) lies in `X`, `A i ∩ B i = ∅`, and `A i ∩ B j ≠ ∅` for distinct
`i, j ∈ s`, then `Σ_{i ∈ s} 1 / C(|A i| + |B i|, |A i|) ≤ 1`.  Proved by strong
induction on `X`. -/
private theorem sum_inv_choose_le_one_of_subset {α ι : Type*} [DecidableEq α]
    (A : ι → Finset α) (X : Finset α) :
    ∀ (s : Finset ι) (B : ι → Finset α), (∀ i ∈ s, A i ⊆ X) → (∀ i ∈ s, B i ⊆ X) →
      (∀ i ∈ s, Disjoint (A i) (B i)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) →
      ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
  induction X using Finset.strongInduction with
  | H X ih =>
  intro s B hAX hBX hdisj hcross
  by_cases hemptyB : ∃ i ∈ s, B i = ∅
  · -- an empty `B i` forces `s = {i}` by the cross condition
    obtain ⟨i, hi, hBi⟩ := hemptyB
    have hs : s = {i} := by
      ext j
      rw [mem_singleton]
      constructor
      · intro hj
        by_contra hji
        exact hcross j hj i hi hji (by rw [hBi]; exact disjoint_empty_right _)
      · rintro rfl
        exact hi
    simp [hs, hBi]
  push Not at hemptyB
  rcases s.eq_empty_or_nonempty with hs | ⟨i0, hi0⟩
  · simp [hs]
  have hXpos : (0 : ℚ) < #X := by
    obtain ⟨y, hy⟩ := hemptyB i0 hi0
    exact_mod_cast card_pos.2 ⟨y, hBX i0 hi0 hy⟩
  -- the induction hypothesis on `X \ {x}` for the pairs `(A i, B i \ {x})`, `x ∉ A i`
  have hIH : ∀ x ∈ X, ∑ i ∈ s with x ∉ A i,
      (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
    intro x hxX
    apply ih (X.erase x) (erase_ssubset hxX)
    · intro i hi y hy
      have hxA : x ∉ A i := (mem_filter.1 hi).2
      exact mem_erase.2 ⟨fun hyx => hxA (hyx ▸ hy), hAX i (mem_filter.1 hi).1 hy⟩
    · intro i hi
      exact erase_subset_erase x (hBX i (mem_filter.1 hi).1)
    · intro i hi
      exact disjoint_of_subset_right (erase_subset _ _) (hdisj i (mem_filter.1 hi).1)
    · intro i hi j hj hij hd
      obtain ⟨y, hyA, hyB⟩ :=
        not_disjoint_iff.1 (hcross i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hij)
      have hxA : x ∉ A i := (mem_filter.1 hi).2
      exact disjoint_left.1 hd hyA (mem_erase.2 ⟨fun hyx => hxA (hyx ▸ hyA), hyB⟩)
  have hkey : (#X : ℚ) * ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤
      (#X : ℚ) * 1 := by
    calc (#X : ℚ) * ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹
        = ∑ i ∈ s, ∑ x ∈ X \ A i,
            (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ := by
          rw [mul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [sum_inv_choose_erase_eq X (A i) (B i) (hAX i hi) (hBX i hi) (hdisj i hi)
            (hemptyB i hi)]
      _ = ∑ x ∈ X, ∑ i ∈ s with x ∉ A i,
            (((#(A i) + #((B i).erase x)).choose #(A i) : ℕ) : ℚ)⁻¹ := by
          refine sum_comm' fun i x => ?_
          simp only [mem_sdiff, mem_filter]
          tauto
      _ ≤ ∑ _x ∈ X, (1 : ℚ) := sum_le_sum hIH
      _ = (#X : ℚ) * 1 := by simp
  exact le_of_mul_le_mul_left hkey hXpos

/-- **Bollobás's set-pairs inequality** (two-families theorem, 1965), copied from
`Proofs/Sorry/Combinatorics/BollobasSetPairs.lean`.  Let
`(A i, B i)`, `i ∈ s`, be pairs of finite sets with `A i ∩ B i = ∅` and
`A i ∩ B j ≠ ∅` for `i ≠ j`.  Then `Σ_{i ∈ s} 1 / C(|A i| + |B i|, |A i|) ≤ 1`. -/
private theorem bollobas_set_pairs {α ι : Type*} (s : Finset ι) (A B : ι → Finset α)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ ≤ 1 := by
  classical
  refine sum_inv_choose_le_one_of_subset A (s.biUnion fun i => A i ∪ B i) s B
    (fun i hi => ?_) (fun i hi => ?_) hdisj hcross
  · exact subset_union_left.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi)
  · exact subset_union_right.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi)

/-- **Uniform Bollobás bound.**  If moreover `|A i| = a` and `|B i| = b` for all
`i ∈ s`, then the number of pairs is at most `C(a + b, a)`. -/
private theorem card_le_choose_of_bollobas {α ι : Type*} (s : Finset ι) (A B : ι → Finset α)
    (a b : ℕ) (hA : ∀ i ∈ s, #(A i) = a) (hB : ∀ i ∈ s, #(B i) = b)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    #s ≤ (a + b).choose a := by
  have hsum := bollobas_set_pairs s A B hdisj hcross
  have hconst : ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℕ) : ℚ)⁻¹ =
      (#s : ℚ) * (((a + b).choose a : ℕ) : ℚ)⁻¹ := by
    rw [sum_congr rfl fun i hi => by rw [hA i hi, hB i hi], sum_const, nsmul_eq_mul]
  have hpos : (0 : ℚ) < ((a + b).choose a : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [hconst, mul_inv_le_iff₀ hpos, one_mul] at hsum
  exact_mod_cast hsum

end Bollobas

/-- **Li's negative result, transversal reading** ([Li25]): a
    transversal-3-critical 3-uniform hypergraph must have a vertex of
    degree ≤ 6.  Transversal criticality via the repo's
    `IsTransversal`-style vocabulary, inlined here: τ(H) = 3 and
    every single-edge deletion has a 2-transversal.  Archived (Li's
    proof is a finite but nontrivial structural argument; Steiner's
    boundedness observation makes it finitely checkable in
    principle). -/
theorem li_transversal_negative (n : ℕ) (H : Finset (Finset (Fin n)))
    (huni : ∀ e ∈ H, e.card = 3)
    (hτ3 : (∃ T : Finset (Fin n), T.card = 3 ∧
              ∀ e ∈ H, (e ∩ T).Nonempty) ∧
           ¬ ∃ T : Finset (Fin n), T.card = 2 ∧ ∀ e ∈ H, (e ∩ T).Nonempty)
    (hcrit : ∀ e ∈ H, ∃ T : Finset (Fin n), T.card = 2 ∧
              ∀ f ∈ H.erase e, (f ∩ T).Nonempty) :
    ∃ v : Fin n, degree H v ≤ 6 := by
  classical
  obtain ⟨⟨T3, hT3card, -⟩, hno2⟩ := hτ3
  by_contra hall
  push Not at hall
  -- the critical pair `T e` for each edge
  let T : Finset (Fin n) → Finset (Fin n) := fun e =>
    if he : e ∈ H then Classical.choose (hcrit e he) else ∅
  have hTcard : ∀ e ∈ H, (T e).card = 2 := by
    intro e he
    simp only [T, dif_pos he]
    exact (Classical.choose_spec (hcrit e he)).1
  have hThit : ∀ e ∈ H, ∀ f ∈ H.erase e, (f ∩ T e).Nonempty := by
    intro e he
    simp only [T, dif_pos he]
    exact (Classical.choose_spec (hcrit e he)).2
  have hdisj : ∀ e ∈ H, Disjoint e (T e) := by
    intro e he
    by_contra hmeet
    rw [Finset.not_disjoint_iff_nonempty_inter] at hmeet
    refine hno2 ⟨T e, hTcard e he, fun f hf => ?_⟩
    by_cases hfe : f = e
    · rw [hfe]
      exact hmeet
    · exact hThit e he f (Finset.mem_erase.2 ⟨hfe, hf⟩)
  have hcross : ∀ i ∈ H, ∀ j ∈ H, i ≠ j → ¬ Disjoint i (T j) := by
    intro i hi j hj hij
    rw [Finset.not_disjoint_iff_nonempty_inter]
    exact hThit j hj i (Finset.mem_erase.2 ⟨hij, hi⟩)
  have hHcard : H.card ≤ 10 :=
    card_le_choose_of_bollobas H (fun e => e) T 3 2 huni hTcard hdisj hcross
  have hsum : ∑ v, degree H v = ∑ e ∈ H, e.card := by
    simp only [degree, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp
  have hsum3 : ∑ e ∈ H, e.card = 3 * H.card := by
    rw [Finset.sum_congr rfl huni, Finset.sum_const, smul_eq_mul, mul_comm]
  have hlow : (Finset.univ : Finset (Fin n)).card • 7 ≤ ∑ v, degree H v :=
    Finset.card_nsmul_le_sum _ _ _ fun v _ => hall v
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlow
  have hn4 : n ≤ 4 := by omega
  have hn3 : 3 ≤ n := by
    have hT3le := Finset.card_le_univ T3
    rw [Fintype.card_fin] at hT3le
    omega
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := 2)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  refine hno2 ⟨S, hScard, fun e he => ?_⟩
  have hunion := Finset.card_union_add_card_inter e S
  have hle : (e ∪ S).card ≤ n := by
    have hESle := Finset.card_le_univ (e ∪ S)
    rwa [Fintype.card_fin] at hESle
  rw [huni e he, hScard] at hunion
  exact Finset.card_pos.1 (by omega)

/-- Satisfiability of chromatic 3-criticality at a small model: the
    Fano plane is 3-chromatic, and it is edge-critical (deleting any
    line leaves a 2-colorable hypergraph).  (Vertex-criticality of
    Fano: deleting a point leaves 4 lines on 6 points — 2-colorable.)
    So `ChromaticallyThreeCritical fano` — the definition is
    non-vacuous.  -- PROVABLE (decide; 2⁷ and 3⁷ sweeps). -/
example : ChromaticallyThreeCritical
    ({{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6},
      {2,4,5}} : Finset (Finset (Fin 7))) := by
  exact fano_chromatically_three_critical

end ErdosCandidates.E834

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 834` exactly.
   - Both criticality readings (transversal and chromatic) faithfully described per DB.
   - Steiner bounded-size observation and AlexisOlson comment (Abbott-Hare, [Er74d] context,
     non-triviality) accurately reflected.
   - Li [Li25] arXiv:2512.24850: both results (transversal negative deg<=6, chromatic positive
     9-vertex min-deg-7 construction) match DB.
   - ChromaticallyThreeCritical def includes edge-deletion AND vertex-deletion; DB says
     "deleting any edge or vertex" -- faithful.
   - Transversal criticality def (tau=3, edge-deletion has 2-transversal) matches DB's first reading.
   - Fano plane degree example: vertex 0 in {0,1,2},{0,3,4},{0,5,6} = 3 edges. Correct.
   - Fano plane is 3-chromatic and edge-critical: standard, correctly used as satisfiability witness.
-/
