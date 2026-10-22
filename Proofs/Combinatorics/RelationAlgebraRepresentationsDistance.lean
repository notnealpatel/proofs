/-
# Finite representations of `30_65` with clique sizes 4 and 5

Eli Atkins, *Relation Algebra Representations from Distance-Regular Graphs*,
arXiv:2605.14190, Section 6, fourth question, asks whether finite
representations of `30_65` can have clique size 4 or 5. Section 4 constructs
a 42-point representation with clique size 6; Maddux excluded size 3.

The witnesses below have 32 points (eight c-cliques of size 4) and 60 points
(twelve c-cliques of size 5, with Z/12 rotation symmetry). Boolean checkers
are proved sound for the colouring definition and applied to these witnesses.
No classification of all possible clique sizes is given.

Table 1 specifies mandatory diversity cycles `aaa ccc abb baa caa abc`;
`bbb acc bcc cbb` are forbidden. A representation is a colouring of the
complete graph in which all triangles are allowed and every mandatory
cycle is witnessed over every edge of the prescribed colour.

## Conventions

* `Atom` lists the three diversity atoms; the identity atom `1'` is the
  diagonal and is not coloured.
* `Allowed30_65 x y z` says that the multiset `{x, y, z}` is one of the six
  mandatory cycles of Table 1.
* `IsRep30_65 col` is the colouring form of a square representation: symmetric
  off the diagonal, every triangle allowed, every mandatory cycle witnessed on
  every edge, and every atom used (atoms are nonzero).
-/
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

-- The kernel evaluations below are memory-heavy; elaborating them
-- synchronously avoids spawning extra worker threads under a memory cap.
set_option Elab.async false

namespace RelationAlgebraRepresentationsDistance

/-! ## The relation algebra `30_65` -/

/-- The three diversity atoms `a`, `b`, `c` of a four-atom symmetric integral
relation algebra (the fourth atom is the identity `1'`). -/
inductive Atom
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The mandatory diversity cycles of `30_65`, read off the paper's Table 1:
`aaa`, `ccc`, `abb`, `baa`, `caa`, `abc`, as multisets of atoms. -/
def mandatoryCycles30_65 : List (Multiset Atom) :=
  [{.a, .a, .a}, {.c, .c, .c}, {.a, .b, .b}, {.b, .a, .a}, {.c, .a, .a}, {.a, .b, .c}]

/-- A triangle whose three edges are coloured `x`, `y`, `z` is allowed in
`30_65` iff `{x, y, z}` is one of its mandatory cycles. -/
def Allowed30_65 (x y z : Atom) : Prop :=
  ({x, y, z} : Multiset Atom) ∈ mandatoryCycles30_65

instance (x y z : Atom) : Decidable (Allowed30_65 x y z) := by
  unfold Allowed30_65; infer_instance

example : Allowed30_65 .a .a .a := by decide
example : Allowed30_65 .c .c .c := by decide
example : Allowed30_65 .b .a .b := by decide
example : Allowed30_65 .a .b .a := by decide
example : Allowed30_65 .a .c .a := by decide
example : Allowed30_65 .c .b .a := by decide
example : ¬ Allowed30_65 .b .b .b := by decide
example : ¬ Allowed30_65 .c .a .c := by decide
example : ¬ Allowed30_65 .c .c .b := by decide
example : ¬ Allowed30_65 .b .c .b := by decide

/-- A colouring `col` of the off-diagonal pairs of `X` by the diversity atoms
is a (square) representation of `30_65`: it is symmetric, every triangle is
an allowed cycle (so the forbidden cycles `bbb acc bcc cbb` never occur),
every mandatory cycle `{h, i, j}` is witnessed over every `h`-edge `xy` by a
point `z` with `xz` coloured `i` and `zy` coloured `j`, and every atom occurs. -/
structure IsRep30_65 {X : Type*} (col : X → X → Atom) : Prop where
  /-- The colouring is symmetric (all atoms are symmetric). -/
  symm : ∀ x y, x ≠ y → col x y = col y x
  /-- Every triangle is an allowed (mandatory) cycle. -/
  tri : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → Allowed30_65 (col x y) (col y z) (col x z)
  /-- Every mandatory cycle is witnessed over every edge. -/
  mand : ∀ x y, x ≠ y → ∀ i j, Allowed30_65 (col x y) i j →
    ∃ z, z ≠ x ∧ z ≠ y ∧ col x z = i ∧ col z y = j
  /-- Every atom is a nonempty relation. -/
  occ : ∀ t, ∃ x y, x ≠ y ∧ col x y = t

/-- The constant `c`-colouring of four points is not a representation
(the atom `a` does not occur), so `IsRep30_65` is not trivially satisfied. -/
example : ¬ IsRep30_65 (fun _ _ : Fin 4 => Atom.c) := fun h => by
  obtain ⟨x, y, _, hxy⟩ := h.occ .a
  exact Atom.noConfusion hxy

/-- In a representation of `30_65` the `c`-edges are transitive: since `acc`
and `bcc` are forbidden, two `c`-edges at a point close to a `c`-edge.  Hence
the `c`-relation (with the diagonal) partitions the points into `c`-cliques,
whose common size is the *clique size* of the representation. -/
theorem IsRep30_65.c_trans {X : Type*} {col : X → X → Atom} (h : IsRep30_65 col)
    {x y z : X} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h1 : col x y = .c) (h2 : col y z = .c) : col x z = .c := by
  have htri := h.tri x y z hxy hyz hxz
  rw [h1, h2] at htri
  revert htri
  generalize col x z = t
  cases t <;> decide

/-- The `c`-class of a point `x`: `x` together with its `c`-neighbours.  In a
representation of `30_65` this is the `c`-clique containing `x`
(`IsRep30_65.c_trans`). -/
def cClass {X : Type*} [Fintype X] [DecidableEq X] (col : X → X → Atom) (x : X) :
    Finset X :=
  Finset.univ.filter fun y => y = x ∨ col x y = .c

/-- The colouring `col` has clique size `k`: every `c`-clique has exactly `k`
points. -/
def HasCliqueSize {X : Type*} [Fintype X] [DecidableEq X] (col : X → X → Atom) (k : ℕ) :
    Prop :=
  ∀ x, (cClass col x).card = k

/-! ## Block colourings

Points are the naturals `k * V + i` with block index `V` and position `i < k`.
Two points in the same block get colour `c`; points `kV+i` and `kW+j` in
different blocks get colour `b` iff `σ V W` sends `i` to `j` (the permutation
`σ V W` is stored as the list of its values), and colour `a` otherwise. -/

/-- The block colouring with block size `k` and permutation data `σ`. -/
def blockCol (k : ℕ) (σ : ℕ → ℕ → List ℕ) (x y : ℕ) : Atom :=
  if x / k = y / k then .c
  else if (σ (x / k) (y / k)).getD (x % k) 0 = y % k then .b
  else .a

/-! ## Boolean checkers and their soundness -/

/-- Boolean form of `Allowed30_65`, by explicit case table. -/
def allowedB : Atom → Atom → Atom → Bool
  | .a, .a, .a => true
  | .c, .c, .c => true
  | .a, .b, .b | .b, .a, .b | .b, .b, .a => true
  | .b, .a, .a | .a, .b, .a | .a, .a, .b => true
  | .c, .a, .a | .a, .c, .a | .a, .a, .c => true
  | .a, .b, .c | .a, .c, .b | .b, .a, .c | .b, .c, .a | .c, .a, .b | .c, .b, .a => true
  | _, _, _ => false

/-- The Boolean case table agrees with the multiset definition. -/
theorem allowedB_iff (x y z : Atom) : allowedB x y z = true ↔ Allowed30_65 x y z := by
  cases x <;> cases y <;> cases z <;> decide

/-- The three atoms, as a list. -/
def atoms : List Atom := [.a, .b, .c]

/-- Every atom is listed in `atoms`. -/
theorem mem_atoms (t : Atom) : t ∈ atoms := by
  cases t <;> simp [atoms]

/-- Triangle check, on `n` points, for all triangles through the point `x` of
the colouring `col`. -/
def triRow (n : ℕ) (col : ℕ → ℕ → Atom) (x : ℕ) : Bool :=
  (List.range n).all fun y => (List.range n).all fun z =>
    x == y || y == z || x == z || allowedB (col x y) (col y z) (col x z)

/-- Mandatory-cycle check, on `n` points, for all edges at the point `x` of
the colouring `col`. -/
def mandRow (n : ℕ) (col : ℕ → ℕ → Atom) (x : ℕ) : Bool :=
  (List.range n).all fun y => x == y || atoms.all fun i => atoms.all fun j =>
    !allowedB (col x y) i j ||
      (List.range n).any fun z => z != x && z != y && col x z == i && col z y == j

/-- Soundness of the triangle checker. -/
theorem tri_of_check {n : ℕ} {col : ℕ → ℕ → Atom}
    (hcheck : ∀ x < n, triRow n col x = true)
    (x y z : Fin n) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Allowed30_65 (col x y) (col y z) (col x z) := by
  simp only [List.all_eq_true, List.mem_range, triRow] at hcheck
  have hrow := hcheck x x.isLt y y.isLt z z.isLt
  rw [← allowedB_iff]
  simpa [Fin.val_ne_of_ne hxy, Fin.val_ne_of_ne hyz, Fin.val_ne_of_ne hxz] using hrow

/-- Soundness of the mandatory-cycle checker. -/
theorem mand_of_check {n : ℕ} {col : ℕ → ℕ → Atom}
    (hcheck : ∀ x < n, mandRow n col x = true)
    (x y : Fin n) (hxy : x ≠ y) (i j : Atom) (hij : Allowed30_65 (col x y) i j) :
    ∃ z : Fin n, z ≠ x ∧ z ≠ y ∧ col x z = i ∧ col z y = j := by
  simp only [List.all_eq_true, List.mem_range, mandRow] at hcheck
  have hrow := hcheck x x.isLt y y.isLt
  rw [← allowedB_iff] at hij
  have hxy' : (x : ℕ) ≠ y := Fin.val_ne_of_ne hxy
  simp only [Bool.or_eq_true, beq_iff_eq, hxy', List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    false_or] at hrow
  have hz := hrow i (mem_atoms i) j (mem_atoms j)
  simp only [hij, Bool.true_eq_false, false_or] at hz
  obtain ⟨z, hzn, ⟨⟨hzx, hzy⟩, hcxz⟩, hczy⟩ := hz
  refine ⟨⟨z, hzn⟩, ?_, ?_, hcxz, hczy⟩
  · exact fun h => hzx (congrArg Fin.val h)
  · exact fun h => hzy (congrArg Fin.val h)

/-- A check over `List.range n` holds at every `x < n`. -/
theorem forall_lt_of_all_range {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) :
    ∀ x < n, p x = true := by
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_range.mpr hx)

/-- Assemble a check at every `x < 6 * m` from checks over the chunks
`[6c, 6c + 6)`, `c < m`. -/
theorem forall_lt_of_chunks {m : ℕ} {p : ℕ → Bool}
    (h : ∀ c < m, (List.range' (6 * c) 6).all p = true) : ∀ x < 6 * m, p x = true := by
  intro x hx
  have hc := h (x / 6) (by omega)
  exact List.all_eq_true.mp hc x (List.mem_range'_1.mpr (by omega))

/-- `blockCol k σ x y` is `c` exactly when `x` and `y` lie in the same block. -/
theorem blockCol_eq_c_iff (k : ℕ) (σ : ℕ → ℕ → List ℕ) (x y : ℕ) :
    blockCol k σ x y = .c ↔ x / k = y / k := by
  unfold blockCol
  split_ifs with h1 h2 <;> simp [h1]

/-! ## The 32-point witness (clique size 4) -/

/-- The table of permutations `σ_{VW}` of `{0,1,2,3}` for eight blocks
(diagonal entries are unused); `σ_{WV} = σ_{VW}⁻¹`. -/
def sigTable4 : List (List (List ℕ)) :=
  [[[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3]],
   [[0,1,2,3],[0,1,2,3],[2,3,1,0],[2,3,0,1],[2,0,3,1],[1,3,0,2],[2,3,0,1],[3,2,0,1]],
   [[0,1,2,3],[3,2,0,1],[0,1,2,3],[2,3,1,0],[3,0,1,2],[1,2,3,0],[3,2,1,0],[3,2,1,0]],
   [[0,1,2,3],[2,3,0,1],[3,2,0,1],[0,1,2,3],[1,3,0,2],[2,0,3,1],[2,3,0,1],[2,3,1,0]],
   [[0,1,2,3],[1,3,0,2],[1,2,3,0],[2,0,3,1],[0,1,2,3],[1,0,3,2],[1,0,3,2],[3,0,1,2]],
   [[0,1,2,3],[2,0,3,1],[3,0,1,2],[1,3,0,2],[1,0,3,2],[0,1,2,3],[1,0,3,2],[1,2,3,0]],
   [[0,1,2,3],[2,3,0,1],[3,2,1,0],[2,3,0,1],[1,0,3,2],[1,0,3,2],[0,1,2,3],[3,2,1,0]],
   [[0,1,2,3],[2,3,1,0],[3,2,1,0],[3,2,0,1],[1,2,3,0],[3,0,1,2],[3,2,1,0],[0,1,2,3]]]

/-- The permutation data of the 32-point witness. -/
def sigma4 (V W : ℕ) : List ℕ := (sigTable4.getD V []).getD W []

/-- The 32-point colouring, on naturals. -/
def colN32 : ℕ → ℕ → Atom := blockCol 4 sigma4

/-- The 32-point colouring of `Fin 32` (eight `c`-cliques of size 4)
witnessing a representation of `30_65`. -/
def col32 (x y : Fin 32) : Atom := colN32 x y

-- Row 0 of the colour table is `.cccbaaabaaabaaabaaabaaabaaabaaa`.
example : col32 0 1 = .c := by decide
example : col32 0 3 = .c := by decide
example : col32 0 4 = .b := by decide
example : col32 0 5 = .a := by decide
example : col32 4 0 = .b := by decide
-- `σ_{12} = [2,3,1,0]`, so `4·1+0 = 4` is `b`-adjacent to `4·2+2 = 10`.
example : col32 4 10 = .b := by decide
example : col32 10 4 = .b := by decide
example : col32 4 11 = .a := by decide

/-- Kernel evaluation: every triangle of the 32-point colouring is allowed. -/
theorem triRows32 : (List.range 32).all (triRow 32 colN32) = true := by decide +kernel

/-- Kernel evaluation: every mandatory cycle is witnessed on every edge of the
32-point colouring. -/
theorem mandRows32 : (List.range 32).all (mandRow 32 colN32) = true := by decide +kernel

/-- `col32` is symmetric. -/
theorem col32_symm : ∀ x y : Fin 32, col32 x y = col32 y x := by
  decide +kernel

/-- Every `c`-class of `col32` has exactly four points. -/
theorem col32_hasCliqueSize : HasCliqueSize col32 4 := by
  unfold HasCliqueSize cClass
  decide +kernel

/-- `col32` is a representation of `30_65` on 32 points. -/
theorem col32_isRep : IsRep30_65 col32 where
  symm x y _ := col32_symm x y
  tri := tri_of_check (forall_lt_of_all_range triRows32)
  mand := mand_of_check (forall_lt_of_all_range mandRows32)
  occ t := by
    cases t
    · exact ⟨0, 5, by decide, by decide⟩
    · exact ⟨0, 4, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide⟩

/-- **Answer to arXiv:2605.14190, Section 6, fourth question, for clique size
4.**  The relation algebra `30_65` has a finite representation with clique
size `4`: there is a colouring of the pairs of a 32-point set by the atoms
`a, b, c` which represents `30_65` (every triangle is a mandatory cycle of the
paper's Table 1 and every mandatory cycle is witnessed on every edge) and all
of whose `c`-cliques have exactly 4 points. -/
theorem exists_rep30_65_cliqueSize_four :
    ∃ col : Fin 32 → Fin 32 → Atom, IsRep30_65 col ∧ HasCliqueSize col 4 :=
  ⟨col32, col32_isRep, col32_hasCliqueSize⟩

/-! ## The 60-point witness (clique size 5)

Twelve blocks of size 5, with `Z/12`-rotation symmetry: `σ_{VW}` depends only
on `(W - V) mod 12`. -/

/-- The permutations `σ_{0,d}` of `{0,…,4}` for `d = 0, …, 11` (entry `0`
unused). -/
def cycTable5 : List (List ℕ) :=
  [[0,1,2,3,4],[3,2,0,1,4],[0,3,4,1,2],[0,2,3,4,1],[1,2,4,0,3],[4,1,3,0,2],
   [2,1,0,4,3],[3,1,4,2,0],[3,0,1,4,2],[0,4,1,2,3],[0,3,4,1,2],[2,3,1,0,4]]

/-- The permutation data of the 60-point witness: `σ_{VW} = σ_{0,(W-V) mod 12}`
(for block indices `V < 12`, so the natural subtraction is exact). -/
def sigma5 (V W : ℕ) : List ℕ := cycTable5.getD ((W + 12 - V) % 12) []

/-- The 60-point colouring, on naturals. -/
def colN60 : ℕ → ℕ → Atom := blockCol 5 sigma5

/-- The 60-point colouring of `Fin 60` (twelve `c`-cliques of size 5)
witnessing a representation of `30_65`. -/
def col60 (x y : Fin 60) : Atom := colN60 x y

example : col60 0 4 = .c := by decide
example : col60 0 5 = .a := by decide
-- `σ_{01} = [3,2,0,1,4]` sends `0` to `3`, so `0` is `b`-adjacent to `5+3 = 8`.
example : col60 0 8 = .b := by decide
-- `σ_{10} = σ_{0,11} = [2,3,1,0,4]` sends `3` to `0`, so `5+3 = 8` is
-- `b`-adjacent to `0`, consistent with `σ_{10} = σ_{01}⁻¹`.
example : col60 8 0 = .b := by decide
example : col60 59 55 = .c := by decide

/-! Kernel evaluation of the 60-point checks, in ten chunks of six rows each
(a single 60-row kernel evaluation exceeds the memory budget). -/

/-- Kernel evaluation: the 60-point triangle check holds on rows `0`–`5`. -/
theorem triChunk60_0 : (List.range' 0 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `6`–`11`. -/
theorem triChunk60_1 : (List.range' 6 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `12`–`17`. -/
theorem triChunk60_2 : (List.range' 12 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `18`–`23`. -/
theorem triChunk60_3 : (List.range' 18 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `24`–`29`. -/
theorem triChunk60_4 : (List.range' 24 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `30`–`35`. -/
theorem triChunk60_5 : (List.range' 30 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `36`–`41`. -/
theorem triChunk60_6 : (List.range' 36 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `42`–`47`. -/
theorem triChunk60_7 : (List.range' 42 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `48`–`53`. -/
theorem triChunk60_8 : (List.range' 48 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point triangle check holds on rows `54`–`59`. -/
theorem triChunk60_9 : (List.range' 54 6).all (triRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`0`–`5`. -/
theorem mandChunk60_0 : (List.range' 0 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`6`–`11`. -/
theorem mandChunk60_1 : (List.range' 6 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`12`–`17`. -/
theorem mandChunk60_2 : (List.range' 12 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`18`–`23`. -/
theorem mandChunk60_3 : (List.range' 18 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`24`–`29`. -/
theorem mandChunk60_4 : (List.range' 24 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`30`–`35`. -/
theorem mandChunk60_5 : (List.range' 30 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`36`–`41`. -/
theorem mandChunk60_6 : (List.range' 36 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`42`–`47`. -/
theorem mandChunk60_7 : (List.range' 42 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`48`–`53`. -/
theorem mandChunk60_8 : (List.range' 48 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Kernel evaluation: the 60-point mandatory-cycle check holds on rows
`54`–`59`. -/
theorem mandChunk60_9 : (List.range' 54 6).all (mandRow 60 colN60) = true := by
  decide +kernel

/-- Every triangle of the 60-point colouring is allowed. -/
theorem triRows60 : ∀ x < 60, triRow 60 colN60 x = true := by
  refine forall_lt_of_chunks (m := 10) fun c hc => ?_
  match c, hc with
  | 0, _ => exact triChunk60_0
  | 1, _ => exact triChunk60_1
  | 2, _ => exact triChunk60_2
  | 3, _ => exact triChunk60_3
  | 4, _ => exact triChunk60_4
  | 5, _ => exact triChunk60_5
  | 6, _ => exact triChunk60_6
  | 7, _ => exact triChunk60_7
  | 8, _ => exact triChunk60_8
  | 9, _ => exact triChunk60_9
  | _ + 10, hc => exact absurd hc (by omega)

/-- Every mandatory cycle is witnessed on every edge of the 60-point colouring. -/
theorem mandRows60 : ∀ x < 60, mandRow 60 colN60 x = true := by
  refine forall_lt_of_chunks (m := 10) fun c hc => ?_
  match c, hc with
  | 0, _ => exact mandChunk60_0
  | 1, _ => exact mandChunk60_1
  | 2, _ => exact mandChunk60_2
  | 3, _ => exact mandChunk60_3
  | 4, _ => exact mandChunk60_4
  | 5, _ => exact mandChunk60_5
  | 6, _ => exact mandChunk60_6
  | 7, _ => exact mandChunk60_7
  | 8, _ => exact mandChunk60_8
  | 9, _ => exact mandChunk60_9
  | _ + 10, hc => exact absurd hc (by omega)

/-- `col60` is symmetric. -/
theorem col60_symm : ∀ x y : Fin 60, col60 x y = col60 y x := by
  decide +kernel

/-- Every `c`-class of `col60` has exactly five points. -/
theorem col60_hasCliqueSize : HasCliqueSize col60 5 := by
  unfold HasCliqueSize cClass
  decide +kernel

/-- `col60` is a representation of `30_65` on 60 points. -/
theorem col60_isRep : IsRep30_65 col60 where
  symm x y _ := col60_symm x y
  tri := tri_of_check triRows60
  mand := mand_of_check mandRows60
  occ t := by
    cases t
    · exact ⟨0, 5, by decide, by decide⟩
    · exact ⟨0, 8, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide⟩

/-- **Answer to arXiv:2605.14190, Section 6, fourth question, for clique size
5.**  The relation algebra `30_65` has a finite representation with clique
size `5`: there is a colouring of the pairs of a 60-point set by the atoms
`a, b, c` which represents `30_65` and all of whose `c`-cliques have exactly 5
points. -/
theorem exists_rep30_65_cliqueSize_five :
    ∃ col : Fin 60 → Fin 60 → Atom, IsRep30_65 col ∧ HasCliqueSize col 5 :=
  ⟨col60, col60_isRep, col60_hasCliqueSize⟩

end RelationAlgebraRepresentationsDistance

