/-
  Covering number (transversal number) τ of a finite set family.

  For a family F : Finset (Finset α) over a finite ground type α, a
  *transversal* (vertex cover / hitting set) is a set T ⊆ α meeting every
  member of F: ∀ A ∈ F, ∃ x ∈ A, x ∈ T.  The *covering number*
  `coveringNumber F` is the minimum cardinality of a transversal — τ(H) in
  hypergraph terminology (Wikipedia, "Vertex cover in hypergraphs").

  Named `coveringNumber`, NOT `Tau`/`tau`, to avoid collision with the
  divisor-count τ used elsewhere in this repository.

  DEGENERACIES (pinned by theorems below, not left to folklore):
  * Empty family: every set — in particular ∅ — is vacuously a transversal,
    so `coveringNumber ∅ = 0` (`coveringNumber_empty`).  This is the honest
    mathematical value, not a junk value.
  * Some member is ∅: no set meets ∅, so no transversal exists; the minimum
    ranges over an empty Finset and `coveringNumber` takes the JUNK value 0
    via `WithTop.untopD 0` (`coveringNumber_of_empty_mem`).  Consumers must
    guard with `∅ ∉ F`; `coveringNumber_eq_zero_iff` shows the value 0
    occurs in exactly these two degenerate cases.

  Design: the minimum is a `Finset.min` over the image of `Finset.card` on
  the Finset `transversals F` of actual transversal witnesses (a filtered
  powerset — nonempty iff `∅ ∉ F`, since `Finset.univ` then hits every
  member).  It is NOT a bounded `iInf` over a possibly-empty Prop, so no
  silent collapse; everything is decidable, and all ground checks close by
  kernel `decide`.

  Downstream consumer: Erdos/ErdosLovasz.lean (OEIS A391599) will take the
  τ definition; its theorems are deliberately NOT stated here.

  Key results (all sorry-free, axioms ⊆ {propext, Classical.choice,
  Quot.sound}):
    coveringNumber_le_card          — τ(F) ≤ |T| for any transversal T
    exists_isTransversal_card_eq    — the minimum is attained when ∅ ∉ F
    coveringNumber_empty            — τ(∅) = 0
    coveringNumber_of_empty_mem     — junk pin: ∅ ∈ F → τ(F) = 0
    coveringNumber_eq_zero_iff      — τ(F) = 0 ↔ F = ∅ ∨ ∅ ∈ F
    coveringNumber_pos              — F ≠ ∅ and ∅ ∉ F → 0 < τ(F)
    coveringNumber_eq_one_of_forall_mem — common element → τ(F) = 1
    coveringNumber_mono             — F ⊆ F' and ∅ ∉ F' → τ(F) ≤ τ(F')
    coveringNumber_le_card_univ     — ∅ ∉ F → τ(F) ≤ |α|
-/
import Mathlib

set_option autoImplicit false

section Transversal

variable {α : Type*}

/-- `IsTransversal F T`: the set `T` meets every member of the family `F`
(a *vertex cover* / *hitting set* / *transversal* of the hypergraph `F`).
Stated with an explicit witness `∃ x ∈ A, x ∈ T` so that no `DecidableEq`
instance enters the statement; see `isTransversal_iff_inter_nonempty` for
the `(A ∩ T).Nonempty` spelling.  Vacuously true for `F = ∅`
(`isTransversal_empty_left`); unsatisfiable when `∅ ∈ F`
(`not_isTransversal_of_empty_mem`). -/
def IsTransversal (F : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ A ∈ F, ∃ x ∈ A, x ∈ T

/-- Transversality is decidable over a decidable ground type, so tiny
families can be checked by `decide`. -/
instance instDecidableIsTransversal [DecidableEq α] (F : Finset (Finset α)) :
    DecidablePred (IsTransversal F) :=
  fun T => decidable_of_iff (∀ A ∈ F, ∃ x ∈ A, x ∈ T) Iff.rfl

/-- Over a `DecidableEq` ground type, `T` is a transversal of `F` iff it has
nonempty intersection with every member — the textbook definition. -/
theorem isTransversal_iff_inter_nonempty [DecidableEq α] {F : Finset (Finset α)}
    {T : Finset α} :
    IsTransversal F T ↔ ∀ A ∈ F, (A ∩ T).Nonempty := by
  simp only [IsTransversal, Finset.Nonempty, Finset.mem_inter]

/-- DEGENERACY (empty family): every set is vacuously a transversal of the
empty family; this is why `coveringNumber ∅ = 0` is honest, not junk. -/
@[simp] theorem isTransversal_empty_left (T : Finset α) :
    IsTransversal (∅ : Finset (Finset α)) T :=
  fun A hA => absurd hA (Finset.notMem_empty A)

/-- The empty set is a transversal of `F` iff `F` is the empty family. -/
@[simp] theorem isTransversal_empty_right_iff {F : Finset (Finset α)} :
    IsTransversal F ∅ ↔ F = ∅ := by
  constructor
  · intro h
    refine Finset.eq_empty_iff_forall_notMem.mpr fun A hA => ?_
    obtain ⟨x, -, hx⟩ := h A hA
    exact absurd hx (Finset.notMem_empty x)
  · rintro rfl
    exact isTransversal_empty_left ∅

/-- DEGENERACY (`∅ ∈ F`): no set meets the empty set, so a family containing
`∅` has no transversal at all. -/
theorem not_isTransversal_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F)
    (T : Finset α) : ¬IsTransversal F T := by
  intro hT
  obtain ⟨x, hx, -⟩ := hT ∅ h
  exact absurd hx (Finset.notMem_empty x)

/-- Enlarging a transversal keeps it a transversal. -/
theorem IsTransversal.mono {F : Finset (Finset α)} {T U : Finset α}
    (h : IsTransversal F T) (hTU : T ⊆ U) : IsTransversal F U :=
  fun A hA => (h A hA).imp fun _x hx => ⟨hx.1, hTU hx.2⟩

/-- A transversal of a family is a transversal of any subfamily. -/
theorem IsTransversal.anti {F F' : Finset (Finset α)} {T : Finset α}
    (h : IsTransversal F' T) (hFF' : F ⊆ F') : IsTransversal F T :=
  fun A hA => h A (hFF' hA)

/-- A transversal of a nonempty family is nonempty (it must meet some
member). -/
theorem IsTransversal.nonempty {F : Finset (Finset α)} {T : Finset α}
    (h : IsTransversal F T) (hF : F.Nonempty) : T.Nonempty := by
  obtain ⟨A, hA⟩ := hF
  obtain ⟨x, -, hxT⟩ := h A hA
  exact ⟨x, hxT⟩

/-- If no member of `F` is empty, the full ground set is a transversal; this
is the witness making `transversals F` nonempty whenever `∅ ∉ F`. -/
theorem isTransversal_univ [Fintype α] {F : Finset (Finset α)} (h : ∅ ∉ F) :
    IsTransversal F Finset.univ := by
  intro A hA
  have hAne : A.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun hAe => h (hAe ▸ hA)
  obtain ⟨x, hx⟩ := hAne
  exact ⟨x, hx, Finset.mem_univ x⟩

end Transversal

section CoveringNumber

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The Finset of all transversals of the family `F` inside the finite
ground type `α`.  Nonempty iff `∅ ∉ F` (`Finset.univ` is then a witness,
`isTransversal_univ`; conversely `not_isTransversal_of_empty_mem`). -/
def transversals (F : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (IsTransversal F)

/-- Membership in `transversals F` is exactly transversality. -/
@[simp] theorem mem_transversals {F : Finset (Finset α)} {T : Finset α} :
    T ∈ transversals F ↔ IsTransversal F T := by
  simp [transversals]

/-- The covering number (transversal number) τ of a finite set family: the
minimum cardinality of a set meeting every member, computed as `Finset.min`
over the cards of the actual transversal witnesses in `transversals F`.

Value conventions (see the file header):
* `coveringNumber ∅ = 0` — honest: `∅` is a transversal of the empty family;
* `∅ ∈ F` → `coveringNumber F = 0` — JUNK: no transversal exists and the
  `min` of the empty Finset is `⊤`, sent to the default `0` by
  `WithTop.untopD 0`.  Guard uses with `∅ ∉ F`.
`coveringNumber_eq_zero_iff` characterizes the two cases. -/
def coveringNumber (F : Finset (Finset α)) : ℕ :=
  ((transversals F).image Finset.card).min.untopD 0

/-- The covering number is a lower bound on the size of every transversal. -/
theorem coveringNumber_le_card {F : Finset (Finset α)} {T : Finset α}
    (h : IsTransversal F T) : coveringNumber F ≤ T.card := by
  have hmem : T.card ∈ (transversals F).image Finset.card :=
    Finset.mem_image_of_mem Finset.card (mem_transversals.mpr h)
  have hmin : ((transversals F).image Finset.card).min ≤ (T.card : WithTop ℕ) :=
    Finset.min_le hmem
  exact WithTop.untopD_le hmin

/-- When no member of `F` is empty the minimum is attained: some transversal
has cardinality exactly `coveringNumber F`.  (For `∅ ∈ F` no transversal
exists and the value is the junk 0.) -/
theorem exists_isTransversal_card_eq {F : Finset (Finset α)} (h : ∅ ∉ F) :
    ∃ T : Finset α, IsTransversal F T ∧ T.card = coveringNumber F := by
  have hne : ((transversals F).image Finset.card).Nonempty :=
    ⟨Finset.univ.card, Finset.mem_image_of_mem Finset.card
      (mem_transversals.mpr (isTransversal_univ h))⟩
  obtain ⟨T, hT, hTcard⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  refine ⟨T, mem_transversals.mp hT, ?_⟩
  have hcoe : ((transversals F).image Finset.card).min
      = (((transversals F).image Finset.card).min' hne : WithTop ℕ) :=
    (Finset.coe_min' hne).symm
  calc T.card = ((transversals F).image Finset.card).min' hne := hTcard
    _ = coveringNumber F := by
        simp only [coveringNumber, hcoe]
        rfl

/-- τ of the empty family is 0: `∅` is vacuously a transversal.  Honest
value, not junk. -/
@[simp] theorem coveringNumber_empty :
    coveringNumber (∅ : Finset (Finset α)) = 0 := by
  have hle : coveringNumber (∅ : Finset (Finset α)) ≤ (∅ : Finset α).card :=
    coveringNumber_le_card (isTransversal_empty_left ∅)
  simpa [Nat.le_zero] using hle

/-- JUNK PIN: a family containing `∅` has no transversal, `transversals F`
is empty, its `min` is `⊤`, and `coveringNumber` takes the default value 0.
Any consumer of `coveringNumber` must exclude this case with `∅ ∉ F`. -/
theorem coveringNumber_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F) :
    coveringNumber F = 0 := by
  have htrans : transversals F = ∅ := by
    ext T
    simp only [mem_transversals, Finset.notMem_empty, iff_false]
    exact not_isTransversal_of_empty_mem h T
  simp only [coveringNumber, htrans, Finset.image_empty, Finset.min_empty,
    WithTop.untopD_top]

/-- A nonempty family with no empty member has positive covering number:
any transversal must be nonempty. -/
theorem coveringNumber_pos {F : Finset (Finset α)} (hF : F.Nonempty)
    (h : ∅ ∉ F) : 0 < coveringNumber F := by
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_card_eq h
  have hTne : T.Nonempty := hT.nonempty hF
  calc 0 < T.card := Finset.card_pos.mpr hTne
    _ = coveringNumber F := hTcard

/-- `coveringNumber F = 0` exactly in the two degenerate cases: the empty
family (honest 0) or a family containing `∅` (junk 0).  Away from these,
the covering number is positive. -/
theorem coveringNumber_eq_zero_iff {F : Finset (Finset α)} :
    coveringNumber F = 0 ↔ F = ∅ ∨ ∅ ∈ F := by
  constructor
  · intro h0
    rcases Finset.eq_empty_or_nonempty F with hFe | hFne
    · exact Or.inl hFe
    · right
      by_contra hnomem
      have hpos : 0 < coveringNumber F := coveringNumber_pos hFne hnomem
      omega
  · rintro (rfl | hmem)
    · exact coveringNumber_empty
    · exact coveringNumber_of_empty_mem hmem

/-- A nonempty family with a common element `x` has covering number exactly
1: `{x}` is a transversal, and positivity needs `F.Nonempty` (for `F = ∅`
the value is 0, not 1). -/
theorem coveringNumber_eq_one_of_forall_mem {F : Finset (Finset α)}
    (hF : F.Nonempty) {x : α} (hx : ∀ A ∈ F, x ∈ A) :
    coveringNumber F = 1 := by
  have hsing : IsTransversal F {x} :=
    fun A hA => ⟨x, hx A hA, Finset.mem_singleton_self x⟩
  have hle : coveringNumber F ≤ 1 := by
    simpa using coveringNumber_le_card hsing
  have hnomem : ∅ ∉ F := fun hmem => absurd (hx ∅ hmem) (Finset.notMem_empty x)
  have hpos : 0 < coveringNumber F := coveringNumber_pos hF hnomem
  omega

/-- Monotonicity in the family: a subfamily is no harder to cover.  The
guard `∅ ∉ F'` keeps the right-hand side off its junk value (with
`∅ ∈ F'` the claim is false: take `F = {{0}}`, `F' = F ∪ {∅}`). -/
theorem coveringNumber_mono {F F' : Finset (Finset α)} (hFF' : F ⊆ F')
    (h : ∅ ∉ F') : coveringNumber F ≤ coveringNumber F' := by
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_card_eq h
  calc coveringNumber F ≤ T.card := coveringNumber_le_card (hT.anti hFF')
    _ = coveringNumber F' := hTcard

/-- When no member is empty the ground set is a transversal, so the covering
number is at most the size of the ground type. -/
theorem coveringNumber_le_card_univ {F : Finset (Finset α)} (h : ∅ ∉ F) :
    coveringNumber F ≤ Fintype.card α := by
  simpa [Finset.card_univ] using coveringNumber_le_card (isTransversal_univ h)

end CoveringNumber

/-! ## Ground checks (kernel `decide`)

Every definition is exercised at concrete tiny models, including both
degeneracies.  All checks close by `decide` — no `native_decide`, no
enlarged trust surface. -/

section GroundChecks

-- `IsTransversal`: positive and negative instances.
example : IsTransversal ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) {1} := by decide
example : ¬IsTransversal ({{0}, {1}} : Finset (Finset (Fin 2))) {0} := by decide
example : IsTransversal (∅ : Finset (Finset (Fin 1))) ∅ := by decide
example : ¬IsTransversal ({∅} : Finset (Finset (Fin 1))) Finset.univ := by decide

-- `transversals`: empty family (everything), `∅ ∈ F` (nothing), one edge.
example : transversals (∅ : Finset (Finset (Fin 1))) = Finset.univ := by decide
example : transversals ({∅} : Finset (Finset (Fin 2))) = ∅ := by decide
example : transversals ({{0, 1}} : Finset (Finset (Fin 2))) = {{0}, {1}, {0, 1}} := by
  decide

-- `coveringNumber`: single-set family.
example : coveringNumber ({{1, 2}} : Finset (Finset (Fin 3))) = 1 := by decide
-- Two disjoint singletons: both vertices needed.
example : coveringNumber ({{0}, {1}} : Finset (Finset (Fin 2))) = 2 := by decide
-- Two disjoint pairs: τ = 2.
example : coveringNumber ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) = 2 := by decide
-- Common element: τ = 1.
example : coveringNumber ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))) = 1 := by decide
-- Triangle graph: no single vertex covers all three edges, τ = 2.
example : coveringNumber ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) = 2 := by
  decide
-- Empty family (honest 0), including on the empty ground type.
example : coveringNumber (∅ : Finset (Finset (Fin 3))) = 0 := by decide
example : coveringNumber (∅ : Finset (Finset (Fin 0))) = 0 := by decide
-- Junk pin: some member is ∅.
example : coveringNumber ({∅} : Finset (Finset (Fin 3))) = 0 := by decide
example : coveringNumber ({∅, {0}} : Finset (Finset (Fin 2))) = 0 := by decide
-- Wikipedia's 3-uniform example (0-indexed): τ({123,145,456,236}) = 2.
example :
    coveringNumber
      ({{0, 1, 2}, {0, 3, 4}, {3, 4, 5}, {1, 2, 5}} : Finset (Finset (Fin 6))) = 2 := by
  decide

end GroundChecks

/-! ## Satisfiability of hypotheses

STYLE.md: every hypothesis-bearing theorem gets a joint concrete
instantiation, so none is vacuous. -/

section Satisfiability

-- `not_isTransversal_of_empty_mem`, `coveringNumber_of_empty_mem`: `∅ ∈ F`.
example : (∅ : Finset (Fin 1)) ∈ ({∅} : Finset (Finset (Fin 1))) := by decide
-- `IsTransversal.mono`: a transversal and a strict superset.
example : IsTransversal ({{0, 1}} : Finset (Finset (Fin 2))) {0} ∧
    ({0} : Finset (Fin 2)) ⊆ {0, 1} := by decide
-- `IsTransversal.anti`: a transversal of the larger family and F ⊆ F'.
example : IsTransversal ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) {1} ∧
    ({{0, 1}} : Finset (Finset (Fin 3))) ⊆ {{0, 1}, {1, 2}} := by decide
-- `IsTransversal.nonempty`: a transversal of a nonempty family.
example : IsTransversal ({{0, 1}} : Finset (Finset (Fin 2))) {1} ∧
    ({{0, 1}} : Finset (Finset (Fin 2))).Nonempty := by decide
-- `isTransversal_univ`, `exists_isTransversal_card_eq`,
-- `coveringNumber_le_card_univ`: `∅ ∉ F` at a nonempty family.
example : ∅ ∉ ({{0}} : Finset (Finset (Fin 2))) := by decide
-- `coveringNumber_le_card`: a concrete transversal.
example : IsTransversal ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) {0, 2} := by decide
-- `coveringNumber_pos`, `coveringNumber_eq_zero_iff` (positive branch):
-- `F.Nonempty` and `∅ ∉ F` jointly.
example : ({{0}} : Finset (Finset (Fin 1))).Nonempty ∧
    ∅ ∉ ({{0}} : Finset (Finset (Fin 1))) := by decide
-- `coveringNumber_eq_one_of_forall_mem`: nonempty family with common element.
example : ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))).Nonempty ∧
    ∀ A ∈ ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))), (0 : Fin 3) ∈ A := by decide
-- `coveringNumber_mono`: F ⊆ F' with ∅ ∉ F', jointly.
example : ({{0, 1}} : Finset (Finset (Fin 4))) ⊆ {{0, 1}, {2, 3}} ∧
    ∅ ∉ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) := by decide
-- `coveringNumber_mono` guard is load-bearing: dropping `∅ ∉ F'` makes the
-- claim false (junk 0 on the right).
example : ¬(coveringNumber ({{0}} : Finset (Finset (Fin 1))) ≤
    coveringNumber ({{0}, ∅} : Finset (Finset (Fin 1)))) := by decide

end Satisfiability
