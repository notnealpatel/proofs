import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Option

set_option autoImplicit false

namespace Erdos64.PartialFisherCore

universe u
variable {V : Type u}

/-- A directed incidence whose first vertex is not the pole. -/
abbrev OrdinaryPort (K : SimpleGraph V) (z : V) :=
  {p : V × V // p.1 ≠ z ∧ K.Adj p.1 p.2}

/-- The pole, represented by `none`, together with the ordinary incidences. -/
abbrev Port (K : SimpleGraph V) (z : V) := Option (OrdinaryPort K z)

/-- Equality or one reversed incidence along an edge of the contraction graph. -/
def PortRel (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (a b : Port K z) : Prop :=
  a = b ∨ match a, b with
    | some p, some r => p.val.1 = r.val.2 ∧ p.val.2 = r.val.1 ∧ M.Adj p.val.1 p.val.2
    | _, _ => False

/-- One-step incidence contraction is symmetric. -/
theorem portRel_symm (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    {a b : Port K z} (h : PortRel K z M a b) : PortRel K z M b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  cases a <;> cases b <;> simp only at h
  apply Or.inr
  refine ⟨h.2.1.symm, h.1.symm, ?_⟩
  simpa only [← h.2.1, ← h.1] using h.2.2.symm

/-- Reversing the coordinates twice returns the same incidence. -/
theorem portRel_trans (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    {a b c : Port K z} (hab : PortRel K z M a b) (hbc : PortRel K z M b c) :
    PortRel K z M a c := by
  rcases hab with hab | hab
  · subst b
    exact hbc
  rcases hbc with hbc | hbc
  · subst c
    exact Or.inr hab
  cases a <;> cases b <;> cases c <;> simp only at hab hbc
  apply Or.inl
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · exact hab.1.trans hbc.2.1
  · exact hab.2.1.trans hbc.1

/-- The direct contraction relation, without a transitive-closure construction. -/
def portSetoid (K : SimpleGraph V) (z : V) (M : SimpleGraph V) : Setoid (Port K z) where
  r := PortRel K z M
  iseqv := ⟨fun _ => Or.inl rfl, portRel_symm K z M, portRel_trans K z M⟩

/-- Vertices of the partially contracted Fisher graph. -/
abbrev QuotientVertex (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :=
  Quotient (portSetoid K z M)

/-- The concrete quotient map on ports. -/
def q (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    Port K z → QuotientVertex K z M := Quotient.mk (portSetoid K z M)

/-- Quotient equality is precisely the one-step contraction relation. -/
theorem q_eq_iff (K : SimpleGraph V) (z : V) (M : SimpleGraph V) (a b : Port K z) :
    q K z M a = q K z M b ↔ PortRel K z M a b := Quotient.eq

/-- The pole is never identified with an ordinary port. -/
theorem q_none_ne_some (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (p : OrdinaryPort K z) : q K z M none ≠ q K z M (some p) := by
  intro h
  have hrel := (q_eq_iff K z M none (some p)).mp h
  simp only [PortRel, reduceCtorEq, or_self] at hrel

/-- On incidences with one fixed first vertex the quotient map is injective. -/
theorem qInjectiveWithinOrdinaryFirst (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x : V) (p r : OrdinaryPort K z) (hp : p.val.1 = x) (hr : r.val.1 = x) :
    q K z M (some p) = q K z M (some r) ↔ p = r := by
  rw [q_eq_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Option.some.inj h
    · have heq : p.val.1 = p.val.2 := (hp.trans hr.symm).trans h.2.1.symm
      have hloop : K.Adj p.val.1 p.val.1 := by
        simpa only [← heq] using p.property.2
      exact False.elim (hloop.ne rfl)
  · rintro rfl
    exact Or.inl rfl

/-- Reversed ordinary incidences are identified exactly on contraction edges. -/
theorem connector_q_eq_iff (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x y : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : K.Adj x y) :
    q K z M (some ⟨(x,y), hx, hxy⟩) =
      q K z M (some ⟨(y,x), hy, hxy.symm⟩) ↔ M.Adj x y := by
  rw [q_eq_iff]
  constructor
  · intro h
    rcases h with h | h
    · have hs : (some x : Option V) = some y :=
        congrArg (fun a : Port K z => a.map (fun p : OrdinaryPort K z => p.val.1)) h
      have heq : x = y := Option.some.inj hs
      exact False.elim (hxy.ne heq)
    · exact h.2.2
  · intro h
    exact Or.inr ⟨rfl, rfl, h⟩

/-- Directed generators: pole spokes, local clique edges, and reversed connectors. -/
def FisherRel (K : SimpleGraph V) (z : V) (a b : Port K z) : Prop :=
  match a, b with
  | none, some p => p.val.2 = z ∧ K.Adj z p.val.1
  | some p, some r =>
      (p.val.1 = r.val.1 ∧ p.val.2 ≠ r.val.2) ∨
      (p.val.1 = r.val.2 ∧ p.val.2 = r.val.1 ∧ K.Adj p.val.1 p.val.2)
  | _, _ => False

/-- The uncontracted port graph, symmetrized with loops removed. -/
def F (K : SimpleGraph V) (z : V) : SimpleGraph (Port K z) :=
  SimpleGraph.fromRel (FisherRel K z)

/-- The partial Fisher quotient graph; `map` discards contracted loops. -/
def G (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    SimpleGraph (QuotientVertex K z M) := (F K z).map (q K z M)

/-- Ordinary ports have a finite enumeration when the underlying vertex type does. -/
noncomputable instance ordinaryPortFintype (K : SimpleGraph V) (z : V) [Fintype V] :
    Fintype (OrdinaryPort K z) := by classical exact Fintype.ofFinite _

/-- The concrete contraction quotient is finite on a finite underlying graph. -/
noncomputable instance quotientVertexFintype (K : SimpleGraph V) (z : V)
    (M : SimpleGraph V) [Fintype V] : Fintype (QuotientVertex K z M) := by
  classical
  exact Quotient.fintype (portSetoid K z M)

/-- Distinct ports at the same ordinary vertex give a quotient clique edge. -/
theorem quotienttriangleedge (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x : V) (p r : OrdinaryPort K z) (hp : p.val.1 = x) (hr : r.val.1 = x)
    (hpr : p ≠ r) : (G K z M).Adj (q K z M (some p)) (q K z M (some r)) := by
  have hq : q K z M (some p) ≠ q K z M (some r) :=
    fun h => hpr ((qInjectiveWithinOrdinaryFirst K z M x p r hp hr).mp h)
  have hseconds : p.val.2 ≠ r.val.2 := by
    intro h
    apply hpr
    apply Subtype.ext
    exact Prod.ext (hp.trans hr.symm) h
  rw [G, SimpleGraph.map_adj']
  refine ⟨hq, some p, some r, ?_, rfl, rfl⟩
  rw [F, SimpleGraph.fromRel_adj]
  exact ⟨fun h => hpr (Option.some.inj h), Or.inl (Or.inl ⟨hp.trans hr.symm, hseconds⟩)⟩

/-- Every edge from the pole gives a spoke in the quotient graph. -/
theorem pole_spoke (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x : V) (hzx : K.Adj z x) :
    (G K z M).Adj (q K z M none)
      (q K z M (some ⟨(x,z), hzx.ne.symm, hzx.symm⟩)) := by
  rw [G, SimpleGraph.map_adj']
  refine ⟨q_none_ne_some K z M _, none,
    some ⟨(x,z), hzx.ne.symm, hzx.symm⟩, ?_, rfl, rfl⟩
  rw [F, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl ⟨rfl, hzx⟩⟩

/-- A connector not selected for contraction survives as a quotient edge. -/
theorem noncontracted_connector_edge (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x y : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : K.Adj x y) (hM : ¬M.Adj x y) :
    (G K z M).Adj (q K z M (some ⟨(x,y), hx, hxy⟩))
      (q K z M (some ⟨(y,x), hy, hxy.symm⟩)) := by
  have hq : q K z M (some ⟨(x,y), hx, hxy⟩) ≠
      q K z M (some ⟨(y,x), hy, hxy.symm⟩) :=
    fun h => hM ((connector_q_eq_iff K z M x y hx hy hxy).mp h)
  rw [G, SimpleGraph.map_adj']
  refine ⟨hq, some ⟨(x,y), hx, hxy⟩, some ⟨(y,x), hy, hxy.symm⟩, ?_, rfl, rfl⟩
  rw [F, SimpleGraph.fromRel_adj]
  exact ⟨fun h => hq (congrArg (q K z M) h), Or.inl (Or.inr ⟨rfl, rfl, hxy⟩)⟩

/-- A contracted connector has equal endpoints and therefore gives no quotient edge. -/
theorem contracted_connector_noAdj (K : SimpleGraph V) (z : V) (M : SimpleGraph V)
    (x y : V) (hx : x ≠ z) (hy : y ≠ z) (hxy : K.Adj x y) (hM : M.Adj x y) :
    ¬(G K z M).Adj (q K z M (some ⟨(x,y), hx, hxy⟩))
      (q K z M (some ⟨(y,x), hy, hxy.symm⟩)) := by
  intro h
  exact h.ne ((connector_q_eq_iff K z M x y hx hy hxy).mpr hM)

-- Definitional checks against the standard subtype, option, quotient, and graph APIs.
example (K : SimpleGraph V) (z : V) :
    OrdinaryPort K z = {p : V × V // p.1 ≠ z ∧ K.Adj p.1 p.2} := rfl

example (K : SimpleGraph V) (z : V) : Port K z = Option (OrdinaryPort K z) := rfl

example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) (p r : OrdinaryPort K z) :
    PortRel K z M (some p) (some r) ↔
      p = r ∨ (p.val.1 = r.val.2 ∧ p.val.2 = r.val.1 ∧ M.Adj p.val.1 p.val.2) := by
  simp [PortRel]

example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    (portSetoid K z M).r = PortRel K z M := rfl

example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    QuotientVertex K z M = Quotient (portSetoid K z M) := rfl

example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) (a : Port K z) :
    q K z M a = Quotient.mk (portSetoid K z M) a := rfl

example (K : SimpleGraph V) (z : V) (p : OrdinaryPort K z) :
    FisherRel K z none (some p) ↔ p.val.2 = z ∧ K.Adj z p.val.1 := Iff.rfl

example (K : SimpleGraph V) (z : V) (p r : OrdinaryPort K z) :
    FisherRel K z (some p) (some r) ↔
      (p.val.1 = r.val.1 ∧ p.val.2 ≠ r.val.2) ∨
      (p.val.1 = r.val.2 ∧ p.val.2 = r.val.1 ∧ K.Adj p.val.1 p.val.2) := Iff.rfl

example (K : SimpleGraph V) (z : V) :
    F K z = SimpleGraph.fromRel (FisherRel K z) := rfl

example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    G K z M = (F K z).map (q K z M) := rfl

-- Joint local hypotheses are realized in the complete graph on four vertices.
example : ∃ p r : OrdinaryPort (⊤ : SimpleGraph (Fin 4)) 0,
    p.val.1 = 1 ∧ r.val.1 = 1 ∧ p ≠ r ∧
    (⊤ : SimpleGraph (Fin 4)).Adj 0 1 ∧
    (⊤ : SimpleGraph (Fin 4)).Adj 1 2 ∧
    (1 : Fin 4) ≠ 0 ∧ (2 : Fin 4) ≠ 0 ∧
    ¬(⊥ : SimpleGraph (Fin 4)).Adj 1 2 := by
  let p : OrdinaryPort (⊤ : SimpleGraph (Fin 4)) 0 := ⟨(1,2), by decide⟩
  let r : OrdinaryPort (⊤ : SimpleGraph (Fin 4)) 0 := ⟨(1,3), by decide⟩
  exact ⟨p, r, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

-- The contracted case is also nonvacuous; the core permits any simple M.
example : (⊤ : SimpleGraph (Fin 4)).Adj 1 2 ∧
    (1 : Fin 4) ≠ 0 ∧ (2 : Fin 4) ≠ 0 ∧
    (⊤ : SimpleGraph (Fin 4)).Adj 1 2 := by decide

example (K : SimpleGraph V) (z : V) : Nonempty (Port K z) := ⟨none⟩
example (K : SimpleGraph V) (z : V) (M : SimpleGraph V) :
    Nonempty (QuotientVertex K z M) := ⟨q K z M none⟩

end Erdos64.PartialFisherCore
