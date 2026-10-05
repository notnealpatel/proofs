import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph

universe u w

/-- A triangle-incidence graph with one distinguished original vertex. Nonroot nodes
represent actual triangles, ordinary connectors represent original edges, and zero
connectors identify a shared triangle vertex. Its zero connectors are a matching
away from a disjoint root star. -/
structure Model {V : Type u} {W : Type w} (G : SimpleGraph V) (K : SimpleGraph W)
    (v : V) (root : W) where
  triangle : W → Finset V
  root_triangle : triangle root = ∅
  triangle_clique : ∀ x, x ≠ root → G.IsNClique 3 (triangle x)
  port : W → W → V
  root_port : ∀ y, K.Adj root y → port root y = v
  port_mem : ∀ x y, x ≠ root → K.Adj x y → port x y ∈ triangle x
  port_injective : ∀ x y z, x ≠ root → K.Adj x y → K.Adj x z →
    port x y = port x z → y = z
  port_surjective : ∀ x a, x ≠ root → a ∈ triangle x →
    ∃ y, K.Adj x y ∧ port x y = a
  connector : ∀ x y, K.Adj x y →
    port x y = port y x ∨ G.Adj (port x y) (port y x)
  zero_unique : ∀ x y z, x ≠ root →
    K.Adj x y → port x y = port y x →
    K.Adj x z → port x z = port z x → y = z
  root_mem_iff : ∀ x, x ≠ root →
    (v ∈ triangle x ↔ K.Adj root x ∧ port root x = port x root)
  overlap : ∀ x y a, x ≠ root → y ≠ root → x ≠ y →
    a ∈ triangle x → a ∈ triangle y →
    (K.Adj x y ∧ port x y = port y x ∧ port x y = a) ∨
    (a = v ∧ K.Adj root x ∧ port root x = port x root ∧
      K.Adj root y ∧ port root y = port y root)
  root_leaves_nonadjacent : ∀ x y,
    K.Adj root x → port root x = port x root →
    K.Adj root y → port root y = port y root → ¬ K.Adj x y

example : Nonempty (Model (⊤ : SimpleGraph (Option (Fin 4 × Fin 4)))
    (⊤ : SimpleGraph (Fin 4)) none 0) := by
  let triangle : Fin 4 → Finset (Option (Fin 4 × Fin 4)) := fun x =>
    if x = 0 then ∅ else (Finset.univ.erase x).image (fun y => some (x, y))
  let port : Fin 4 → Fin 4 → Option (Fin 4 × Fin 4) := fun x y =>
    if x = 0 then none else some (x, y)
  exact ⟨{
    triangle := triangle
    root_triangle := by decide
    triangle_clique := by decide
    port := port
    root_port := by decide
    port_mem := by decide
    port_injective := by decide
    port_surjective := by decide
    connector := by decide
    zero_unique := by decide
    root_mem_iff := by decide
    overlap := by
      intro x y a hx hy hxy hax hay
      simp only [triangle, if_neg hx, Finset.mem_image] at hax
      obtain ⟨b, hb, rfl⟩ := hax
      simp only [triangle, if_neg hy, Finset.mem_image] at hay
      obtain ⟨c, hc, heq⟩ := hay
      exact (hxy (congrArg Prod.fst (Option.some.inj heq)).symm).elim
    root_leaves_nonadjacent := by decide }⟩

end Erdos64.TriangleIncidence
