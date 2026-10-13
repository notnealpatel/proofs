import Combinatorics.IndependencePolynomialCertificate
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic

set_option autoImplicit false

namespace ErdosCandidates.E993

open SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

instance (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [SimpleGraph.sum] <;> infer_instance

instance (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- The number of independent vertex sets of size `k`, counted as complement cliques. -/
def indepCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ((Gᶜ).cliqueFinset k).card

/-- A sequence rises to a peak and then falls, including its infinite tail. -/
def Unimodal (a : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧
    (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

example : indepCount (⊥ : SimpleGraph (Fin 0)) 0 = 1 := by decide
example : Unimodal (fun _ => 0) := ⟨0, by simp, by simp⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
private theorem clique_sum_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (s : Finset V) (t : Finset W) :
    (G ⊕g H)ᶜ.IsClique (s.disjSum t) ↔ Gᶜ.IsClique s ∧ Hᶜ.IsClique t := by
  simp only [SimpleGraph.isClique_iff]
  constructor
  · intro h
    constructor
    · intro x hx y hy hxy
      simpa using h (x := Sum.inl x) (y := Sum.inl y)
        (by simpa using hx) (by simpa using hy) (by simpa using hxy)
    · intro x hx y hy hxy
      simpa using h (x := Sum.inr x) (y := Sum.inr y)
        (by simpa using hx) (by simpa using hy) (by simpa using hxy)
  · rintro ⟨hs, ht⟩ (x | x) hx (y | y) hy hxy
    · simpa using hs (by simpa using hx) (by simpa using hy) (by simpa using hxy)
    · simp [SimpleGraph.compl_adj]
    · simp [SimpleGraph.compl_adj]
    · simpa using ht (by simpa using hx) (by simpa using hy) (by simpa using hxy)

/-- Independent sets in the canonical disjoint graph sum split uniquely by size,
so their counts are the convolution of the two independent-set sequences. -/
theorem indepCount_sum (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) :
    indepCount (G ⊕g H) k =
      ∑ p ∈ Finset.antidiagonal k, indepCount G p.1 * indepCount H p.2 := by
  classical
  let parts := (Finset.antidiagonal k).sigma
    (fun p => (Gᶜ.cliqueFinset p.1).product (Hᶜ.cliqueFinset p.2))
  have hc : parts.card = ((G ⊕g H)ᶜ.cliqueFinset k).card := by
    apply Finset.card_bij (fun a _ => a.2.1.disjSum a.2.2)
    · intro a ha
      obtain ⟨hp, hs, ht⟩ := (by simpa [parts] using ha :
        a.1 ∈ Finset.antidiagonal k ∧
        Gᶜ.IsNClique a.1.1 a.2.1 ∧ Hᶜ.IsNClique a.1.2 a.2.2)
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      rw [SimpleGraph.isNClique_iff]
      exact ⟨(clique_sum_iff G H _ _).mpr ⟨hs.1, ht.1⟩,
        by simpa [hs.2, ht.2] using hp⟩
    · intro a ha b hb hab
      have he := Finset.disjSum_inj.mp hab
      obtain ⟨hp, hs, ht⟩ := (by simpa [parts] using ha :
        a.1 ∈ Finset.antidiagonal k ∧
        Gᶜ.IsNClique a.1.1 a.2.1 ∧ Hᶜ.IsNClique a.1.2 a.2.2)
      obtain ⟨hq, hu, hv⟩ := (by simpa [parts] using hb :
        b.1 ∈ Finset.antidiagonal k ∧
        Gᶜ.IsNClique b.1.1 b.2.1 ∧ Hᶜ.IsNClique b.1.2 b.2.2)
      have hpq : a.1 = b.1 := Prod.ext
        (by rw [← hs.2, ← hu.2, he.1]) (by rw [← ht.2, ← hv.2, he.2])
      have hsnd : a.2 = b.2 := Prod.ext he.1 he.2
      exact Sigma.ext hpq (by simpa using hsnd)
    · intro u hu
      have h := SimpleGraph.mem_cliqueFinset_iff.mp hu
      have hsplit := (clique_sum_iff G H u.toLeft u.toRight).mp
        (by simpa only [Finset.toLeft_disjSum_toRight] using h.1)
      refine ⟨⟨(u.toLeft.card, u.toRight.card), (u.toLeft, u.toRight)⟩, ?_,
        Finset.toLeft_disjSum_toRight⟩
      simpa [parts, SimpleGraph.isNClique_iff] using
        (show u.toLeft.card + u.toRight.card = k ∧
          Gᶜ.IsClique u.toLeft ∧ Hᶜ.IsClique u.toRight from
          ⟨Finset.card_toLeft_add_card_toRight.trans h.2, hsplit⟩)
  rw [indepCount, ← hc]
  simp [parts, Finset.card_sigma, Finset.card_product, indepCount]

example : indepCount (pathGraph 4) 0 = 1 ∧ indepCount (pathGraph 4) 1 = 4 ∧
    indepCount (pathGraph 4) 2 = 3 ∧ indepCount (pathGraph 4) 3 = 0 := by decide

private theorem indepCount_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    indepCount G k = ((Finset.univ.powersetCard k).filter
      (fun s : Finset V => Gᶜ.IsClique s)).card := by
  unfold indepCount
  congr 1
  ext s
  simp [SimpleGraph.isNClique_iff, and_comm]

/-- The join has a valley at sizes one, two, and three. -/
theorem valleyGraph_counts : indepCount valleyGraph 1 = 16 ∧
    indepCount valleyGraph 2 = 15 ∧ indepCount valleyGraph 3 = 20 := by
  simpa only [indepCount_eq_filter] using valleyGraph_certificate

/-- A concrete general graph has a nonunimodal independent-set sequence. -/
theorem valleyGraph_not_unimodal : ¬ Unimodal (indepCount valleyGraph) := by
  rintro ⟨m, hr, hf⟩
  obtain ⟨h1, h2, h3⟩ := valleyGraph_counts
  by_cases hm : 2 ≤ m
  · have h := hr 1 2 (by omega) hm
    rw [h1, h2] at h
    omega
  · have h := hf 2 3 (by omega) (by omega)
    rw [h2, h3] at h
    omega

end ErdosCandidates.E993
