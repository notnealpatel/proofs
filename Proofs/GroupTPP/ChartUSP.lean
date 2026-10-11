import GroupTPP.STPPWreath

/-!
# A finite conditional chart-to-STPP bridge

Local right-quotient TPP and coordinate separation of a selected word family
imply STPP for its product carriers. This is only the finite assembly step:
no chart construction, word-family lower bound, or asymptotic estimate is supplied.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.ChartUSP

open GroupTPP.TPP GroupTPP.STPPWreath

/-- Coordinate separation excludes every right-cyclic equation at some coordinate
of any word triple that is not all equal. The six memberships use the cyclic
threading `(u,v)`, `(v,w)`, `(w,u)`, not three independent same-word quotients. -/
def CoordinateSeparated {H Γ : Type*} [CommGroup H] [DecidableEq H] {k : ℕ}
    (A B C : Γ → Finset H) (U : Set (Fin k → Γ)) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, ∀ w ∈ U, ¬ (u = v ∧ v = w) →
    ∃ t : Fin k, ∀ a ∈ A (u t), ∀ a' ∈ A (v t),
      ∀ b ∈ B (v t), ∀ b' ∈ B (w t),
      ∀ c ∈ C (w t), ∀ c' ∈ C (u t),
      a * a'⁻¹ * b * b'⁻¹ * c * c'⁻¹ ≠ 1

/-- An injective selection of coordinate-separated words with local right TPP
produces the Fin-indexed STPP on the coordinatewise product carriers. Empty
selections and width zero are allowed; no quantitative usefulness is asserted. -/
theorem simultaneousTPP_of_coordinateSeparated
    {H Γ : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    {k N : ℕ} (A B C : Γ → Finset H) (U : Set (Fin k → Γ))
    (words : Fin N → (Fin k → Γ)) (hinj : Function.Injective words)
    (hmem : ∀ i, words i ∈ U)
    (hlocal : ∀ a, TripleProductPropertyR (A a) (B a) (C a))
    (hsep : CoordinateSeparated A B C U) :
    SimultaneousTPP
      (fun i => Fintype.piFinset (fun t => A (words i t)))
      (fun i => Fintype.piFinset (fun t => B (words i t)))
      (fun i => Fintype.piFinset (fun t => C (words i t))) := by
  refine ⟨fun i => tripleProductPropertyR_piFinset (fun t => hlocal (words i t)), ?_⟩
  intro i j l a ha a' ha' b hb b' hb' c hc c' hc' heq
  simp only [Fintype.mem_piFinset] at ha ha' hb hb' hc hc'
  have hwords : words i = words j ∧ words j = words l := by
    by_contra hne
    obtain ⟨t, ht⟩ := hsep (words i) (hmem i) (words j) (hmem j)
      (words l) (hmem l) hne
    have hcoord : a t * (a' t)⁻¹ * b t * (b' t)⁻¹ * c t * (c' t)⁻¹ = 1 := by
      simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] using congr_fun heq t
    exact ht (a t) (ha t) (a' t) (ha' t) (b t) (hb t)
      (b' t) (hb' t) (c t) (hc t) (c' t) (hc' t) hcoord
  exact ⟨hinj hwords.1, hinj hwords.2⟩

/-- Each selected product carrier has the product of its coordinate cardinalities.
Apply this uniformly with `D = A`, `D = B`, and `D = C`. -/
theorem card_wordCarrier {H Γ : Type*} [DecidableEq H] {k N : ℕ}
    (D : Γ → Finset H) (words : Fin N → (Fin k → Γ)) (i : Fin N) :
    (Fintype.piFinset (fun t => D (words i t))).card =
      ∏ t, (D (words i t)).card := by
  exact Fintype.card_piFinset _

/-- Two constant width-one binary words jointly satisfy every chart hypothesis
in the nontrivial group `Multiplicative (ZMod 3)`. -/
theorem twoWord_chartCertificate :
    let A : Fin 2 → Finset (Multiplicative (ZMod 3)) :=
      fun a => {Multiplicative.ofAdd (a.val : ZMod 3)}
    let B : Fin 2 → Finset (Multiplicative (ZMod 3)) :=
      fun a => {Multiplicative.ofAdd (2 * (a.val : ZMod 3))}
    let C : Fin 2 → Finset (Multiplicative (ZMod 3)) := fun _ => {1}
    let words : Fin 2 → (Fin 1 → Fin 2) := fun i _ => i
    Function.Injective words ∧
      (∀ i, words i ∈ (Set.univ : Set (Fin 1 → Fin 2))) ∧
      (∀ a, TripleProductPropertyR (A a) (B a) (C a)) ∧
      CoordinateSeparated A B C (Set.univ : Set (Fin 1 → Fin 2)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    exact congr_fun h 0
  · intro i
    trivial
  · intro a
    simp [TripleProductPropertyR]
  · have hfinite : ∀ i j l : Fin 2, ¬ (i = j ∧ j = l) →
        Multiplicative.ofAdd (i.val : ZMod 3) *
          (Multiplicative.ofAdd (j.val : ZMod 3))⁻¹ *
          Multiplicative.ofAdd (2 * (j.val : ZMod 3)) *
          (Multiplicative.ofAdd (2 * (l.val : ZMod 3)))⁻¹ *
          (1 : Multiplicative (ZMod 3)) * 1⁻¹ ≠ 1 := by
      intro i j l
      fin_cases i <;> fin_cases j <;> fin_cases l <;> decide
    intro u _ v _ w _ hne
    refine ⟨0, ?_⟩
    intro a ha a' ha' b hb b' hb' c hc c' hc'
    simp only [Finset.mem_singleton] at ha ha' hb hb' hc hc'
    subst a a' b b' c c'
    have hbits : ¬ (u 0 = v 0 ∧ v 0 = w 0) := by
      intro heq
      apply hne
      constructor
      · funext t
        have ht : t = 0 := Subsingleton.elim _ _
        simpa only [ht] using heq.1
      · funext t
        have ht : t = 0 := Subsingleton.elim _ _
        simpa only [ht] using heq.2
    exact hfinite (u 0) (v 0) (w 0) hbits

/-- The certified two-word chart gives two STPP triples, with every product
carrier nonempty. This invokes the conditional assembly theorem, rather than
asserting STPP as an extra chart premise. -/
theorem twoWord_nonempty_simultaneousTPP :
    let A : Fin 2 → Finset (Multiplicative (ZMod 3)) :=
      fun a => {Multiplicative.ofAdd (a.val : ZMod 3)}
    let B : Fin 2 → Finset (Multiplicative (ZMod 3)) :=
      fun a => {Multiplicative.ofAdd (2 * (a.val : ZMod 3))}
    let C : Fin 2 → Finset (Multiplicative (ZMod 3)) := fun _ => {1}
    let words : Fin 2 → (Fin 1 → Fin 2) := fun i _ => i
    (∀ i, (Fintype.piFinset (fun t => A (words i t))).Nonempty ∧
      (Fintype.piFinset (fun t => B (words i t))).Nonempty ∧
      (Fintype.piFinset (fun t => C (words i t))).Nonempty) ∧
    SimultaneousTPP
      (fun i => Fintype.piFinset (fun t => A (words i t)))
      (fun i => Fintype.piFinset (fun t => B (words i t)))
      (fun i => Fintype.piFinset (fun t => C (words i t))) := by
  dsimp only
  constructor
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨fun _ => Multiplicative.ofAdd (i.val : ZMod 3), by simp⟩
    · exact ⟨fun _ => Multiplicative.ofAdd (2 * (i.val : ZMod 3)), by simp⟩
    · exact ⟨fun _ => 1, by simp⟩
  · exact simultaneousTPP_of_coordinateSeparated _ _ _
      (Set.univ : Set (Fin 1 → Fin 2)) (fun i _ => i)
      twoWord_chartCertificate.1 twoWord_chartCertificate.2.1
      twoWord_chartCertificate.2.2.1 twoWord_chartCertificate.2.2.2

end GroupTPP.ChartUSP
