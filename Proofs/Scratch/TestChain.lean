import Xlib.CharDegrees

open Xlib.CharDegrees

noncomputable def piMonoidAlgFwd {R : Type*} [CommSemiring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    {M : Type*} [Monoid M] :
    MonoidAlgebra (Π j, A j) M →ₐ[R] Π j, MonoidAlgebra (A j) M :=
  Pi.algHom R (fun j => MonoidAlgebra (A j) M)
    (fun j => MonoidAlgebra.mapAlgHom M (Pi.evalAlgHom R A j))

-- Use AlgEquiv.ofBijective
noncomputable def piMonoidAlgEquiv {R : Type*} [CommSemiring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    {M : Type*} [DecidableEq M] [Monoid M] :
    MonoidAlgebra (Π j, A j) M ≃ₐ[R] Π j, MonoidAlgebra (A j) M :=
  AlgEquiv.ofBijective piMonoidAlgFwd ⟨
    -- Injective
    fun f g h => by
      ext m j
      have := congrFun (show piMonoidAlgFwd f j = piMonoidAlgFwd g j from congrFun h j) m
      -- this : (piMonoidAlgFwd f) j m = (piMonoidAlgFwd g) j m
      -- piMonoidAlgFwd f j = MonoidAlgebra.mapAlgHom M (Pi.evalAlgHom R A j) f
      -- which maps f to (fun m => (f m) j)
      simpa [piMonoidAlgFwd, MonoidAlgebra.mapAlgHom, Finsupp.mapRange_apply] using this,
    -- Surjective
    fun fs => by
      refine ⟨Finsupp.onFinset
        (Finset.univ.biUnion (fun j => (fs j).support))
        (fun m => fun j => fs j m)
        (fun m hm => ?_), ?_⟩
      · rw [Finset.mem_biUnion]
        by_contra h
        push_neg at h
        apply hm
        funext j
        exact (Finsupp.mem_support_iff.not.mp (h j (Finset.mem_univ j)))
      · ext j m
        simp [piMonoidAlgFwd, MonoidAlgebra.mapAlgHom, Finsupp.mapRange_apply]⟩
