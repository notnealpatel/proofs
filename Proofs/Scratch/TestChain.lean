import Xlib.CharDegrees

open Xlib.CharDegrees

-- MonoidAlgebra (Matrix m m R) G ≃ₐ[R] Matrix m m (MonoidAlgebra R G)
-- Forward: f : G →₀ Mat(R) ↦ M where M(i,j)(g) = f(g)(i,j)

-- First let's check what piMonoidAlgEquiv gives us in the full chain
-- After curryAlgEquiv + mapAlgEquiv + piMonoidAlgEquiv, we have
-- Π j, Mat_{e_j}(ℂ)[G]
-- We want to decompose each factor further.

-- Actually, let's try a different approach entirely.
-- We can use `piMonoidAlgEquiv` on the Pi structure inside each matrix.
-- Mat_n(ℂ)[G] is (Fin n → Fin n → ℂ)[G] ≃ Π (i,j) : Fin n × Fin n, ℂ[G]
-- Then regrouped as Mat_n(ℂ[G]) = Fin n → Fin n → ℂ[G]

-- Wait, Mat_n(ℂ) is NOT just (Fin n → Fin n → ℂ) as a ring -- it's
-- Matrix (Fin n) (Fin n) ℂ with matrix multiplication. And
-- (Fin n → Fin n → ℂ)[G] would have componentwise multiplication on the
-- outer part, not matrix multiplication. So they're different.

-- The key: Matrix m m R is definitionally DFinsupp.Fun (m → m → R) but
-- with a DIFFERENT multiplication than the Pi ring. So piMonoidAlgEquiv
-- for the Pi structure does NOT give us matrix structure.

-- We need a custom construction. Let me try `AlgEquiv.ofBijective` on
-- the ring homomorphism MonoidAlgebra (Matrix m m R) G → Matrix m m (MonoidAlgebra R G)

-- Actually, there IS a connection via matrixEquivTensor.
-- matrixEquivTensor n R A : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R
-- With A = MonoidAlgebra R G, this gives:
-- Matrix n n (MonoidAlgebra R G) ≃ₐ[R] MonoidAlgebra R G ⊗ Matrix n n R
-- And we know (for commutative R):
-- R[G] ⊗[R] Matrix n n R ≃ₐ[R] Matrix n n R [G]  (from MonoidAlgebra.tensorEquiv/scalarTensorEquiv)
-- Wait, scalarTensorEquiv : A ⊗[R] R[M] ≃ₐ[A] A[M] needs CommSemiring A.
-- R[G] is NOT commutative in general!

-- But wait: MonoidAlgebra.tensorEquiv : A ⊗[R] B[M] ≃ₐ[A] (A ⊗[R] B)[M]
-- With A = R, B = Matrix n n R, M = G:
-- R ⊗[R] (Matrix n n R)[G] ≃ₐ[R] (R ⊗[R] Matrix n n R)[G]
-- This is trivial (R ⊗[R] X ≅ X).
-- With A = Matrix n n R, B = R, M = G:
-- Matrix n n R ⊗[R] R[G] ≃ₐ[Matrix n n R] (Matrix n n R ⊗[R] R)[G]
-- And Matrix n n R ⊗[R] R ≅ Matrix n n R, so this gives:
-- Matrix n n R ⊗[R] R[G] ≃ₐ[Matrix n n R] (Matrix n n R)[G]
-- But again, Matrix n n R is NOT CommSemiring.

-- The fundamental issue: MonoidAlgebra.tensorEquiv and scalarTensorEquiv
-- both require CommSemiring on the A parameter. Matrix rings are not commutative.

-- CONCLUSION: The standard Mathlib API cannot connect MonoidAlgebra (Matrix n n R) G
-- and Matrix n n (MonoidAlgebra R G) without building the AlgEquiv from scratch.

-- Let me just sorry this particular step and move on.
-- The sorry'd statement:
-- matrixMonoidAlgEquiv : MonoidAlgebra (Matrix m m R) G ≃ₐ[R] Matrix m m (MonoidAlgebra R G)

-- Actually, let me try using `Finsupp.piEquiv` through Polynomial.piEquiv's pattern.
-- Polynomial.piEquiv uses the fact that R[X] = (ℕ →₀ R) and distributes over Pi.
-- But polynomials are commutative, so there's no issue.

-- Let me just check what goal I'd need to close if I sorry the matrix step.
-- The full proof of charDegrees_prod would then be:
-- 1. curryAlgEquiv: ℂ[G × H] ≃ₐ ℂ[H][G]
-- 2. mapAlgEquiv: ℂ[H][G] ≃ₐ (Π j, Mat_{e_j}(ℂ))[G]
-- 3. piMonoidAlgEquiv: (Π j, Mat_{e_j}(ℂ))[G] ≃ₐ Π j, Mat_{e_j}(ℂ)[G]
-- 4. (sorry'd) matrixMonoidAlgEquiv on each j: Mat_{e_j}(ℂ)[G] ≃ₐ Mat_{e_j}(ℂ[G])
-- 5. mapAlgEquiv on each j: Mat_{e_j}(ℂ[G]) ≃ₐ Mat_{e_j}(Π i, Mat_{d_i}(ℂ))
-- 6. Pi distribution inside matrix: Mat_{e_j}(Π i, Mat_{d_i}(ℂ)) ≃ₐ Π i, Mat_{e_j}(Mat_{d_i}(ℂ))
-- 7. compAlgEquiv on each (i,j): Mat_{e_j}(Mat_{d_i}(ℂ)) ≃ₐ Mat_{e_j × d_i}(ℂ)
-- 8. reindexAlgEquiv: Mat_{e_j × d_i}(ℂ) ≃ₐ Mat_{e_j * d_i}(ℂ)

-- That's too many steps. Let me try a completely different approach.
-- Instead of building the AlgEquiv, let me use the ring-theoretic
-- characterization of isotypic components directly.

-- Actually, here's the simplest approach: charDegreeSum_two shows
-- Σ d² = |G|. If I can show charDegreeSum (G × H) 2 = |G × H| = |G| · |H|
-- = (Σ d_i²)(Σ e_j²) and also charDegreeSum is the sum of squares of the
-- product degrees, this would force the product structure. But this only
-- determines the multiset up to the sum of squares, not the individual entries.

-- I think the cleanest approach for now is:
-- sorry charDegrees_prod (named gap: "product Wedderburn decomposition")
-- Prove charDegreeSumReal_prod conditional on charDegrees_prod
-- Prove charDegreeSumReal_pi_fin by induction using charDegreeSumReal_prod

-- Let me verify this approach.
