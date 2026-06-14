# Bp1: Compute the decisive dimensions for M_4 border apolarity feasibility.
#
# For M_n, the border apolarity algorithm operates on:
#   A = U* tensor V,  B = V* tensor W,  C = W* tensor U
# with U = V = W = C^n.
#
# As a GL(U) x GL(V) x GL(W) module:
#   A* tensor B* = U tensor V* tensor V tensor W*
#                = U tensor (sl(V) + Id_V) tensor W*
#   (since V* tensor V = sl(V) + C*Id)
#
# E_110' lives in U* tensor sl(V) tensor W (working dually).
# dim E_110' = r - n^2 where r is the target border rank.
#
# The (210) map is:  E_110 tensor A -> S^2(A) tensor B
# equivalently, testing the kernel of: E_110^perp tensor A -> Lambda^2(A) tensor B
#
# Critical dimensions to compute for n = 2, 3, 4:

for n in [2, 3, 4]:
    print("=" * 60)
    print("n = %d" % n)
    print("=" * 60)

    dimA = n^2
    dimB = n^2
    dimC = n^2
    dimslV = n^2 - 1

    # Space U* tensor sl(V) tensor W
    dim_space = n * dimslV * n

    # For the Koszul+border-sub bound: r = 2n^2 - ceil(log_2(n)) - 1
    import math
    r_koszul = 2*n^2 - int(math.ceil(math.log2(n))) - 1

    # dim E_110' = r - n^2
    dim_E110_prime = r_koszul - n^2

    # codim F_110 in A* tensor B* is r
    # codim F_110 in T(C*)^perp is r - n^2 (= dim of U* tensor Id_V tensor W)

    # (210) map target: S^2(A*) tensor B* has dimension binom(n^2+1,2) * n^2
    dim_S2A_star_times_B_star = binomial(n^2 + 1, 2) * n^2

    # (120) map target: A* tensor S^2(B*) has dimension n^2 * binom(n^2+1,2)
    dim_A_star_times_S2B_star = n^2 * binomial(n^2 + 1, 2)

    # Dual (210) map: E_110 tensor A -> Lambda^2(A) tensor B
    dim_Lambda2A_times_B = binomial(n^2, 2) * n^2

    # For the (111) test:
    # F_110 tensor C* + F_101 tensor B* + F_011 tensor A* -> A* tensor B* tensor C*
    dim_ABC = (n^2)^3

    # Representation theory decomposition of V tensor sl(V):
    # V tensor sl(V) = V_{2w1+w_{v-1}} + V_{w2+w_{v-1}} + V_{w1}
    # (equation (6.5) in CHL)
    # dim V_{2w1+w_{v-1}} = (1/2)*v^3 + (1/2)*v^2 - v
    # dim V_{w2+w_{v-1}} = (1/2)*v^3 - (1/2)*v^2 - v
    # dim V_{w1} = v
    v = n  # dim V
    dim_V_2w1_wvm1 = v^3 // 2 + v^2 // 2 - v
    dim_V_w2_wvm1 = v^3 // 2 - v^2 // 2 - v
    dim_V_w1 = v

    # The (210) map kernel contribution is governed by (Proposition 5.4):
    # a = dim[(V tensor X) cap V_{2w1+w_{v-1}}] + dim[(V tensor X) cap V_{w2+w_{v-1}}]
    # b = n * dim[(V tensor X) cap V_w1] - dim[(V tensor X) cap V_{w2+w_{v-1}}]

    # Weight zero subspace of sl(V): dim = n-1 (Cartan subalgebra of sl_n)
    dim_weight_zero_slV = n - 1

    # The B-fixed E_110' subspaces involve choosing from the weight diagram
    # of U* tensor sl(V) tensor W. The key parametric families come from
    # weight multiplicities in sl(V), specifically the weight-zero space.

    print("  dim(A) = dim(B) = dim(C) = %d" % dimA)
    print("  dim(sl(V)) = %d" % dimslV)
    print("  dim(U* tensor sl(V) tensor W) = %d" % dim_space)
    print("  Koszul+border-sub bound r = %d" % r_koszul)
    print("  dim(E_110') = r - n^2 = %d" % dim_E110_prime)
    print()
    print("  V tensor sl(V) decomposition:")
    print("    dim V_{2w1+w_{v-1}} = %d" % dim_V_2w1_wvm1)
    print("    dim V_{w2+w_{v-1}} = %d" % dim_V_w2_wvm1)
    print("    dim V_w1 = %d" % dim_V_w1)
    print("    total = %d (should be %d)" % (dim_V_2w1_wvm1 + dim_V_w2_wvm1 + dim_V_w1, v * dimslV))
    print()
    print("  Weight-zero subspace of sl_%d: dim = %d" % (n, dim_weight_zero_slV))
    print()

    # (210)/(120) matrix dimensions
    # The (210) map: F_110 tensor A* -> S^2(A*) tensor B*
    # F_110 has dim = n^4 - r (since A* tensor B* has dim n^4)
    dim_F110 = n^4 - r_koszul
    # Source: F_110 tensor A* has dim = dim_F110 * n^2
    dim_210_source = dim_F110 * n^2
    # Target: S^2(A*) tensor B* has dim = binom(n^2+1,2) * n^2
    dim_210_target = dim_S2A_star_times_B_star

    print("  (210) map dimensions:")
    print("    source: F_110 tensor A* = %d x %d = %d" % (dim_F110, n^2, dim_210_source))
    print("    target: S^2(A*) tensor B* = %d" % dim_210_target)
    print("    matrix size: %d x %d" % (dim_210_source, dim_210_target))
    print()

    # Dual formulation (what CHL actually use):
    # E_110^perp tensor A -> Lambda^2(A) tensor B
    # E_110 has dim r, E_110^perp has dim n^4 - r = dim_F110
    # Wait -- E_110 = F_110^perp, so dim(E_110) = n^4 - dim(F_110) = r
    # E_110^perp = F_110, so dim = n^4 - r
    # No wait. E_110 \subset A tensor B has dim r.
    # F_110 \subset A* tensor B* has dim n^4 - r (codim r).
    # E_110 = F_110^perp.
    # The dual (210) test: E_110 tensor A -> Lambda^2(A) tensor B
    dim_E110 = r_koszul
    dim_dual_210_source = dim_E110 * n^2
    dim_dual_210_target = binomial(n^2, 2) * n^2

    print("  Dual (210) map (CHL formulation):")
    print("    source: E_110 tensor A = %d x %d = %d" % (dim_E110, n^2, dim_dual_210_source))
    print("    target: Lambda^2(A) tensor B = %d" % dim_dual_210_target)
    print("    matrix size: %d x %d" % (dim_dual_210_source, dim_dual_210_target))
    print()

    # For (111) test:
    # Source: F_110 tensor C* + F_101 tensor B* + F_011 tensor A*
    # Target: A* tensor B* tensor C* (dim n^6)
    # Each F has dim n^4 - r, each tensored with n^2
    dim_111_one_term = dim_F110 * n^2
    dim_111_target = n^6
    print("  (111) map dimensions:")
    print("    each source term: %d x %d = %d" % (dim_F110, n^2, dim_111_one_term))
    print("    total source (3 terms): %d" % (3 * dim_111_one_term))
    print("    target: A* tensor B* tensor C* = %d" % dim_111_target)
    print()

    # The KEY measurement: parameter count of the Borel-fixed families.
    # For M_n, the outer structure grid is n x n.
    # At each grid point (s,t), the inner structure is a B-fixed subspace of sl(V).
    # The weight-zero subspace of sl_n has dimension n-1.
    # This is where parameters appear: a j-dim B-fixed subspace at a site (s,t)
    # where weight multiplicities exist requires choosing from a family.
    #
    # For sl_n, the weight diagram has levels. The Cartan subalgebra (weight zero)
    # has dimension n-1. When n=3, dim=2, giving a P^1 family.
    # When n=4, dim=3, giving P^2 (or more complex) families.
    #
    # But there are MORE weight multiplicities in sl_4 than sl_3:
    # sl_3: weights have multiplicity at most 2 (at weight zero)
    # sl_4: weights have multiplicity at most 3 (at weight zero)
    # AND additional multiplicity-2 weights appear

    # Let's compute the weight multiplicities of sl_n
    # The roots of sl_n are e_i - e_j for i != j
    # Weight zero has multiplicity n-1 (the Cartan subalgebra)
    # Other weights in the adjoint rep have multiplicity 1

    print("  sl_%d weight structure:" % n)
    print("    dim(sl_%d) = %d" % (n, dimslV))
    print("    weight-zero multiplicity = %d" % dim_weight_zero_slV)
    print("    number of roots (multiplicity-1 weights) = %d" % (n*(n-1)))
    print("    total = %d (check: %d)" % (dim_weight_zero_slV + n*(n-1), dimslV))
    print()

    # For U* tensor sl(V) tensor W, the outer structure is on the n x n grid
    # of (U*, W) weights: (u^i, w_j) for i,j = 1,...,n.
    # At each grid point (i,j), the fiber is sl(V), with the full weight
    # structure of sl_n.
    #
    # The inner B-fixed subspaces of sl_n of various dimensions:
    # These correspond to choosing B-fixed subspaces of the adjoint representation.
    # The B-fixed subspaces are determined by choosing "upper sets" in the
    # weight partial order, with parameters at weight-multiplicity sites.

    # The critical number: how many parameters appear in the B-fixed families
    # For sl_3 (n=3): weight zero dim 2, so 1-parameter families (P^1)
    # For sl_4 (n=4): weight zero dim 3, so up to 2-parameter families (P^2 or Gr(k,3))

    # But the full parameter count is more subtle: it depends on how many
    # grid points have inner structure touching the weight-zero subspace.

    # For dim(E_110') = 13 in a space of dim 240:
    # We need to fill 13 slots in the n x n = 4 x 4 grid.
    # At each (s,t), we can have inner structure dim 0 to 15.
    # The TOTAL inner structure dim sums to 13.
    #
    # When a grid point (s,t) has inner dim j >= n (covering the weight-zero
    # subspace), we get a Gr(d, n-1) family where d depends on how many
    # weight-zero vectors we include.

    # The Grassmannian of k-planes in C^{n-1} has dimension k(n-1-k).
    # Max dim = floor((n-1)^2/4) when k = floor((n-1)/2).

    max_grass_dim = (n-1)^2 // 4
    print("  Maximum Grassmannian parameter at one site: Gr(k,%d)" % (n-1))
    print("    max dim = %d (at k=%d)" % (max_grass_dim, (n-1)//2))
    print()

    # Total parameter count depends on the outer structure.
    # Each grid point touching weight zero can contribute Gr(d,n-1) parameters.
    # The number of such grid points times the per-point parameter dimension
    # gives the total.

    # For M_3 (n=3): dim(E_110') = 7
    # Inner dim at each site is at most 8 (= dim sl_3)
    # Grid is 3x3. Weight-zero dim = 2.
    # CHL report: "positive dimensional families" -- P^1 parameters.
    # 8 candidates pass, giving 512 triples.

    # For M_4 (n=4): dim(E_110') = 13
    # Inner dim at each site is at most 15 (= dim sl_4)
    # Grid is 4x4. Weight-zero dim = 3.
    # Gr(k,3) max dim = 2 (at k=1 or k=2, both give dim 2).
    # If multiple grid points touch weight zero, parameters multiply.

print()
print("=" * 60)
print("COMPARISON TABLE: M_2 vs M_3 vs M_4")
print("=" * 60)
for n in [2, 3, 4]:
    import math
    r = 2*n^2 - int(math.ceil(math.log2(n))) - 1
    dim_E = r - n^2
    dim_ambient = n * (n^2 - 1) * n
    # (210) matrix: source = r * n^2, target = binom(n^2,2) * n^2
    mat_rows = r * n^2
    mat_cols = binomial(n^2, 2) * n^2
    print("  M_%d: r=%d, dim(E')=%d, ambient=%d, (210) dual matrix: %d x %d" % (
        n, r, dim_E, dim_ambient, mat_rows, mat_cols))
    print("        weight-zero dim in sl_%d = %d" % (n, n-1))
    print("        max Gr parameter per site = %d" % ((n-1)^2 // 4))
