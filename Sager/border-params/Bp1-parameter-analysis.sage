# Bp1: Detailed parameter analysis for M_4 border apolarity.
#
# The decisive measurement: dimension of the parametrized family
# of Borel-fixed F_1100 subspaces.
#
# For M_n at r = 2n^2 - ceil(log2(n)) - 1:
#   E_110' is a (r-n^2)-dimensional B-fixed subspace of U* tensor sl(V) tensor W.
#
# The B-fixed subspaces are described by:
# 1. An "outer structure": a Young-diagram-like filling of the n x n grid
#    of (U*, W)-weight pairs, recording how many inner dimensions sit at each site.
# 2. At each site (s,t), an "inner structure": a B_V-fixed subspace of sl(V).
#    This is where parameters arise if weight multiplicities occur.
#
# For sl_n (the adjoint representation of GL_n):
# - The weight diagram has a partial order on roots e_i - e_j
# - Weight zero (the Cartan subalgebra) has multiplicity n-1
# - All other weights (the root spaces) have multiplicity 1
#
# A B_V-fixed j-dimensional subspace of sl_n is determined by:
# - Taking the j highest root spaces (multiplicity 1, no parameters), PLUS
# - At the weight-zero level: choosing a k-dimensional subspace of C^{n-1}
#   (the Cartan subalgebra), giving a Gr(k, n-1) family.
#
# So parameters arise ONLY when the inner structure includes the weight-zero level.
# For sl_n, the weight-zero level is reached when j >= number of positive roots + 1.
# Number of positive roots = n(n-1)/2.
#
# For the inner structure at a site to touch weight zero, we need:
#   j >= (number of root spaces above weight zero) + 1
# In sl_n, the root spaces are ordered by the partial order on weights.
# The highest weight line spans v_1 tensor v^n.
# Lowering by sl(V) gives a chain of root spaces.
#
# More precisely, sl_n has the root system A_{n-1}.
# The positive roots form a partially ordered set.
# A B-fixed subspace must be an "upper set" (order ideal) plus possibly
# a subspace of the weight-zero space.
#
# The positive roots of sl_n are e_i - e_j for i < j, with n(n-1)/2 elements.
# The partial order: (e_i - e_j) >= (e_k - e_l) iff i <= k and j <= l and (i,j) != (k,l).
#
# An upper set (down-set in weight ordering, up-set in the paper's conventions)
# of the positive root poset determines the B_V-fixed subspace structure.
# The number of antichains (= upper sets) in the positive root poset of A_{n-1}
# gives the number of discrete B_V-fixed subspace configurations.
# Parameters arise when the upper set includes all positive roots (reaching
# the weight-zero level).

print("=" * 60)
print("PARAMETER ANALYSIS")
print("=" * 60)

for n in [2, 3, 4]:
    num_pos_roots = n*(n-1)//2
    num_neg_roots = n*(n-1)//2
    dim_cartan = n - 1
    dim_sl = n^2 - 1

    print()
    print("sl_%d:" % n)
    print("  positive roots: %d" % num_pos_roots)
    print("  weight-zero (Cartan) dim: %d" % dim_cartan)
    print("  negative roots: %d" % num_neg_roots)
    print("  total dim(sl_%d) = %d" % (n, dim_sl))

    # The inner dim j at which weight-zero is first touched:
    # This depends on the poset structure of positive roots.
    # For sl_n, the unique highest root is e_1 - e_n (simple roots summed).
    # The "levels" from highest to lowest weight:
    # Level 0: e_1 - e_n (1 root)
    # Level 1: e_1 - e_{n-1}, e_2 - e_n (2 roots)
    # ...
    # Level k: roots at "height" n-1-k (where height = sum of simple root coefficients)
    # ...
    # The first j for which all positive roots are included:
    # j = n(n-1)/2 means all positive roots are taken.
    # Then j = n(n-1)/2 + 1 first touches weight zero.

    j_weight_zero = num_pos_roots + 1
    print("  inner dim j to first touch weight zero: %d" % j_weight_zero)
    print("  at that j, choosing 1 of %d Cartan vectors -> Gr(1,%d) = P^%d" % (
        dim_cartan, dim_cartan, dim_cartan - 1))

    # Maximum parameter dimension for a single site:
    # This is max over k of dim Gr(k, n-1).
    max_param = 0
    best_k = 0
    for k in range(1, dim_cartan + 1):
        d = k * (dim_cartan - k)
        if d > max_param:
            max_param = d
            best_k = k
    print("  max Grassmannian parameter per site: Gr(%d,%d), dim = %d" % (
        best_k, dim_cartan, max_param))

print()
print("=" * 60)
print("DETAILED M_4 ANALYSIS (n=4, r=29, dim(E')=13)")
print("=" * 60)

n = 4
r = 29
dim_Ep = r - n^2  # = 13
dim_sl4 = 15
num_pos_roots_sl4 = 6

# The sl_4 weight diagram for the adjoint representation:
# Positive roots: e1-e2, e1-e3, e1-e4, e2-e3, e2-e4, e3-e4
# Height (sum of simple root coefficients):
#   e1-e2: height 1 (simple root alpha_1)
#   e2-e3: height 1 (simple root alpha_2)
#   e3-e4: height 1 (simple root alpha_3)
#   e1-e3: height 2 (alpha_1 + alpha_2)
#   e2-e4: height 2 (alpha_2 + alpha_3)
#   e1-e4: height 3 (alpha_1 + alpha_2 + alpha_3) = highest root
# Negative roots: -(each positive root), same heights negated.
# Zero weight: 3-dimensional Cartan subalgebra.

print()
print("sl_4 adjoint weight diagram by level:")
print("  Level 0 (height 3): e1-e4                    [1 root]")
print("  Level 1 (height 2): e1-e3, e2-e4             [2 roots]")
print("  Level 2 (height 1): e1-e2, e2-e3, e3-e4      [3 roots]")
print("  Level 3 (weight 0): Cartan subalgebra         [dim 3]")
print("  Level 4 (height -1): e2-e1, e3-e2, e4-e3     [3 roots]")
print("  Level 5 (height -2): e3-e1, e4-e2             [2 roots]")
print("  Level 6 (height -3): e4-e1                    [1 root]")
print("  Cumulative from top: 1, 3, 6, 9, 12, 14, 15")
print()

# B_V-fixed subspaces of sl_4 by dimension j:
# j=1: just the highest root space. Unique. No parameters.
# j=2: {e1-e4} + one of {e1-e3, e2-e4}. Two choices. No parameters.
#       (Actually: need B_V-fixed 2-plane. Must be upper set of size 2.
#        Upper sets: {e1-e4, e1-e3} or {e1-e4, e2-e4}. Two choices.)
# j=3: all of levels 0,1: {e1-e4, e1-e3, e2-e4}. One upper set. No parameters.
#       OR: {e1-e4} + one height-2 + one height-1. Need to check B-fixed.
#       Upper sets of size 3 in the positive root poset:
#       {e1-e4, e1-e3, e2-e4} (all height >= 2)
#       {e1-e4, e1-e3, e1-e2}
#       {e1-e4, e1-e3, e2-e3}
#       {e1-e4, e2-e4, e2-e3}
#       {e1-e4, e2-e4, e3-e4}
#       Wait - need to verify these are actually upper sets.

# An upper set S in the poset means: if x in S and y >= x, then y in S.
# The poset order: (e_i - e_j) >= (e_k - e_l) iff i <= k, j >= l, (i,j) != (k,l).
# Actually for roots of sl_n, the standard partial order is:
# alpha >= beta iff alpha - beta is a sum of positive roots.
# Equivalently, alpha = e_i - e_j, beta = e_k - e_l:
#   alpha >= beta iff i <= k AND j >= l.

# Let me enumerate all upper sets of the positive root poset of sl_4.
# Positive roots: r12=e1-e2, r13=e1-e3, r14=e1-e4, r23=e2-e3, r24=e2-e4, r34=e3-e4
# Partial order (alpha >= beta iff alpha covers beta):
#   r14 >= r13, r14 >= r24
#   r13 >= r12, r13 >= r23
#   r24 >= r23, r24 >= r34
# So the Hasse diagram is:
#       r14
#      /    \
#    r13    r24
#    / \    / \
#  r12 r23  r34
#      (r23 appears under both r13 and r24)

# Upper sets (order ideals of the dual poset):
# Empty, {r14}, {r14,r13}, {r14,r24}, {r14,r13,r24},
# {r14,r13,r12}, {r14,r13,r23}, {r14,r24,r23}, {r14,r24,r34},
# {r14,r13,r24,r12}, {r14,r13,r24,r23}, {r14,r13,r24,r34},
# {r14,r13,r12,r23}, {r14,r24,r23,r34},
# {r14,r13,r24,r12,r23}, {r14,r13,r24,r23,r34}, {r14,r13,r24,r12,r34},
# {r14,r13,r12,r23,r34}... wait, need r24 if r34 is in.
# Actually r34 requires nothing above it except itself. Let me be more careful.

# The dual poset (reversing the order) has:
# r12, r23, r34 at the bottom (minimal elements in original = maximal in dual)
# Wait no. In the ORIGINAL poset, r14 is the maximum.
# Upper set in original poset = contains all elements above any element it contains.
# = if beta in S and alpha >= beta, then alpha in S.

# So: if r12 in S, then r13 in S (since r13 >= r12), hence r14 in S.
# If r23 in S, then r13 in S and r24 in S, hence r14 in S.
# If r34 in S, then r24 in S, hence r14 in S.
# If r13 in S, then r14 in S.
# If r24 in S, then r14 in S.

# Let me enumerate by size:
# Size 0: {} (empty)
# Size 1: {r14}
# Size 2: {r14,r13}, {r14,r24}
# Size 3: {r14,r13,r24}, {r14,r13,r12}, {r14,r24,r34}
#   Note: {r14,r13,r23} -- r23 requires r13 AND r24 to be above it.
#   Wait: r13 >= r23 and r24 >= r23, so if r23 is in S, both r13 and r24
#   must be in S. So {r14,r13,r23} is NOT an upper set (missing r24).
#   Correction: {r14,r13,r24,r23} is valid for size 4.
# Size 3 (revised): {r14,r13,r24}, {r14,r13,r12}, {r14,r24,r34}
# Size 4: {r14,r13,r24,r12}, {r14,r13,r24,r23}, {r14,r13,r24,r34},
#          {r14,r13,r12,r24}... wait that's the same as {r14,r13,r24,r12}.
#   Also: {r14,r24,r34,r13}... = {r14,r13,r24,r34}.
#   What about {r14,r13,r12,r24}? Same as above.
#   Can we have {r14,r13,r12,r34}? r34 requires r24, not present. NO.
# Size 4: {r14,r13,r24,r12}, {r14,r13,r24,r23}, {r14,r13,r24,r34}
# Size 5: {r14,r13,r24,r12,r23}, {r14,r13,r24,r12,r34},
#          {r14,r13,r24,r23,r34}
# Size 6: {r14,r13,r24,r12,r23,r34} = all positive roots

# Let me verify computationally
from itertools import combinations

roots = ['r12', 'r13', 'r14', 'r23', 'r24', 'r34']
# Covering relations: (alpha, beta) means alpha >= beta
covers = {
    'r14': ['r13', 'r24'],
    'r13': ['r12', 'r23'],
    'r24': ['r23', 'r34'],
    'r12': [],
    'r23': [],
    'r34': []
}

# Build full partial order (transitive closure)
above = {}
for r in roots:
    above[r] = set()
def build_above(r):
    if above[r]:
        return above[r]
    for c in covers[r]:
        build_above(c)
    for c in covers[r]:
        above[r].add(c)
        above[r] |= above[c]
    return above[r]
for r in roots:
    build_above(r)

# above[r] = set of roots strictly below r
# For upper set: if beta in S, then everything above beta must be in S.
# "above" in our poset sense: alpha >= beta means alpha is higher.
# So: if beta in S, then all alpha with alpha >= beta must be in S.
# Equivalently: all alpha such that beta in above[alpha] must be in S.
# Actually let me rebuild: "parents" of beta = roots alpha such that alpha >= beta.

parents = {}
for r in roots:
    parents[r] = set()
for r in roots:
    for c in above[r]:
        parents[c].add(r)

# Upper set: if beta in S, then all parents of beta must be in S.
upper_sets_by_size = {}
for sz in range(0, 7):
    upper_sets_by_size[sz] = []
    for combo in combinations(roots, sz):
        S = set(combo)
        valid = True
        for beta in S:
            for p in parents[beta]:
                if p not in S:
                    valid = False
                    break
            if not valid:
                break
        if valid:
            upper_sets_by_size[sz].append(S)

print("Upper sets of positive root poset of sl_4:")
total_upper = 0
for sz in range(0, 7):
    count = len(upper_sets_by_size[sz])
    total_upper += count
    print("  size %d: %d upper sets" % (sz, count))
    for S in upper_sets_by_size[sz]:
        print("    %s" % sorted(S))
print("  Total upper sets: %d" % total_upper)

print()
print("=" * 60)
print("B_V-FIXED SUBSPACES OF sl_4 BY DIMENSION")
print("=" * 60)
print()
print("A B_V-fixed j-dim subspace of sl_4 is determined by:")
print("  1. An upper set U of positive roots (gives the 'above-zero' part)")
print("  2. A subspace of the 3-dim Cartan (if j > |U|)")
print("  3. A 'lower set' of negative roots (if j > |U| + Cartan contribution)")
print()
print("For the apolarity computation, we need dim(E_110') = 13.")
print("Each site (s,t) in the 4x4 grid contributes some inner dim j_st.")
print("Sum of all j_st = 13.")
print()

# Now the key: at each grid point (s,t), if the inner structure includes
# Cartan (weight zero) vectors, we get Gr(k, 3) parameters.
# The question: for a typical outer structure filling 13 slots in 4x4,
# how many sites touch weight zero?

# Critical: to touch weight zero, the inner dim j at that site must be
# >= 7 (= 6 positive roots + 1 Cartan). At that point we have Gr(1,3) = P^2.
# But wait: we need to fill 13 total across all sites.
# If one site has j >= 7, the remaining sites share at most 13 - 7 = 6.
# If two sites have j >= 7, remaining share at most 13 - 14 < 0. Impossible.

# So at MOST ONE site can touch weight zero.

# But actually the inner structure need not go through all positive roots
# sequentially. The inner dim at a site can include a "mixed" selection.
# Let me reconsider.
#
# At a site (s,t), the fiber is sl_4. A B_V-fixed subspace of sl_4 must
# be a B_V-fixed subspace. The B_V-fixed subspaces of sl_4 are described
# by upper sets of the FULL weight poset (positive roots, zero, negative roots).
# Actually, more precisely: a B-fixed k-plane in sl_4 corresponds to a
# highest weight line in Lambda^k(sl_4). The weight zero space of sl_4 is
# the Cartan, and choosing a k-plane in the Cartan gives a Gr(k,3) family.
#
# However, a B_V-fixed subspace of sl_4 of dim j is an upper set of the
# root poset EXTENDED to include choices from the Cartan and negative roots.
# The Cartan vectors are at weight 0, and the partial order has them
# incomparable to each other but below all positive roots and above all
# negative roots.

# So a B_V-fixed j-dimensional subspace decomposes as:
# j = |positive roots chosen| + |Cartan vectors chosen| + |negative roots chosen|
# with: positive chosen = an upper set of positive root poset
#        Cartan chosen = any k-dimensional subspace of C^3 (k can be 0,...,3)
#        negative chosen = a lower set (= complement of upper set of negative root poset)
# AND: if any Cartan vector is chosen, ALL positive roots must be chosen
#        if any negative root is chosen, ALL Cartan must be chosen (k = 3)
# (because positive roots have strictly higher weight than Cartan, and
#  Cartan has strictly higher weight than negative roots)
#
# Wait, this is too strict. A B-fixed subspace is a subspace stabilized by
# the Borel. Since the Borel acts on sl(V) by the adjoint representation,
# a B-fixed subspace must be an "upper set" in the sense that it is closed
# under the raising operators. But raising operators map lower-weight vectors
# to higher-weight vectors. So a B-fixed subspace W satisfies:
# if w in W and u is a raising operator, then u.w in W (if nonzero).
#
# For a B-fixed subspace to contain a negative root e_j - e_i (j > i),
# acting by the raising operator taking e_j to e_i would give a Cartan
# element, which must be in the subspace. So negative roots force Cartan.
# And acting on a Cartan element by a raising operator gives... nothing
# in the adjoint representation (since [h, e_alpha] = alpha(h) e_alpha,
# this maps Cartan to root spaces, not the other way). Actually,
# the action of raising operators e_{ij} (i<j) on sl_4 by [e_{ij}, -]:
# [e_{ij}, e_{kl}] = delta_{jk} e_{il} - delta_{il} e_{kj}
# So e_{12} acting on e_{21} (a negative root) gives [e_{12}, e_{21}] = h_1 - h_2
# (a Cartan element). So including e_{21} forces h_1 - h_2 to be in the subspace.
#
# Including Cartan elements: [e_{12}, h] = -alpha_1(h) e_{12} for h in Cartan.
# This is a positive root, which is already "above" Cartan. So having Cartan
# elements does NOT force positive roots to be in the subspace. Wait --
# the RAISING operator e_{12} acts on h as [e_{12}, h] = -alpha_1(h) e_{12}.
# For this to be zero, we need alpha_1(h) = 0.
# So if h is in the subspace and alpha_1(h) != 0, then e_{12} is forced to
# be in the subspace (since [e_{12}, h] is proportional to e_{12}).
# BUT [e_{12}, h] is a POSITIVE root space vector, and we said the subspace
# is closed under RAISING operators. The raising operator maps h -> e_{12}.
# So e_{12} must be in the subspace. More generally: if h is in the subspace
# and alpha(h) != 0 for some positive root alpha, then the root space for alpha
# is forced. But if h is in ker(alpha), then no forcing for that root.

# Hmm, this is getting subtle. Let me think about it differently.
# A B-fixed subspace is a submodule of the adjoint representation as a B-module.
# The adjoint representation of sl_n decomposes into weight spaces.
# A B-submodule is a span of weight spaces that is closed under the Borel action.

# The key issue: the Cartan subalgebra (weight 0) is NOT irreducible under B.
# In fact, B acts on the Cartan trivially (the torus T normalizes h, and the
# upper-triangular part acts by 0 on h since [e_{ij}, h] is a root space vector
# and h_k -> [e_{ij}, h_k] has weight alpha_{ij} != 0).

# Wait, I need to be more careful. In the adjoint representation of sl_n:
# B = T x U (upper triangular = torus times unipotent upper triangular)
# T acts on weight spaces by the weight character
# U (raising operators) map: if f_alpha is a root vector of weight alpha,
# then e_beta . f_alpha = [e_beta, f_alpha] which is:
#   - a root vector of weight alpha + beta if alpha + beta is a root
#   - a Cartan element if alpha + beta = 0 (i.e., alpha = -beta)
#   - 0 otherwise

# For a B-fixed subspace W:
# If f_{-alpha} in W (negative root), then e_alpha . f_{-alpha} = [e_alpha, f_{-alpha}]
# = h_alpha (Cartan element), which must be in W.
# If h in W (Cartan), then e_alpha . h = [e_alpha, h] = -alpha(h) e_alpha.
# If alpha(h) != 0, then e_alpha must be in W.

# So: Cartan elements FORCE positive root spaces!
# Specifically, if h is in the subspace, then for every positive root alpha
# with alpha(h) != 0, the root space for alpha is forced.

# This means: to have a B-fixed subspace containing a Cartan vector h,
# we need all positive root spaces alpha where alpha(h) != 0 to also be in W.

# For sl_4, the simple roots are alpha_1, alpha_2, alpha_3.
# A Cartan element h can be written as c_1 h_1 + c_2 h_2 + c_3 h_3
# where h_i = e_{ii} - e_{i+1,i+1} (the coroots).
# alpha_1(h) = c_1, alpha_2(h) = c_2, alpha_3(h) = c_3,
# (alpha_1+alpha_2)(h) = c_1 + c_2, (alpha_2+alpha_3)(h) = c_2 + c_3,
# (alpha_1+alpha_2+alpha_3)(h) = c_1 + c_2 + c_3.

# For a GENERIC h (all alpha(h) != 0), ALL positive root spaces are forced.
# For h in ker(alpha_i) (some i), fewer are forced.

# Actually, for the B-fixed subspaces of sl_n, the correct picture is:
# A B-fixed subspace is a sum of certain root spaces plus a subspace of
# the Cartan, where the root spaces included must be an upper set (closed
# under raising), AND the Cartan subspace must be in the intersection of
# kernels of all positive roots whose root spaces are NOT included.

# That's the precise condition:
# Choose an upper set S of positive roots.
# Choose a lower set L of negative roots (upper set in the reversed order).
# Choose a subspace H of Cartan such that H <= intersection of ker(alpha)
#   for all positive roots alpha NOT in S.
# AND: for each negative root -alpha in L, the Cartan element h_alpha must
#   be in H (forced by raising).
# These constraints determine the possible B-fixed subspaces.

# For sl_4, the Cartan is 3-dimensional.
# The positive roots give 6 linear functionals on the Cartan.
# If S = all 6 positive roots, then H can be any subspace of the 3-dim Cartan.
# If S is missing some positive root alpha, then H <= ker(alpha).

# KEY CALCULATION: Given S (upper set of positive roots), what is
# dim(intersection of ker(alpha) for alpha not in S)?

print("For each upper set S of positive roots of sl_4,")
print("compute dim(Cartan subspace consistent with S):")
print()

# The Cartan of sl_4 is 3-dimensional, spanned by h_1, h_2, h_3.
# Positive roots and their values on (h_1, h_2, h_3):
# alpha_1 = e_1 - e_2:    (2, -1, 0)  [Cartan matrix row 1]
# alpha_2 = e_2 - e_3:    (-1, 2, -1)
# alpha_3 = e_3 - e_4:    (0, -1, 2)
# alpha_1 + alpha_2:      (1, 1, -1)
# alpha_2 + alpha_3:      (-1, 1, 1)
# alpha_1+alpha_2+alpha_3:(1, 0, 1)

root_vals = {
    'r12': (2, -1, 0),     # alpha_1
    'r23': (-1, 2, -1),    # alpha_2
    'r34': (0, -1, 2),     # alpha_3
    'r13': (1, 1, -1),     # alpha_1 + alpha_2
    'r24': (-1, 1, 1),     # alpha_2 + alpha_3
    'r14': (1, 0, 1)       # alpha_1 + alpha_2 + alpha_3
}

for sz in range(7):
    for S in upper_sets_by_size[sz]:
        # Roots NOT in S
        missing = [r for r in roots if r not in S]
        if not missing:
            cartan_dim = 3  # No constraints
        else:
            # Build the constraint matrix: rows are root_vals for missing roots
            M = matrix(QQ, [[root_vals[r][i] for i in range(3)] for r in missing])
            cartan_dim = 3 - M.rank()

        # Total dimension of B-fixed subspace:
        # |S| positive roots + cartan_dim Cartan choices + possible negative roots
        # (For now, just count the parameter dimension at this level)
        #
        # If cartan_dim > 0, we get Gr(k, cartan_dim) parameters for k = 1,...,cartan_dim
        # when we include k Cartan vectors.
        #
        # Total dim j = |S| + k (Cartan) + |negative roots chosen|
        # Negative roots chosen = lower set of negative root poset, consistent with
        # forcing from Cartan.

        if sz <= 6 and cartan_dim > 0 and sz > 0:  # Only print interesting cases
            param_max = (cartan_dim)^2 // 4 if cartan_dim > 1 else 0
            print("  S = %s (|S|=%d): Cartan freedom = %d" % (
                sorted(S), sz, cartan_dim))
            if cartan_dim > 1:
                print("    -> Gr(k,%d) parameter family, max dim = %d" % (
                    cartan_dim, param_max))

print()
print("CRITICAL: Inner dim j that reaches weight zero and its parameters:")
print()

# For each upper set S of all 6 positive roots:
S_full = set(roots)
# cartan_dim = 3 (no constraints)
# j = 6 + k where k = 1,...,3 (Cartan vectors chosen)
# k=1: j=7, Gr(1,3)=P^2, param dim = 2
# k=2: j=8, Gr(2,3)=P^2, param dim = 2
# k=3: j=9, Gr(3,3)=point, param dim = 0

for k in range(1, 4):
    j = 6 + k
    param = k * (3 - k)
    print("  j=%d (all pos roots + %d Cartan): Gr(%d,3), param dim = %d" % (j, k, k, param))

print()
print("=" * 60)
print("THE DECISIVE NUMBER FOR M_4")
print("=" * 60)
print()
print("dim(E_110') = 13 must be distributed across the 4x4 outer grid.")
print("At each site (s,t), the inner structure has dim j_{s,t}.")
print("Sum of j_{s,t} = 13.")
print()
print("Weight zero is touched at site (s,t) iff j_{s,t} >= 7")
print("(need all 6 positive roots + at least 1 Cartan vector).")
print()
print("Maximum number of sites touching weight zero with sum 13:")
print("  If 1 site has j >= 7: remaining sum <= 13 - 7 = 6. Possible.")
print("  If 2 sites have j >= 7: remaining sum <= 13 - 14 < 0. Impossible.")
print()
print("So AT MOST 1 site touches weight zero.")
print("If exactly 1 site has j = 7: Gr(1,3) = P^2, 2 parameters.")
print("If exactly 1 site has j = 8: Gr(2,3) = P^2, 2 parameters.")
print("If exactly 1 site has j = 9: Gr(3,3) = point, 0 parameters.")
print("If exactly 1 site has j = 10: 9 + lower set. Need all Cartan (j=9)")
print("   then 1 negative root. But we need sum = 13, leaving 3 for others.")
print()
print("HOWEVER: there is additional parametrization from non-full upper sets")
print("that happen to land in ker(alpha) for the missing roots.")
print("These give PARTIAL Cartan freedom even below j=7.")
print()

# Check which non-full upper sets allow Cartan freedom
print("Non-full upper sets with Cartan freedom > 0:")
for sz in range(7):
    for S in upper_sets_by_size[sz]:
        missing = [r for r in roots if r not in S]
        if not missing:
            continue
        M = matrix(QQ, [[root_vals[r][i] for i in range(3)] for r in missing])
        cartan_dim = 3 - M.rank()
        if cartan_dim > 0:
            print("  S = %s (|S|=%d): Cartan freedom = %d" % (
                sorted(S), sz, cartan_dim))
            # What's the kernel?
            K = M.right_kernel()
            print("    ker = %s" % K.basis())
