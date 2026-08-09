# Bp1: Compute total parameter count across all outer structures for M_4.
#
# The question: for dim(E_110') = 13 distributed across the 4x4 grid,
# what is the total parameter dimension of the family of B-fixed E_110'?
#
# At each site (s,t), inner dim j_st contributes parameters based on
# which upper set of positive roots is chosen and how many Cartan vectors.
#
# From the previous computation, the parametric configurations at a single site:
#
# j=0: no parameters (empty)
# j=1 to 6: upper sets of size j from positive roots.
#   Multiple discrete choices (the upper set), but ALSO:
#   some upper sets of size 3,4,5 allow 1 or 2 Cartan vectors,
#   giving parameters. However, this means j = |S| + k where k >= 1
#   is Cartan, so j > |S|.
#   Example: S = {r12,r13,r14} (size 3), Cartan freedom 1.
#   If we include 1 Cartan vector from ker: j = 3 + 1 = 4.
#   But we could also have an upper set of size 4 with no Cartan.
#   So at j=4, we have BOTH discrete choices (14 upper sets of size <= 4)
#   AND 1-parameter families from size-3 upper sets + 1 Cartan.

# Let me enumerate ALL possible B_V-fixed j-dim subspaces of sl_4
# and count parameters for each j.

from itertools import combinations

roots = ['r12', 'r13', 'r14', 'r23', 'r24', 'r34']
covers = {
    'r14': ['r13', 'r24'],
    'r13': ['r12', 'r23'],
    'r24': ['r23', 'r34'],
    'r12': [],
    'r23': [],
    'r34': []
}
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
parents = {}
for r in roots:
    parents[r] = set()
for r in roots:
    for c in above[r]:
        parents[c].add(r)

root_vals = {
    'r12': (2, -1, 0),
    'r23': (-1, 2, -1),
    'r34': (0, -1, 2),
    'r13': (1, 1, -1),
    'r24': (-1, 1, 1),
    'r14': (1, 0, 1)
}

upper_sets = []
for sz in range(7):
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
            upper_sets.append(S)

# For each upper set S, compute Cartan freedom
def cartan_freedom(S):
    missing = [r for r in roots if r not in S]
    if not missing:
        return 3
    M = matrix(QQ, [[root_vals[r][i] for i in range(3)] for r in missing])
    return 3 - M.rank()

print("=" * 60)
print("PARAMETRIC B_V-FIXED SUBSPACES OF sl_4 BY INNER DIM j")
print("=" * 60)
print()

# For each j from 0 to 15, list the possible (upper_set, cartan_choice) pairs
# and the parameter dimension.
# j = |S| + k (Cartan) + l (negative roots from lower set)
# where k = 0,...,cartan_freedom(S)
# and l = lower set of negative root poset, subject to forcing from Cartan.
#
# For the (210)/(120) tests, we only need the inner structure up to the point
# of specifying E_110'. The negative roots don't appear in E_110' since
# E_110' lives in U* tensor sl(V) tensor W and the "inner structure" at (s,t)
# is just the choice of B_V-fixed subspace of sl(V).
#
# Actually, wait. E_110' DOES live in U* tensor sl(V) tensor W, and sl(V)
# is the FULL adjoint representation, not just the positive roots + Cartan.
# So the B_V-fixed subspace of sl(V) = sl_4 of dim j can include negative
# root spaces too. The parameter count depends on the full subspace choice.
#
# Let me now compute: for each inner dim j (0 to 15), what is the maximum
# parameter dimension of the family of B_V-fixed j-planes in sl_4?

# The negative root poset is the reverse of the positive root poset.
# B_V-fixed subspace of sl_4:
# Choose upper set S of positive roots (closed under raising)
# Choose k-dim subspace H of Cartan, with H in ker(alpha) for alpha not in S
# Choose lower set L of negative roots: if -alpha in L, then h_alpha in H.
#   (raising -alpha gives h_alpha, which must be in H)
# Also, L must be a "lower set" in the negative root poset:
#   if -alpha in L and -beta <= -alpha (i.e., beta >= alpha), then -beta in L.
#   Wait, the negative roots have the reversed partial order.
#   For negative roots, the "lower" ones are those with "more negative" weight.
#   The most negative is -(e_1 - e_4) = e_4 - e_1.
#   A B-fixed subspace containing e_4 - e_1 must contain everything above it
#   by the raising action... but the raising operators send negative roots to
#   other negative roots, then to Cartan, then to positive roots.
#
# Actually, let me think about this from the B_V-fixed definition directly.
# W subset sl_4 is B_V-fixed iff for all b in B_V, b.W = W (adjoint action).
# Equivalently (infinitesimally): for all e_alpha (positive root), [e_alpha, W] <= W.
# This means: W is a B_V-submodule of the adjoint representation.
#
# The B_V-submodules of sl_n are well-understood. They are exactly the
# "parabolic subalgebras" and their intersections with weight spaces.
# More precisely, they correspond to "standard" B-stable subspaces.
#
# For our purposes: a B_V-fixed j-plane in sl_4 is a B_V-submodule of dim j.
# The maximal ones are the parabolic subalgebras containing B_V.
# The minimal ones are the individual root lines.
#
# The parameter families arise from weight multiplicities, which for sl_4
# only occur at weight 0 (the Cartan). The analysis above about upper sets
# + Cartan + lower sets with forcing is correct.

# For the purpose of counting parameters, the crucial point is:
# Parameters arise ONLY from the choice of Cartan subspace H.
# The discrete choices (upper set S, lower set L) are finite and finite families.
# The continuous parameters are Gr(k, cartan_freedom(S)).

# Let me build a table: for each j, list (discrete_count, max_param_dim)

print("Inner dim j | Configurations | Max parameter dim | Notes")
print("-" * 75)

for j in range(16):
    configs = []  # list of (S, k, l_count, param_dim, description)
    for S in upper_sets:
        cf = cartan_freedom(S)
        s_size = len(S)
        # k = number of Cartan vectors chosen (0,...,min(cf, j - s_size))
        # l = number of negative roots chosen
        # j = s_size + k + l
        # l = j - s_size - k >= 0
        # Also need l <= 6 (at most 6 negative roots)
        for k in range(0, min(cf, j - s_size) + 1):
            l = j - s_size - k
            if l < 0 or l > 6:
                continue
            # Check: if l > 0, we need k = cf (all allowed Cartan forced)
            # Actually no: negative roots force specific Cartan elements, but
            # these might already be in the allowed subspace.
            # For a crude bound: any l with 0 <= l <= 6 is potentially possible
            # (the precise count depends on which negative roots are compatible).
            # The parameter dim is k * (cf - k) = dim Gr(k, cf).
            param_dim = k * (cf - k)
            configs.append((sorted(S), k, l, param_dim))

    if configs:
        max_pd = max(c[3] for c in configs)
        n_configs = len(configs)
        # How many have positive param dim?
        n_parametric = sum(1 for c in configs if c[3] > 0)
        notes = ""
        if n_parametric > 0:
            notes = "PARAMETRIC (%d families)" % n_parametric
        print("%11d | %14d | %17d | %s" % (j, n_configs, max_pd, notes))
    else:
        print("%11d | %14d | %17d |" % (j, 0, 0))

print()
print("=" * 60)
print("COMPARISON: M_3 vs M_4 PARAMETER LANDSCAPE")
print("=" * 60)
print()

# For M_3: dim(E') = 6 (at r=15, to prove r >= 16, actually r=16 for CHL)
# Wait, CHL prove R(M_3) >= 17 by testing at r = 16.
# dim(E_110') = r - n^2 = 16 - 9 = 7.
# In sl_3: positive roots = 3, Cartan dim = 2.
# Upper sets of positive roots of sl_3:
# sl_3 roots: alpha_1 (e1-e2), alpha_2 (e2-e3), alpha_1+alpha_2 (e1-e3)
# Poset: alpha_1+alpha_2 >= alpha_1, alpha_1+alpha_2 >= alpha_2
# Upper sets: {}, {alpha_1+alpha_2}, {alpha_1+alpha_2, alpha_1},
#   {alpha_1+alpha_2, alpha_2}, {alpha_1+alpha_2, alpha_1, alpha_2}
# That's 5 upper sets (sizes 0,1,2,2,3).

print("M_3: dim(E') = 7 in sl_3 (dim 8), 3x3 grid")
print("  sl_3 positive roots: 3, Cartan dim: 2")
print("  Inner dim j to touch weight zero: 4 (3 pos roots + 1 Cartan)")
print("  At j=4: Gr(1,2) = P^1, param dim = 1")
print("  At j=5: Gr(2,2) = point, param dim = 0")
print("  Sum = 7 across 3x3 grid:")
print("  - 1 site at j=4 + remaining 3 across others: 1 parameter")
print("  - Multiple sites touching weight zero: requires 4+4=8 > 7. Impossible.")
print("  => M_3 has at most 1 parametric dimension per outer structure.")
print("  => CHL report P^1 families. Confirmed.")
print()

print("M_4: dim(E') = 13 in sl_4 (dim 15), 4x4 grid")
print("  sl_4 positive roots: 6, Cartan dim: 3")
print("  Full-root weight zero at j=7: Gr(1,3) = P^2, param dim = 2")
print("  BUT also partial upper sets with Cartan freedom:")
print("  - S = {r12,r13,r14} (size 3): 1-dim Cartan, from j=4")
print("  - S = {r14,r24,r34} (size 3): 1-dim Cartan, from j=4")
print("  - S = {r12,r13,r14,r24} etc (size 4): 1-dim Cartan, from j=5")
print("  - S = 5 roots (3 ways): 2-dim Cartan, from j=6: Gr(1,2)=P^1, 1 param")
print()
print("  With dim(E') = 13 across 4x4 grid:")
print("  WORST CASE for parameters:")
print("  - 1 site at j=7 (2 params) + 6 remaining: 2 params total at that site")
print("  - 2 sites at j=4 each (1 param each) + 5 remaining: 2 params total")
print("  - 3 sites at j=4 each (1 param each) + 1 remaining: 3 params total!!")
print()
print("  HOWEVER: each parametric site contributes to the SYMBOLIC Groebner step.")
print("  The total parameter count = sum of parameter dimensions across all sites.")
print()

# Compute maximum total parameter dimension for dim(E')=13 on 4x4 grid
# This is the key measurement requested in the task card.

# For each site (s,t), inner dim j produces parameter dim p(j).
# p(j) = max over all B_V-fixed j-planes of Gr-parameter-dim.
# We want to maximize sum of p(j_{s,t}) subject to sum j_{s,t} = 13.

# From the table above, the max parameter dim per j:
max_param_by_j = {}
for j in range(16):
    mp = 0
    for S in upper_sets:
        cf = cartan_freedom(S)
        s_size = len(S)
        for k in range(0, min(cf, j - s_size) + 1):
            l = j - s_size - k
            if l < 0 or l > 6:
                continue
            pd = k * (cf - k)
            if pd > mp:
                mp = pd
    max_param_by_j[j] = mp

print("Max parameter dim per inner dim j:")
for j in range(16):
    print("  j=%2d: max param = %d" % (j, max_param_by_j[j]))
print()

# Now maximize total params across all sites with sum of j's = 13
# This is a simple optimization: greedily pick the j values with
# highest param-per-unit ratio.

# j=4 gives 1 param for 4 units
# j=5 gives 1 param for 5 units
# j=6 gives 1 param for 6 units
# j=7 gives 2 params for 7 units
# j=8 gives 2 params for 8 units
# j=9 gives 0 params for 9 units

# Best ratio: j=4 -> 1/4 = 0.25 param per unit
# j=7 -> 2/7 = 0.286 param per unit

# With budget 13:
# Option A: j=7 + 3 sites with j summing to 6 -> 2 params
# Option B: 3 sites at j=4 + 1 unit left -> 3 * 1 = 3 params!
#   But wait: j_remaining = 13 - 3*4 = 1. One site at j=1: 0 params. Total = 3.
# Option C: 2 sites at j=4 + budget 5 left -> 2 params + possible 1 more at j=5
#   = 2 + 1 = 3 params
# Actually wait, we need to check Option B more carefully.
# 3 sites at j=4: each uses S of size 3 with 1 Cartan freedom.
# But each such S requires a specific arrangement on the 4x4 grid.
# The outer structure sites are independent, so this should work.

print("=" * 60)
print("MAXIMUM TOTAL PARAMETER DIMENSION (THE DECISIVE NUMBER)")
print("=" * 60)
print()

# Brute force: try all partitions of 13 into at most 16 parts (0 to 15)
# and compute total parameter dim.
# Since each site contributes independently, this is a partition optimization.

from itertools import combinations_with_replacement

best_total = 0
best_partition = None

# We need partitions of 13 into at most 16 parts (each 0 to 15)
# This is equivalent to partitions of 13 with at most 16 parts.
# Use a recursive approach.

def maximize_params(remaining, max_parts, max_val=15):
    """Find partition of 'remaining' into at most max_parts parts (each 0..max_val)
    that maximizes sum of max_param_by_j[part]."""
    if remaining == 0 or max_parts == 0:
        return 0, []
    best = 0
    best_parts = []
    for j in range(min(remaining, max_val), 0, -1):
        p = max_param_by_j[j]
        sub_best, sub_parts = maximize_params(remaining - j, max_parts - 1, j)
        total = p + sub_best
        if total > best:
            best = total
            best_parts = [j] + sub_parts
    return best, best_parts

# This might be slow for large values. Let me use a DP approach instead.
# Actually with remaining=13 and max_parts=16, the recursion tree is manageable.

best_params, best_partition = maximize_params(13, 16)
print("Maximum total parameter dim for dim(E')=13:")
print("  Best total: %d parameters" % best_params)
print("  Best partition: %s" % best_partition)
print("  Verification: sum = %d" % sum(best_partition))
print()

# Also compute for M_3 (dim(E')=7, sl_3)
# For sl_3, quick manual check:
# j=0: 0, j=1: 0, j=2: 0, j=3: 0, j=4: 1, j=5: 0, j=6: 0, j=7: 0, j=8: 0
# Wait, for sl_3:
# Upper sets of positive roots: sizes 0,1,2,2,3 -> 5 upper sets
# Cartan freedom:
# S={}: missing all 3 roots. Matrix of (alpha_1, alpha_2, alpha_1+alpha_2) values.
#   For sl_3 Cartan is 2-dim with basis h_1, h_2.
#   alpha_1(h) = (2, -1), alpha_2(h) = (-1, 2), (alpha_1+alpha_2)(h) = (1, 1)
#   Matrix [[2,-1],[-1,2],[1,1]], rank = 2, kernel dim = 0.
# S={alpha_1+alpha_2}: missing alpha_1, alpha_2.
#   Matrix [[2,-1],[-1,2]], rank = 2, kernel dim = 0.
# S={alpha_1+alpha_2, alpha_1}: missing alpha_2.
#   Matrix [[-1,2]], rank = 1, kernel dim = 1.
# S={alpha_1+alpha_2, alpha_2}: missing alpha_1.
#   Matrix [[2,-1]], rank = 1, kernel dim = 1.
# S={alpha_1+alpha_2, alpha_1, alpha_2}: missing none. Cartan freedom = 2.

# So for sl_3, inner dim j parameter dims:
# j=1: S={alpha_1+alpha_2}, k=0 -> 0 params. Only choice.
# j=2: S has size 2, k=0 -> 0 params. Two choices.
# j=3: S=all, k=0 -> 0 params (all positive roots, no Cartan). 1 choice.
#   OR S has size 2, k=1 (Cartan freedom 1) -> j=2+1=3, param = 1*(1-1)=0. No.
#   Wait: Gr(1,1) = point, param dim = 0. So j=3 from size-2 upper set + 1 Cartan
#   gives 0 params. So j=3: 0 params.
# j=4: S=all (size 3), k=1 -> Gr(1,2), param = 1. 1 param.
#   OR S size 2 + k=1 (Cartan freedom 1) + l=1 negative root -> param 0.
#   Max is 1.
# j=5: S=all, k=2 -> Gr(2,2) = point, param = 0.
#   Max is 0.
# j=6,7,8: All include negative roots. S=all, k=2, l=j-5.
#   Params come from Cartan, which is already determined. 0 extra.

print("M_3 comparison:")
print("  dim(E')=7 on 3x3 grid (sl_3 dim 8)")
print("  j=4 gives 1 param (Gr(1,2)=P^1)")
print("  Max total: 1 site at j=4 + remaining 3 = 1 param total")
print("  (Cannot have 2 sites at j=4: 4+4=8 > 7)")
print("  => M_3 total parameter dim = 1")
print()

print("M_4 summary:")
print("  dim(E')=13 on 4x4 grid (sl_4 dim 15)")
print("  Maximum total parameter dim = %d" % best_params)
print("  This is the SYMBOLIC VARIABLE COUNT in the Groebner step.")
print()

# Now compute the Groebner complexity estimate
print("=" * 60)
print("GROEBNER COMPLEXITY ESTIMATE")
print("=" * 60)
print()
print("CHL's algorithm at the (210)/(120) tests:")
print("  When parameters are present, the rank test becomes:")
print("  'Find the locus in parameter space where a symbolic matrix drops rank.'")
print("  This is a SYMBOLIC determinantal computation.")
print()
print("For M_3 at r=16:")
print("  1 parameter (P^1)")
print("  (210) matrix: 144 x 405 (CHL line 974)")
print("  Symbolic rank computation in 1 variable: feasible")
print("  CHL used bespoke localization recursion (lines 1006-1021)")
print()
print("For M_4 at r=29:")
print("  %d parameters (worst case)" % best_params)
print("  (210) dual matrix: 464 x 1920")
print("  Symbolic rank computation in %d variables:" % best_params)
if best_params <= 2:
    print("  Challenging but potentially feasible with elimination theory")
elif best_params <= 3:
    print("  VERY challenging. Groebner basis in 3 variables over matrices")
    print("  of size ~500 x ~2000 is likely intractable without bespoke methods.")
else:
    print("  Almost certainly intractable.")
