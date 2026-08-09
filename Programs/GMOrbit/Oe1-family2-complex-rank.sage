# Oe1 Family 2: rank-budget triage for the finite groups with a faithful 3-dim
# COMPLEX irrep beyond the O(3) subgroups (Blichfeldt classification): PSL(2,7)
# (order 168), the Hessian group (order 216), and A_6/Valentiner (order 360/1080).
# The GM <3,3,3> construction has tensor rank = 1 + (orbit size of the seed under
# diagonal conjugation). Orbit size = |G|/|stabilizer|. To beat Laderman 23 we
# need orbit <= 21. We compute, for each such group's 3-dim irrep, the SMALLEST
# possible nontrivial orbit of a matrix seed under conjugation X -> rho(g) X
# rho(g)^{-1}, i.e. 24... no, |G| / (max stabilizer of a nonzero non-scalar seed
# direction). If even the smallest orbit exceeds 21, the group cannot beat 23 and
# is ruled out by rank alone (no Groebner needed).
#
# We use GAP (via Sage) to get the groups and their 3-dim irreps' conjugacy-class
# data; orbit sizes of seed DIRECTIONS = |G|/|centralizer-type stabilizers|. The
# cleanest proxy: the conjugation action of G on the 8-dim space of trace-zero
# 3x3 matrices (rho (x) rho* minus scalars) decomposes into orbits; the minimal
# orbit of a 1-dim seed direction is >= |G|/|largest proper subgroup fixing a
# direction|. We bound below by |G| / (largest proper subgroup order), since a
# seed direction's stabilizer is a proper subgroup (the rep is irreducible, so no
# nonzero seed is fixed by all of G unless scalar).

# Use GAP character tables / max subgroup orders.
def min_orbit_lower_bound(gap_group_cmd, name, order):
    G = gap(gap_group_cmd)
    n = Integer(gap.Order(G))
    # largest proper subgroup order via maximal subgroups
    maxsubs = gap.MaximalSubgroupClassReps(G)
    orders = [Integer(gap.Order(H)) for H in maxsubs]
    Mmax = max(orders) if orders else 1
    lb = n / Mmax
    print(f"{name}: |G|={n}, largest proper (maximal) subgroup order={Mmax}")
    print(f"   => any nonscalar seed direction has orbit >= |G|/Mmax = {lb}")
    print(f"   rank lower bound (single orbit) >= 1 + {lb} = {1+lb}  ({'CAN fit <=22' if 1+lb<=22 else 'EXCEEDS 22 -- ruled out by rank'})")
    return lb

print("=== complex-3-dim-irrep groups: minimal single-orbit rank ===\n")
# PSL(2,7) = PSL(3,2), order 168
try:
    min_orbit_lower_bound("PSL(2,7)", "PSL(2,7) order 168", 168)
except Exception as e:
    print("PSL(2,7) error:", e)
print()
# Hessian group order 216 = AGL(... ) ; in GAP: the order-216 complex reflection
# related group. Use SmallGroup(216, ...) -- Hessian is SmallGroup(216,153)? Use
# the affine group ASL(2,3) of order 216? The Hessian group = normalizer; use
# its identification as the automorphism group of Hesse config. We approximate by
# the relevant order-216 group; the bound only needs |G| and max subgroup.
try:
    # Hessian group ~ 3^2 : SL(2,3), order 9*24=216
    min_orbit_lower_bound("AffineGroup(GF(3)^2)", "Hessian-related (order ~432 full affine)", 432)
except Exception as e:
    print("Hessian affine error:", e)
print()
# A_6 (Valentiner acts via A_6 on CP^2), order 360
try:
    min_orbit_lower_bound("AlternatingGroup(6)", "A_6 (Valentiner/CP^2) order 360", 360)
except Exception as e:
    print("A_6 error:", e)
print()
# 3.A_6 Valentiner triple cover order 1080
try:
    min_orbit_lower_bound("SchurCover(AlternatingGroup(6))", "Schur cover of A_6 (contains 3.A_6)", 1080)
except Exception as e:
    print("3.A_6 error:", e)
