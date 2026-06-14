# Bp1: Compute (210)/(120) kernel contribution bounds for sl_4.
#
# CHL's Lemma 5.3 (sl_2) and Lemma 5.7 (sl_3) give coefficients a_j, b_j
# such that the kernel contribution at site (s,t) with inner dim j is a_j*s + b_j.
# These feed Lemma 5.2 to bound the minimum kernel across (210) and (120) maps.
#
# For sl_4, we need the analogous computation using Proposition 5.4:
#
# The kernel contribution is determined by (CHL eq. 5.10):
# a = dim[(V tensor X) cap V_{2w1+w3}] + dim[(V tensor X) cap V_{w2+w3}]
# b = n * dim[(V tensor X) cap V_w1] - dim[(V tensor X) cap V_{w2+w3}]
#
# where V = C^4, n = dim U = dim W = 4.
# V_{2w1+w3} has dim 36
# V_{w2+w3} has dim 20
# V_w1 = V has dim 4
#
# X ranges over B_V-fixed subspaces of sl_4 of dimension j.
# We want the MAXIMUM a_j*s + b_j = max_a * s + max_b for the worst case.
# This feeds the optimization bound.
#
# Let me compute these by decomposing V tensor sl_4 into irreducible components.

print("Computing V tensor sl(V) decomposition for V = C^4")
print()

# V = standard rep of sl_4, weight (1,0,0)
# sl(V) = adjoint rep, weight (1,0,1) (= highest root)
# V tensor sl(V) decomposes as:
# (1,0,0) tensor (1,0,1) = sum of irreps determined by Clebsch-Gordan

# Using SageMath's representation theory
# sl_4 = Lie algebra of type A_3
W = WeylCharacterRing('A3', style='coroots')
V_fund = W(1,0,0)      # fundamental rep V
adj = W(1,0,1)          # adjoint rep
VtslV = V_fund * adj    # tensor product

print("V tensor sl(V) = %s" % VtslV)
print()

# Expected from CHL equation (6.5):
# V tensor sl(V) = V_{2w1+w_{v-1}} + V_{w2+w_{v-1}} + V_w1
# For v=4: V_{2w1+w3} + V_{w2+w3} + V_w1
# In coroot notation: (2,0,1) + (0,1,1) + (1,0,0)

V_2w1w3 = W(2,0,1)
V_w2w3 = W(0,1,1)
V_w1 = W(1,0,0)

print("Expected decomposition:")
print("  V_{2w1+w3} = %s, dim = %d" % (V_2w1w3, V_2w1w3.degree()))
print("  V_{w2+w3}  = %s, dim = %d" % (V_w2w3, V_w2w3.degree()))
print("  V_{w1}     = %s, dim = %d" % (V_w1, V_w1.degree()))
print("  Sum of dims = %d" % (V_2w1w3.degree() + V_w2w3.degree() + V_w1.degree()))
print("  dim(V tensor sl(V)) = %d" % VtslV.degree())
print()

# Verify decomposition
check = V_2w1w3 + V_w2w3 + V_w1
print("Decomposition check: V tensor sl(V) == V_{2w1+w3} + V_{w2+w3} + V_w1: %s" % (VtslV == check))
print()

# Now for each B_V-fixed subspace X of sl_4 of dimension j,
# compute dim[(V tensor X) cap V_{2w1+w3}], dim[(V tensor X) cap V_{w2+w3}],
# and dim[(V tensor X) cap V_w1].
#
# We need to work with the weight space decomposition explicitly.

# The adjoint rep of sl_4 has weights:
# Positive roots: e1-e2 = (2,-1,0), e1-e3 = (1,1,-1), e1-e4 = (1,0,1),
#                 e2-e3 = (-1,2,-1), e2-e4 = (-1,1,1), e3-e4 = (0,-1,2)
# Zero weights (Cartan): 3-dimensional, weight (0,0,0) with mult 3
# Negative roots: -(each positive root)

# Each weight space of V tensor sl_4 is V_wt(v_i) + wt(e_alpha)
# We need to decompose the weight spaces of V tensor X into their
# projections onto V_{2w1+w3}, V_{w2+w3}, V_w1.

# This is a concrete computation. Let me work with the weight multiplicities.

# Weight multiplicities of each irrep:
print("Weight multiplicities of V_{2w1+w3}:")
for wt, mult in V_2w1w3.weight_multiplicities().items():
    print("  %s: %d" % (wt, mult))

print()
print("Weight multiplicities of V_{w2+w3}:")
for wt, mult in V_w2w3.weight_multiplicities().items():
    print("  %s: %d" % (wt, mult))

print()
print("Weight multiplicities of V_{w1}:")
for wt, mult in V_w1.weight_multiplicities().items():
    print("  %s: %d" % (wt, mult))
