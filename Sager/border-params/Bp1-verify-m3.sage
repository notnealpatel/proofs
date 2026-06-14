# Bp1: Verify the a_j, b_j + Lemma 5.2 computation against CHL's M_3 result.
#
# CHL Lemma 5.7 gives a_j, b_j for sl_3 (j=1,...,8).
# CHL's published values:
# j=1: a=1, b=0
# j=2: a=4, b=-1
# j=3: a=10, b=-4
# j=4: a=11, b=-4
# j=5: a=15, b=n-4
# j=6: a=20, b=n-6
# j=7: a=21, b=2n-6
# j=8: a=21, b=3n-6
#
# Let me compute these using the same machinery as above.

W_ring = WeylCharacterRing('A2', style='coroots')
RS = RootSystem('A2')

V15 = W_ring(2,1)   # V_{2w1+w2} for sl_3, dim should be 15
V6 = W_ring(0,2)    # V_{w2+w2} = V_{2w2} for sl_3, dim should be 6
V3 = W_ring(1,0)    # V_{w1}, dim 3

print("sl_3 decomposition check:")
print("  V_{2w1+w2} dim = %d (should be 15)" % V15.degree())
print("  V_{2w2} dim = %d (should be 6)" % V6.degree())
print("  V_w1 dim = %d (should be 3)" % V3.degree())
print()

wm15 = V15.weight_multiplicities()
wm6 = V6.weight_multiplicities()
wm3 = V3.weight_multiplicities()

def make_lookup(wm):
    lookup = {}
    for wt, mult in wm.items():
        coords = tuple(QQ(wt[i]) for i in range(3))
        lookup[coords] = lookup.get(coords, 0) + mult
    return lookup

l15 = make_lookup(wm15)
l6 = make_lookup(wm6)
l3 = make_lookup(wm3)

# V = C^3 standard weights in A2 epsilon coords:
# e_1 = (2/3, -1/3, -1/3)
# e_2 = (-1/3, 2/3, -1/3)
# e_3 = (-1/3, -1/3, 2/3)
V_wts_3 = [
    (QQ(2)/3, QQ(-1)/3, QQ(-1)/3),
    (QQ(-1)/3, QQ(2)/3, QQ(-1)/3),
    (QQ(-1)/3, QQ(-1)/3, QQ(2)/3),
]

# sl_3 root weights:
adj3_wts = {
    'e1-e3': (QQ(1), QQ(0), QQ(-1)),    # highest root
    'e1-e2': (QQ(1), QQ(-1), QQ(0)),     # simple root alpha_1
    'e2-e3': (QQ(0), QQ(1), QQ(-1)),     # simple root alpha_2
    'h':     (QQ(0), QQ(0), QQ(0)),      # Cartan (mult 2)
    'e2-e1': (QQ(-1), QQ(1), QQ(0)),
    'e3-e2': (QQ(0), QQ(-1), QQ(1)),
    'e3-e1': (QQ(-1), QQ(0), QQ(1)),     # lowest root
}

def wt_add(a, b):
    return tuple(a[i] + b[i] for i in range(len(a)))

# sl_3 weight diagram levels:
levels_3 = [
    [('e1-e3', 1)],                      # height 2 (highest root)
    [('e1-e2', 1), ('e2-e3', 1)],        # height 1
    [('h', 2)],                           # Cartan
    [('e2-e1', 1), ('e3-e2', 1)],        # height -1
    [('e3-e1', 1)],                       # height -2
]

from collections import Counter

def compute_proj(weight_list, l15, l6, l3):
    wt_counts = Counter(weight_list)
    d15 = sum(min(cnt, l15.get(wt, 0)) for wt, cnt in wt_counts.items())
    d6 = sum(min(cnt, l6.get(wt, 0)) for wt, cnt in wt_counts.items())
    d3 = sum(min(cnt, l3.get(wt, 0)) for wt, cnt in wt_counts.items())
    return d15, d6, d3

j = 0
all_vx_wts = []
n = 3  # dim U = dim W for M_3

print("sl_3 a_j, b_j computation:")
print("j  | root   | d15 d6 d3 | a   | b     | CHL a | CHL b")
print("-" * 65)

chl_a = [None, 1, 4, 10, 11, 15, 20, 21, 21]
chl_b = [None, 0, -1, -4, -4, n-4, n-6, 2*n-6, 3*n-6]

for level in levels_3:
    for root_label, mult in level:
        root_wt = adj3_wts[root_label]
        for m in range(mult):
            j += 1
            new_wts = [wt_add(v, root_wt) for v in V_wts_3]
            all_vx_wts.extend(new_wts)

            d15, d6, d3 = compute_proj(all_vx_wts, l15, l6, l3)
            a = d15 + d6
            b = n * d3 - d6

            label = root_label
            if mult > 1:
                label = "%s(%d)" % (root_label, m+1)

            chl_a_val = chl_a[j] if j < len(chl_a) else "?"
            chl_b_val = chl_b[j] if j < len(chl_b) else "?"

            match_a = "OK" if a == chl_a_val else "DIFF"
            match_b = "OK" if b == chl_b_val else "DIFF"

            print("%2d | %-6s | %3d %2d %2d | %3d | %5d | %5s %s | %5s %s" % (
                j, label, d15, d6, d3, a, b,
                chl_a_val, match_a, chl_b_val, match_b))

print()

# Now compute the Lemma 5.2 bound for M_3
rho_m3 = 7  # dim(E_110') for M_3 at r=16: 16 - 9 = 7
r_m3 = 16
n_m3 = 3

# Actually for CHL, they test at r = 16 to prove R >= 17.
# But the asymptotic formula (Theorem 1.4) uses different rho.
# Let me just compute the bound for M_3 at r=16.

print("Lemma 5.2 bound for M_3 at r=16, rho=7:")
print("j  | a | b | bound")
print("-" * 40)

j = 0
all_vx_wts = []
max_bound_m3 = 0

for level in levels_3:
    for root_label, mult in level:
        root_wt = adj3_wts[root_label]
        for m in range(mult):
            j += 1
            new_wts = [wt_add(v, root_wt) for v in V_wts_3]
            all_vx_wts.extend(new_wts)
            d15, d6, d3 = compute_proj(all_vx_wts, l15, l6, l3)
            a = d15 + d6
            b = n_m3 * d3 - d6
            bound = a * rho_m3^2 / (8 * j^2) + (a + b) * rho_m3 / j
            print("%2d | %3d | %3d | %.4f" % (j, a, b, float(bound)))
            if bound > max_bound_m3:
                max_bound_m3 = bound

print()
print("Max bound for M_3: %.4f" % float(max_bound_m3))
print("Target r: %d" % r_m3)
print()

# The Lemma 5.2 bound is an UPPER BOUND on the minimum kernel.
# It measures: for ANY outer structure, what is the MOST the smaller
# of (210)/(120) kernels can be?
# If this bound < r, then for ALL outer structures, at least one of
# (210)/(120) fails. But CHL found 8 candidates that pass BOTH tests!
# How?
#
# The answer: the bound from Lemma 5.2 is NOT tight for small n.
# For M_3, the bound (with CHL's exact a_j, b_j for j=3) gives:
# j=3: a=10, b=-4 -> 10*49/72 + 6*7/3 = 6.806 + 14 = 20.806
# This exceeds r=16, so the bound does NOT rule out all candidates.
# Some candidates can pass both (210) and (120) tests.
# Those candidates then go to the (111) test.
#
# For M_4:
# The question is: does the bound exceed r=29?
# If YES: there exist candidates passing both (210)/(120) tests.
# Those need case-by-case + (111) analysis. This is the parametric wall.
# If NO: all candidates fail, proving R(M_4) >= 30 from (210)/(120) alone.

print("=" * 60)
print("INTERPRETATION FOR M_4")
print("=" * 60)
print()
print("The Lemma 5.2 bound for M_4 gives a maximum of ~252 >> r = 29.")
print("This means the asymptotic/uniform bound is USELESS for M_4 at r=29.")
print("Some outer structures will have candidates passing both tests.")
print()
print("But this is EXPECTED -- it was the same for M_3!")
print("The bound ~20.8 > r=16 for M_3, yet CHL still proved R(M_3) >= 17")
print("by enumerating the finitely many candidates (8 seven-planes)")
print("and showing all 512 triples fail the (111) test.")
print()
print("The critical question for M_4 is not whether the ASYMPTOTIC bound")
print("rules out all candidates, but whether the ENUMERATION of candidates")
print("is computationally feasible.")
print()
print("That feasibility depends on:")
print("1. How many candidates pass (210)+(120)? (Was 8 for M_3)")
print("2. The parameter dimension of the families (was 1 = P^1 for M_3)")
print("3. The size of the symbolic Groebner computation (was tractable for M_3)")
