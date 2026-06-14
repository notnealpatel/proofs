# Bp1: Corrected kernel dimension computation for sl_4.
# Fix: use SageMath's own weight objects for lookups.

W_ring = WeylCharacterRing('A3', style='coroots')
RS = RootSystem('A3')
ambient = RS.ambient_space()

V36 = W_ring(2,0,1)  # V_{2w1+w3}, dim 36
V20 = W_ring(0,1,1)  # V_{w2+w3}, dim 20
V4 = W_ring(1,0,0)   # V_{w1}, dim 4

wm36 = V36.weight_multiplicities()
wm20 = V20.weight_multiplicities()
wm4 = V4.weight_multiplicities()

# Build lookup with frozen tuples from actual coordinates
def make_lookup(wm):
    lookup = {}
    for wt, mult in wm.items():
        # Extract coordinates as a tuple of rationals
        coords = tuple(QQ(wt[i]) for i in range(4))
        lookup[coords] = lookup.get(coords, 0) + mult
    return lookup

l36 = make_lookup(wm36)
l20 = make_lookup(wm20)
l4 = make_lookup(wm4)

# V standard weights in epsilon coordinates (sum = 0 for A3):
# e_1 = (3/4, -1/4, -1/4, -1/4)
# e_2 = (-1/4, 3/4, -1/4, -1/4)
# e_3 = (-1/4, -1/4, 3/4, -1/4)
# e_4 = (-1/4, -1/4, -1/4, 3/4)
V_wts = [
    (QQ(3)/4, QQ(-1)/4, QQ(-1)/4, QQ(-1)/4),
    (QQ(-1)/4, QQ(3)/4, QQ(-1)/4, QQ(-1)/4),
    (QQ(-1)/4, QQ(-1)/4, QQ(3)/4, QQ(-1)/4),
    (QQ(-1)/4, QQ(-1)/4, QQ(-1)/4, QQ(3)/4),
]

# sl_4 root weights in epsilon coordinates:
# e_i - e_j has epsilon weight with 1 at position i, -1 at position j, 0 elsewhere
# But we need sum=0 convention? No, e_i - e_j already has sum 0.
# In the ambient space of A3, e_i has coordinates where the i-th entry is 1
# and others are 0, MINUS the average (to make sum=0).
# Actually, for A3 the ambient space has vectors summing to 0.
# e_1 - e_2 = (1, -1, 0, 0) in standard epsilon basis
# But in the sum=0 convention: (1, -1, 0, 0) already sums to 0. Good.

adj_wts = {
    'e1-e4': (QQ(1), QQ(0), QQ(0), QQ(-1)),
    'e1-e3': (QQ(1), QQ(0), QQ(-1), QQ(0)),
    'e2-e4': (QQ(0), QQ(1), QQ(0), QQ(-1)),
    'e1-e2': (QQ(1), QQ(-1), QQ(0), QQ(0)),
    'e2-e3': (QQ(0), QQ(1), QQ(-1), QQ(0)),
    'e3-e4': (QQ(0), QQ(0), QQ(1), QQ(-1)),
    'h':     (QQ(0), QQ(0), QQ(0), QQ(0)),  # Cartan (mult 3)
    'e2-e1': (QQ(-1), QQ(1), QQ(0), QQ(0)),
    'e3-e2': (QQ(0), QQ(-1), QQ(1), QQ(0)),
    'e4-e3': (QQ(0), QQ(0), QQ(-1), QQ(1)),
    'e3-e1': (QQ(-1), QQ(0), QQ(1), QQ(0)),
    'e4-e2': (QQ(0), QQ(-1), QQ(0), QQ(1)),
    'e4-e1': (QQ(-1), QQ(0), QQ(0), QQ(1)),
}

def wt_add(a, b):
    return tuple(a[i] + b[i] for i in range(4))

# Test: v_1 + (e1-e4) should be (3/4+1, -1/4, -1/4, -1/4-1) = (7/4, -1/4, -1/4, -5/4)
test = wt_add(V_wts[0], adj_wts['e1-e4'])
print("Test: v1 + (e1-e4) = %s" % (test,))
print("  In l36? %s (should be True, mult 1)" % (test in l36,))
print("  In l20? %s" % (test in l20,))
print("  In l4?  %s" % (test in l4,))
print()

# Now compute the projection dimensions for each root
levels = [
    [('e1-e4', 1)],                                    # height 3
    [('e1-e3', 1), ('e2-e4', 1)],                      # height 2
    [('e1-e2', 1), ('e2-e3', 1), ('e3-e4', 1)],        # height 1
    [('h', 3)],                                         # Cartan
    [('e2-e1', 1), ('e3-e2', 1), ('e4-e3', 1)],        # height -1
    [('e3-e1', 1), ('e4-e2', 1)],                       # height -2
    [('e4-e1', 1)],                                     # height -3
]

def compute_projections_cumulative(x_weight_list):
    """Given a list of weights from V tensor X, compute dim of projection to each irrep."""
    from collections import Counter
    wt_counts = Counter(x_weight_list)
    d36 = sum(min(cnt, l36.get(wt, 0)) for wt, cnt in wt_counts.items())
    d20 = sum(min(cnt, l20.get(wt, 0)) for wt, cnt in wt_counts.items())
    d4 = sum(min(cnt, l4.get(wt, 0)) for wt, cnt in wt_counts.items())
    return d36, d20, d4

print("%-10s | mult | V tensor x landing: d36 d20 d4 | Cum: d36  d20   d4 | a_j    b_j" % "Root")
print("-" * 90)

j = 0
all_vx_wts = []
ab_table = []

for level in levels:
    for root_label, mult in level:
        root_wt = adj_wts[root_label]

        for m in range(mult):
            j += 1

            # Add the 4 weights from V tensor x_root
            new_wts = [wt_add(v, root_wt) for v in V_wts]
            all_vx_wts.extend(new_wts)

            # Per-root contribution
            from collections import Counter
            new_counts = Counter(new_wts)
            nd36 = sum(min(cnt, l36.get(wt, 0)) for wt, cnt in new_counts.items())
            nd20 = sum(min(cnt, l20.get(wt, 0)) for wt, cnt in new_counts.items())
            nd4 = sum(min(cnt, l4.get(wt, 0)) for wt, cnt in new_counts.items())

            # Cumulative
            cd36, cd20, cd4 = compute_projections_cumulative(all_vx_wts)

            a = cd36 + cd20
            b = 4 * cd4 - cd20

            ab_table.append((j, root_label + ("'" if mult > 1 and m > 0 else ""),
                           nd36, nd20, nd4, cd36, cd20, cd4, a, b))

            label = root_label
            if mult > 1:
                label = "%s(%d)" % (root_label, m+1)
            print("%-10s | %4d | new: %3d %3d %2d           | cum: %3d  %3d   %2d | %4d  %4d" % (
                label, mult, nd36, nd20, nd4, cd36, cd20, cd4, a, b))

print()
print("=" * 60)
print("LEMMA 5.2 BOUND FOR M_4 at r=29, rho=13")
print("=" * 60)
print()

n = 4
rho = 13
r = 29

print("j  | a_j | b_j | bound = a*rho^2/(8j^2) + (a+b)*rho/j")
print("-" * 60)

max_bound = 0
max_j = 0
for j_idx, (j, label, nd36, nd20, nd4, cd36, cd20, cd4, a, b) in enumerate(ab_table):
    if a == 0 and b == 0:
        bound = 0
    else:
        bound = a * rho^2 / (8 * j^2) + (a + b) * rho / j
    print("%2d | %3d | %3d | %.4f" % (j, a, b, float(bound)))
    if bound > max_bound:
        max_bound = bound
        max_j = j

print()
print("Maximum bound: %.4f at j=%d" % (float(max_bound), max_j))
print("Target (need bound < r): %d" % r)
print("Target (need bound < n^2+rho): %d" % (n^2 + rho))
print()

if max_bound == 0:
    print("ERROR: All a_j, b_j are zero. Weight lookup issue persists.")
    print()
    # Debug: check a specific lookup
    print("Debug: checking specific weight lookups")
    test_wt = (QQ(7)/4, QQ(-1)/4, QQ(-1)/4, QQ(-5)/4)
    print("  l36 keys (first 5): %s" % list(l36.keys())[:5])
    print("  Looking up %s: %s" % (test_wt, l36.get(test_wt, 'NOT FOUND')))
    print("  l36 type check: key type = %s, lookup type = %s" % (
        type(list(l36.keys())[0]), type(test_wt)))
    print("  l36 key[0] == test_wt? %s" % (list(l36.keys())[0] == test_wt))
    # Print first few keys with values
    for k, v in list(l36.items())[:5]:
        print("  key=%s (type %s), value=%d" % (k, type(k[0]), v))
        print("    test: k == test_wt? %s" % (k == test_wt))
        print("    elements: %s vs %s" % ([type(x) for x in k], [type(x) for x in test_wt]))
