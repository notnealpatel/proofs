"""
residual_aut_cascade.sage — For each orbit representative of rank-1 tensors
under Aut(<2,2,2>), compute the Lie algebra dimension of Stab(T') in GL(4,F2)^3,
where T' = T + u (x) v (x) w is the residual tensor after peeling one rank-1 term.

Key question: does symmetry survive after removing one rank-1 term from
the matrix multiplication tensor?

Usage:
    sage /tmp/residual_aut_cascade.sage | tee /tmp/residual_aut_cascade.log
"""
import sys
import time

F = GF(2)

# ─────────────────────────────────────────────────────────
# 1. Construct T = <2,2,2> as a 4x4x4 tensor over GF(2)
# ─────────────────────────────────────────────────────────
# Row-major: e_{ij} -> 2*i + j.
# T[a,b,c] = 1 iff j1==i2 and i1==i3 and j2==j3
# where a = 2*i1+j1, b = 2*i2+j2, c = 2*i3+j3.

N = 4  # dimension of each factor space

T = [[[F(0)]*N for _ in range(N)] for _ in range(N)]
for a in range(N):
    i1, j1 = a // 2, a % 2
    for b in range(N):
        i2, j2 = b // 2, b % 2
        for c in range(N):
            i3, j3 = c // 2, c % 2
            if j1 == i2 and i1 == i3 and j2 == j3:
                T[a][b][c] = F(1)

T_weight = sum(1 for a in range(N) for b in range(N) for c in range(N)
               if T[a][b][c] != 0)
T_support = frozenset(
    (a, b, c) for a in range(N) for b in range(N) for c in range(N)
    if T[a][b][c] != 0
)


# ─────────────────────────────────────────────────────────
# 2. Build Aut(T) = GL(2,F2)^3 . S2  (432 elements)
# ─────────────────────────────────────────────────────────
# The (P,Q,R) embedding into GL(4)^3:
#   g1 = P (x) Q^{-T}
#   g2 = Q (x) R^{-T}
#   g3 = P^{-T} (x) R
# Plus the transpose involution sigma that swaps factors 1<->2.

GL2 = GL(2, F)

def kron(A, B):
    """Kronecker product of two 2x2 matrices -> 4x4 matrix over F."""
    return A.tensor_product(B)


# Build the 432-element group acting on triples of 4-vectors.
# Each element is (g1, g2, g3) in GL(4,F2)^3 plus the swap.
# For orbits on rank-1 triples (u,v,w), the action is:
#   (g1,g2,g3) . (u,v,w) = (g1*u, g2*v, g3*w)
#   swap . (u,v,w) = (sigma*v, sigma*u, sigma*w)
# where sigma is the 4x4 transposition permutation matrix.

# Transpose permutation: e_{ij} -> e_{ji}, so index 2i+j -> 2j+i.
perm = [0]*N
for i in range(2):
    for j in range(2):
        perm[2*i+j] = 2*j+i
sigma_mat = matrix(F, N, N, lambda i, j: F(1) if j == perm[i] else F(0))

aut_elements = []  # list of (g1, g2, g3) 4x4 matrices

for P in GL2:
    for Q in GL2:
        for R in GL2:
            Pm = P.matrix()
            Qm = Q.matrix()
            Rm = R.matrix()
            PiT = Pm.inverse().transpose()
            QiT = Qm.inverse().transpose()
            RiT = Rm.inverse().transpose()

            g1 = kron(Pm, QiT)
            g2 = kron(Qm, RiT)
            g3 = kron(PiT, Rm)
            aut_elements.append((g1, g2, g3))

# Add swap-composed elements: swap . (P,Q,R) for each triple.
swap_aut = []
for (g1, g2, g3) in aut_elements:
    # swap sends (u,v,w) -> (sigma*v, sigma*u, sigma*w)
    # composed with (g1,g2,g3): first apply g, then swap.
    # So total: (sigma*g2*v, sigma*g1*u, sigma*g3*w) ... but we want
    # the action on triples to be (h1*u, h2*v, h3*w).
    # swap . g . (u,v,w) = swap(g1*u, g2*v, g3*w) = (sigma*g2*v, sigma*g1*u, sigma*g3*w)
    # This means: h1 acting on u doesn't factor as h1*u alone with a single matrix.
    # Instead, the swap interchanges which vector each matrix acts on.
    # For orbit computation on rank-1 tensors by support, apply directly.
    h1 = sigma_mat * g2  # acts on v -> sigma*g2*v but maps to slot 1
    h2 = sigma_mat * g1  # acts on u -> sigma*g1*u but maps to slot 2
    h3 = sigma_mat * g3
    swap_aut.append((h1, h2, h3, True))  # True = swap flag

all_aut = [(g1, g2, g3, False) for (g1, g2, g3) in aut_elements]
all_aut.extend(swap_aut)

print("Aut(T) size: %d" % len(all_aut))

# ─────────────────────────────────────────────────────────
# 3. Enumerate rank-1 tensors and partition into orbits
# ─────────────────────────────────────────────────────────

nonzero_vecs = []
for bits in range(1, 2**N):
    v = vector(F, [(bits >> i) & 1 for i in range(N)])
    nonzero_vecs.append(v)

def rank1_support(u, v, w):
    s = set()
    for a in range(N):
        if u[a] == 0: continue
        for b in range(N):
            if v[b] == 0: continue
            for c in range(N):
                if w[c] == 0: continue
                s.add((a, b, c))
    return frozenset(s)

def vec_to_bits(v):
    """Canonical integer key for a GF(2) vector."""
    return sum(int(v[i]) << i for i in range(len(v)))

# Build all unique rank-1 tensors by support, keeping one (u,v,w) per support.
support_to_rep = {}  # support -> (u, v, w)
for u in nonzero_vecs:
    for v in nonzero_vecs:
        for w in nonzero_vecs:
            s = rank1_support(u, v, w)
            if s not in support_to_rep:
                support_to_rep[s] = (u, v, w)

print("Unique rank-1 tensors (by support): %d" % len(support_to_rep))

# Partition into orbits under Aut(T).
remaining = set(support_to_rep.keys())
orbits = []  # list of (rep_support, rep_uvw, orbit_size)

while remaining:
    rep_supp = min(remaining, key=lambda s: sorted(s))
    rep_uvw = support_to_rep[rep_supp]

    # Compute the full orbit of this support.
    orbit_supports = set()
    orbit_supports.add(rep_supp)

    u0, v0, w0 = rep_uvw
    for (g1, g2, g3, is_swap) in all_aut:
        if is_swap:
            # swap: (u,v,w) -> (g1*v, g2*u, g3*w)  [g1,g2 already incorporate sigma]
            nu = g1 * v0
            nv = g2 * u0
            nw = g3 * w0
        else:
            nu = g1 * u0
            nv = g2 * v0
            nw = g3 * w0
        s = rank1_support(nu, nv, nw)
        orbit_supports.add(s)

    orbits.append((rep_supp, rep_uvw, len(orbit_supports)))
    remaining -= orbit_supports

orbits.sort(key=lambda x: -x[2])

print("Number of orbits: %d" % len(orbits))
total_in_orbits = sum(sz for _, _, sz in orbits)
print("Total tensors in orbits: %d (expect %d)" % (total_in_orbits, len(support_to_rep)))
assert total_in_orbits == len(support_to_rep), "Orbit partition mismatch!"

# ─────────────────────────────────────────────────────────
# 4. For each orbit rep, compute residual T' and its Lie dim
# ─────────────────────────────────────────────────────────

def make_residual(T_orig, u, v, w):
    """Compute T' = T + u (x) v (x) w over F2 (subtraction = addition)."""
    Tp = [[[T_orig[a][b][c] for c in range(N)] for b in range(N)] for a in range(N)]
    for a in range(N):
        if u[a] == 0: continue
        for b in range(N):
            if v[b] == 0: continue
            for c in range(N):
                if w[c] == 0: continue
                Tp[a][b][c] += F(1)
    return Tp


def tensor_weight(Tp):
    """Number of nonzero entries in a 4x4x4 tensor."""
    return sum(1 for a in range(N) for b in range(N) for c in range(N)
               if Tp[a][b][c] != 0)


def stabilizer_lie_dim(Tp):
    """
    Dimension of the stabilizer Lie algebra of Tp in gl(4,F2)^3.

    Linearized condition at (I, I, I):
      sum_{a'} X1[a,a'] Tp[a',b,c]
    + sum_{b'} X2[b,b'] Tp[a,b',c]
    + sum_{c'} X3[c,c'] Tp[a,b,c']  = 0    for all (a,b,c).

    Variables: 3 * 16 = 48 entries of (X1, X2, X3).
    Equations: 64 scalar equations over F2.
    """
    nvars = 3 * N * N  # 48
    rows = []
    for a in range(N):
        for b in range(N):
            for c in range(N):
                row = [F(0)] * nvars
                # X1 block: columns [0, 16)
                for ap in range(N):
                    if Tp[ap][b][c] != 0:
                        row[a * N + ap] += F(1)
                # X2 block: columns [16, 32)
                for bp in range(N):
                    if Tp[a][bp][c] != 0:
                        row[N * N + b * N + bp] += F(1)
                # X3 block: columns [32, 48)
                for cp in range(N):
                    if Tp[a][b][cp] != 0:
                        row[2 * N * N + c * N + cp] += F(1)
                rows.append(row)

    A = matrix(F, rows)
    return A.right_kernel().dimension()


# ─────────────────────────────────────────────────────────
# 5. Compute and print results
# ─────────────────────────────────────────────────────────

# First, Lie dim of the original T for reference.
t0 = time.time()
T_lie_dim = stabilizer_lie_dim(T)
print("\nOriginal T = <2,2,2>: weight=%d, Lie(Stab) dim=%d (elapsed %.2fs)"
      % (T_weight, T_lie_dim, time.time() - t0))

# Generic tensor check: random tensor for reference.
import random
random.seed(int(42))
Trand = [[[F(random.randint(0, 1)) for _ in range(N)]
          for _ in range(N)] for _ in range(N)]
generic_lie_dim = stabilizer_lie_dim(Trand)
print("Random tensor: Lie(Stab) dim=%d (generic baseline)" % generic_lie_dim)

print("\n" + "="*72)
print("Residual Lie algebra dimensions for T' = T + u(x)v(x)w")
print("="*72)
fmt = "%-8s  %-10s  %-44s  %-8s  %-8s  %-10s"
print(fmt % ("Orbit", "Size", "Representative (u,v,w)", "Weight", "LieDim", "Subtensor"))
print("-" * 72)

max_lie_dim = 0
cascade_candidates = []

for idx, (supp, (u, v, w), orbit_sz) in enumerate(orbits):
    t0 = time.time()
    Tp = make_residual(T, u, v, w)
    wt = tensor_weight(Tp)
    lie_dim = stabilizer_lie_dim(Tp)
    elapsed = time.time() - t0

    is_sub = supp.issubset(T_support)
    rep_str = "(%s,%s,%s)" % (list(u), list(v), list(w))

    print(fmt % (idx, orbit_sz, rep_str, wt, lie_dim,
                 "YES" if is_sub else "NO"))

    if lie_dim > max_lie_dim:
        max_lie_dim = lie_dim
    if lie_dim > 0:
        cascade_candidates.append((idx, orbit_sz, rep_str, wt, lie_dim))

print("\n" + "="*72)
print("SUMMARY")
print("="*72)
print("Original T: Lie dim = %d" % T_lie_dim)
print("Generic tensor: Lie dim = %d" % generic_lie_dim)
print("Max residual Lie dim = %d" % max_lie_dim)

if cascade_candidates:
    print("\nCascade candidates (Lie dim > 0):")
    for (idx, sz, rep, wt, ld) in cascade_candidates:
        print(f"  Orbit {idx} (size {sz}): rep={rep}, weight={wt}, Lie dim={ld}")
    print("\nSymmetry survives: the cascade can continue.")
else:
    print("\nNo residuals have Lie dim > 0: symmetry is fully broken after one peel.")
