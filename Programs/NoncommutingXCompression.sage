from itertools import product

def image(A):
    P = list(A)
    L0 = [(y, -x, 0) for x, y, z in P]
    L1 = [(z, 0, -x) for x, y, z in P]
    L2 = [(0, z, -y) for x, y, z in P]
    return {(a[0] + b[0] + c[0], a[1] + b[1] + c[1], a[2] + b[2] + c[2])
            for a in L0 for b in L1 for c in L2}

def compress(A):
    fibers = {}
    for x, y, z in A:
        fibers[y, z] = fibers.get((y, z), 0) + 1
    return {(j, y, z) for (y, z), k in fibers.items() for j in range(k)}

A = {(0,0,0), (0,0,1), (1,0,0), (1,1,0)}
C = compress(A)
MA, MC = image(A), image(C)
expected_C = {(0,0,0), (0,0,1), (0,1,0), (1,0,0)}
expected_MA = {
    (0,-1,-2),(0,-1,-1),(0,-1,0),(0,0,-2),(0,0,-1),(0,0,0),
    (0,1,-1),(0,1,0),(1,-1,-2),(1,-1,-1),(1,-1,0),(1,0,-1),
    (1,0,0),(1,1,0),(2,-1,-1),(2,-1,0),(2,0,0)}
expected_MC = {
    (0,-1,-2),(0,-1,-1),(0,-1,0),(0,0,-2),(0,0,-1),(0,0,0),
    (0,1,-1),(0,1,0),(1,-1,-1),(1,-1,0),(1,0,-2),(1,0,-1),
    (1,0,0),(1,1,-1),(1,1,0),(2,0,-1),(2,0,0),(2,1,0)}
assert C == expected_C
assert MA == expected_MA
assert MC == expected_MC
assert len(MA) == 17 and len(MC) == 18
Bsum = {(0,0,0), (1,0,0), (0,0,-1)}
L2sum = {(0,0,0), (0,1,0), (0,0,-1)}
Bsum = {(a[0] + b[0], a[1] + b[1], a[2] + b[2])
        for a in Bsum for b in L2sum}
U = Bsum | {(x, y - 1, z) for x, y, z in Bsum}
ex = (1,0,0)
ey = (0,1,0)
old_translate = {(x + ex[0] - ey[0], y + ex[1] - ey[1], z + ex[2] - ey[2])
                 for x, y, z in Bsum}
new_translate = {(x + ex[0], y + ex[1], z + ex[2]) for x, y, z in Bsum}
assert len(Bsum) == 8 and len(U) == 13
assert len(old_translate & U) == 4 and len(new_translate & U) == 3
print('A', sorted(A)); print('Cx(A)', sorted(C))
print('M(A)', sorted(MA)); print('M(Cx(A))', sorted(MC))
print('removed', sorted(MA - MC)); print('added', sorted(MC - MA))
print('sizes', len(MA), len(MC))

# Bounded early-stopped search over at most 255 nonempty candidates in {0,1}^3.
B = list(product(range(2), repeat=3))
for mask in range(1, 1 << len(B)):
    S = {B[i] for i in range(len(B)) if (mask >> i) & 1}
    if len(image(compress(S))) > len(image(S)):
        print('first witness in bounded early-stopped search', sorted(S)); break
