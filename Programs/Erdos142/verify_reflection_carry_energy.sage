from collections import Counter
import json


def audit(N, A):
    centers = {}
    for c in range(N^2):
        centers[c] = [a for a in A if a != c and 2*a-c in A]
    E = sum(len(C)^2 for C in centers.values())
    M = sum(len(C) for C in centers.values())
    K = Counter()
    W = Counter()
    for c, C in centers.items():
        for a in C:
            for aa in C:
                s = a % N + aa % N + c % N
                z, k = s % N, s // N
                assert 0 <= z < N and 0 <= k < 3
                K[(z, k)] += 1
                W[z] += 1
    assert E == sum(K.values())
    assert all(W[z] == sum(K[(z, k)] for k in range(3)) for z in range(N))
    assert E <= 3*N*max([K[(z,k)] for z in range(N) for k in range(3)])
    digit_K = Counter()
    digit_W = Counter()
    for i in range(N):
        for j in range(N):
            for v in range(N):
                for x in range(N):
                    for y in range(N):
                        for z in range(N):
                            n = (z-x-y) % N
                            c = n+N*v
                            a, aa = x+N*i, y+N*j
                            valid = a in A and aa in A and a != c and aa != c \
                                and 2*a-c in A and 2*aa-c in A
                            if valid:
                                digit_W[z] += 1
                            for k in range(3):
                                nn = z+k*N-x-y
                                if 0 <= nn < N:
                                    cc = nn+N*v
                                    if a in A and aa in A and a != cc and aa != cc \
                                            and 2*a-cc in A and 2*aa-cc in A:
                                        digit_K[(z,k)] += 1
    assert K == digit_K
    assert W == digit_W
    return M, E, K


def scalar_free(A):
    return all(a == b or 2*a-b not in A for a in A for b in A)


checked, free_checked = 0, 0
for N in range(1, 4):
    for mask in range(2^(N^2)):
        A = set(a for a in range(N^2) if mask & (1 << a))
        audit(N, A)
        checked += 1
        free_checked += int(scalar_free(A))

stress = [(3, {1,2,4,8}), (3, {0,3}), (3, {2,5}), (4, {0,1,4,5}),
          (4, set(range(16))), (5, {0,1,4,7,13,19,24})]
reports = []
for N, A in stress:
    M, E, K = audit(N, A)
    reports.append({"N": int(N), "A": sorted(int(a) for a in A), "scalar_free": scalar_free(A),
                    "mass": int(M), "energy": int(E),
                    "slices": [[int(z),int(k),int(n)] for (z,k),n in sorted(K.items())]})
print(json.dumps({"exhaustive_N": [int(n) for n in range(1,4)], "all_subsets_checked": int(checked),
                  "scalar_free_subsets_checked": int(free_checked),
                  "identities": ["energy=sum slices", "wrapped=sum three carries",
                                 "energy<=3*N*largest slice", "digit predicate=count"],
                  "stress": reports}, sort_keys=True))
