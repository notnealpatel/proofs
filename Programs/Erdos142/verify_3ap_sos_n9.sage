from sage.all import QQ, diagonal_matrix, identity_matrix, matrix, vector, zero_matrix
from pathlib import Path
import itertools
import json
import sys

script = Path(sys.argv[0]).resolve()
assert script.suffix == ".sage"
certificate = script.with_name("3ap-sos-N9-degree4-exact.json")
d = json.loads(certificate.read_text())
assert d["format"] == "3ap-quotient-gram-scaled-v1"
N, C, t = d["N"], d["C"], d["degree"] // 2
assert (N, C, t) == (9, 5, 2)


def masks(k):
    return [sum(1 << i for i in c) for c in itertools.combinations(range(N), k)]


edges = [
    sum(1 << x for x in (a, a + q, a + 2 * q))
    for q in range(1, (N - 1) // 2 + 1)
    for a in range(N - 2 * q)
]


def free(mask):
    return all(mask & edge != edge for edge in edges)


basis = [mask for k in range(t + 1) for mask in masks(k) if free(mask)]
assert len(edges) == 16 and len(basis) == 46

size = len(basis)
values = d["gram_upper_numerators"]
denominator = d["gram_denominator"]
assert denominator > 0 and len(values) == size * (size + 1) // 2
Q = zero_matrix(QQ, size)
pos = 0
for i in range(size):
    for j in range(i, size):
        Q[i, j] = QQ(values[pos]) / denominator
        Q[j, i] = Q[i, j]
        pos += 1

quotient_coefficients = 0
for k in range(2 * t + 1):
    for u in masks(k):
        if not free(u):
            continue
        got = sum(
            Q[i, j]
            for i, left in enumerate(basis)
            for j, right in enumerate(basis)
            if left | right == u
        )
        want = QQ(C if u == 0 else (-1 if k == 1 else 0))
        assert got == want
        quotient_coefficients += 1

extremal_masks = d["extremal_masks"]
assert extremal_masks == [
    mask for mask in range(1 << N) if free(mask) and mask.bit_count() == C
]
kernel_columns = [
    vector(QQ, [1 if support & mask == support else 0 for support in basis])
    for mask in extremal_masks
]
standard_indices = d["standard_basis_columns"]
assert len(standard_indices) == size - len(kernel_columns)
standard_columns = [
    vector(QQ, [1 if row == col else 0 for row in range(size)])
    for col in standard_indices
]
P = matrix(QQ, kernel_columns + standard_columns).transpose()
assert P.nrows() == P.ncols() == size and P.det() != 0
B = P.transpose() * Q * P
kernel_dimension = len(kernel_columns)
assert kernel_dimension == 4
assert B[:kernel_dimension, :] == 0 and B[:, :kernel_dimension] == 0

H = B[kernel_dimension:, kernel_dimension:]
ldl_size = H.nrows()
L = identity_matrix(QQ, ldl_size)
pivots = []
for j in range(ldl_size):
    pivot = H[j, j] - sum(L[j, k] ** 2 * pivots[k] for k in range(j))
    assert pivot > 0
    pivots.append(pivot)
    for i in range(j + 1, ldl_size):
        L[i, j] = (
            H[i, j] - sum(L[i, k] * L[j, k] * pivots[k] for k in range(j))
        ) / pivot
assert L * diagonal_matrix(QQ, pivots) * L.transpose() == H

checked = 0
for assignment in range(1 << N):
    if not free(assignment):
        continue
    evaluation = vector(
        QQ, [1 if support & assignment == support else 0 for support in basis]
    )
    value = evaluation.dot_product(Q * evaluation)
    assert value == C - assignment.bit_count()
    assert value >= 0
    checked += 1
assert checked == 169

print("PASS", certificate)
print("N", N, "degree", 2 * t, "C", C, "basis", size)
print("quotient_coefficients", quotient_coefficients)
print("PSD: kernel", kernel_dimension, "positive_LDL_pivots", len(pivots))
print("valid_boolean_assignments", checked)
