from sage.all import AA, CyclotomicField, QQ, RealIntervalField

N = 16
Q = 4 * N
r3 = 8
B = {0, 1, 6, 8, 13, 14}
E = {(9, 0), (10, 1), (1, 12), (2, 13), (3, 14), (4, 15)}


def is_integer_cap(points, length):
    points = set(points)
    return all(
        not (a in points and a + step in points and a + 2 * step in points)
        for a in range(length)
        for step in range(1, length)
        if a + 2 * step < length
    )


def mask_is_cap(mask, length):
    return all(
        not (
            mask & (1 << a)
            and mask & (1 << (a + step))
            and mask & (1 << (a + 2 * step))
        )
        for a in range(length)
        for step in range(1, length)
        if a + 2 * step < length
    )


r3_16 = max(
    mask.bit_count()
    for mask in range(1 << N)
    if mask_is_cap(mask, N)
)
assert r3_16 == r3 == 8

G = {
    (x, y)
    for x in range(N)
    for y in range(N)
    if (x - y) % N in B
}
G.update(E)
assert len(G) == 102

A = {x + N * y for x, y in G}
m = len(A)
assert m == 102
assert m**3 == 1061208
assert N**2 * r3**4 == 1048576
assert m**3 > N**2 * r3**4

rows = {
    y: {x for x, y0 in G if y0 == y}
    for y in range(N)
}
cols = {
    x: {y for x0, y in G if x0 == x}
    for x in range(N)
}
assert set(rows) == set(range(N))
assert set(cols) == set(range(N))
assert all(rows[y] for y in range(N))
assert all(cols[x] for x in range(N))
assert all(is_integer_cap(rows[y], N) and len(rows[y]) <= r3 for y in range(N))
assert all(is_integer_cap(cols[x], N) and len(cols[x]) <= r3 for x in range(N))
assert {y for x, y in G} == set(range(N))
assert {x for x, y in G} == set(range(N))

assert {0, 9, 18}.issubset(A)
assert 0 + 18 == 2 * 9

K64 = CyclotomicField(Q)
zeta = K64.gen()


def phi(y, x):
    return 1 if (x, y) in G else 0


def hat_phi(y, frequency):
    if not (0 <= y < N):
        return K64(0)
    return sum(
        phi(y, x) * zeta ** ((-frequency * x) % Q)
        for x in range(N)
    )


C = []
for frequency in range(Q):
    total = K64(0)
    for t in (-1, 0, 1):
        phase = zeta ** ((t * N * frequency) % Q)
        for y in range(N):
            for q in range(-N, N + 1):
                y0 = y - q
                y2 = y + q - t
                if not (0 <= y0 < N and 0 <= y2 < N):
                    continue
                total += (
                    phase
                    * hat_phi(y0, frequency)
                    * hat_phi(y, -2 * frequency)
                    * hat_phi(y2, frequency)
                )
    C.append(total / Q)

M0 = C[0]
assert M0 == QQ(48183) / 32
assert sum(C) == 1564

S = sum(
    AA(C[frequency] * C[frequency].conjugate()).sqrt()
    for frequency in range(1, Q)
)
K_squared = AA(N**4 * r3**8).nth_root(3)
rhs = AA(M0) + m - AA(m**3) / K_squared
assert S > rhs

RIF = RealIntervalField(256)
print("PASS exact unequal-fiber relaxation certificate")
print("N", N, "Q", Q, "subsets checked", 1 << N)
print("r3(16)", r3_16, "m", m)
print("m^3", m**3, "N^2*r3^4", N**2 * r3**4)
print("full projections", len({x for x, y in G}), len({y for x, y in G}))
print("row/column caps", all(is_integer_cap(rows[y], N) for y in range(N)),
      all(is_integer_cap(cols[x], N) for x in range(N)))
print("witness 0,9,18", 0 in A and 9 in A and 18 in A)
print("M0", M0, "T", sum(C))
print("S interval", S.interval_exact(RIF))
print("rhs interval", rhs.interval_exact(RIF))
print("gap interval", (S - rhs).interval_exact(RIF))
print("K^2 interval", K_squared.interval_exact(RIF))
