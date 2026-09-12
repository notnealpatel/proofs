from sage.all import QQ

N = 9
capacities = [1, 2, 2, 3, 4, 4, 4, 4]


def progression_free(mask, length):
    return all(
        not all(mask & (1 << point) for point in (a, a + step, a + 2 * step))
        for step in range(1, (length - 1) // 2 + 1)
        for a in range(length - 2 * step)
    )


computed_capacities = [
    max(mask.bit_count() for mask in range(1 << length) if progression_free(mask, length))
    for length in range(1, N)
]
assert computed_capacities == capacities

windows = []
for length in range(1, N):
    steps = [0] if length == 1 else range(1, (N - 1) // (length - 1) + 1)
    for step in steps:
        starts = range(N) if length == 1 else range(N - (length - 1) * step)
        for start in starts:
            points = (start,) if length == 1 else tuple(
                start + offset * step for offset in range(length)
            )
            windows.append((points, capacities[length - 1]))
assert len(windows) == 85

primal = {tuple(range(8)): QQ(1), (8,): QQ(1)}
assert all(
    sum(weight for points, weight in primal.items() if point in points) >= 1
    for point in range(N)
)
primal_cost = sum(
    capacity * primal.get(points, 0) for points, capacity in windows
)
assert primal_cost == 5

dual_mask = 355
dual = [QQ(1) if dual_mask & (1 << point) else QQ(0) for point in range(N)]
assert all(
    sum(dual[point] for point in points) <= capacity
    for points, capacity in windows
)
dual_value = sum(dual)
assert dual_value == primal_cost == 5

print("PASS exact proper-affine-window LP certificate")
print("N", N, "windows", len(windows), "capacities", capacities)
print("primal_cost", primal_cost, "dual_value", dual_value)
