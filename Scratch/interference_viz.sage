#!/usr/bin/env sage
"""
Interference pattern visualization: Strassen vs Schoolbook for <2,2,2>.
"""

# === Data ===

outputs = ["1", "2", "3", "4"]

strassen_products = ["m1", "m2", "m3", "m4", "m5", "m6", "m7", "  "]
# coverage[i][j] = sign of product i in output j, 0 if absent
strassen_coverage = [
    # C11  C12  C21  C22
    [+1,    0,   0,  +1],  # M1
    [ 0,    0,  +1,  -1],  # M2
    [ 0,   +1,   0,  +1],  # M3
    [+1,    0,  +1,   0],  # M4
    [-1,   +1,   0,   0],  # M5
    [ 0,    0,   0,  +1],  # M6
    [+1,    0,   0,   0],  # M7
    [ 0,    0,   0,   0],  # (saved)
]

schoolbook_products = ["m1", "m2", "m3", "m4", "m5", "m6", "m7", "m8"]
schoolbook_coverage = [
    # C11  C12  C21  C22
    [+1,    0,   0,   0],  # p1
    [+1,    0,   0,   0],  # p2
    [ 0,   +1,   0,   0],  # p3
    [ 0,   +1,   0,   0],  # p4
    [ 0,    0,  +1,   0],  # p5
    [ 0,    0,  +1,   0],  # p6
    [ 0,    0,   0,  +1],  # p7
    [ 0,    0,   0,  +1],  # p8
]

# === Helpers ===

def sign_char(v):
    if v == +1: return "+"
    if v == -1: return "-"
    return "."

def print_coverage_matrix(title, products, coverage, outputs):
    """Outputs as rows, products as columns."""
    print(f"\n  {title}")
    print(f"  {'=' * len(title)}\n")

    prod_w = max(len(p) for p in products) + 1
    out_w = 4

    hdr = f"  {'':>{out_w}}"
    for p in products:
        hdr += f" {p:^{prod_w}}"
    hdr += "  hits"
    print(hdr)
    print(f"  {'-'*out_w}" + f" {'-'*prod_w}" * len(products) + "  ----")

    for j, o in enumerate(outputs):
        hits = sum(1 for row in coverage if row[j] != 0)
        line = f"  {o:<{out_w}}"
        for i in range(len(products)):
            v = coverage[i][j]
            c = sign_char(v)
            if c == ".":
                line += f" {'.':^{prod_w}}"
            else:
                marker = f"[{c}]" if hits > 2 else f" {c} "
                line += f" {marker:^{prod_w}}"
        line += f"  {hits}"
        print(line)
    print()

# === Main output ===

print_coverage_matrix(
    "SCHOOLBOOK (rank 8)",
    schoolbook_products, schoolbook_coverage, outputs
)

print_coverage_matrix(
    "STRASSEN (rank 7)",
    strassen_products, strassen_coverage, outputs
)

# Summary line
for label, products, coverage in [
    ("Schoolbook", schoolbook_products, schoolbook_coverage),
    ("Strassen", strassen_products, strassen_coverage),
]:
    total_nz = sum(sum(1 for v in row if v != 0) for row in coverage)
    density = float(total_nz) / float(len(products) * len(outputs))
    multi = sum(1 for row in coverage if sum(1 for v in row if v != 0) > 1)
    print(f"  {label:>10}: density={density:.0%}  multi-hit={multi}/{len(products)}")
print()
