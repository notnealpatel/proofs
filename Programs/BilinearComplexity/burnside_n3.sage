# Burnside's lemma: exact orbit count of nonzero rank-1 tensors in (GF(2)^9)^3
# under the GL(3,GF(2))^3 action (P,Q,R) -> (P*Q^{-T}, Q*R^{-T}, P^{-T}*R).

F = GF(2)
G = GL(3, F)
I9 = identity_matrix(F, 9)

# Conjugacy classes of GL(3, GF(2))
classes = G.conjugacy_classes()
print("Number of conjugacy classes of GL(3,GF(2)): %d" % len(classes))

# Precompute representative matrices and class sizes
reps = []
sizes = []
for cc in classes:
    rep = cc.representative().matrix()
    sz = cc.cardinality()
    reps.append(rep)
    sizes.append(sz)
    print("  Class size %d, rep:\n%s" % (sz, rep))

order_G = G.order()
print("\n|GL(3,GF(2))| = %d" % order_G)
print("Number of class triples: %d" % (len(classes)^3))

# Burnside sum
burnside_sum = Integer(0)

for i in range(len(reps)):
    Pi = reps[i]
    Pi_invT = Pi.inverse().transpose()
    for j in range(len(reps)):
        Qj = reps[j]
        Qj_invT = Qj.inverse().transpose()
        for k in range(len(reps)):
            Rk = reps[k]

            # g1 = P tensor Q^{-T}
            g1 = Pi.tensor_product(Qj_invT)
            # g2 = Q tensor R^{-T}
            g2 = Qj.tensor_product(Rk.inverse().transpose())
            # g3 = P^{-T} tensor R
            g3 = Pi_invT.tensor_product(Rk)

            d1 = (g1 - I9).right_kernel().dimension()
            d2 = (g2 - I9).right_kernel().dimension()
            d3 = (g3 - I9).right_kernel().dimension()

            fixed = (2^d1 - 1) * (2^d2 - 1) * (2^d3 - 1)
            weight = sizes[i] * sizes[j] * sizes[k]
            burnside_sum += weight * fixed

total_group = order_G^3
assert burnside_sum % total_group == 0, "Burnside sum not divisible by |G|^3"
n_orbits = burnside_sum // total_group

print("\nBurnside weighted sum = %d" % burnside_sum)
print("|G|^3 = %d" % total_group)
print("Number of orbits = %d" % n_orbits)

# Free-action estimate for comparison
free_est = Rational((2^9 - 1)^3, total_group)
print("\nFree-action estimate (511^3 / 168^3) = %s = %.6f" % (free_est, float(free_est)))
