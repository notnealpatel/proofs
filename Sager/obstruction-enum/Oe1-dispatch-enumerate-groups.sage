# Oe1 DISPATCH (medium, single-core): EXHAUSTIVE enumeration of finite groups
# admitting the GM <3,3,3> ansatz, to confirm the candidate list is complete.
#
# The GM construction needs a finite group G with (a) a faithful irreducible
# 3-dim representation rho and (b) an order-3 element sigma. For G to possibly
# BEAT Laderman 23, some seed orbit under conjugation must have size <= 21, i.e.
# G must have a subgroup H (the seed-direction stabilizer, a proper subgroup with
# nonzero rho(x)rho* fixed space) with |G|/|H| <= 21, so |H| >= |G|/21.
#
# This script scans GAP's SmallGroups library up to a chosen order bound, lists
# every group with a faithful irreducible 3-dim irrep and an order-3 element, and
# reports its smallest achievable orbit (over conjugacy classes of subgroups with
# nonzero fixed space). Groups whose smallest orbit > 21 are RULED OUT by rank;
# the rest are flagged as feasibility candidates (most are the O(3) point groups
# A_4/S_4/A_5 and the complex Blichfeldt groups already handled).
#
# Run:  sager Sager/Oe1-dispatch-enumerate-groups.sage
# Emits one JSON line per group with a faithful 3-dim irrep + a final summary.
#
# COST: character-table lookups over many small groups (cheap) plus, for the
# candidates with small-enough orbit, a fixed-dim computation. No Groebner here --
# this only IDENTIFIES candidates; feasibility is the other dispatch scripts.
# Bound the order to keep it single-core-bounded (default 200; raise if needed,
# but |G| up to ~1080 covers Valentiner).

import json, math
ORDER_BOUND = 168   # covers A_4(12),S_4(24),A_5(60),PSL(2,7)(168). Raise to 1080
                    # (slow, dedicate a core) to also sweep Hessian(216) and
                    # Valentiner 3.A_6(1080).

def emit(d): print(json.dumps(d))

def min_orbit_lb(G, order):
    # smallest orbit |G|/|H| over maximal subgroups H -> true lower bound on any
    # seed-direction orbit (its stabilizer is a proper subgroup). orbit>21 => the
    # group cannot beat Laderman 23, ruled out by rank with no Groebner.
    try:
        maxs=gap.MaximalSubgroupClassReps(G); Mmax=1
        for t in range(1,Integer(gap.Length(maxs))+1):
            mo=Integer(gap.Order(maxs[t]))
            if mo>Mmax: Mmax=mo
        return order//Mmax if Mmax>0 else order
    except Exception:
        return order

candidates=[]
for order in range(3, ORDER_BOUND+1):
    if order % 3 != 0:
        # need an order-3 element => 3 | |G|
        continue
    try:
        ngroups=Integer(gap.NumberSmallGroups(order))
    except Exception:
        continue
    for gi in range(1, ngroups+1):
        try:
            G=gap.SmallGroup(order, gi)
            ct=gap.CharacterTable(G)
            irr=gap.Irr(ct)
            # degrees
            degs=[Integer(gap.Degree(irr[t])) for t in range(1,Integer(gap.Length(irr))+1)]
            if 3 not in degs:
                continue
            # check there is an order-3 element
            ords=[Integer(x) for x in gap.OrdersClassRepresentatives(ct)]
            if 3 not in ords:
                continue
            # check FAITHFUL 3-dim irrep exists: kernel trivial
            faithful3=False
            for t in range(1,Integer(gap.Length(irr))+1):
                if Integer(gap.Degree(irr[t]))!=3: continue
                ker=gap.KernelOfCharacter(irr[t])
                if Integer(gap.Order(ker))==1:
                    faithful3=True; break
            if not faithful3:
                continue
            name=str(gap.StructureDescription(G))
            mlb=min_orbit_lb(G, order)
            rank_lb=1+mlb
            can_fit=rank_lb<=22
            candidates.append((order,gi,name,mlb,can_fit))
            emit({"order":int(order),"id":int(gi),"structure":name,
                  "min_orbit_lower_bound":int(mlb),"min_rank_lower_bound":int(rank_lb),
                  "can_fit_rank_le_22":bool(can_fit),
                  "note":"faithful 3-dim irrep + order-3 element"})
        except Exception:
            continue

fitting=[(o,i,n,m) for (o,i,n,m,c) in candidates if c]
emit({"summary":True,"order_bound":int(ORDER_BOUND),
      "num_groups_with_faithful_3dim_irrep_and_order3":int(len(candidates)),
      "num_that_can_fit_rank_le_22":int(len(fitting)),
      "fitting_candidates":[{"order":int(o),"id":int(i),"structure":n,"min_orbit":int(m)} for (o,i,n,m) in fitting]})
emit({"interpretation":
      "Cross-check against the handled set {A_4=SmallGroup(12,3), S_4=SmallGroup(24,12), "
      "A_5=SmallGroup(60,5)} plus the complex Blichfeldt groups PSL(2,7) (order 168), "
      "Hessian/ST25 (216/648), Valentiner 3.A_6 (1080). Any candidate NOT in this set, "
      "with smallest orbit <= 21, needs its own feasibility dispatch."})
