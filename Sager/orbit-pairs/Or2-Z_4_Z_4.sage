import json
K.<sqrt3> = QuadraticField(3)
R = PolynomialRing(K, 6, "x0,x1,x2,x3,x4,x5")
x0,x1,x2,x3,x4,x5 = R.gens()
gens = [
  (24) + (24)*x0*x0*x0 + (144)*x0*x0*x2 + (288)*x0*x2*x2 + (192)*x2*x2*x2 + (24)*x3*x3*x3 + (144)*x3*x3*x5 + (288)*x3*x5*x5 + (192)*x5*x5*x5,
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (-2),
  (-2),
  (-2),
  (2),
  (2),
  (2),
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (-3/4) + (6)*x0*x0*x0 + (-18)*x0*x0*x2 + (18)*x0*x2*x2 + (-6)*x2*x2*x2 + (6)*x3*x3*x3 + (-18)*x3*x3*x5 + (18)*x3*x5*x5 + (-6)*x5*x5*x5,
  (3/4) + (-6)*x0*x0*x0 + (18)*x0*x0*x2 + (-18)*x0*x2*x2 + (6)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x3*x5 + (-18)*x3*x5*x5 + (6)*x5*x5*x5,
  (1),
  (-1/2),
  (-3/2),
  (-1/2),
  (3/2),
  (-1),
  (3/2),
  (1/2),
  (-3/2),
  (1/2),
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (3/4) + (-6)*x0*x0*x0 + (18)*x0*x0*x2 + (-18)*x0*x2*x2 + (6)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x3*x5 + (-18)*x3*x5*x5 + (6)*x5*x5*x5,
  (-3/2) + (-6)*x0*x0*x0 + (18)*x0*x2*x2 + (-12)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x5*x5 + (-12)*x5*x5*x5,
  (3/4) + (-6)*x0*x0*x0 + (18)*x0*x0*x2 + (-18)*x0*x2*x2 + (6)*x2*x2*x2 + (-6)*x3*x3*x3 + (18)*x3*x3*x5 + (-18)*x3*x5*x5 + (6)*x5*x5*x5,
  ((1)*sqrt3),
  ((1/2)*sqrt3),
  ((-1/2)*sqrt3),
  ((-1/2)*sqrt3),
  ((-1/2)*sqrt3),
  ((-1)*sqrt3),
  ((1/2)*sqrt3),
  ((-1/2)*sqrt3),
  ((1/2)*sqrt3),
  ((1/2)*sqrt3),
  (-2),
  (1),
  ((-1)*sqrt3),
  (-2),
  (1),
  (-1),
  (-1),
  (-1),
  (1),
  ((1)*sqrt3),
  (-1),
  (-1),
  (1),
  (-1),
  (-2),
  (-1/2),
  (3/2),
  ((1/2)*sqrt3),
  ((1/2)*sqrt3),
  (-1),
  (1),
  (-2),
  (-1/2),
  ((1/2)*sqrt3),
  (-1),
  (-1),
  (1),
  (-1),
  (-3/2),
  ((-1/2)*sqrt3),
  (-1),
  (-1),
  (-2),
  (-1/2),
  (-3/2),
  ((-1/2)*sqrt3),
  ((1/2)*sqrt3),
  (-1),
  (-1),
  (-1),
  (1),
  (-2),
  (-1/2),
  ((-1/2)*sqrt3),
  (-1),
  (-1),
  (1),
  (-1),
  (3/2),
  ((-1/2)*sqrt3),
  (2),
  (-1),
  ((1)*sqrt3),
  ((-1)*sqrt3),
  (-1),
  (-1),
  (1),
  (-1),
  (2),
  (-1),
  (-1),
  (-1) + (32)*x1*x1*x1 + (32)*x4*x4*x4,
  (-1),
  (1) + (-32)*x1*x1*x1 + (-32)*x4*x4*x4,
  (2),
  (-3/2),
  (1/2),
  ((-1/2)*sqrt3),
  ((-1/2)*sqrt3),
  (1),
  (-1),
  (3/2),
  ((1/2)*sqrt3),
  (-1),
  (-1),
  (-1),
  (1) + (-32)*x1*x1*x1 + (-32)*x4*x4*x4,
  (2),
  (1/2),
  ((-1/2)*sqrt3),
  (-1),
  (-1) + (32)*x1*x1*x1 + (32)*x4*x4*x4,
  (2),
  (3/2),
  (1/2),
  ((-1/2)*sqrt3),
  ((1/2)*sqrt3),
  (-1),
  (-1),
  (1),
  (-1),
  (-3/2),
  ((1/2)*sqrt3),
  (-1),
  (-1) + (32)*x1*x1*x1 + (32)*x4*x4*x4,
  (-1),
  (1) + (-32)*x1*x1*x1 + (-32)*x4*x4*x4,
  (2),
  (1/2),
  ((1/2)*sqrt3),
]

if len(gens) == 0:
    print(json.dumps({"verdict":"DEGENERATE","reason":"no constraints"}))
else:
    I = R.ideal(gens)
    try:
        gb = I.groebner_basis()
    except Exception as e:
        print(json.dumps({"verdict":"ERROR","reason":str(e)}))
    else:
        gbs = [str(g) for g in gb]
        is_unit = (R.one() in I) if hasattr(R,'one') else any(str(g)=="1" for g in gb)
        if is_unit:
            print(json.dumps({"verdict":"INFEASIBLE","groebner":gbs}))
        else:
            try:
                d = I.dimension()
            except Exception as e:
                d = None
            out = {"verdict":"SOLUTION-FOUND","dimension":(int(d) if d is not None else None),"groebner":gbs}
            if d == 0:
                try:
                    V = I.variety(ring=QQbar)
                    out["num_points"] = len(V)
                    pts = []
                    for sol in V[:8]:
                        pts.append({str(k): str(v) for k,v in sol.items()})
                    out["points"] = pts
                except Exception as e:
                    out["variety_error"] = str(e)
            print(json.dumps(out))
