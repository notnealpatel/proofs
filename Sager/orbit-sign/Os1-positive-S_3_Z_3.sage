import json
K.<sqrt3> = QuadraticField(3)
R = PolynomialRing(K, 5, "x0,x1,x2,x3,x4")
x0,x1,x2,x3,x4 = R.gens()
gens = [
  (-5832) + (648)*x1*x1*x1 + (648)*x4*x4*x4,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (-64) + (64)*x0*x0*x0 + (24)*x2*x2*x2 + (72)*x2*x2*x3 + (72)*x2*x3*x3 + (24)*x3*x3*x3,
  (192) + (-96)*x0*x0*x1 + (72)*x2*x2*x4 + (144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (24)*x2*x2*x2 + (-24)*x2*x2*x3 + (-24)*x2*x3*x3 + (24)*x3*x3*x3,
  (-288) + (72)*x2*x2*x4 + (-144)*x2*x3*x4 + (72)*x3*x3*x4,
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
