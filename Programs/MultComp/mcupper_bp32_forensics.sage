# mcupper_bp32_forensics.sage
# MCUPPER Step 0: forensics on the Boyar-Matthews-Peralta 32-AND AES S-box
# circuit (J. Cryptology 26 (2013), Figs. 10/11/12; ePrint 2009/191).
# Transcribed verbatim from References/doi-10-1007-s00145-012-9124-7/paper.txt
# lines 1664-1822.
#
# Tests:
#   T1  full circuit == AES S-box on all 256 inputs (auto-detect bit order)
#   T2  syntactic cut checks: output stage reads ONLY {t29,t33,t37,t40} + y's/x7;
#       inverter reads only t21..t24 + internal; M1 stage ANDs are (x-lin)x(x-lin)
#   T3  rank of the 256x32 matrix { x_bits (x) tensor T*(x)_bits } over GF(2)
#       (T* = inverter output wires).  rank 32  <=>  any bilinear-in-(x,T)
#       output stage is uniquely determined by its values on the realizable set
#   T4  inverter block (t21..t24) -> (t29,t33,t37,t40) is linearly equivalent
#       to inversion on GF(16): exists psi_in, psi_out in GL(4,2) with
#       psi_out o J = inv o psi_in;  also report single-basis solutions
#
# Deterministic; no randomness.

import itertools

# ---------- gate lists (verbatim transcription) ----------
# format: name -> (op, in1, in2); op in {'+', '*', 'n'}  ('n' = XNOR)

TOP = {
 't0':('+','x1','x2'),  't1':('+','x4','y12'),
 'y1':('+','t0','x7'),  'y2':('+','y1','x0'),  'y3':('+','y5','y8'),
 'y4':('+','y1','x3'),  'y5':('+','y1','x6'),  'y6':('+','y15','x7'),
 'y7':('+','x7','y11'), 'y8':('+','x0','x5'),  'y9':('+','x0','x3'),
 'y10':('+','y15','t0'),'y11':('+','y20','y9'),'y12':('+','y13','y14'),
 'y13':('+','x0','x6'), 'y14':('+','x3','x5'), 'y15':('+','t1','x5'),
 'y16':('+','t0','y11'),'y17':('+','y10','y11'),'y18':('+','x0','y16'),
 'y19':('+','y10','y8'),'y20':('+','t1','x1'), 'y21':('+','y13','y16'),
}

MIDDLE = {
 't2':('*','y12','y15'), 't3':('*','y3','y6'),   't4':('+','t3','t2'),
 't5':('*','y4','x7'),   't6':('+','t5','t2'),   't7':('*','y13','y16'),
 't8':('*','y5','y1'),   't9':('+','t8','t7'),   't10':('*','y2','y7'),
 't11':('+','t10','t7'), 't12':('*','y9','y11'), 't13':('*','y14','y17'),
 't14':('+','t13','t12'),'t15':('*','y8','y10'), 't16':('+','t15','t12'),
 't17':('+','t4','t14'), 't18':('+','t6','t16'), 't19':('+','t9','t14'),
 't20':('+','t11','t16'),'t21':('+','t17','y20'),'t22':('+','t18','y19'),
 't23':('+','t19','y21'),'t24':('+','t20','y18'),
 't25':('+','t21','t22'),'t26':('*','t21','t23'),'t27':('+','t24','t26'),
 't28':('*','t25','t27'),'t29':('+','t28','t22'),'t30':('+','t23','t24'),
 't31':('+','t22','t26'),'t32':('*','t31','t30'),'t33':('+','t32','t24'),
 't34':('+','t23','t33'),'t35':('+','t27','t33'),'t36':('*','t24','t35'),
 't37':('+','t36','t34'),'t38':('+','t27','t36'),'t39':('*','t29','t38'),
 't40':('+','t25','t39'),
 't41':('+','t40','t37'),'t42':('+','t29','t33'),'t43':('+','t29','t40'),
 't44':('+','t33','t37'),'t45':('+','t42','t41'),
 'z0':('*','t44','y15'), 'z1':('*','t37','y6'),  'z2':('*','t33','x7'),
 'z3':('*','t43','y16'), 'z4':('*','t40','y1'),  'z5':('*','t29','y7'),
 'z6':('*','t42','y11'), 'z7':('*','t45','y17'), 'z8':('*','t41','y10'),
 'z9':('*','t44','y12'), 'z10':('*','t37','y3'), 'z11':('*','t33','y4'),
 'z12':('*','t43','y13'),'z13':('*','t40','y5'), 'z14':('*','t29','y2'),
 'z15':('*','t42','y9'), 'z16':('*','t45','y14'),'z17':('*','t41','y8'),
}

BOTTOM = {
 't46':('+','z15','z16'),'t47':('+','z10','z11'),'t48':('+','z5','z13'),
 't49':('+','z9','z10'), 't50':('+','z2','z12'), 't51':('+','z2','z5'),
 't52':('+','z7','z8'),  't53':('+','z0','z3'),  't54':('+','z6','z7'),
 't55':('+','z16','z17'),'t56':('+','z12','t48'),'t57':('+','t50','t53'),
 't58':('+','z4','t46'), 't59':('+','z3','t54'), 't60':('+','t46','t57'),
 't61':('+','z14','t57'),'t62':('+','t52','t58'),'t63':('+','t49','t58'),
 't64':('+','z4','t59'), 't65':('+','t61','t62'),'t66':('+','z1','t63'),
 't67':('+','t64','t65'),
 's0':('+','t59','t63'), 's1':('n','t64','s3'),  's2':('n','t55','t67'),
 's3':('+','t53','t66'), 's4':('+','t51','t66'), 's5':('+','t47','t65'),
 's6':('n','t56','t62'), 's7':('n','t48','t60'),
}

GATES = {}
GATES.update(TOP); GATES.update(MIDDLE); GATES.update(BOTTOM)

def evaluate(inputs, override=None, gates=GATES):
    """inputs: dict x0..x7 -> 0/1.  override: dict wire -> 0/1 (cut injection)."""
    val = dict(inputs)
    if override: val.update(override)
    def ev(w):
        if w in val: return val[w]
        op, u, v = gates[w]
        a, b = ev(u), ev(v)
        r = (a & b) if op == '*' else (a ^^ b) if op == '+' else (1 ^^ a ^^ b)
        val[w] = r
        return r
    return ev, val

def run_circuit(n, in_msb0, out_msb0):
    bits = [(n >> i) & 1 for i in range(8)]           # bits[i] = coeff of x^i
    if in_msb0: xs = {('x%d' % i): bits[7 - i] for i in range(8)}
    else:       xs = {('x%d' % i): bits[i] for i in range(8)}
    ev, _ = evaluate(xs)
    ss = [ev('s%d' % i) for i in range(8)]
    if out_msb0: return sum(ss[i] << (7 - i) for i in range(8))
    else:        return sum(ss[i] << i for i in range(8))

# ---------- reference AES S-box (FIPS-197) ----------
R.<X> = GF(2)[]
K8.<g> = GF(2^8, modulus=X^8 + X^4 + X^3 + X + 1)
def byte_to_f(n): return K8(sum(((n >> i) & 1) * X^i for i in range(8)))
def f_to_byte(e): return sum(int(c) << i for i, c in enumerate(e.polynomial().coefficients(sparse=False))) if e else 0
def aes_sbox(n):
    v = byte_to_f(n)
    inv = f_to_byte(v^254) if n else 0
    b = [(inv >> i) & 1 for i in range(8)]
    c = 0x63
    return sum(((b[i] ^^ b[(i+4)%8] ^^ b[(i+5)%8] ^^ b[(i+6)%8] ^^ b[(i+7)%8] ^^ ((c >> i) & 1)) << i) for i in range(8))
assert aes_sbox(0x00) == 0x63 and aes_sbox(0x01) == 0x7c and aes_sbox(0x53) == 0xed

# ---------- T1: full-circuit verification, bit-order autodetect ----------
print("== T1: full circuit vs AES S-box ==")
match = None
for in_m in [True, False]:
    for out_m in [True, False]:
        ok = all(run_circuit(n, in_m, out_m) == aes_sbox(n) for n in range(256))
        print("  in_msb0=%-5s out_msb0=%-5s -> %s" % (in_m, out_m, "MATCH (all 256)" if ok else "no"))
        if ok: match = (in_m, out_m)
print("T1 RESULT:", "PASS convention=%s" % (match,) if match else "FAIL")
assert match is not None
IN_MSB0, OUT_MSB0 = match

# ---------- T2: syntactic cut checks ----------
print("== T2: syntactic structure ==")
IFACE = ['t29', 't33', 't37', 't40']       # inverter output wires
DIN   = ['t21', 't22', 't23', 't24']       # inverter input wires
XLIN  = set(TOP.keys()) | {'x%d' % i for i in range(8)}   # linear in x

def support(w, stop):
    """transitive fan-in of wire w, stopping at wires in `stop`."""
    seen = set()
    def go(u):
        if u in seen or u in stop: return
        seen.add(u)
        if u in GATES:
            op, a, b = GATES[u]
            go(a); go(b)
    go(w)
    return seen

# 2a: output stage (t41..t45, z*, bottom, s*) reads only IFACE + x-linear wires
stage_wires = ['t4%d' % i for i in range(1, 6)] + ['z%d' % i for i in range(18)] + list(BOTTOM.keys())
viol = []
for w in stage_wires:
    sup = support(w, stop=set(IFACE))
    bad = [u for u in sup if u in MIDDLE and u not in stage_wires and u not in IFACE]
    if bad: viol.append((w, bad))
print("  2a output stage cut clean (reads only IFACE + linear-in-x):", "PASS" if not viol else ("FAIL %s" % viol))

# 2b: every z-gate is (span{IFACE}) x (x-linear)
def lin_over(w, basis):
    """w is an XOR-combination of `basis` wires (treating basis as atoms)?"""
    if w in basis or w in XLIN: return True
    if w not in GATES: return False
    op, a, b = GATES[w]
    return op == '+' and lin_over(a, basis) and lin_over(b, basis)
ok2b = True
for i in range(18):
    op, a, b = MIDDLE['z%d' % i]
    tside = a if a.startswith('t') else b
    yside = b if a.startswith('t') else a
    tok = lin_over(tside, set(IFACE)) and not (support(tside, set(IFACE)) & XLIN)
    yok = yside in XLIN
    if not (op == '*' and tok and yok): ok2b = False
print("  2b all 18 z-gates bilinear (IFACE-lin) x (x-lin):", "PASS" if ok2b else "FAIL")

# 2c: inverter block reads only DIN; M1 ANDs are (x-lin)x(x-lin)
inv_wires = ['t%d' % i for i in range(25, 41)]
ok2c = all(not (support(w, set(DIN)) - set(inv_wires)) for w in inv_wires)
print("  2c inverter reads only t21..t24:", "PASS" if ok2c else "FAIL")
m1_ands = ['t2','t3','t5','t7','t8','t10','t12','t13','t15']
ok2d = all(MIDDLE[w][0] == '*' and MIDDLE[w][1] in XLIN and MIDDLE[w][2] in XLIN for w in m1_ands)
print("  2d M1 ANDs all (x-lin)x(x-lin):", "PASS" if ok2d else "FAIL")
nand = len([w for w in MIDDLE if MIDDLE[w][0] == '*'])
print("  2e AND count in middle section:", nand, "(expect 32)")
assert nand == 32

# ---------- T3: bilinear-rigidity rank test ----------
print("== T3: rank of {x tensor T*(x)} over GF(2) ==")
Tstar = {}
Dstar = {}
for n in range(256):
    bits = [(n >> i) & 1 for i in range(8)]
    if IN_MSB0: xs = {('x%d' % i): bits[7 - i] for i in range(8)}
    else:       xs = {('x%d' % i): bits[i] for i in range(8)}
    ev, _ = evaluate(xs)
    Tstar[n] = tuple(ev(w) for w in IFACE)
    Dstar[n] = tuple(ev(w) for w in DIN)
rows = []
for n in range(256):
    xb = [(n >> i) & 1 for i in range(8)]
    tb = Tstar[n]
    rows.append([xb[i] * tb[j] for i in range(8) for j in range(4)])
Mrk = matrix(GF(2), rows)
rk = Mrk.rank()
print("  rank = %d of 32" % rk)
print("T3 RESULT:", "FULL RANK - bilinear stage uniquely determined by realizable set"
      if rk == 32 else "RANK DEFICIT %d - bilinear don't-care freedom exists" % (32 - rk))

# also: rank of realizable D-side (sanity: which (x,T) pairs occur)
print("  |{T*(x): x}| =", len(set(Tstar.values())), " (expect 16: all of GF(2)^4)")
print("  |{D*(x): x}| =", len(set(Dstar.values())))

# ---------- T4: inverter linearly equivalent to GF(16) inversion? ----------
print("== T4: inverter block vs GF(16) inversion (linear equivalence) ==")
# J: 4-bit -> 4-bit, from DIN to IFACE, simulated standalone
Jmap = {}
for v in range(16):
    ov = {DIN[i]: (v >> i) & 1 for i in range(4)}
    ev, _ = evaluate({}, override=ov)
    Jmap[v] = sum(ev(IFACE[i]) << i for i in range(4))
print("  J bijective:", sorted(Jmap.values()) == list(range(16)), "; J(0) =", Jmap[0])

K4.<w4> = GF(16, modulus=X^4 + X + 1)
elts = {n: K4(sum(((n >> i) & 1) * X^i for i in range(4))) for n in range(16)}
def n_of(e):
    if e == 0: return 0
    cs = e.polynomial().coefficients(sparse=False)
    return sum(int(c) << i for i, c in enumerate(cs))
INV = {n: (n_of(elts[n]^14) if n else 0) for n in range(16)}

# psi_in over GL(4,2): psi_out := inv o psi_in o J^{-1} must be linear
Jinv = {v: k for k, v in Jmap.items()}
GL_count = 0; sols = 0; single_basis = 0
example = None
Vs = list(range(16))
from itertools import permutations
def all_gl42():
    # enumerate invertible 4x4 GF(2) matrices as basis images (b1,b2,b4,b8)
    for b1 in range(1, 16):
        for b2 in range(1, 16):
            if b2 == b1: continue
            s2 = {0, b1, b2, b1 ^^ b2}
            for b4 in range(1, 16):
                if b4 in s2: continue
                s3 = s2 | {x ^^ b4 for x in s2}
                for b8 in range(1, 16):
                    if b8 in s3: continue
                    yield (b1, b2, b4, b8)
def apply_lin(bs, v):
    r = 0
    for i in range(4):
        if (v >> i) & 1: r ^^= bs[i]
    return r
for bs in all_gl42():
    GL_count += 1
    # candidate psi_in: bit i -> bs[i];  compute F := psi_in^{-1}? we need:
    # psi_out(J(v)) = INV_field(psi_in(v)) as 4-bit codes in K4 coords
    # define target T(v) = INV[apply_lin(bs, v)]; require v -> T(Jinv[v]) linear... careful:
    # condition: psi_out o J = invF o psi_in, so psi_out(u) = invF(psi_in(Jinv[u])).
    img = [INV[apply_lin(bs, Jinv[u])] for u in range(16)]
    # linearity check: img[a^b] == img[a]^img[b], img[0]==0
    if img[0] != 0: continue
    lin = True
    for a in range(16):
        for b in range(16):
            if img[a ^^ b] != (img[a] ^^ img[b]): lin = False; break
        if not lin: break
    if lin:
        sols += 1
        if img == [apply_lin(bs, u) for u in range(16)]:
            # psi_out == psi_in? compare as maps on codes:  psi_out(u)=img[u], psi_in(u)=apply_lin(bs,u)
            single_basis += 1
        if example is None: example = (bs, img[1], img[2], img[4], img[8])
print("  GL(4,2) size enumerated:", GL_count, "(expect 20160)")
print("  linear-equivalence solutions (psi_in count):", sols)
print("  single-basis (psi_out == psi_in) solutions:", single_basis)
print("T4 RESULT:", "PASS - inverter IS GF(16) inversion up to linear encodings" if sols > 0 else "FAIL")

print("== forensics core done ==")
