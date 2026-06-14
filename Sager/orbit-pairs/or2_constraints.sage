# Or2: reconcile the Fourier constraint count.
# Two numbers in play:
#  (A) Or1's N = (1/24) sum chi_{rho⊗rho*}(g)^3 = #trivial subreps of (rho⊗rho*)^{⊗3}
#      under the DIAGONAL S_4 action.  Or1 got 31.
#  (B) GM's *operative* system for the single-orbit n=3 ansatz: 3 trace
#      conditions (uv-necessary) + 3 Fourier eqs (4std, 4anti-std, 4box).
# These count different things; clarify both.

# rho = standard 3-dim irrep of S_4. Character on classes:
#   class:      e   (ab)  (ab)(cd) (abc) (abcd)
#   size:       1    6      3        8      6
#   chi_rho:    3    1     -1        0     -1
sizes  = [1,6,3,8,6]
chirho = [3,1,-1,0,-1]
# rho⊗rho* character = chi_rho * conj(chi_rho); rho is real so = chi_rho^2
chi_rr = [c^2 for c in chirho]   # [9,1,1,0,1]
# Number of trivial subreps of (rho⊗rho*)^{⊗k} under diagonal S_4:
#   N_k = (1/|G|) sum_g chi_rr(g)^k
def Nk(k):
    return sum(s*ch^k for s,ch in zip(sizes,chi_rr)) / 24
for k in [1,2,3]:
    print(f"N_{k} = (1/24) sum size*chi_rr^{k} =", Nk(k))

# Decompose rho⊗rho* into S_4 irreps to label the trivial copies.
# S_4 irreps: triv(1), sign(1), std-2dim 'box'(2), std(3)=rho, antistd(3)=rho'
# character table rows (on the 5 classes above):
chars = {
 'triv': [1,1,1,1,1],
 'sign': [1,-1,1,1,-1],
 'box':  [2,0,2,-1,0],
 'rho':  [3,1,-1,0,-1],
 'rhop': [3,-1,-1,0,1],
}
def inner(a,b):
    return sum(s*x*y for s,x,y in zip(sizes,a,b))/24
print("\nrho⊗rho* multiplicities:")
for name,ch in chars.items():
    print(f"  {name}: {inner(chi_rr,ch)}")
