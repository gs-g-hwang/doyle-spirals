"""Two triangle shapes, Doyle's pair, generic parameters.

Unknown: an integer exponent vector l(u) in Z^2 on the 2-ring ball (radius A^a B^b).
Each lattice triangle must carry the radius pattern of Doyle's up-shape
{(0,0),(1,0),(0,1)} or down-shape {(0,0),(0,1),(-1,1)} (up to translation,
any assignment of vertices), and the cell-triangle angles at every interior
vertex must sum to 2*pi for generic (A,B) (tested at two random pairs).
Question: is every solution an affine function of u (a Doyle radius function)?
"""
import math, itertools, random
DIRS = [(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
def norm(p,q): return max(abs(p),abs(q),abs(p+q))
M = 2
pts = sorted([(p,q) for p in range(-M,M+1) for q in range(-M,M+1) if norm(p,q)<=M],
             key=lambda u:(norm(*u), math.atan2(u[1]+u[0]*0.5, u[0]*0.8660254+1e-9*u[1])))
idx = {u:i for i,u in enumerate(pts)}
tris = []
for (p,q) in pts:
    for t in [((p,q),(p+1,q),(p,q+1)), ((p+1,q),(p+1,q-1+1-1+1),(p,q+1))]:
        pass
tris = set()
for (p,q) in pts:
    for a,b in [((1,0),(0,1)), ((0,1),(-1,1))]:
        tri = ((p,q),(p+a[0],q+a[1]),(p+b[0],q+b[1]))
        if all(v in idx for v in tri): tris.add(tri)
tris = list(tris)
SH = [frozenset({(0,0),(1,0),(0,1)}), frozenset({(0,0),(0,1),(-1,1)})]
def ok_tri(ls):
    for t in ls:
        s = frozenset((l[0]-t[0], l[1]-t[1]) for l in ls)
        if s in SH: return True
    return False
STEPS = [(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
interior = [u for u in pts if norm(*u) <= M-1]
random.seed(1)
PARS = [(1.3172, 1.7891), (0.6431, 2.2719)]
def ang(x,y,z):   # angle at the vertex of radius x
    return math.acos(((x+y)**2+(x+z)**2-(y+z)**2)/(2*(x+y)*(x+z)))
def anglesum_ok(l, v):
    tot = []
    for A,B in PARS:
        r = lambda u: A**l[u][0]*B**l[u][1]
        s = 0
        for i in range(6):
            d1, d2 = DIRS[i], DIRS[(i+1)%6]
            u1 = (v[0]+d1[0], v[1]+d1[1]); u2 = (v[0]+d2[0], v[1]+d2[1])
            s += ang(r(v), r(u1), r(u2))
        if abs(s-2*math.pi) > 1e-9: return False
    return True
order = pts
sols = []
l = {}
tri_of = {u:[t for t in tris if u in t] for u in pts}
def consistent(u):
    for t in tri_of[u]:
        if all(v in l for v in t) and not ok_tri([l[v] for v in t]): return False
    for v in interior:
        nb = [(v[0]+d[0], v[1]+d[1]) for d in DIRS]
        if v in l and all(w in l for w in nb) and u in nb+[v]:
            if not anglesum_ok(l, v): return False
    return True
def rec(i):
    if i == len(order):
        sols.append(dict(l)); return
    u = order[i]
    if i == 0:
        l[u] = (0,0); rec(1); del l[u]; return
    nbs = [w for w in order[:i] if (u[0]-w[0], u[1]-w[1]) in DIRS]
    w = nbs[0]
    for s in STEPS:
        l[u] = (l[w][0]+s[0], l[w][1]+s[1])
        if consistent(u): rec(i+1)
        del l[u]
rec(0)
def affine(L):
    a = L[(1,0)]; b = L[(0,1)]
    return all(L[(p,q)] == (p*a[0]+q*b[0], p*a[1]+q*b[1]) for (p,q) in pts)
print("solutions:", len(sols), " affine:", sum(affine(L) for L in sols))
for L in sols:
    print(" l(1,0)=", L[(1,0)], " l(0,1)=", L[(0,1)], " affine" if affine(L) else " NOT affine")
