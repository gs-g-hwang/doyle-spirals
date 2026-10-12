"""Interval-arithmetic verification of the bounds s_2 > 14.8376 and s_3 > 3.7317.

Input: the optimizer's k-ring packing (sk_best_k{k}.npy, log radii of all circles,
central radius 1). Procedure:
 1. Fix the boundary radii as exact binary rationals (the double-precision values).
 2. Interior log-radii v solve F(v) = 0, F_i = (angle sum at interior vertex i) - 2*pi.
    Refine a high-precision approximation by Newton's method, then prove that a box
    X around it contains a unique zero with the Krawczyk test
        K(X) = m - C F(m) + (I - C J(X)) (X - m)  contained in int(X),
    where J(X) is an interval enclosure of the Jacobian (explicit formulas below).
 3. Lay out the packing in interval arithmetic: around each interior vertex the
    directions to its neighbours are obtained by adding the cell angles.
 4. Verify: every pair of non-adjacent circles has (lower bound of distance^2) >
    (upper bound of (r_i+r_j)^2); report a rigorous lower bound for
    rho = r(1,0)/r(0,0).
Angle at the vertex of radius x in a triangle of tangent circles x,y,z:
    theta = 2 atan( sqrt(yz) / sqrt(x s) ),  s = x+y+z  (Lemma 3.3),
    d theta / d log x = -sqrt(u)(1+x/s)/(1+u),  d theta / d log y = sqrt(u)(1-y/s)/(1+u),
    u = yz/(x s).
"""
import sys
import numpy as np
from mpmath import mp, mpf, iv, matrix, lu_solve
import sk_optimize as S

mp.dps = 60
iv.dps = 60
k = int(sys.argv[1]) if len(sys.argv) > 1 else 2
pts, idx, edges, interior, nonadj, place = S.setup(k)
x = np.load(f"sk_best_k{k}.npy")
lr0 = [0.0] + list(x)                      # double-precision log radii (central = 0)
bnd = [i for i in range(len(pts)) if i not in interior]
nbrs = {}
for v in interior:
    u = pts[v]
    nbrs[v] = [idx[(u[0] + d[0], u[1] + d[1])] for d in S.DIRS]


def theta(X, Y, Z, ctx):
    s = X + Y + Z
    return 2 * ctx.atan2(ctx.sqrt(Y * Z), ctx.sqrt(X * s))


def dtheta(X, Y, Z, ctx):
    s = X + Y + Z
    u = Y * Z / (X * s)
    su = ctx.sqrt(u)
    return (-su * (1 + X / s) / (1 + u), su * (1 - Y / s) / (1 + u), su * (1 - Z / s) / (1 + u))


# boundary radii: exact binary rationals
Rb = {i: mpf(float(np.exp(lr0[i]))) for i in bnd}


def radii(vals, ctx):
    R = {}
    for i in bnd:
        R[i] = ctx.mpf(Rb[i])
    for j, i in enumerate(interior):
        R[i] = ctx.exp(vals[j])
    return R


def F(vals, ctx):
    R = radii(vals, ctx)
    out = []
    for v in interior:
        s = 0
        for t in range(6):
            a, b = nbrs[v][t], nbrs[v][(t + 1) % 6]
            s = s + theta(R[v], R[a], R[b], ctx)
        out.append(s - 2 * ctx.pi)
    return out


def J(vals, ctx):
    R = radii(vals, ctx)
    n = len(interior)
    pos = {i: j for j, i in enumerate(interior)}
    M = [[ctx.mpf(0) for _ in range(n)] for _ in range(n)]
    for r_, v in enumerate(interior):
        for t in range(6):
            a, b = nbrs[v][t], nbrs[v][(t + 1) % 6]
            dv, da, db = dtheta(R[v], R[a], R[b], ctx)
            for node, dd in ((v, dv), (a, da), (b, db)):
                if node in pos:
                    M[r_][pos[node]] = M[r_][pos[node]] + dd
    return M


# 1. high-precision Newton for the interior log radii
m = [mpf(float(lr0[i])) for i in interior]
for it in range(60):
    Fm = F(m, mp)
    Jm = J(m, mp)
    step = lu_solve(matrix(Jm), matrix(Fm))
    m = [m[j] - step[j] for j in range(len(m))]
    if max(abs(f) for f in Fm) < mpf(10) ** (-50):
        break
print("Newton residual", mp.nstr(max(abs(f) for f in F(m, mp)), 5))

# 2. Krawczyk test on the box m +- eps
n = len(interior)
eps = mpf(10) ** (-30)
Xbox = [iv.mpf([m[j] - eps, m[j] + eps]) for j in range(n)]
C = matrix(J(m, mp)) ** -1
Fm_iv = F([iv.mpf(mj) for mj in m], iv)
JX = J(Xbox, iv)
K = []
for i in range(n):
    acc = iv.mpf(m[i])
    for j in range(n):
        acc = acc - iv.mpf(C[i, j]) * Fm_iv[j]
    for j in range(n):
        cij = (1 if i == j else 0) - sum(iv.mpf(C[i, l]) * JX[l][j] for l in range(n))
        acc = acc + cij * (Xbox[j] - iv.mpf(m[j]))
    K.append(acc)
inside = all(K[i].a > Xbox[i].a and K[i].b < Xbox[i].b for i in range(n))
print("Krawczyk K(X) inside int(X):", inside)
assert inside

# 3. interval layout (true radii lie in the box)
R = radii(Xbox, iv)
zc = {0: (iv.mpf(0), iv.mpf(0))}
direction = {0: (idx[(1, 0)], iv.mpf(0))}     # vertex -> (neighbour index, direction to it)
queue = [0]
done = set()
while queue:
    v = queue.pop(0)
    if v in done:
        continue
    done.add(v)
    nb = nbrs[v]
    j0 = nb.index(direction[v][0])
    phi = direction[v][1]
    for t in range(6):
        jj = (j0 + t) % 6
        w = nb[jj]
        if w not in zc:
            d = R[v] + R[w]
            zc[w] = (zc[v][0] + d * iv.cos(phi), zc[v][1] + d * iv.sin(phi))
        if w in interior and w not in direction:
            direction[w] = (v, phi + iv.pi)
            queue.append(w)
        a, b = nb[jj], nb[(jj + 1) % 6]
        phi = phi + theta(R[v], R[a], R[b], iv)
assert len(zc) == len(pts)

# 4. verify disjointness of non-adjacent pairs and bound rho
worst = None
for i, j in nonadj:
    dx = zc[i][0] - zc[j][0]
    dy = zc[i][1] - zc[j][1]
    d2 = dx * dx + dy * dy
    rs = R[i] + R[j]
    margin = d2.a - (rs * rs).b
    rel = margin / (rs * rs).b
    if worst is None or rel < worst:
        worst = rel
    assert margin > 0, (pts[i], pts[j])
rho = R[idx[(1, 0)]] / R[0]
print(f"k={k}: all {len(nonadj)} non-adjacent pairs verified disjoint; "
      f"min relative margin of d^2-(ri+rj)^2: {mp.nstr(worst, 4)}")
print(f"rho in [{mp.nstr(rho.a, 12)}, {mp.nstr(rho.b, 12)}]  =>  s_{k} >= {mp.nstr(rho.a - 1, 10)}")
