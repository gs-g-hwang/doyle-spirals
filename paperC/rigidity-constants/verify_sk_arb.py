"""Independent re-verification of Proposition C 5.1 (s_2 > 14.8376, s_3 > 3.7317) in Arb
ball arithmetic (python-flint), as a cross-check of verify_sk.py (mpmath intervals).

Shared with verify_sk.py: only the certificate (sk_best_k{k}.npy: double-precision log radii,
central radius 1) and the combinatorics of the k-ring patch (sk_optimize.setup).
Independent: the arithmetic library (Arb instead of mpmath.iv), the angle formula
theta = 2 atan(sqrt(yz/(x s))) instead of 2 atan2(sqrt(yz), sqrt(x s)), the Newton refinement
(Arb midpoints), the Krawczyk operator (Arb matrices) and the layout.

Steps:
 1. Boundary radii: exact binary rationals (the double-precision values of the certificate).
 2. Krawczyk test: the box m +- eps (eps = 1e-30) around the Newton solution m of
    F_v = (angle sum at interior vertex v) - 2 pi = 0 contains a unique zero.
 3. Layout of the centers in ball arithmetic, adding cell angles around each interior vertex.
 4. Every non-adjacent pair: lower bound of |z_i - z_j|^2 > upper bound of (r_i + r_j)^2.
    Lower bound for rho = r(1,0)/r(0,0).
Usage: python verify_sk_arb.py [k]   (k = 2 or 3)
"""
import sys
import numpy as np
from flint import arb, arb_mat, ctx
import sk_optimize as S

ctx.prec = 240                      # about 72 decimal digits
k = int(sys.argv[1]) if len(sys.argv) > 1 else 2
pts, idx, edges, interior, nonadj, place = S.setup(k)
x = np.load(f"sk_best_k{k}.npy")
lr0 = [0.0] + list(x)
bnd = [i for i in range(len(pts)) if i not in interior]
nbrs = {v: [idx[(pts[v][0] + d[0], pts[v][1] + d[1])] for d in S.DIRS] for v in interior}
n = len(interior)
pos = {i: j for j, i in enumerate(interior)}

# 1. exact boundary radii: the binary64 value converts to an exact Arb number
Rb = {i: arb(float(np.exp(lr0[i]))) for i in bnd}
for i in bnd:
    assert Rb[i].rad() == 0


def radii(vals):
    R = dict(Rb)
    for j, i in enumerate(interior):
        R[i] = vals[j].exp()
    return R


def theta(X, Y, Z):
    return 2 * (Y * Z / (X * (X + Y + Z))).sqrt().atan()


def dtheta(X, Y, Z):
    s = X + Y + Z
    u = Y * Z / (X * s)
    su = u.sqrt()
    return (-su * (1 + X / s) / (1 + u), su * (1 - Y / s) / (1 + u), su * (1 - Z / s) / (1 + u))


def F(vals):
    R = radii(vals)
    out = []
    for v in interior:
        s = arb(0)
        for t in range(6):
            a, b = nbrs[v][t], nbrs[v][(t + 1) % 6]
            s += theta(R[v], R[a], R[b])
        out.append(s - 2 * arb.pi())
    return out


def J(vals):
    R = radii(vals)
    M = [[arb(0) for _ in range(n)] for _ in range(n)]
    for r_, v in enumerate(interior):
        for t in range(6):
            a, b = nbrs[v][t], nbrs[v][(t + 1) % 6]
            for node, dd in zip((v, a, b), dtheta(R[v], R[a], R[b])):
                if node in pos:
                    M[r_][pos[node]] += dd
    return arb_mat(M)


# 2a. Newton refinement on midpoints
m = [arb(float(lr0[i])) for i in interior]
for it in range(80):
    Fm = F(m)
    step = J(m).solve(arb_mat([[f] for f in Fm]))
    m = [(m[j] - step[j, 0]).mid() for j in range(n)]
    if max(abs(float(f.mid())) for f in Fm) < 1e-60:
        break
res = max(abs(f) for f in F(m))
print(f"k={k}: n={n} interior unknowns, Newton residual < {float(res.upper()):.2e}")

# 2b. Krawczyk test on the box m +- eps
eps = arb("1e-30")
Xbox = [arb(mj, eps) for mj in m]
Jm = J(m)
C = arb_mat([[Jm.inv()[i, j].mid() for j in range(n)] for i in range(n)])  # exact midpoints
Fm = arb_mat([[f] for f in F(m)])
JX = J(Xbox)
I = arb_mat([[1 if i == j else 0 for j in range(n)] for i in range(n)])
D = arb_mat([[Xbox[j] - m[j]] for j in range(n)])
K = arb_mat([[mj] for mj in m]) - C * Fm + (I - C * JX) * D
inside = all(Xbox[i].contains_interior(K[i, 0]) for i in range(n))
print("Krawczyk K(X) inside int(X):", inside)
assert inside

# 3. layout of the centers (the true radii lie in the box)
R = radii(Xbox)
zc = {0: (arb(0), arb(0))}
direction = {0: (idx[(1, 0)], arb(0))}
queue, done = [0], set()
while queue:
    v = queue.pop(0)
    if v in done:
        continue
    done.add(v)
    nb = nbrs[v]
    j0 = nb.index(direction[v][0])
    ph = direction[v][1]
    for t in range(6):
        jj = (j0 + t) % 6
        w = nb[jj]
        if w not in zc:
            d = R[v] + R[w]
            zc[w] = (zc[v][0] + d * ph.cos(), zc[v][1] + d * ph.sin())
        if w in interior and w not in direction:
            direction[w] = (v, ph + arb.pi())
            queue.append(w)
        a, b = nb[jj], nb[(jj + 1) % 6]
        ph = ph + theta(R[v], R[a], R[b])
assert len(zc) == len(pts)

# 4. disjointness of the non-adjacent pairs and the bound for rho
worst = None
for i, j in nonadj:
    dx = zc[i][0] - zc[j][0]
    dy = zc[i][1] - zc[j][1]
    d2 = dx * dx + dy * dy
    rs2 = (R[i] + R[j]) ** 2
    assert d2.lower() > rs2.upper(), (pts[i], pts[j])
    rel = float(((d2.lower() - rs2.upper()) / rs2.upper()).lower())
    worst = rel if worst is None else min(worst, rel)
rho = R[idx[(1, 0)]] / R[0]
print(f"k={k}: all {len(nonadj)} non-adjacent pairs disjoint; min relative margin {worst:.3e}")
print(f"rho in [{rho.lower().str(16, radius=False)}, {rho.upper().str(16, radius=False)}]"
      f"  =>  s_{k} >= {(rho.lower() - 1).str(10, radius=False)}")
