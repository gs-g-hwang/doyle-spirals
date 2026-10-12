"""fig05_tilings.py — Figure: tilings of the punctured plane by similar triangles.

Purpose (Section 8, Theorem 8.6): the center triangulation of a coherent
hexagonal circle packing all of whose triangles are similar is, up to
similarity, the regular one or that of D_{B_n}, n >= 2. Shown: n = 3 and
n = 6, triangles shaded by orientation of the lattice triangle (the two
classes 'up' (u, u+(1,0), u+(0,1)) and 'down' (u, u+(0,1), u+(-1,1))),
recentered at the puncture X. All triangles in each panel are similar to
the cell triangle with half-angle cotangents proportional to 1 : B : B^2.
"""
import doylefig as D
from matplotlib.patches import Polygon

B3 = 1.9057818444840
B6 = 1.3593473017938
fig, axes = D.plt.subplots(1, 2, figsize=(10.5, 5.2))
for ax, B, n in ((axes[0], B3, 3), (axes[1], B6, 6)):
    ax.set_aspect("equal"); ax.axis("off")
    X, beta = D.family_X(B), D.family_beta(B)
    z = lambda p, q: D.closed_center(B, p, q, X, beta) - X
    R_in, R_out = 0.02 * abs(X), 40.0 * abs(X)
    for p in range(-40, 41):
        for q in range(0, 2 * n):           # one fundamental domain mod (-n,2n)
            for tri, col in ((((p, q), (p + 1, q), (p, q + 1)), "#E8D9B5"),
                             (((p, q), (p, q + 1), (p - 1, q + 1)), "#C9DDD9")):
                pts = [z(*t) for t in tri]
                if not all(R_in <= abs(w) <= R_out for w in pts):
                    continue
                ax.add_patch(Polygon([(w.real, w.imag) for w in pts], closed=True,
                                     fc=col, ec=D.INK, lw=0.35, zorder=2))
    ax.scatter([0], [0], s=16, color=D.GOLD, zorder=6)
    L = 1.15 * abs(X) * (3.0 if n == 3 else 2.2)
    ax.set_xlim(-L, L); ax.set_ylim(-L, L)
    ax.set_title(rf"$B=B_{n}\approx{B:.4f}$: ${n}$-fold symmetric tiling", fontsize=11)
D.save(fig, "fig05_tilings")
