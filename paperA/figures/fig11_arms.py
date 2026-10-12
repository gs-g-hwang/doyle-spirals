"""fig11_arms.py — Figure: spiral polylines and arm counts.

Purpose (Section 7, Theorem 7.7): for the resonant members B = B_n of the
quadratic family the three families of polylines close up into
  n arms in direction (0,1)  (teal),
  n arms in direction (-1,1) (plum),
  2n straight rays in direction (1,0) (gold),
i.e. arm counts (n, 2n, n), Beardon-Dubejko-Stephenson parameters [n,2n].
One arm of each family is drawn thick. Right panel: the golden case, whose
arms never close up (psi/pi irrational, Corollary 7.8), so the drawn arms
cross each other.
Centers use the closed form z(p,q) = X + B^(2p) beta^q (0 - X)
(Proposition 5.4); the picture is recentered at X and shows an annulus.
Panels: B_6 (psi = 30 deg), B_4 (psi = 45 deg), phi (psi = 46.02 deg).
"""
import math
import doylefig as D

B6 = 1.3593473017938          # psi = pi/6
B4 = 1.5996347174376842       # psi = pi/4
panels = [(B6, r"$B=B_6$: arms $(6,12,6)$"),
          (B4, r"$B=B_4$: arms $(4,8,4)$"),
          (D.PHI, r"$B=\varphi$: arms do not close")]

fig, axes = D.plt.subplots(1, 3, figsize=(13.5, 4.8))
for ax, (B, title) in zip(axes, panels):
    ax.set_aspect("equal"); ax.axis("off")
    X, beta = D.family_X(B), D.family_beta(B)
    z = lambda p, q: D.closed_center(B, p, q, X, beta) - X   # recentered
    R_in, R_out = 0.12 * abs(X), 7.0 * abs(X)
    pts = [(p, q) for p in range(-30, 31) for q in range(-12, 13)
           if R_in <= abs(z(p, q)) <= R_out]
    S = set(pts)
    for (p, q) in pts:
        for d, col in (((1, 0), D.ROW), ((0, 1), D.DIAG1), ((-1, 1), D.DIAG2)):
            w = (p + d[0], q + d[1])
            if w in S:
                a, b = z(p, q), z(*w)
                ax.plot([a.real, b.real], [a.imag, b.imag], color=col,
                        lw=0.4, alpha=0.6, zorder=2)
    # one highlighted arm per family, followed through the annulus
    for d, col, start in (((1, 0), D.ROW, (0, 0)), ((0, 1), D.DIAG1, (0, 0)),
                          ((-1, 1), D.DIAG2, (0, 0))):
        chain = [start]
        for sgn in (1, -1):
            p, q = start
            while True:
                p, q = p + sgn * d[0], q + sgn * d[1]
                if (p, q) not in S: break
                if sgn == 1: chain.append((p, q))
                else: chain.insert(0, (p, q))
        xs = [z(*c).real for c in chain]; ys = [z(*c).imag for c in chain]
        ax.plot(xs, ys, color=col, lw=1.9, zorder=4, solid_capstyle="round")
    ax.scatter([0], [0], s=30, facecolors="none", edgecolors=D.GOLD, lw=1.4, zorder=6)
    ax.set_xlim(-R_out * 0.42, R_out * 0.42); ax.set_ylim(-R_out * 0.42, R_out * 0.42)
    ax.set_title(title, fontsize=11)
D.save(fig, "fig11_arms")
