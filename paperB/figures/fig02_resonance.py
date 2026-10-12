"""fig02_resonance.py — Figure: the golden configuration next to its resonant neighbor.

Purpose (Section 7.3, Proposition 7.5; Section 7.5, Theorem 7.14): in the quadratic family
the configuration closes up around X exactly when arg(beta) = pi/n. For n = 4
this happens at B_4 = 1.5996347..., just below phi (arg beta = 45 deg versus
46.018 deg). Left: B = B_4 with four rings -- the circles at (0,4) and (4,-4)
(highlighted) coincide and nothing overlaps. Right: the golden case B = phi --
the same two circles are rotated about X by 8(arg beta - 45 deg) = 8.15 deg
relative to each other and overlap (compare Figure 4).
"""
import math
import doylefig as D

B4 = 1.5996347174376842          # root of arg(beta(B)) = pi/4 (mpmath, 30 digits)
fig, axes = D.plt.subplots(1, 2, figsize=(11.5, 5.0))
for ax, B, title in ((axes[0], B4, r"$B=B_4\approx1.59963$, $\arg\beta=45^\circ$"),
                     (axes[1], D.PHI, r"$B=\varphi$, $\arg\beta\approx46.02^\circ$")):
    ax.set_aspect("equal"); ax.axis("off")
    cen, rad = D.build_config(B * B, B, 4)
    D.draw_circles(ax, cen, rad, lw=0.6, highlight=[(0, 4), (4, -4)])
    D.mark_X(ax, D.family_X(B), size=30)
    X = D.family_X(B)
    ax.set_xlim(X - 26, X + 18); ax.set_ylim(-22, 22)
    ax.set_title(title, fontsize=11)
D.save(fig, "fig02_resonance")
