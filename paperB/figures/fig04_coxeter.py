"""fig04_coxeter.py — Figure: the right-angle spiral D_{B_2} and Coxeter's spiral.

Purpose (Section 7.4, Proposition 7.10, Corollary 7.13): B_2 = phi + sqrt(phi) is Coxeter's
ratio. Left: D_{B_2}, recentered at X = -sqrt(phi); each (0,1)-step turns by
psi = 90 degrees about X (beta = i B_2), and the cell triangle with radii
1, B, B^2 is shaded. Right: Coxeter's loxodromic sequence, i.e. the Doyle
spiral with (A,B) = (k^2, k^3), k = phi + sqrt(phi); four consecutive circles
C_0..C_3 (radii 1, k, k^2, k^3) are mutually tangent, and the triangle of the
centers of C_0, C_1, C_2 (shaded) is congruent to the shaded cell triangle on
the left, by Lemma 3.3.
"""
import math, cmath
import doylefig as D
from matplotlib.patches import Circle, Polygon

k = D.PHI + math.sqrt(D.PHI)                 # = B_2
fig, axes = D.plt.subplots(1, 2, figsize=(11.5, 5.4))

# ---- left: D_{B_2} recentered at X
ax = axes[0]; ax.set_aspect("equal"); ax.axis("off")
X, beta = D.family_X(k), D.family_beta(k)
z = lambda p, q: D.closed_center(k, p, q, X, beta) - X
seen = []
for p in range(-6, 4):
    for q in range(-1, 3):                    # q = -1..2 covers one turn (period (-2,4))
        c, r = z(p, q), k ** (2 * p + q)
        if not (0.02 < abs(c) < 40): continue
        ax.add_patch(Circle((c.real, c.imag), r, fill=False, ec=D.INK, lw=0.6))
tri = [z(0, 0), z(0, 1), z(1, 0)]
ax.add_patch(Polygon([(w.real, w.imag) for w in tri], closed=True, fc=D.GOLD,
                     alpha=0.25, ec=D.GOLD, lw=1.4, zorder=4))
# Corollary 7.13: mirror image Q' of K(1,1) in the line through the centers of
# K(0,1) and K(1,0); together with the shaded triple it is Coxeter's quadruple.
P1, P0, Q = z(0, 1), z(1, 0), z(1, 1)
ud = (P0 - P1) / abs(P0 - P1)
Qm = P1 + ud * ((Q - P1) / ud).conjugate()
ax.add_patch(Circle((Qm.real, Qm.imag), k ** 3, fill=False, ec=D.OVERLAP,
                    lw=1.5, ls=(0, (5, 3)), zorder=5))
ax.text(-3.2, -4.6, "$Q'$ (radius $B^3$)", color=D.OVERLAP, fontsize=10)
for w in tri[:2]:
    ax.plot([0, w.real], [0, w.imag], color=D.DIAG1, lw=1.3, zorder=5)
s = 0.35                                     # right-angle mark at X
u0, u1 = tri[0] / abs(tri[0]), tri[1] / abs(tri[1])
pts = [s * u0, s * (u0 + u1), s * u1]
ax.plot([p.real for p in pts], [p.imag for p in pts], color=D.DIAG1, lw=1.0, zorder=5)
ax.scatter([0], [0], s=40, facecolors="none", edgecolors=D.GOLD, lw=1.6, zorder=6)
ax.scatter([0], [0], s=6, color=D.GOLD, zorder=6)
ax.annotate("$X$", (0, 0), textcoords="offset points", xytext=(-14, -12), color=D.GOLD, fontsize=12)
for w, lab in zip(tri, ["$1$", "$B$", "$B^2$"]):
    ax.text(w.real, w.imag, lab, ha="center", va="center", fontsize=10, zorder=7,
            bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.8))
ax.set_xlim(-4.5, 10.5); ax.set_ylim(-5.5, 6.5)
ax.set_title(r"$\mathcal{D}_{B_2}$, $B_2=\varphi+\sqrt{\varphi}$: $\psi=90^\circ$", fontsize=11)

# ---- right: Coxeter's spiral, Doyle parameters (A,B) = (k^2, k^3)
ax = axes[1]; ax.set_aspect("equal"); ax.axis("off")
cen, rad = D.build_config(k * k, k ** 3, 3)
drawn = []
for pt, c in cen.items():
    r = rad[pt]
    if any(abs(c - c2) < 1e-6 * r and abs(r - r2) < 1e-6 * r for c2, r2 in drawn):
        continue                              # coincident copies (coherent spiral)
    drawn.append((c, r))
C = {0: (0, 0), 1: (-1, 1), 2: (1, 0), 3: (0, 1)}  # radii 1, k, k^2, k^3
for m, pt in C.items():
    c, r = cen[pt], rad[pt]
for c, r in drawn:
    hi = any(abs(c - cen[pt]) < 1e-6 * r for pt in C.values())
    ax.add_patch(Circle((c.real, c.imag), r, fill=False,
                        ec=(D.OVERLAP if hi else D.INK), lw=(1.5 if hi else 0.6)))
tri = [cen[C[0]], cen[C[1]], cen[C[2]]]
ax.add_patch(Polygon([(w.real, w.imag) for w in tri], closed=True, fc=D.GOLD,
                     alpha=0.25, ec=D.GOLD, lw=1.4, zorder=4))
for m, pt in C.items():
    w = cen[pt]
    if m == 3:                                # center far outside: label on the arc
        w = w + rad[pt] * (cen[(0, 0)] - w) / abs(cen[(0, 0)] - w) * 1.0 + (-1.2 - 1.2j)
    ax.text(w.real, w.imag, f"$C_{m}$", ha="center", va="center", fontsize=10, zorder=7,
            bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.8))
xs = [c.real for c, r in drawn if r < 30]; ys = [c.imag for c, r in drawn if r < 30]
cx, cy = cen[(0, 0)].real, cen[(0, 0)].imag
ax.set_xlim(cx - 10, cx + 22); ax.set_ylim(cy - 14, cy + 14)
ax.set_title(r"Coxeter's sequence, ratio $\varphi+\sqrt{\varphi}$", fontsize=11)
D.save(fig, "fig04_coxeter")
print("check C1-C2 tangency:", abs(cen[(-1, 1)] - cen[(1, 0)]) - (k + k * k))
print("check C0-C3 tangency:", abs(cen[(0, 1)] - cen[(0, 0)]) - (1 + k ** 3))
