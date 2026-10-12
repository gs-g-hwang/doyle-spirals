"""fig12_bds_sector.py — Figure: the quadratic family in the parameter plane of
Beardon, Dubejko and Stephenson (1994).

Their spirals P_A are parametrized by A in the sector 0 <= arg A <= pi/6
outside the hexagon of circumradius 4 (condition (11)); A in the lattice
H = Z w1 + Z w3 (w1 = 1 - sqrt3 i, w3 = 1 + sqrt3 i) gives the coherent
spirals, A = p w1 + q w3 with 1 <= p <= q <= 2p (their Table I).
Section 7 shows that the quadratic family A=B^2 is the boundary ray
arg A = pi/6, A = t (3 + sqrt3 i) with t = pi/psi(B) > 1; the resonant B_n
are t = n (BDS parameter (n,2n)); the golden case is t = 3.91148 (not in H).
The other boundary ray, arg A = 0 (p = q), is the 'ring' family.
"""
import math
import doylefig as D

s3 = math.sqrt(3)
w1, w3 = complex(1, -s3), complex(1, s3)
fig, ax = D.plt.subplots(figsize=(8.6, 4.4))
ax.set_aspect("equal")
# lattice points of H in the sector
for p in range(1, 13):
    for q in range(p, 2 * p + 1):
        A = p * w1 + q * w3
        if A.real > 31: continue
        ax.scatter(A.real, A.imag, s=9, color="#9AA3AE", zorder=2)
# sector boundaries and excluded hexagon
R = 31.5
ax.plot([0, R], [0, 0], color=D.SLATE, lw=1.2)
ax.plot([0, R * math.cos(math.pi / 6)], [0, R * math.sin(math.pi / 6)], color=D.GOLD, lw=2.0)
hexv = [4 * complex(math.cos(k * math.pi / 3), math.sin(k * math.pi / 3)) for k in range(7)]
ax.plot([h.real for h in hexv], [h.imag for h in hexv], color=D.INK, lw=0.8, ls="--")
# quadratic family resonant points t = n and the golden point
for n in range(2, 10):
    A = n * complex(3, s3)
    ax.scatter(A.real, A.imag, s=26, color=D.GOLD, zorder=4)
    ax.annotate(f"$B_{n}$", (A.real, A.imag), textcoords="offset points",
                xytext=(-4, 7), fontsize=8, color=D.GOLD)
tg = math.pi / (2 * math.atan((D.PHI - 1) / (D.PHI + 1) * math.sqrt((D.PHI**2 + D.PHI + 1) / D.PHI)))
Ag = tg * complex(3, s3)
ax.scatter(Ag.real, Ag.imag, s=90, marker="*", color=D.OVERLAP, zorder=5)
ax.annotate(r"golden, $t\approx3.911$", (Ag.real, Ag.imag), textcoords="offset points",
            xytext=(-118, 8), fontsize=9, color=D.OVERLAP)
# BDS Table I examples
table = {"Fig. 1": (4, 6), "6(a)": (2, 4), "6(b)": (7, 7), "6(c)": (9, 18),
         "6(d)": (6, 9), "6(e)": (8, 12), "6(f)": (7, 8)}
for name, (p, q) in table.items():
    A = p * w1 + q * w3
    ax.scatter(A.real, A.imag, s=46, facecolors="none", edgecolors=D.DIAG2, lw=1.4, zorder=6)
    ax.annotate(f"{name} $[{p},{q}]$", (A.real, A.imag), textcoords="offset points",
                xytext=(5, -11 if name in ("6(a)", "6(c)") else 4), fontsize=7.5, color=D.DIAG2)
ax.text(12.6, 11.2, r"quadratic family $\arg\mathfrak{A}=\pi/6$", color=D.GOLD, fontsize=9, rotation=27)
ax.text(18, -1.6, r"ring family $\arg\mathfrak{A}=0$ ($[\mathfrak{p},\mathfrak{p}]$)", color=D.SLATE, fontsize=9)
ax.set_xlim(-4.5, 33); ax.set_ylim(-3, 18.5)
ax.set_xlabel(r"$\mathrm{Re}\,\mathfrak{A}$"); ax.set_ylabel(r"$\mathrm{Im}\,\mathfrak{A}$")
for sp in ("top", "right"): ax.spines[sp].set_visible(False)
D.save(fig, "fig12_bds_sector")
