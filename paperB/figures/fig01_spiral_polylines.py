"""fig01_spiral_polylines.py — Figure: spiral polylines of D_B for B = 5/4, recentered at X.

Purpose (Section 5, Remark 5.5, and the concluding remarks): extending the
non-straight polylines row by row produces arcs winding around X, with the
distance to X scaled by B per (0,1)-step. Implementation: instead of
propagating a huge hexagonal ball as the original did, the centers come from
the closed form of Proposition 5.4,

    z(p,q) = X + B^(2p) * beta^q * (0 - X),      |beta| = B,

so each arm can be followed as far in or out as the picture needs.
Improvements: the two arm families get the two arm colors (teal: S-orbits,
fixed p; plum: T^{-1}S-orbits, direction (-1,1)); X is marked; and one true
logarithmic spiral with multiplier beta (dashed gold) is overlaid on an
S-arm, visualizing the concluding remark that the polylines approximate
logarithmic spirals.
"""
import math
import cmath
import doylefig as D

B = 1.25
X = D.family_X(B)
beta = D.family_beta(B)
R0 = abs(X)                     # |z(0,0) - X|
RMIN, RMAX = 0.35, 190.0        # radial window around X for all arms

fig, ax = D.new_axes((6.6, 5.8))

# --- family 1 (teal): S-orbits, p fixed, q varying; |z-X| = R0 * B^(2p+q)
for p in range(-2, 4):
    qlo = math.floor(math.log(RMIN / R0, B)) - 2 * p
    qhi = math.ceil(math.log(RMAX / R0, B)) - 2 * p
    pts = [D.closed_center(B, p, q, X, beta) for q in range(qlo, qhi + 1)]
    pts = [z for z in pts if RMIN * 0.8 <= abs(z - X) <= RMAX * 1.05]
    ax.plot([z.real for z in pts], [z.imag for z in pts],
            color=D.DIAG1, lw=1.2, alpha=0.95, zorder=3)

# --- family 2 (plum): T^{-1}S-orbits, direction (-1,1): p = p0 - q
for p0 in range(-2, 4):
    pts = []
    for q in range(-40, 41):
        z = D.closed_center(B, p0 - q, q, X, beta)
        if RMIN * 0.8 <= abs(z - X) <= RMAX * 1.05:
            pts.append(z)
    ax.plot([z.real for z in pts], [z.imag for z in pts],
            color=D.DIAG2, lw=1.2, alpha=0.9, zorder=2)

# --- one true logarithmic spiral (dashed gold) through the p=0 S-arm:
#     w(t) = X + R0 * B^t * exp(i t arg(beta)),  matching z(0,t) at integers
targ = cmath.phase(beta)
ts, ws = [], []
t = math.log(RMIN / R0, B)
while t <= math.log(RMAX / R0, B):
    ws.append(X + R0 * (B ** t) * cmath.exp(1j * t * targ))
    t += 0.05
ax.plot([w.real for w in ws], [w.imag for w in ws],
        color=D.GOLD, lw=1.0, ls=(0, (5, 4)), alpha=0.8, zorder=4)

D.mark_X(ax, X, size=52)
ax.set_xlim(-200, 120)
ax.set_ylim(-90, 205)
D.save(fig, "fig01_spiral_polylines")
