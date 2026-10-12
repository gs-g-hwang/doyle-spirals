"""doylefig.py — shared geometry and rendering helpers for the paper figures.

Each figure script f001.py ... f013.py imports this module, builds the
configuration it needs, and renders with a consistent style. The geometry here
is exactly the paper's construction:

  * Circles are indexed by the triangular lattice L = Z^2 with the six
    directions (1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1); the circle at (p,q)
    has radius r(p,q) = A^p * B^q (eq. (7) of the paper).
  * Centers are computed by lattice propagation (Section 2.2): starting from
    z(0,0)=0 and z(1,0)=1+A, each new circle is placed as the apex of a
    triangle over two already-placed mutually tangent neighbors, side lengths
    being sums of radii, with the orientation inherited from the lattice.
  * For the quadratic family A=B^2 the closed form of Proposition 5.4,
    z(p,q) = X + B^(2p) * beta^q * (0 - X), is also provided; it lets f013
    extend the spiral arms beyond any hexagonal ball.

All styling constants live here so the whole figure set shares one palette
(the same palette as the companion web page).
"""

import math
import cmath
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

# ---------------------------------------------------------------- palette ---
INK      = "#3A3A3A"   # generic circle strokes
SLATE    = "#51617A"   # center-graph segments in the flower figures
ROW      = "#B07C1C"   # row direction (1,0): straight rays through X
DIAG1    = "#2E7D74"   # diagonal direction (0,1): first spiral-arm family
DIAG2    = "#8A4E7D"   # diagonal direction (-1,1): second spiral-arm family
GOLD     = "#9A6B0F"   # the limit point X and golden accents
OVERLAP  = "#B3402E"   # highlight for the first overlapping pair
# six identifying hues for the ring-1 petals, in petal order rho_0..rho_5
PETALS   = ["#C24E4E", "#C2913A", "#6E9E48", "#3E8E86", "#5C7DB5", "#9B62A8"]

DIRS = [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
PHI = (1 + math.sqrt(5)) / 2


# --------------------------------------------------------------- geometry ---
def hexdist(p, q):
    """Ring number of lattice point (p,q)."""
    return max(abs(p), abs(q), abs(p + q))


def build_config(A, B, m):
    """Propagate the configuration on the hexagonal ball of m rings.

    Returns (centers, radii): dicts keyed by (p,q). This is the same
    propagation as verify2.py / companion.html: each unplaced circle adjacent
    to two placed, mutually adjacent circles is the apex of a triangle with
    known side lengths (sums of radii); of the two apex positions, the one
    whose orientation matches the lattice orientation is kept.
    """
    pts = [(p, q) for p in range(-m, m + 1) for q in range(-m, m + 1)
           if hexdist(p, q) <= m]
    rad = {(p, q): A ** p * B ** q for (p, q) in pts}
    cen = {(0, 0): 0 + 0j, (1, 0): (1 + A) + 0j}
    E = lambda w: complex(w[0] + 0.5 * w[1], math.sqrt(3) / 2 * w[1])  # ref. embedding
    changed = True
    while changed:
        changed = False
        for (p, q) in pts:
            if (p, q) in cen:
                continue
            for a in range(6):
                n1 = (p + DIRS[a][0], q + DIRS[a][1])
                n2 = (p + DIRS[(a + 1) % 6][0], q + DIRS[(a + 1) % 6][1])
                if n1 in cen and n2 in cen:
                    z1, z2 = cen[n1], cen[n2]
                    aa, bb = rad[n1] + rad[(p, q)], rad[n2] + rad[(p, q)]
                    d12 = abs(z2 - z1)
                    cg = max(-1.0, min(1.0, (aa * aa + d12 * d12 - bb * bb) / (2 * aa * d12)))
                    g = math.acos(cg)
                    u = (z2 - z1) / d12
                    v1 = E((p - n1[0], q - n1[1]))
                    v2 = E((n2[0] - n1[0], n2[1] - n1[1]))
                    cl = v2.real * v1.imag - v2.imag * v1.real
                    for s in (1, -1):
                        cand = z1 + aa * u * cmath.exp(1j * s * g)
                        cc = ((z2 - z1).real * (cand - z1).imag
                              - (z2 - z1).imag * (cand - z1).real)
                        if cl * cc > 0:
                            cen[(p, q)] = cand
                            changed = True
                            break
                    break
    return cen, rad


def flower_theta0(A, B):
    """Angle of the first cell triangle at the origin (law of cosines, eq. (4))."""
    r0, r1 = A, B
    c = ((1 + r0) ** 2 + (1 + r1) ** 2 - (r0 + r1) ** 2) / (2 * (1 + r0) * (1 + r1))
    return math.acos(max(-1.0, min(1.0, c)))


def family_X(B):
    """Fixed point X = -(B^2+1)/(B^2-1) of the homothety T (Theorem 5.1)."""
    return -(B * B + 1) / (B * B - 1)


def family_beta(B):
    """Multiplier beta of the step similarity S (Proposition 5.4):
    beta = (z(0,1) - X)/(0 - X) with z(0,1) = (1+B) e^{i theta_0}."""
    X = family_X(B)
    z01 = (1 + B) * cmath.exp(1j * flower_theta0(B * B, B))
    return (z01 - X) / (0 - X)


def closed_center(B, p, q, X=None, beta=None):
    """Closed form z(p,q) = X + B^(2p) beta^q (0 - X) (Proposition 5.4)."""
    if X is None:
        X = family_X(B)
    if beta is None:
        beta = family_beta(B)
    return X + (B ** (2 * p)) * (beta ** q) * (0 - X)


def ring_points(k):
    """Lattice points of ring k in label order: counterclockwise from (k,0)."""
    if k == 0:
        return [(0, 0)]
    out, p, q = [], k, 0
    for d in [(-1, 1), (-1, 0), (0, -1), (1, -1), (1, 0), (0, 1)]:
        for _ in range(k):
            out.append((p, q))
            p, q = p + d[0], q + d[1]
    return out


def ring_label(p, q):
    """Label 'k-i' used throughout the paper (Figure 3)."""
    k = hexdist(p, q)
    return f"{k}-{ring_points(k).index((p, q))}"


# --------------------------------------------------------------- rendering ---
def new_axes(figsize=(6.4, 5.2)):
    """Blank equal-aspect canvas: no frame, no ticks (coordinates are
    arbitrary; where a point matters we mark the point itself)."""
    fig, ax = plt.subplots(figsize=figsize)
    ax.set_aspect("equal")
    ax.axis("off")
    return fig, ax


def draw_circles(ax, cen, rad, lw=0.9, color=INK, petal_hues=False,
                 highlight=(), highlight_color=OVERLAP):
    """Draw all circles; optionally tint the six ring-1 petals with the
    identifying hues, and stroke the lattice points in `highlight` thicker."""
    order = {pt: i for i, pt in enumerate(ring_points(1))}
    for pt, z in cen.items():
        ec, w, zo = color, lw, 2
        if petal_hues and pt in order:
            ec, w, zo = PETALS[order[pt]], 1.6, 3
        if pt in highlight:
            ec, w, zo = highlight_color, 2.0, 4
        ax.add_patch(Circle((z.real, z.imag), rad[pt],
                            fill=False, ec=ec, lw=w, zorder=zo))


def draw_grid(ax, cen, lw=1.0, by_direction=True, alpha=0.95):
    """Join centers of tangent circles. With by_direction=True the three
    lattice directions get the row/diag1/diag2 colors, which is exactly the
    decomposition into rays and the two spiral-arm families (Prop. 5.4)."""
    styles = {(1, 0): (ROW if by_direction else INK),
              (0, 1): (DIAG1 if by_direction else INK),
              (-1, 1): (DIAG2 if by_direction else INK)}
    for (p, q), z in cen.items():
        for d, col in styles.items():
            w = (p + d[0], q + d[1])
            if w in cen:
                z2 = cen[w]
                ax.plot([z.real, z2.real], [z.imag, z2.imag],
                        color=col, lw=lw, alpha=alpha, zorder=2,
                        solid_capstyle="round")


def mark_X(ax, X, label=True, size=44):
    """Mark the limit point X with the gold bullseye used on the web page."""
    ax.scatter([X], [0], s=size, facecolors="none", edgecolors=GOLD,
               lw=1.6, zorder=6)
    ax.scatter([X], [0], s=6, color=GOLD, zorder=6)
    if label:
        ax.annotate("$X$", (X, 0), textcoords="offset points",
                    xytext=(-11, 7), color=GOLD, fontsize=12, zorder=6)


def label_center(ax, z, text, fontsize=6.5):
    """Ring label with a white halo so it stays readable over strokes."""
    ax.text(z.real, z.imag, text, ha="center", va="center",
            fontsize=fontsize, color="#222222", zorder=5,
            bbox=dict(boxstyle="round,pad=0.12", fc="white",
                      ec="none", alpha=0.72))


def fit_view(ax, xs, ys, margin=0.04):
    """Set limits to the data with a small margin (replaces default frames)."""
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    mx, my = margin * (x1 - x0), margin * (y1 - y0)
    ax.set_xlim(x0 - mx, x1 + mx)
    ax.set_ylim(y0 - my, y1 + my)


def circle_extent(cen, rad):
    """xs, ys covering every circle (for fit_view)."""
    xs, ys = [], []
    for pt, z in cen.items():
        r = rad[pt]
        xs += [z.real - r, z.real + r]
        ys += [z.imag - r, z.imag + r]
    return xs, ys


def save(fig, name):
    """300-dpi print-quality PNG under the figure's own name."""
    fig.savefig(f"{name}.png", dpi=300, bbox_inches="tight",
                pad_inches=0.06, facecolor="white")
    plt.close(fig)
    print(f"wrote {name}.png")
