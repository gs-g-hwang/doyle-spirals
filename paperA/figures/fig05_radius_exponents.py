"""fig05_radius_exponents.py — Figure: radii of D_B as powers of B (exponent 2p+q).

Purpose (Section 3, eq. (9)): under each ring label the exponent n = 2p+q of
the radius B^n is shown; along a row the exponent grows by 2 per step, along
the diagonals by 1. This is a schematic lattice diagram, so it is drawn on
the regular packing layout (as in the original). Improvements: print-quality
text, and each circle is shaded on a subtle gold gradient by its exponent,
so the doubling rule is visible as well as readable.
"""
import math
import doylefig as D
from matplotlib.patches import Circle

M = 6
cen, rad = D.build_config(1.0, 1.0, M)      # regular layout, schematic

def expo(p, q):
    return 2 * p + q

lo = min(expo(p, q) for (p, q) in cen)
hi = max(expo(p, q) for (p, q) in cen)

fig, ax = D.new_axes((6.8, 6.2))
for pt, z in cen.items():
    t = (expo(*pt) - lo) / (hi - lo)        # 0..1 across the exponent range
    # blend white -> soft gold with the exponent
    r0, g0, b0 = 1.0, 1.0, 1.0
    r1, g1, b1 = 0.937, 0.836, 0.567        # light gold
    fc = (r0 + (r1 - r0) * t, g0 + (g1 - g0) * t, b0 + (b1 - b0) * t)
    ax.add_patch(Circle((z.real, z.imag), rad[pt], fc=fc, ec="#3A3A3A",
                        lw=0.7, zorder=2))
    ax.text(z.real, z.imag + 0.16, D.ring_label(*pt), ha="center",
            va="center", fontsize=5.4, color="#222222", zorder=5)
    ax.text(z.real, z.imag - 0.24, f"{expo(*pt)}", ha="center", va="center",
            fontsize=6.4, color=D.GOLD, fontweight="bold", zorder=5)
D.fit_view(ax, *D.circle_extent(cen, rad))
D.save(fig, "fig05_radius_exponents")
