"""fig06_golden_center_grid.py — Figure: center grid of the golden configuration, three rings.

Purpose (Section 5): every cell triangle is similar to every other
(Theorem 3.4), and the horizontal rows lie on straight rays through X
(Corollary 5.3). Improvement: the three lattice directions are drawn in the
row/arm colors of Proposition 5.4 (gold rows, teal and plum diagonals), and
the limit point X = (-sqrt5, 0) is marked, so the ray structure is visible
rather than implied.
"""
import doylefig as D

B = D.PHI
cen, rad = D.build_config(B * B, B, 3)

fig, ax = D.new_axes((6.6, 5.2))
D.draw_grid(ax, cen, lw=1.1)
for z in cen.values():
    ax.plot(z.real, z.imag, "o", ms=2.2, color="#3A3A3A", zorder=4)
D.mark_X(ax, D.family_X(B))
xs = [z.real for z in cen.values()] + [D.family_X(B) - 0.6]
ys = [z.imag for z in cen.values()]
D.fit_view(ax, xs, ys)
D.save(fig, "fig06_golden_center_grid")
