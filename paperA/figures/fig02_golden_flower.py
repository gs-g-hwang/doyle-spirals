"""fig02_golden_flower.py — Figure: the golden flower, A = phi^2, B = phi.

Purpose (Section 2.1): the golden member of the quadratic family. Improvement
over the original plot: a dashed horizontal line marks the symmetry axis, so
the mirror symmetry asserted by Theorem 4.1 is literally visible; the equal
shapes of the six cell triangles (Theorem 3.4) show in the slate center graph.
"""
import doylefig as D

B = D.PHI
A = B * B
cen, rad = D.build_config(A, B, 1)

fig, ax = D.new_axes((5.6, 5.2))
xs, ys = D.circle_extent(cen, rad)
ax.axhline(0, color=D.GOLD, lw=0.9, ls=(0, (5, 4)), alpha=0.65, zorder=1)
D.draw_circles(ax, cen, rad, petal_hues=True)
D.draw_grid(ax, cen, by_direction=False, lw=1.1)
for z in cen.values():
    ax.plot(z.real, z.imag, "o", ms=2.6, color=D.SLATE, zorder=4)
D.fit_view(ax, xs, ys)
D.save(fig, "fig02_golden_flower")
