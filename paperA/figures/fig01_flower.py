"""fig01_flower.py — Figure: the flower for a generic parameter pair A=1.2, B=1.4.

Purpose in the paper (Section 2.1): introduce the six petals with radii
A, B, B/A, 1/A, 1/B, A/B around the unit circle, and the six cell triangles
of the center graph. The petals carry the six identifying hues used across
all figures; the center graph is drawn in slate.
"""
import doylefig as D

A, B = 1.2, 1.4
cen, rad = D.build_config(A, B, 1)          # the flower is the 1-ring ball

fig, ax = D.new_axes((5.6, 5.2))
D.draw_circles(ax, cen, rad, petal_hues=True)
D.draw_grid(ax, cen, by_direction=False, lw=1.1)          # cell-triangle edges
for z in cen.values():                                     # center dots
    ax.plot(z.real, z.imag, "o", ms=2.6, color=D.SLATE, zorder=4)
D.fit_view(ax, *D.circle_extent(cen, rad))
D.save(fig, "fig01_flower")
