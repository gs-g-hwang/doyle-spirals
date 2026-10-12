"""fig03_ring_labels.py — Figure: the ring-label scheme k-i on the regular packing A=B=1.

Purpose (Section 2.2): purely combinatorial legend for the labels used in
later figures — ring k has 6k circles, numbered counterclockwise from the
positive horizontal axis. Redrawn at print resolution so the labels are
actually readable; the ring-1 petals carry the identifying hues to tie this
diagram to Figures 1 and 2.
"""
import doylefig as D

M = 6
cen, rad = D.build_config(1.0, 1.0, M)

fig, ax = D.new_axes((6.8, 6.2))
D.draw_circles(ax, cen, rad, lw=0.7, petal_hues=True)
for pt, z in cen.items():
    D.label_center(ax, z, D.ring_label(*pt), fontsize=5.6)
D.fit_view(ax, *D.circle_extent(cen, rad))
D.save(fig, "fig03_ring_labels")
