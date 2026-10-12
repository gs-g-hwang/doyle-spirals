"""fig04_golden_four_rings.py — Figure: the golden configuration with four rings; first overlap.

Purpose (Remark 6.6 / Section 7): four rings is the experimentally determined
onset of overlap, showing the golden configuration is immersed but not
embedded. Improvement: the first overlapping pair, lattice points (0,4) and
(4,-4) (mirror images of each other), is highlighted in red instead of
leaving the reader to spot the crossing.
"""
import doylefig as D

B = D.PHI
cen, rad = D.build_config(B * B, B, 4)

fig, ax = D.new_axes((6.6, 5.2))
D.draw_circles(ax, cen, rad, lw=0.7, highlight=[(0, 4), (4, -4)])
# fixed window: keep the overlap region prominent, clip the huge right circles
ax.set_xlim(-42, 80)
ax.set_ylim(-52, 52)
D.save(fig, "fig04_golden_four_rings")
