"""fig07_grid_B5over4.py — Figure: center grid of D_B for B = 5/4 (A = 25/16), six rings.

Purpose (Corollary 5.3): the grid triangles are all similar and the rows lie
on rays that meet at X = -(B^2+1)/(B^2-1) = (-41/9, 0). Improvements: the
rays are actually drawn (faint gold lines from X through each row, extended
slightly beyond the configuration), the directions are color-coded, and X is
marked and labeled.
"""
import doylefig as D

B = 1.25
M = 6
cen, rad = D.build_config(B * B, B, M)
X = D.family_X(B)

fig, ax = D.new_axes((6.8, 5.2))
# faint full rays from X through each row (one representative center per row)
for q in range(-M, M + 1):
    zr = next((cen[(p, q)] for p in range(-M, M + 1) if (p, q) in cen), None)
    if zr is None:
        continue
    d = zr - X
    d /= abs(d)
    far = X + d * 95
    ax.plot([X, far.real], [X * 0 + 0, far.imag], color=D.ROW, lw=0.7,
            alpha=0.35, zorder=1)
D.draw_grid(ax, cen, lw=0.9)
for z in cen.values():
    ax.plot(z.real, z.imag, "o", ms=1.6, color="#3A3A3A", zorder=4)
D.mark_X(ax, X)
xs = [z.real for z in cen.values()] + [X - 1.5]
ys = [z.imag for z in cen.values()]
D.fit_view(ax, xs, ys)
D.save(fig, "fig07_grid_B5over4")
