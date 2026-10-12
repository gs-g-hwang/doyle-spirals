"""fig08_grid_B4over5.py — Figure: center grid for B = 4/5 (A = 16/25), six rings.

Purpose (Section 5): the mirror image of Figure 7 — for B < 1 the
accumulation point sits on the right, at X = +41/9 (the revised Section 5
explains D_{1/B} = -D_B plus conjugation symmetry). Same treatment as fig07_grid_B5over4.py.
"""
import doylefig as D

B = 0.8
M = 6
cen, rad = D.build_config(B * B, B, M)
X = D.family_X(B)          # positive for B < 1

fig, ax = D.new_axes((6.8, 5.2))
for q in range(-M, M + 1):
    zr = next((cen[(p, q)] for p in range(-M, M + 1) if (p, q) in cen), None)
    if zr is None:
        continue
    d = zr - X
    d /= abs(d)
    far = X + d * 95
    ax.plot([X, far.real], [0, far.imag], color=D.ROW, lw=0.7,
            alpha=0.35, zorder=1)
D.draw_grid(ax, cen, lw=0.9)
for z in cen.values():
    ax.plot(z.real, z.imag, "o", ms=1.6, color="#3A3A3A", zorder=4)
D.mark_X(ax, X)
xs = [z.real for z in cen.values()] + [X + 1.5]
ys = [z.imag for z in cen.values()]
D.fit_view(ax, xs, ys)
D.save(fig, "fig08_grid_B4over5")
