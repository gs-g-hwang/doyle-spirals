"""fig09_grid_zoom.py — Figure: enlargement of Figure 7 with ring labels.

Purpose (Section 5): through each center pass one straight row ray and two
crossing polylines; the labels identify circles so the reader can follow a
row or an arm. Fix relative to the original: the old plot placed labels on
all 127 centers, which collide into an unreadable cluster near X and spill
outside the frame. Here the view is cropped to the neighborhood of X and a
label is drawn only where the local mesh is large enough to carry it
(centers whose circle radius B^(2p+q) >= 0.5 and which lie in the window);
the direction coloring identifies the rest.
"""
import doylefig as D

B = 1.25
M = 6
cen, rad = D.build_config(B * B, B, M)
X = D.family_X(B)
WIN = (-9.5, 8.5, -7.0, 7.0)          # crop window around X

fig, ax = D.new_axes((6.8, 5.6))
for q in range(-M, M + 1):
    zr = next((cen[(p, q)] for p in range(-M, M + 1) if (p, q) in cen), None)
    if zr is None:
        continue
    d = zr - X
    d /= abs(d)
    far = X + d * 40
    ax.plot([X, far.real], [0, far.imag], color=D.ROW, lw=0.7,
            alpha=0.3, zorder=1)
D.draw_grid(ax, cen, lw=1.0)
for pt, z in cen.items():
    ax.plot(z.real, z.imag, "o", ms=1.8, color="#3A3A3A", zorder=4)
    inside = WIN[0] < z.real < WIN[1] and WIN[2] < z.imag < WIN[3]
    if inside and rad[pt] >= 0.5:
        D.label_center(ax, z, D.ring_label(*pt), fontsize=6.2)
D.mark_X(ax, X)
ax.set_xlim(WIN[0], WIN[1])
ax.set_ylim(WIN[2], WIN[3])
D.save(fig, "fig09_grid_zoom")
