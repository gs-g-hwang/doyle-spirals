"""fig01_rigidity_s2.py — Figure: Doyle spirals versus the extremal problem for s_k.

Left: the univalent 2-generation hexagonal packing with neighbor ratio 15.8377
found by numerical optimization (scripts1005f/sk_optimize.py, verified to 40
digits by scripts1005f/sk_verify.py). Radii are those printed by the verifier;
the center circle (radius 1) and its large petal (radius 15.84) are shaded.
Two boundary circles have radii 2.2e7 and 1.9e5 and appear as nearly straight
arcs. Right: the normalized bounds k*(rho-1) for s_k. Doyle spirals of the
quadratic family (Table 4: B_{k+1} and B*_k) tend to 2*pi/sqrt(3) (Theorem 7.19),
below the asymptotic value 4/R of Doyle, He and Rodin; the numerical
2-generation packing lies far above them.
"""
import math
import doylefig as D

PTS = [(0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1), (2, 0), (1, 1), (0, 2),
       (-1, 2), (-2, 2), (-2, 1), (-2, 0), (-1, -1), (0, -2), (1, -2), (2, -2), (2, -1)]
RADII = [1.0, 15.837684647118901, 1.6782220609184578, 0.31347297983328774,
         0.16062014132333937, 0.43819356921177901, 2.8254142062357118, 21759091.46721951,
         16.035096979936029, 1.1547830642570235, 0.47783366940695978, 0.12202535224942378,
         0.064039187371180218, 0.01523603751168618, 0.10839328573455994, 0.19760576626071222,
         0.83953729716006784, 2.7008249386880666, 190931.10082436484]
r = dict(zip(PTS, RADII))


def emb(u):
    return complex(u[0] + 0.5 * u[1], math.sqrt(3) / 2 * u[1])


def adjacent(u, v):
    return (v[0] - u[0], v[1] - u[1]) in D.DIRS


# lay out: each new circle from two placed, mutually adjacent neighbors (positive orientation)
z = {(0, 0): 0j, (1, 0): complex(r[(0, 0)] + r[(1, 0)], 0)}
todo = [u for u in PTS if u not in z]
while todo:
    for u in todo:
        pair = None
        for a in z:
            for b in z:
                if a != b and adjacent(a, u) and adjacent(b, u) and adjacent(a, b):
                    if ((emb(b) - emb(a)).conjugate() * (emb(u) - emb(a))).imag > 0:
                        pair = (a, b)
                        break
            if pair:
                break
        if pair:
            a, b = pair
            dab = abs(z[b] - z[a]); da = r[a] + r[u]; db = r[b] + r[u]
            c = (da * da + dab * dab - db * db) / (2 * da * dab)
            z[u] = z[a] + (z[b] - z[a]) / dab * da * complex(c, math.sqrt(max(0.0, 1 - c * c)))
            todo.remove(u)
            break

fig, (ax, bx) = D.plt.subplots(1, 2, figsize=(10.0, 4.6), gridspec_kw={"width_ratios": [1.05, 1]})
def draw(a, lw):
    for u in PTS:
        fc = "#E7D3A6" if u == (0, 0) else ("#F1E6CC" if u == (1, 0) else "none")
        a.add_patch(D.plt.Circle((z[u].real, z[u].imag), r[u], fill=(fc != "none"), facecolor=fc,
                                 edgecolor=D.INK, lw=lw, zorder=2))
    for u in PTS:
        for d in D.DIRS:
            v = (u[0] + d[0], u[1] + d[1])
            if v in z and PTS.index(v) > PTS.index(u) and max(r[u], r[v]) < 1e3:
                a.plot([z[u].real, z[v].real], [z[u].imag, z[v].imag], color=D.SLATE, lw=0.5, zorder=3)
    a.set_aspect("equal"); a.set_xticks([]); a.set_yticks([])


draw(ax, 0.8)
ax.set_xlim(-22, 40); ax.set_ylim(-31, 31); ax.axis("off")
ax.text(z[(1, 0)].real, z[(1, 0)].imag - 7, r"petal, $\rho\approx15.84$", ha="center", fontsize=9)
ins = ax.inset_axes([0.0, 0.0, 0.36, 0.36])
draw(ins, 0.6)
ins.set_xlim(-2.2, 3.2); ins.set_ylim(-2.7, 2.7)
ins.text(0, 0, r"$c_{0}$", ha="center", va="center", fontsize=8, zorder=5)
ax.indicate_inset_zoom(ins, edgecolor="#888888")

ks = [2, 3, 4, 6, 10, 20, 100, 1000]
lower = [5.26401, 4.67649, 4.40000, 4.13383, 3.92758, 3.77632, 3.65716, 3.63055]
upper = [7.32298, 5.66185, 5.02811, 4.48983, 4.11498, 3.86116, 3.67281, 3.63209]
x = [1 / k for k in ks]
bx.plot(x, upper, "o-", ms=4, color=D.DIAG1, lw=1.2, label=r"$k((B_k^{*})^{2}-1)$, quadratic family")
bx.plot(x, lower, "s--", ms=3.5, color=D.DIAG2, lw=1.0, label=r"$k(B_{k+1}^{2}-1)$, quadratic family")
bx.axhline(2 * math.pi / math.sqrt(3), color=D.GOLD, lw=1.2)
bx.axhline(4.45165, color=D.OVERLAP, lw=1.0, ls=":")
bx.plot([0.5], [2 * 14.8377], "*", ms=11, color=D.OVERLAP, label="numerical packing, $k=2$")
bx.text(0.31, 3.32, r"$2\pi/\sqrt{3}$ (Theorem 7.19)", color=D.GOLD, fontsize=8.5)
bx.text(0.015, 4.62, r"$4/R$ (Doyle-He-Rodin)", color=D.OVERLAP, fontsize=8.5)
bx.set_yscale("log"); bx.set_ylim(2.8, 40); bx.set_xlim(-0.01, 0.53)
bx.set_yticks([3, 4, 5, 7, 10, 20, 30]); bx.set_yticklabels(["3", "4", "5", "7", "10", "20", "30"])
bx.set_xlabel(r"$1/k$"); bx.set_ylabel(r"normalized lower bound $k(\rho-1)$ for $k\,s_{k}$")
bx.legend(fontsize=7.5, loc="upper left", frameon=False)
for s in ("top", "right"):
    bx.spines[s].set_visible(False)
D.save(fig, "fig01_rigidity_s2")
