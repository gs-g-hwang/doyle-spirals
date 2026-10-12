"""fig03_first_overlap.py — Figure: the first-overlap rule (Theorem 7.14).

For B in [1.15, 4) the fractional part r = t - floor(t) of t = pi/psi(B) is
plotted against B. The curve r*(B) = arcsin(tanh log B)/psi(B) (gold)
separates the two cases of the theorem: below it the first overlap occurs at
floor(t) rings, above it at ceil(t). Dots: the 1140 parameters of the scan of
Section 9.4, colored by the first-overlap ring found by brute force
(scripts20261004a/first_overlap_full.py): teal = floor(t), plum = ceil(t).
Vertical lines: the resonant parameters B_n (r = 0).
"""
import math, sys
sys.path.insert(0, ".")
import doylefig as D
from first_overlap import psi
from first_overlap_full_core import first_pairs, m_formula

fig, ax = D.plt.subplots(figsize=(8.0, 3.8))
Bs = [1.15 + 0.0025 * k for k in range(1140)]
for B in Bs:
    t = math.pi / psi(B); fl = math.floor(t)
    mb, _ = first_pairs(B, m_formula(B) + 1)
    ax.scatter([B], [t - fl], s=4, color=(D.DIAG1 if mb == fl else D.DIAG2), zorder=3)
xs = [1.15 + 0.001 * k for k in range(2851)]
ax.plot(xs, [math.asin(math.tanh(math.log(B))) / psi(B) for B in xs], color=D.GOLD, lw=1.8, zorder=4)
for n in range(2, 14):
    lo, hi = 1.0001, 4.0
    for _ in range(80):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if psi(mid) < math.pi / n else (lo, mid)
    if lo >= 1.15 and n <= 7:
        ax.axvline(lo, color="#BBBBBB", lw=0.6, zorder=1)
        ax.text(lo, 1.02, f"$B_{{{n}}}$", ha="center", va="bottom", fontsize=8, color="#555555")
ax.set_xlim(1.15, 4.0); ax.set_ylim(0, 1)
ax.set_xlabel("$B$"); ax.set_ylabel(r"$t-\lfloor t\rfloor$,  $t=\pi/\psi$")
ax.text(3.35, 0.62, r"$r^{*}(B)$", color=D.GOLD, fontsize=11)
ax.text(2.2, 0.9, r"first overlap at $\lceil t\rceil$ rings", color=D.DIAG2, fontsize=9)
ax.text(2.95, 0.12, r"first overlap at $\lfloor t\rfloor$ rings", color=D.DIAG1, fontsize=9)
for s in ("top", "right"): ax.spines[s].set_visible(False)
D.save(fig, "fig03_first_overlap")
