"""fig14_similarity_residual.py — Figure: where are all six cell triangles similar?

Residual F(A,B) = min over the six vertex bijections of the distance between the
normalized radius vectors of Delta_1 and Delta_0 (Lemma 3.3), on a 1601 x 1601 grid
in (log2 A, log2 B) in [-2,2]^2, shown as log10 F. The three curves of
Theorem 3.4 (A = B^2, B = A^2, AB = 1) are overlaid dashed; they are the only
valleys. Replaces the exact-hit grid scan of the earlier versions (referee B1);
same computation as scripts1005f/residual_scan.py.
"""
import itertools
import numpy as np
import doylefig as D


def residual(A, B):
    x0 = np.stack([A, B, np.ones_like(A)])          # radii at P0, P1, O of Delta_0
    x1 = np.stack([np.ones_like(A), B, B / A])      # radii at O, P1, P2 of Delta_1
    x1 = x1 / np.linalg.norm(x1, axis=0)
    best = np.full(A.shape, np.inf)
    for perm in itertools.permutations(range(3)):
        y = x0[list(perm)]
        y = y / np.linalg.norm(y, axis=0)
        best = np.minimum(best, np.linalg.norm(x1 - y, axis=0))
    return best


u = np.linspace(-2, 2, 1601)
U, V = np.meshgrid(u, u)
F = residual(2.0 ** U, 2.0 ** V)
fig, ax = D.plt.subplots(figsize=(6.2, 5.2))
im = ax.imshow(np.log10(np.maximum(F, 1e-6)), extent=(-2, 2, -2, 2), origin="lower",
               cmap="cividis", vmin=-4, vmax=0, interpolation="bilinear")
t = np.linspace(-2, 2, 200)
kw = dict(color="white", lw=1.0, ls="--")
ax.plot(2 * t[np.abs(2 * t) <= 2], t[np.abs(2 * t) <= 2], **kw)      # A = B^2
ax.plot(t[np.abs(2 * t) <= 2], 2 * t[np.abs(2 * t) <= 2], **kw)      # B = A^2
ax.plot(t, -t, **kw)                                                  # AB = 1
ax.text(1.55, 0.62, r"$A=B^{2}$", color="#1E2A44", fontsize=9)
ax.text(0.55, 1.55, r"$B=A^{2}$", color="#1E2A44", fontsize=9)
ax.text(-1.85, 1.62, r"$AB=1$", color="#1E2A44", fontsize=9)
ax.plot([np.log2(D.PHI ** 2)], [np.log2(D.PHI)], "*", ms=9, color=D.GOLD, mec="white", mew=0.6)
ax.set_xlabel(r"$\log_{2}A$")
ax.set_ylabel(r"$\log_{2}B$")
cb = fig.colorbar(im, ax=ax, shrink=0.85)
cb.set_label(r"$\log_{10}F(A,B)$")
D.save(fig, "fig14_similarity_residual")
