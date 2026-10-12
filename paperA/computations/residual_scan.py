"""Residual map F(A,B): distance of Delta_1 from similarity with Delta_0 (Lemma 3.3 radii)."""
import numpy as np, itertools
def F(A, B):
    x0 = np.stack([A, B, np.ones_like(A)])             # radii at P0,P1,O of Delta_0
    x1 = np.stack([np.ones_like(A), B, B/A])           # radii at O,P1,P2 of Delta_1
    x1 = x1/np.linalg.norm(x1, axis=0)
    best = np.full(A.shape, np.inf)
    for perm in itertools.permutations(range(3)):
        y = x0[list(perm)]; y = y/np.linalg.norm(y, axis=0)
        best = np.minimum(best, np.linalg.norm(x1-y, axis=0))
    return best
u = np.linspace(-2, 2, 1601)                            # log2 A, log2 B in [-2,2]
U, V = np.meshgrid(u, u)
R = F(2**U, 2**V)
np.save('residual.npy', R)
# local minima of R along each row: where are the valleys?
for thr in [1e-2, 1e-3]:
    m = R < thr
    # distance of low points from the three curves in log coords: a=2b, b=2a, a=-b
    a, b = U[m], V[m]
    d = np.minimum.reduce([abs(a-2*b)/np.sqrt(5), abs(b-2*a)/np.sqrt(5), abs(a+b)/np.sqrt(2)])
    print(thr, m.sum(), 'max distance of low points to the 3 curves (log2 units):', d.max())
print('min/max R', R.min(), R.max())
