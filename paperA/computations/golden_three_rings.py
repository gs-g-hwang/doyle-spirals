"""golden_three_rings.py -- exact-precision check of the golden configuration.

For B = phi (A = phi^2) the centers are z(p,q) = X + B^(2p) beta^q (-X) with
X = -sqrt(5), beta = B e^{i psi}, cos psi = eta^2 + eta - 1, eta = sech log B,
and the radii are r(p,q) = B^(2p+q).  For every pair of non-adjacent lattice
points in the m-ring ball we compute the ratio d/(r1+r2) of the distance of the
centers to the sum of the radii.  Two circles overlap iff this ratio is < 1.

Output: for m = 3 the minimum ratio (it is > 1: no overlap), and for m = 4 the
overlapping pairs.  All arithmetic is done with 50 significant digits.
"""
from itertools import combinations
from mpmath import mp, mpf, sqrt, acos, exp, mpc, fabs, sin

mp.dps = 50
DIRS = {(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)}


def norm(p, q):
    return max(abs(p), abs(q), abs(p + q))


def setup(B):
    eta = 2 * B / (B * B + 1)
    psi = acos(eta * eta + eta - 1)
    X = -(B * B + 1) / (B * B - 1)
    beta = B * exp(mpc(0, 1) * psi)
    return X, beta, psi


def center(p, q, B, X, beta):
    return X + B ** (2 * p) * beta ** q * (-X)


def scan(m, B):
    X, beta, psi = setup(B)
    pts = [(p, q) for p in range(-m, m + 1) for q in range(-m, m + 1)
           if norm(p, q) <= m]
    worst = None
    overlaps = []
    for u, v in combinations(pts, 2):
        w = (v[0] - u[0], v[1] - u[1])
        if w in DIRS:
            continue
        d = abs(center(*u, B, X, beta) - center(*v, B, X, beta))
        rs = B ** (2 * u[0] + u[1]) + B ** (2 * v[0] + v[1])
        ratio = d / rs
        if worst is None or ratio < worst[0]:
            worst = (ratio, u, v)
        if ratio < 1:
            overlaps.append((u, v, ratio))
    return len(pts), worst, overlaps, psi


if __name__ == "__main__":
    phi = (1 + sqrt(5)) / 2
    n3, worst3, ov3, psi = scan(3, phi)
    print("psi(phi) in degrees:", mp.nstr(psi * 180 / mp.pi, 12))
    print("|sin 4 psi| =", mp.nstr(fabs(sin(4 * psi)), 12),
          " 1/sqrt5 =", mp.nstr(1 / sqrt(5), 12))
    pairs3 = n3 * (n3 - 1) // 2
    print(f"m=3: {n3} circles, {pairs3} pairs")
    print("  min d/(r1+r2) over non-adjacent pairs:",
          mp.nstr(worst3[0], 15), "at", worst3[1], worst3[2])
    print("  overlapping pairs:", len(ov3))
    n4, worst4, ov4, _ = scan(4, phi)
    print(f"m=4: {n4} circles; overlapping pairs: {len(ov4)}")
    for u, v, r in sorted(ov4, key=lambda t: t[2]):
        print("   ", u, v, mp.nstr(r, 10))
