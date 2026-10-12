"""check_appendix_A1.py -- numerical check of Proposition A.4 of the paper.

Proposition A.1: let B > 1, lambda = log B, psi = psi(B), t = pi/psi, k >= 1.
If (i) t >= k+1, or (ii) k < t < k+1 and sin((t-k) psi) > tanh(lambda), then no
two circles of the k-ring patch of D_B coincide or overlap.

Brute force: K(u) and K(u+w) overlap or coincide iff K(0) and K(w) do
(self-similarity), and both lie in the k-ring ball for some u iff ||w|| <= 2k.
For each w with ||w|| <= 2k, not 0 and not a lattice direction, we compare
|z(w) - z(0)| with 1 + r(w), using the closed form z(p,q) = X + B^{2p} beta^q (-X).

For k = 1..15 and a grid of B in (B_{k+2}, B_k) (B_1 = infinity, capped) we
check that the hypothesis of A.1 implies univalence, and report how often the
converse holds (it should, apart from the tangency boundary).
"""
import numpy as np

DIRS = {(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)}


def psi_of(B):
    eta = 2 * B / (B * B + 1)
    return np.arccos(eta * eta + eta - 1)


def B_n(n):
    from scipy.optimize import brentq
    return brentq(lambda B: psi_of(B) - np.pi / n, 1 + 1e-12, 1e6)


def univalent(B, k, tol=1e-12):
    psi = psi_of(B)
    X = -(B * B + 1) / (B * B - 1)
    beta = B * np.exp(1j * psi)
    for a in range(-2 * k, 2 * k + 1):
        for b in range(-2 * k, 2 * k + 1):
            if max(abs(a), abs(b), abs(a + b)) > 2 * k:
                continue
            if (a, b) == (0, 0) or (a, b) in DIRS:
                continue
            z = X + B ** (2 * a) * beta ** b * (-X)
            d = abs(z)          # z(0,0) = 0
            if d < (1 + B ** (2 * a + b)) * (1 - tol):
                return False
    return True


def hypothesis(B, k):
    psi = psi_of(B)
    t = np.pi / psi
    if t >= k + 1:
        return True
    if k < t < k + 1:
        return np.sin((t - k) * psi) > np.tanh(np.log(B))
    return False


if __name__ == "__main__":
    bad = 0
    total = 0
    conv_fail = 0
    for k in range(1, 16):
        lo = B_n(k + 2)
        hi = B_n(k) if k >= 2 else 50.0
        for B in np.linspace(lo, hi, 400)[1:-1]:
            h = hypothesis(B, k)
            u = univalent(B, k)
            total += 1
            if h and not u:
                bad += 1
                print("COUNTEREXAMPLE", k, B)
            if u and not h:
                conv_fail += 1
    print(f"tested {total} (k,B) pairs; hypothesis true but not univalent: {bad};"
          f" univalent but hypothesis false: {conv_fail}")
