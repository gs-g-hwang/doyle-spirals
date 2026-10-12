"""Core of the brute-force first-overlap search (used by first_overlap_full.py and f019.py)."""
import math
from first_overlap import centers, norm, NB, m_formula, psi

def first_pairs(B, M):
    X, z, r = centers(B)
    for m in range(1, M+1):
        pts = [(p,q) for p in range(-m,m+1) for q in range(-m,m+1) if norm(p,q) <= m]
        new = [u for u in pts if norm(*u) == m]
        found = set()
        for u in new:
            for v in pts:
                w = (v[0]-u[0], v[1]-u[1])
                if w == (0,0) or w in NB: continue
                d = abs(z(*v)-z(*u)); R = r(*u)+r(*v)
                if 1e-9*R < d < (1-1e-9)*R:
                    found.add(w if (w[1] > 0 or (w[1] == 0 and w[0] > 0)) else (-w[0], -w[1]))
        if found: return m, found
    return None, None

