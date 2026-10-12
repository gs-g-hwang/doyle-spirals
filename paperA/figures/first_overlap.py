"""first_overlap.py -- checks for Section 7.5 of em20261004a.tex.

Criterion (Theorem 7.10): K(0,0) and K(a,b) of D_B have overlapping interiors iff
    sinh^2(s*lam/2)/sinh^2(lam) + coth^2(lam) * sin^2(b*psi/2) < 1,  s = 2a+b, lam = log B.
First-overlap formula (Theorem 7.11): with t = pi/psi, r = t - floor(t),
    m(B) = floor(t) if sin(r*psi) < tanh(lam), else ceil(t).
Both are compared with a brute-force overlap search in the ring construction.
"""
import math, cmath

def psi(B):
    return 2*math.atan((B-1)/(B+1)*math.sqrt((B*B+B+1)/B))

def centers(B):
    X = -(B*B+1)/(B*B-1); beta = B*cmath.exp(1j*psi(B))
    z = lambda p, q: X + (B**(2*p))*(beta**q)*(-X)
    r = lambda p, q: B**(2*p+q)
    return X, z, r

def norm(p, q): return max(abs(p), abs(q), abs(p+q))
NB = {(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)}

def overlap_direct(B, a, b, tol=1e-9):
    X, z, r = centers(B)
    return abs(z(a,b)-z(0,0)) < (1-tol)*(r(a,b)+1)

def omega(B, a, b):
    lam = math.log(B); s = 2*a+b
    return math.sinh(s*lam/2)**2/math.sinh(lam)**2 + (1/math.tanh(lam))**2*math.sin(b*psi(B)/2)**2

def m_brute(B, M=40):
    """smallest m such that two non-adjacent circles within m rings overlap
    (pairs that coincide, i.e. differ by a resonance period, are not overlaps)."""
    X, z, r = centers(B)
    for m in range(1, M+1):
        pts = [(p,q) for p in range(-m,m+1) for q in range(-m,m+1) if norm(p,q) <= m]
        # only differences w with ||w|| = 2m-1 or 2m are new at ring m, but test all for safety
        for i, u in enumerate(pts):
            for v in pts[i+1:]:
                w = (v[0]-u[0], v[1]-u[1])
                if w in NB: continue
                d = abs(z(*v)-z(*u)); R = r(*u)+r(*v)
                if d < (1-1e-9)*R and d > 1e-9*R:
                    return m
    return None

def m_formula(B):
    t = math.pi/psi(B); fl = math.floor(t); rr = t-fl
    if rr < 1e-12: return None
    return fl if math.sin(rr*psi(B)) < math.tanh(math.log(B)) else fl+1

if __name__ == "__main__":
    # 1. criterion vs direct test on a grid of lattice vectors
    bad = 0; tested = 0
    for k in range(1, 300):
        B = 1.02 + 0.013*k
        for a in range(-25, 26):
            for b in range(-50, 51):
                if (a,b) == (0,0) or (a,b) in NB: continue
                tested += 1
                X, z, r = centers(B)
                d = abs(z(a,b)-z(0,0)); R = r(a,b)+1
                if abs(d/R-1) < 1e-7: continue        # tangency/coincidence: skip ties
                if (d < R) != (omega(B,a,b) < 1): bad += 1
    print(f"criterion vs direct: {tested} pairs, {bad} disagreements")
    # 2. formula vs brute force for m(B)
    bad = []; stat = {"floor":0, "ceil":0}
    Bs = [1.15+0.0025*k for k in range(1140)]
    for B in Bs:
        mf = m_formula(B)
        if mf is None: continue
        mb = m_brute(B, M=mf+1) if mf <= 8 else None
        t = math.pi/psi(B)
        stat["floor" if mf == math.floor(t) else "ceil"] += 1
        if mb is not None and mb != mf: bad.append((B, mf, mb))
    print("m(B) formula vs brute force (m<=8):", "all agree" if not bad else bad[:10])
    print("floor/ceil counts:", stat)
    # threshold r*(B) = arcsin(tanh lam)/psi
    for B in [1.001, 1.01, 1.1, 1.25, 1.5, (1+5**0.5)/2, 2.0, 2.89]:
        print(f"B={B:.4f}  t={math.pi/psi(B):9.4f}  r*={math.asin(math.tanh(math.log(B)))/psi(B):.4f}")
    phi = (1+5**0.5)/2
    t = math.pi/psi(phi)
    print("golden: t=%.6f, m formula=%d, sin(r psi)=%.4f, tanh=%.4f" %
          (t, m_formula(phi), math.sin((t-math.floor(t))*psi(phi)), math.tanh(math.log(phi))))
