"""(1) Which cases the Lemma 7.11 check excluded as ties; (2) exact delta(B)."""
import numpy as np, mpmath as mp
def psi(B):
    e = 2*B/(B*B+1); return np.arccos(e*e+e-1)
# (1) replicate the grid of Section 9.5: 299 values of B in [1.033,4.907]
Bs = np.linspace(1.033, 4.907, 299)
tot = excl = mism = 0; exset = {}
for B in Bs:
    lam = np.log(B); ps = psi(B); X = -(B*B+1)/(B*B-1); beta = B*np.exp(1j*ps)
    for a in range(-25, 26):
        for b in range(-50, 51):
            tot += 1
            s = 2*a+b
            Om = np.sinh(s*lam/2)**2/np.sinh(lam)**2 + (1/np.tanh(lam))**2*np.sin(b*ps/2)**2
            z = X + B**(2*a)*beta**b*(-X); R = B**s
            d = abs(z); direct = d - (1+R)        # <0 overlap
            if abs(Om-1) < 1e-7 or abs(direct) < 1e-7*(1+R):
                excl += 1; exset[(a,b)] = exset.get((a,b),0)+1; continue
            if (Om < 1) != (direct < 0): mism += 1
print("total", tot, "excluded", excl, "checked", tot-excl, "mismatches", mism)
print("excluded differences:", sorted(exset.items()))
# (2) delta(B): max distance from arc beta^s (0<=s<=1) to chord [1,beta]
mp.mp.dps = 30
def delta(B):
    B = mp.mpf(B); e = 2*B/(B*B+1); ps = mp.acos(e*e+e-1); L0 = mp.log(B)+1j*ps
    beta = mp.exp(L0); ch = beta-1
    f = lambda s: abs(mp.im((mp.exp(s*L0)-1)*mp.conj(ch)))/abs(ch)
    df = lambda s: mp.diff(f, s)
    s0 = mp.findroot(df, 0.5)
    return f(s0), s0, abs(ch)
for B in ['1.01','1.1','1.25',mp.phi,'2']:
    d, s0, c = delta(B)
    lead = mp.sqrt(3)/4*(mp.mpf(B)-1)**2
    print(B if isinstance(B,str) else 'phi', mp.nstr(d,6), 's*=', mp.nstr(s0,6), 'ratio', mp.nstr(d/c,5), 'lead', mp.nstr(lead,4))
