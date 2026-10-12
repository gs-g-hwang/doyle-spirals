"""Recompute Table 1 of paper C (tab:sk): B_{k+1}, k(B_{k+1}^2 - 1), B*_k, k((B*_k)^2 - 1),
and the constants 2 pi/sqrt 3 and lim k s_k quoted in its caption; compare with the printed table.

  psi(B):   cos psi = -(B^4 - 2B^3 - 2B^2 - 2B + 1)/(B^2 + 1)^2,  psi in (0, pi)
  B_n:      psi(B_n) = pi/n (closed form, paper A Cor. 7.2)
  B*_k:     the smallest B > B_{k+1} with sin(k psi(B)) = tanh log B; it lies in (B_{k+1}, B_k)
            (paper C, Prop. 3.1). Found by bisection on g(B) = sin(k psi(B)) - tanh(log B),
            which is > 0 just above B_{k+1} (where k psi < pi ... psi > pi/(k+1)) and < 0 at B_k.
Usage: python table_sk.py [path/to/paperC.tex]
"""
import re
import sys
from mpmath import mp, mpf, sqrt, cos, acos, sin, tanh, log, pi, findroot

mp.dps = 40


def psi(B):
    return acos(-(B**4 - 2 * B**3 - 2 * B**2 - 2 * B + 1) / (B**2 + 1) ** 2)


def B_res(n):
    eta = (sqrt(5 + 4 * cos(pi / n)) - 1) / 2
    return (1 + sqrt(1 - eta**2)) / eta


def B_star(k):
    lo, hi = B_res(k + 1), B_res(k)
    g = lambda B: sin(k * psi(B)) - tanh(log(B))
    # scan for the first sign change above B_{k+1}
    N = 2000
    prev_x, prev_g = lo * (1 + mpf(10) ** -30), g(lo * (1 + mpf(10) ** -30))
    assert prev_g > 0
    for i in range(1, N + 1):
        x = lo + (hi - lo) * i / N
        gx = g(x)
        if gx <= 0:
            a, b = prev_x, x
            for _ in range(200):
                m = (a + b) / 2
                if g(m) > 0:
                    a = m
                else:
                    b = m
            return (a + b) / 2
        prev_x, prev_g = x, gx
    raise ValueError("no root")


rows = []
for k in (2, 3, 4, 6, 10, 20, 100, 1000):
    b1 = B_res(k + 1)
    bs = B_star(k)
    rows.append((str(k), f"{float(b1):.7f}", f"{float(k * (b1**2 - 1)):.5f}",
                 f"{float(bs):.7f}", f"{float(k * (bs**2 - 1)):.5f}"))
print("k  B_{k+1}  k(B_{k+1}^2-1)  B*_k  k((B*_k)^2-1)")
for r in rows:
    print("  ".join(r))
print("2 pi/sqrt 3 =", f"{float(2 * pi / sqrt(3)):.5f}")

if len(sys.argv) > 1:
    tex = open(sys.argv[1], encoding="utf-8").read()
    body = tex[tex.index(r"\label{tab:sk}"):]
    body = body[:body.index(r"\end{tabular}")]
    printed = [ln for ln in body.splitlines() if "&" in ln and "$k$" not in ln]
    bad = 0
    for r, ln in zip(rows, printed):
        cells = [x.strip().replace("\\\\", "").strip() for x in ln.split("&")]
        for got, want in zip(r, cells):
            if got != want:
                bad += 1
                print(f"tab:sk mismatch, k={r[0]}: computed {got}, printed {want}")
    cap = re.search(r"2\\pi/\\sqrt3=([0-9.]+)", tex[tex.index(r"\caption{Lower bounds"):])
    if cap and cap.group(1) != f"{float(2 * pi / sqrt(3)):.5f}":
        bad += 1
        print("caption constant mismatch", cap.group(1))
    print(f"checked against {sys.argv[1]}: {'all values agree' if bad == 0 else f'{bad} mismatches'}")
