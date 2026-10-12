"""Degree and leading coefficient of the primitive minimal polynomial of B_n (paper B, Table 1,
columns "deg" and "lead"), for n = 2..9 and for the golden ratio.

B_n is the root > 1 of  cos psi(B) = cos(pi/n),  cos psi(B) = -(B^4-2B^3-2B^2-2B+1)/(B^2+1)^2.
So B_n is a root of  P_n(B) = -(B^4-2B^3-2B^2-2B+1) - c (B^2+1)^2  with c = cos(pi/n);
taking the norm from Q(c) to Q (resultant with the minimal polynomial of c) and
factoring gives the minimal polynomial; the factor vanishing at the numerical B_n is chosen.
Usage: python table_Bn_algebraic.py [path/to/paperB.tex]   (with a path, all eight columns of
the printed table are checked; B_n, A_n and the angles by the formulas of paper A, Prop. 7.1)
"""
import sys
from sympy import symbols, cos, pi, minimal_polynomial, resultant, factor_list, Poly, sqrt, N, nsimplify
from mpmath import mp, mpf
import mpmath

mp.dps = 50
B, c = symbols("B c")


def B_num(n):
    eta = (mpmath.sqrt(5 + 4 * mpmath.cos(mpmath.pi / n)) - 1) / 2
    return (1 + mpmath.sqrt(1 - eta**2)) / eta


rows = []
for n in range(2, 10):
    mc = minimal_polynomial(cos(pi / n), c)
    P = -(B**4 - 2 * B**3 - 2 * B**2 - 2 * B + 1) - c * (B**2 + 1) ** 2
    R = resultant(P, mc, c)
    x = B_num(n)
    best = None
    for f, _ in factor_list(R)[1]:
        pf = Poly(f, B)
        val = abs(mpmath.polyval([mpf(int(a)) for a in pf.all_coeffs()], x))
        if best is None or val < best[0]:
            best = (val, pf)
    pf = best[1]
    coeffs = [int(a) for a in pf.all_coeffs()]
    if coeffs[0] < 0:
        coeffs = [-a for a in coeffs]
    rows.append((n, pf.degree(), coeffs[0]))
    assert best[0] < mpf(10) ** -30
x = (1 + mpmath.sqrt(5)) / 2
rows.append(("phi", 2, 1))       # x^2 - x - 1
for r in rows:
    print(*r)


def cos_psi(b):
    return -(b**4 - 2 * b**3 - 2 * b**2 - 2 * b + 1) / (b**2 + 1) ** 2


def angle_at(x, y, z):
    """Angle at the center of the circle of radius x, for mutually tangent radii x, y, z."""
    a, b, c_ = x + y, x + z, y + z
    return mpmath.acos((a * a + b * b - c_ * c_) / (2 * a * b))


if len(sys.argv) > 1:
    tex = open(sys.argv[1], encoding="utf-8").read()
    body = tex[tex.index(r"\label{tab:Bn}"):]
    body = body[:body.index(r"\end{tabular}")]
    printed = [ln for ln in body.splitlines() if ln.strip()[:1].isdigit() or ln.strip().startswith(r"$\gr$")]
    assert len(printed) == len(rows), len(printed)
    bad = 0
    for (n, deg, lead), ln in zip(rows, printed):
        x = B_num(n) if n != "phi" else (1 + mpmath.sqrt(5)) / 2
        if n != "phi":
            assert abs(mpmath.acos(cos_psi(x)) - mpmath.pi / n) < mpf(10) ** -25
        one = mpf(1)
        ang = [mpmath.degrees(angle_at(one, x, x**2)), mpmath.degrees(angle_at(x, one, x**2)),
               mpmath.degrees(angle_at(x**2, one, x))]
        got = [str(n), mpmath.nstr(x, 11, strip_zeros=False), mpmath.nstr(x**2, 8, strip_zeros=False)]
        got += [f"{float(a):.3f}" for a in ang] + [str(deg), str(lead)]
        cells = [c_.strip().replace(r"$^{\circ}$", "").replace("\\\\", "").strip() for c_ in ln.split("&")]
        cells[0] = "phi" if "gr" in cells[0] else cells[0]
        for g, w in zip(got, cells):
            if g != w:
                bad += 1
                print(f"tab:Bn mismatch, row {n}: computed {g}, printed {w}")
    print(f"\nchecked against {sys.argv[1]}: {'all values agree' if bad == 0 else f'{bad} mismatches'}")
