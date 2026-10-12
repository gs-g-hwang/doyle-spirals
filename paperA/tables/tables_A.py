"""Recompute Table 1 (resonant members, tab:Bn) and Table 2 (comparison with Beardon-Dubejko-
Stephenson, tab:bdscompare) of paper A, and compare them with the printed values.

Formulas (paper A):
  cos psi(B) = -(B^4 - 2B^3 - 2B^2 - 2B + 1)/(B^2 + 1)^2              (Prop. 7.1)
  B_n solves psi(B) = pi/n:  eta = (sqrt(5 + 4 cos(pi/n)) - 1)/2,
                             B_n = (1 + sqrt(1 - eta^2))/eta           (Cor. 7.2)
  cell triangle with radii 1, B, B^2: sides 1+B, B+B^2, 1+B^2; the angle at the
  vertex of radius x is given by the law of cosines (theta_O at 1, theta_P1 at B,
  theta_P0 at B^2).
Usage: python tables_A.py [path/to/paperA.tex]   (with a path, the printed tables are checked)
"""
import re
import sys
from mpmath import mp, mpf, sqrt, cos, acos, pi, degrees, nstr

mp.dps = 30


def cos_psi(B):
    return -(B**4 - 2 * B**3 - 2 * B**2 - 2 * B + 1) / (B**2 + 1) ** 2


def B_res(n):
    eta = (sqrt(5 + 4 * cos(pi / n)) - 1) / 2
    return (1 + sqrt(1 - eta**2)) / eta


def angle_at(x, y, z):
    """Angle at the center of the circle of radius x, for mutually tangent radii x, y, z."""
    a, b, c = x + y, x + z, y + z          # c is opposite the vertex of radius x
    return acos((a * a + b * b - c * c) / (2 * a * b))


def cell_angles(B):
    one, b, b2 = mpf(1), B, B**2
    return [degrees(angle_at(one, b, b2)), degrees(angle_at(b, one, b2)),
            degrees(angle_at(b2, one, b))]


rows_Bn = []
for n in range(2, 10):
    B = B_res(n)
    assert abs(acos(cos_psi(B)) - pi / n) < mpf(10) ** -25
    tO, tP1, tP0 = cell_angles(B)
    assert abs((tO - tP0) - mpf(180) / n) < mpf(10) ** -20      # Prop 7.1
    rows_Bn.append((str(n), nstr(B, 11, strip_zeros=False), nstr(B**2, 8, strip_zeros=False),
                    f"{float(tO):.3f}", f"{float(tP1):.3f}", f"{float(tP0):.3f}"))
phi = (1 + sqrt(5)) / 2
tO, tP1, tP0 = cell_angles(phi)
rows_Bn.append(("phi", nstr(phi, 11, strip_zeros=False), nstr(phi**2, 8, strip_zeros=False), f"{float(tO):.3f}", f"{float(tP1):.3f}",
                f"{float(tP0):.3f}"))

print("Table tab:Bn  (n, B_n, A_n = B_n^2, theta_O, theta_P1, theta_P0 in degrees)")
for r in rows_Bn:
    print("  " + "  ".join(r))

rows_bds = []
for n in (2, 9):
    B = B_res(n)
    rows_bds.append((str(n), f"{float(B**2):.4f}", f"{float(1 / B):.4f}", f"{float(B):.4f}"))
print("\nTable tab:bdscompare, our side  (n, B_n^2, 1/B_n, B_n), to compare with BDS Table I")
for r in rows_bds:
    print("  " + "  ".join(r))

if len(sys.argv) > 1:
    tex = open(sys.argv[1], encoding="utf-8").read()
    bad = 0
    body = tex[tex.index(r"\label{tab:Bn}"):]
    body = body[:body.index(r"\end{tabular}")]
    printed = [ln for ln in body.splitlines() if "&" in ln and "$n$" not in ln]
    for r, ln in zip(rows_Bn, printed):
        cells = [c.strip().replace(r"$^{\circ}$", "").replace(r"\\", "").strip()
                 for c in ln.split("&")]
        cells[0] = "phi" if "gr" in cells[0] else cells[0]
        for got, want in zip(r, cells):
            if got != want:
                bad += 1
                print(f"tab:Bn mismatch, row {r[0]}: computed {got}, printed {want}")
    body = tex[tex.index(r"\label{tab:bdscompare}"):]
    body = body[:body.index(r"\end{tabular}")]
    for r in rows_bds:
        m = re.search(r"&\s*\$" + r[0] + r"\$\s*&\s*\$([^$]*)\$", body)
        want = re.findall(r"[0-9.]+", m.group(1))
        got = [r[1], r[1], r[2], r[3]]
        if got != want:
            bad += 1
            print(f"tab:bdscompare mismatch, n={r[0]}: computed {got}, printed {want}")
    print(f"\nchecked against {sys.argv[1]}: {'all values agree' if bad == 0 else f'{bad} mismatches'}")
