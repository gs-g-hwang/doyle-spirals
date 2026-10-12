"""High-precision verification of a k-ring packing found by sk_optimize.py.
Re-solves the interior radii from the boundary radii (Newton in mpmath), lays out,
and checks: all lattice edges tangent, all center triangles positively oriented,
all non-adjacent pairs disjoint (reports the minimal relative gap)."""
import numpy as np, mpmath as mp, sys, math
import sk_optimize as S
mp.mp.dps = 40
def verify(k, x):
    pts, idx, edges, interior, nonadj, place = S.setup(k)
    r = [mp.mpf(1)] + [mp.e**mp.mpf(float(t)) for t in x]
    def asum(rr, v):
        u = pts[v]; s = 0
        for t in range(6):
            a = idx[(u[0]+S.DIRS[t][0],u[1]+S.DIRS[t][1])]; b = idx[(u[0]+S.DIRS[(t+1)%6][0],u[1]+S.DIRS[(t+1)%6][1])]
            X,Y,Z = rr[v],rr[a],rr[b]
            s += mp.acos(((X+Y)**2+(X+Z)**2-(Y+Z)**2)/(2*(X+Y)*(X+Z)))
        return s
    # Newton on interior radii except the center (center fixed =1, its petals are interior unknowns
    # when k>=2); unknowns: interior vertices other than 0 -> but then 0's angle sum is extra.
    # Instead keep the center and boundary fixed, solve the other interior radii, then report
    # the residual angle sum at the center (should be ~1e-12 or better).
    unk = list(interior)
    def F(*ys):
        rr = list(r)
        for v,y in zip(unk, ys): rr[v] = mp.e**y
        return [asum(rr, v)-2*mp.pi for v in unk]
    y0 = [mp.log(r[v]) for v in unk]
    ys = mp.findroot(F, y0)
    ys = ys if hasattr(ys,'__len__') else [ys]
    for v,y in zip(unk, ys): r[v] = mp.e**y
    sc = r[0]; r = [t/sc for t in r]
    res0 = max(abs(asum(r, v) - 2*mp.pi) for v in interior)
    # layout
    z = [mp.mpc(0)]*len(pts); z[1] = mp.mpc(r[0]+r[1])
    for i,a,b in place:
        dab = abs(z[b]-z[a]); da = r[a]+r[i]; db = r[b]+r[i]
        c = (da*da+dab*dab-db*db)/(2*da*dab)
        z[i] = z[a] + (z[b]-z[a])/dab*da*mp.mpc(c, mp.sqrt(1-c*c))
    tang = max(abs(abs(z[i]-z[j])-(r[i]+r[j]))/(r[i]+r[j]) for i,j in edges)
    gap = min((abs(z[i]-z[j])-(r[i]+r[j]))/(r[i]+r[j]) for i,j in nonadj)
    # orientation of all lattice triangles
    def emb(v): return complex(v[0]+0.5*v[1], math.sqrt(3)/2*v[1])
    ori = []
    for u in pts:
        for d1,d2 in [((1,0),(0,1)),((0,1),(-1,1))]:
            a,b = (u[0]+d1[0],u[1]+d1[1]),(u[0]+d2[0],u[1]+d2[1])
            if a in idx and b in idx:
                i,j,l = idx[u],idx[a],idx[b]
                ori.append(mp.im(mp.conj(z[j]-z[i])*(z[l]-z[i]))/((r[i]+r[j])*(r[i]+r[l])))
    rho = max(r[idx[d]] for d in S.DIRS)/r[0]
    return dict(rho=rho, center_anglesum_residual=res0, max_tangency_err=tang, min_gap=gap, min_orientation=min(ori), r=r, z=z)
if __name__ == "__main__":
    k = int(sys.argv[1]); x = np.load(f"sk_best_k{k}.npy")
    v = verify(k, x)
    for key in ['rho','center_anglesum_residual','max_tangency_err','min_gap','min_orientation']:
        print(key, mp.nstr(v[key], 12))
    print('radii:', [mp.nstr(t,6) for t in v['r']])
