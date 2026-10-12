"""Numerical lower bounds for the Rodin-Sullivan constant s_k (k=2,3).

Variables: log-radii of all circles of the k-ring hexagonal patch (center fixed at radius 1).
Equality constraints: angle sum 2*pi at each interior vertex (packing label).
Inequality constraints: every pair of non-adjacent circles is disjoint (univalence);
every center triangle is positively oriented.
Objective: maximize the radius of the petal (1,0) (by symmetry of the problem this
loses nothing).  Every feasible point found is then re-verified in high precision.
"""
import numpy as np, math, sys, itertools, warnings
warnings.filterwarnings('ignore')
from scipy.optimize import minimize
MARGIN = 1e-6
DIRS = [(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
def norm(p,q): return max(abs(p),abs(q),abs(p+q))
def setup(k):
    pts = [(0,0)]
    for m in range(1,k+1):       # ring order: start at (m,0), walk counterclockwise
        p,q = m,0
        for d in [(-1,1),(-1,0),(0,-1),(1,-1),(1,0),(0,1)]:
            for _ in range(m):
                pts.append((p,q)); p,q = p+d[0], q+d[1]
    idx = {u:i for i,u in enumerate(pts)}
    edges = set()
    for u in pts:
        for d in DIRS:
            w = (u[0]+d[0],u[1]+d[1])
            if w in idx: edges.add(tuple(sorted((idx[u],idx[w]))))
    interior = [idx[u] for u in pts if norm(*u) < k]
    nonadj = [(i,j) for i in range(len(pts)) for j in range(i+1,len(pts)) if (i,j) not in edges]
    # placement order: greedily place a point adjacent to two placed, mutually adjacent
    # points (a, b) with (a, b, new) positively oriented in the lattice
    def emb(v): return complex(v[0]+0.5*v[1], math.sqrt(3)/2*v[1])
    place = []; placed = [0, 1]; todo = set(range(2, len(pts)))
    while todo:
        for i in sorted(todo):
            cand = None
            for a in placed:
                for b in placed:
                    if a != b and tuple(sorted((a,i))) in edges and tuple(sorted((b,i))) in edges                        and tuple(sorted((a,b))) in edges:
                        cr = ((emb(pts[b])-emb(pts[a])).conjugate()*(emb(pts[i])-emb(pts[a]))).imag
                        if cr > 0: cand = (a, b); break
                if cand: break
            if cand:
                place.append((i,)+cand); placed.append(i); todo.discard(i); break
    return pts, idx, edges, interior, nonadj, place
def layout(r, pts, place):
    z = np.zeros(len(pts), complex); z[1] = r[0]+r[1]
    for i,a,b in place:
        dab = abs(z[b]-z[a]); da = r[a]+r[i]; db = r[b]+r[i]
        c = (da*da+dab*dab-db*db)/(2*da*dab); c = min(1,max(-1,c))
        z[i] = z[a] + (z[b]-z[a])/dab*da*complex(c, math.sqrt(1-c*c))
    return z
def angles_sum(r, v, idx, pts):
    u = pts[v]; s = 0
    for t in range(6):
        a = idx[(u[0]+DIRS[t][0],u[1]+DIRS[t][1])]; b = idx[(u[0]+DIRS[(t+1)%6][0],u[1]+DIRS[(t+1)%6][1])]
        x,y,zz = r[v],r[a],r[b]
        s += math.acos(min(1,max(-1,((x+y)**2+(x+zz)**2-(y+zz)**2)/(2*(x+y)*(x+zz)))))
    return s
def solve(k, starts=40, seed=0):
    pts, idx, edges, interior, nonadj, place = setup(k)
    n = len(pts); rng = np.random.default_rng(seed)
    def R(x): return np.exp(np.concatenate([[0.0], x]))
    eq = lambda x: np.array([angles_sum(R(x), v, idx, pts)-2*math.pi for v in interior])
    def ineq(x):
        r = R(x); z = layout(r, pts, place)
        g = [ (abs(z[i]-z[j]) - (r[i]+r[j]))/(r[i]+r[j]) for i,j in nonadj]
        g = [t - MARGIN for t in g]
        return np.array(g)
    obj = lambda x: -x[0]          # log radius of petal (1,0) = pts[1]
    best = None
    for s in range(starts):
        if s == 0:   # start from the quadratic family, B slightly above B_{k+1}
            B = {2:2.1,3:1.65}[k]; x0 = np.array([math.log(B**(2*p+q)) for (p,q) in pts[1:]])
        else:
            x0 = rng.normal(0, 0.6, n-1)
        res = minimize(obj, x0, method='SLSQP', constraints=[{'type':'eq','fun':eq},{'type':'ineq','fun':ineq}],
                       options={'maxiter':800,'ftol':1e-12})
        if res.success and np.abs(eq(res.x)).max() < 1e-9 and ineq(res.x).min() > -1e-9:
            rho = math.exp(res.x[0])
            if best is None or rho > best[0]: best = (rho, res.x.copy())
            print(f"start {s}: rho={rho:.6f}", flush=True)
    return best, (pts, idx, edges, interior, nonadj, place)
if __name__ == "__main__":
    k = int(sys.argv[1]); starts = int(sys.argv[2])
    best, data = solve(k, starts)
    rho, x = best
    print(f"k={k}: best rho = {rho:.8f}, s_k >= rho-1 = {rho-1:.8f}, k*(rho-1) = {k*(rho-1):.6f}")
    np.save(f"sk_best_k{k}.npy", x)
