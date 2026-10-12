"""k=3: SLSQP on all log-radii (angle-sum equalities, univalence inequalities),
starts = Doyle spirals D_B near B*_3 with small random perturbations."""
import numpy as np, math, warnings
from scipy.optimize import minimize
import sk_optimize as S
warnings.filterwarnings('ignore')
pts, idx, edges, interior, nonadj, place = S.setup(3)
R = lambda x: np.exp(np.concatenate([[0.0], x]))
eq = lambda x: np.array([S.angles_sum(R(x), v, idx, pts)-2*math.pi for v in interior])
def ineq(x):
    r = R(x); z = S.layout(r, pts, place)
    return np.array([(abs(z[i]-z[j])-(r[i]+r[j]))/(r[i]+r[j]) - 1e-6 for i, j in nonadj])
rng = np.random.default_rng(7); best = None
for s in range(40):
    B = 1.60 + 0.09*rng.random()
    x0 = np.array([(2*p+q)*math.log(B) for (p, q) in pts[1:]]) + (0 if s == 0 else rng.normal(0, 0.05*(1+s//10), len(pts)-1))
    res = minimize(lambda x: -x[0], x0, method='SLSQP',
                   constraints=[{'type': 'eq', 'fun': eq}, {'type': 'ineq', 'fun': ineq}],
                   options={'maxiter': 3000, 'ftol': 1e-12})
    ok = np.abs(eq(res.x)).max() < 1e-9 and ineq(res.x).min() > -1e-9
    rho = math.exp(res.x[0])
    print(f"start {s}: B0={B:.3f} rho={rho:.6f} feasible={ok}", flush=True)
    if ok and (best is None or rho > best[0]): best = (rho, res.x.copy()); np.save('sk_best_k3.npy', res.x)
print("best", best[0] if best else None)
