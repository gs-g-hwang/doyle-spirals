"""Minimal polynomials, degrees, units and Salem property of the resonant B_n."""
import sympy as sp, time
x = sp.symbols('x')
print("n deg 2phi(2n) lead const palin outside onUC")
for n in range(2, 17):
    t = time.time()
    c = sp.cos(sp.pi/n); eta = (sp.sqrt(5+4*c)-1)/2; Bn = (1+sp.sqrt(1-eta**2))/eta
    p = sp.Poly(sp.minimal_polynomial(Bn, x), x)
    co = p.all_coeffs(); 
    if co[0] < 0: co = [-a for a in co]
    rts = [complex(r) for r in p.nroots(n=40, maxsteps=200)]
    out = sum(abs(r) > 1+1e-12 for r in rts); on = sum(abs(abs(r)-1) < 1e-10 for r in rts)
    print(n, p.degree(), 2*sp.totient(2*n), co[0], co[-1], co == co[::-1], out, on, f"{time.time()-t:.1f}s", flush=True)
