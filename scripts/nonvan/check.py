"""Numerical checks for LucasU/NonVan (eps = +-1, general 0 < t <= 1/phi).

* cauchyF_node: F(w^{-a}) = 2 t^a (Xi - S_a), F(z) = sum_{n>=1} 2 rho^n w^n z/(z - w^n)^3.
* cauchyF_inv_eq: F(1/u) = u sum_k nu_k u^k.
* Delta_K(Xi) != 0 for small K (Gram determinant of L(s^{i+j}/D_K) via the formal entries).
"""
from mpmath import mp, mpf, nsum, inf, matrix, det, sqrt
mp.dps = 60
phi = (1 + sqrt(5)) / 2

def check(eps, t):
    w, rho = eps * t**2, eps * t
    psi = lambda N: t**(3*N) / (1 - w**N)**3
    Xi = nsum(psi, [1, inf])
    S = lambda a: sum(psi(N) for N in range(1, a+1))
    F = lambda z: nsum(lambda n: 2*rho**n*w**n*z/(z - w**n)**3, [1, inf])
    err1 = max(abs(F(w**(-a)) - 2*t**a*(Xi - S(a))) for a in range(1, 6))
    nu = lambda k: k*(k+1)*rho*w**k/(1 - rho*w**k)
    u = mpf('0.3')
    err2 = abs(F(1/u) - u*nsum(lambda k: nu(int(k))*u**int(k), [0, inf]))
    # Hankel of the real functional L(h) = sum rho^n [theta(theta+1)h](w^n) on h = s^k / D_K
    dets = []
    for K in range(1, 6):
        def Lmon(k):
            def term(n):
                n = int(n); x = w**n
                f = lambda s: s**k / mp.fprod([1 - w**a*s for a in range(1, K+1)])
                return rho**n * (x**2*mp.diff(f, x, 2) + 2*x*mp.diff(f, x, 1))
            return nsum(term, [1, inf])
        M = matrix(K, K)
        for i in range(K):
            for j in range(K):
                M[i, j] = Lmon(i+j)
        dets.append(mp.nstr(det(M), 5))
    print(f"eps={eps:+d} t={mp.nstr(t,6)}: node err {mp.nstr(err1,3)}, inv err {mp.nstr(err2,3)}, Delta_K(Xi) K=1..5: {dets}")

mp.dps = 40
for eps in (1, -1):
    for t in (1/phi, mpf('0.4'), mpf('0.1')):
        check(eps, t)
