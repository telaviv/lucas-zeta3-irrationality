"""Exact check of `Integrality ε` (LucasU/Statements.lean) for small K, both signs.

Builds Delta_K(X) over Q(τ) exactly as in LucasU/Defs.lean (moments nu_k, tails psi_N,
nodes w^{-a}, Hankel matrix of L_X(s^{i+j}/D_K)), multiplies each X-coefficient by
C_K(τ) = prod_{d <= 4K} Phi_d(τ)^{b_{K,d}} and checks that the result is a Laurent polynomial
in τ (denominator a power of τ).  Run: python check_integrality.py [Kmax]
"""
import sys
from math import gcd
import sympy as sp

t, X, s = sp.symbols('tau X s')


def order_mod(num, den):
    # order of exp(2 pi i num/den) as a root of unity
    return den // gcd(num % den, den)


def eW(eps, d):
    # w(zeta) = eps zeta^2 = exp(2 pi i (2/d + [eps=-1]/2))
    num, den = (4, 2 * d) if eps == 1 else (4 + d, 2 * d)
    return order_mod(num, den)


def is_alpha_root(eps, d, k):
    # alpha_k(zeta) = eps^{k+1} zeta^{2k+1}
    sgn = 0 if (eps == 1 or (k + 1) % 2 == 0) else 1
    num = 2 * (2 * k + 1) + sgn * d
    return num % (2 * d) == 0


def cW(m):
    return sum(m + 2 - 2 * j for j in range(m - 1)) if m >= 1 else 0


def cWp(m):
    return sum(m + 2 - 2 * j for j in range(m))


def cluster_size(K, e, r):
    return sum(1 for a in range(1, K + 1) if a % e == r % e)


def nExp(eps, K, d):
    e = eW(eps, d)
    nw = 0
    if 1 <= e <= K:
        nw = sum(cW(cluster_size(K, e, r)) for r in range(1, e)) + cWp(cluster_size(K, e, e))
    ks = [k for k in range(1, K - 1) if is_alpha_root(eps, d, k)]
    na = K - 1 - ks[0] if ks else 0
    return nw + na


def Delta(eps, K):
    w = eps * t**2
    alpha = lambda k: eps * t * w**k
    nu = lambda k: sp.Integer(0) if k == 0 else k * (k + 1) * alpha(k) / (1 - alpha(k))
    psi = lambda N: t**(3 * N) / (1 - w**N)**3
    S = lambda a: sum(psi(N) for N in range(1, a + 1))
    node = lambda a: w**(-a)
    F = sp.prod([s - node(a) for a in range(1, K + 1)])
    Fp = sp.diff(F, s)
    nrm = (-1)**K / w**(K * (K + 1) // 2)

    def entry(k):
        q, _ = sp.div(sp.Poly(s**k, s), sp.Poly(F, s))
        Lq = sum(c * nu(j) for (j,), c in q.terms())
        res = [node(a)**k / Fp.subs(s, node(a)) for a in range(1, K + 1)]
        mC = Lq + 2 * sum(res[a - 1] * t**a * S(a) for a in range(1, K + 1))
        mL = -2 * sum(res[a - 1] * t**a for a in range(1, K + 1))
        return nrm * (X * mL + mC)

    M = sp.Matrix(K, K, lambda i, j: entry(i + j))
    return sp.Poly(sp.together(M.det()), X)


def check(eps, K):
    CK = sp.prod([sp.cyclotomic_poly(d, t)**nExp(eps, K, d) for d in range(1, 4 * K + 1)])
    D = Delta(eps, K)
    ok = True
    for c in D.all_coeffs():
        num, den = sp.fraction(sp.cancel(sp.together(c * CK)))
        den = sp.Poly(den, t)
        if den.degree() > 0 and den != sp.Poly(den.LC() * t**den.degree(), t):
            ok = False
        # integer coefficients after clearing the power of tau
        numP = sp.Poly(num, t)
        if not all((sp.Rational(x) / den.LC()).q == 1 for x in numP.coeffs()):
            ok = False
    return ok


if __name__ == '__main__':
    Kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for eps in (1, -1):
        for K in range(1, Kmax + 1):
            print(f"eps={eps:+d} K={K}: {'OK' if check(eps, K) else 'FAIL'}", flush=True)
