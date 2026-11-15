"""Referee check: Binet/Xi identity, moments vs direct functional, decay and conjugate bounds, at several (P,Q)."""
import mpmath as mp
from math import ceil
mp.mp.dps = 600

def setup(P, Q, tau):
    w = Q * tau ** 2; rho = Q * tau
    return w, rho

def entries(P, Q, tau, K, X):
    w = Q * tau ** 2
    alpha = lambda k: Q ** (k + 1) * tau ** (2 * k + 1)
    nu = [k * (k + 1) * alpha(k) / (1 - alpha(k)) for k in range(2 * K)]
    lam = {a: 2 * Q ** a * tau ** (-a) for a in range(1, K + 1)}
    S = {}; acc = 0
    for a in range(1, K + 1):
        acc += tau ** (3 * a) / (1 - w ** a) ** 3; S[a] = acc
    DK = [mp.mpf(1)]
    for a in range(1, K + 1):
        new = [mp.mpf(0)] * (len(DK) + 1)
        for i, cf in enumerate(DK):
            new[i] += cf; new[i + 1] -= cf * w ** a
        DK = new
    den = {a: mp.fprod([1 - w ** (b - a) for b in range(1, K + 1) if b != a]) for a in range(1, K + 1)}
    Y = []
    for k in range(2 * K - 1):
        num = [mp.mpf(0)] * k + [mp.mpf(1)]
        quot = [mp.mpf(0)] * max(0, k - K + 1)
        for i in range(k, K - 1, -1):
            qq = num[i] / DK[K]; quot[i - K] = qq
            for j in range(K + 1): num[i - K + j] -= qq * DK[j]
        val = sum(quot[j] * nu[j] for j in range(len(quot)))
        for a in range(1, K + 1):
            val += (w ** (-a)) ** k / den[a] * lam[a] * (X - S[a])
        Y.append(val)
    return Y, DK

def direct_L(P, Q, t, g_poly_over_DK, K, nterms):
    """L(g) = sum rho^n [s^2 g'' + 2 s g'](w^n) for g = s^k/D_K, computed with mpmath.diff"""
    pass

def run(P, Q, Ks):
    D = P * P - 4 * Q
    eta = (P + mp.sqrt(D)) / 2
    t = 1 / eta; st = Q / t
    w = Q * t ** 2
    U = [mp.mpf(0), mp.mpf(1)]
    for n in range(2, 3000): U.append(P * U[-1] - Q * U[-2])
    zsum = mp.fsum(1 / U[n] ** 3 for n in range(1, 3000) if abs(U[n]) < mp.mpf(10) ** 500)
    Xi = mp.nsum(lambda N: t ** (3 * N) / (1 - w ** N) ** 3, [1, mp.inf])
    print(f"(P,Q)=({P},{Q}) D={D} eta={mp.nstr(eta,8)}: sum U^-3 - D sqrt(D) Xi = {mp.nstr(zsum - D*mp.sqrt(D)*Xi, 5)}")
    # moments check vs direct functional at K=3
    K = 3
    rho = Q * t
    def L(g):
        return mp.nsum(lambda n: rho ** n * (lambda s: s ** 2 * mp.diff(g, s, 2) + 2 * s * mp.diff(g, s, 1))(w ** int(n)), [1, 80])
    Y, DK = entries(P, Q, t, K, Xi)
    DKf = lambda s: mp.fsum(DK[i] * s ** i for i in range(len(DK)))
    mp.mp.dps = 60
    errs = [abs(L(lambda s, k=k: s ** k / DKf(s)) - Y[k]) for k in range(2 * K - 1)]
    mp.mp.dps = 600
    print("  max |L(s^k/D_K) direct - formula| (K=3):", mp.nstr(max(errs), 3))
    C0 = mp.nprod(lambda i: 1 / (1 - ((1 + mp.sqrt(5)) / 2) ** (-2 * i)), [1, mp.inf])
    ph = (1 + mp.sqrt(5)) / 2
    for K in Ks:
        Y, _ = entries(P, Q, t, K, Xi)
        dR = mp.det(mp.matrix([[Y[i + j] for j in range(K)] for i in range(K)]))
        Ys, _ = entries(P, Q, st, K, -Xi)
        dC = mp.det(mp.matrix([[Ys[i + j] for j in range(K)] for i in range(K)]))
        iota = {0: 0, 1: 4, 2: 2}[K % 3]
        decay_main = -mp.mpf(2) / 9 * (K ** 3 + 3 * K ** 2 - iota) * mp.log(eta)
        MK = C0 * (K ** 2 / ((1 - ph ** -3) * (1 - ph ** -2)) + ph ** 2)
        conj_bd = -K ** 2 * (K + 1) * mp.log(eta) + K * mp.log(mp.sqrt(K) * MK)
        lr = mp.log(abs(dR)); lc = mp.log(abs(dC))
        print(f"  K={K}: log|Delta(Xi)|={mp.nstr(lr,8)}  main term={mp.nstr(decay_main,8)}  (excess/K^2={mp.nstr((lr-decay_main)/K**2,4)});"
              f"  log|sDelta(-Xi)|={mp.nstr(lc,8)} <= bound {mp.nstr(conj_bd,8)}: {lc <= conj_bd}")

if __name__ == "__main__":
    for P, Q in [(1, -1), (2, -1), (3, 1), (4, -1), (7, 1), (10, -1)]:
        run(P, Q, [4, 6, 8, 10, 12])
