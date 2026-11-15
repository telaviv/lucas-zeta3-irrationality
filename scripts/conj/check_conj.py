# Numerical checks for the LucasU ConjBound proof plan (tau' = eps/t, X = -Xi), eps = +-1, 0 < t <= 1/phi.
from mpmath import mp, mpf, sqrt, nsum, inf, binomial
mp.dps = 120
phi = (1 + sqrt(5)) / 2

def polymul(a, b):
    r = [mpf(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r

def polydiv(num, den):
    num = num[:]; q = [mpf(0)] * max(1, len(num) - len(den) + 1)
    for i in range(len(num) - len(den), -1, -1):
        c = num[i + len(den) - 1] / den[-1]; q[i] = c
        for j in range(len(den)): num[i + j] -= c * den[j]
    return q

def check(eps, t):
    wp = lambda tau: eps * tau**2
    psi = lambda tau, N: tau**(3 * N) / (1 - wp(tau)**N)**3
    alpha = lambda tau, k: (eps * tau) * wp(tau)**k
    tau = eps / t; w = wp(t)
    Xi = nsum(lambda N: psi(t, N), [1, inf])
    assert abs(wp(tau) - 1 / w) < mpf(10)**-100
    for N in range(1, 12): assert abs(psi(tau, N) + psi(t, N)) < mpf(10)**-80
    for k in range(0, 10):
        assert abs(alpha(tau, k) - eps / alpha(t, k)) < mpf(10)**-80
        nu = k * (k + 1) * alpha(tau, k) / (1 - alpha(tau, k))
        assert abs(nu) <= k * (k + 1) / (1 - t) + mpf(10)**-80
    worst = 0
    for K in [1, 2, 3, 5]:
        r = [None] + [w**a for a in range(1, K + 1)]
        W = [None] + [1 / mp.fprod([r[a] - r[b] for b in range(1, K + 1) if b != a]) for a in range(1, K + 1)]
        E = lambda m: sum(r[a]**m * W[a] for a in range(1, K + 1))
        for m in range(4 * K + 5): assert abs(E(m)) <= (1 / (1 - t**2))**K
        F = [mpf(1)]
        for a in range(1, K + 1): F = polymul(F, [-r[a], mpf(1)])
        nu = lambda k: k * (k + 1) * alpha(tau, k) / (1 - alpha(tau, k))
        S = lambda a: sum(psi(tau, N) for N in range(1, a + 1))
        for k in range(0, 2 * K - 1):
            q = polydiv([mpf(0)] * k + [mpf(1)], F) if k >= K else [mpf(0)]
            res = [None] + [r[a]**k * W[a] for a in range(1, K + 1)]
            P = sum(q[j] * nu(j) for j in range(len(q)))
            mc = P + 2 * sum(res[a] * tau**a * S(a) for a in range(1, K + 1))
            ml = -2 * sum(res[a] * tau**a for a in range(1, K + 1))
            T = mc - Xi * ml
            T3 = P + nsum(lambda M: 2 * t**(3 * M) * nsum(lambda j: binomial(j + 2, 2) * w**(M * j) * E(k + 1 + j), [0, inf]), [1, inf])
            assert abs(T - T3) < mpf(10)**-40, (eps, t, K, k, T, T3)
            worst = max(worst, abs(T))
    print('eps', eps, 't', mp.nstr(t, 8), 'max|T_k|', mp.nstr(worst, 8))

for eps in (1, -1):
    for t in (1 / phi, 1 / (1 + sqrt(2)), 2 / (3 + sqrt(5)), mpf(1) / 10):
        check(eps, t)
print('all checks OK')
