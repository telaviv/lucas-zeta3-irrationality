"""Numerical check of LucasU.EntryIdentity and the constant-free part of DecayBound
for eps = +1 and -1 at several t in (0, 1/phi].  [Numerical]

Entry: nrm*(mConst + Xi*mLin) (formal side, LucasU/Defs.lean) versus
Lfun(s^k/D_K) = sum_n rho^n [theta(theta+1) h](w^n) (direct node sum).
Also checks t^2 <= 1/2 on the range (the only golden-ratio input of the decay proof).
"""
from mpmath import mp, mpf, sqrt, diff, nsum, inf, matrix, det
mp.dps = 40
phi = (1 + sqrt(5)) / 2

def run(eps, t, K):
    w = eps * t**2; rho = eps * t
    psi = lambda N: t**(3*N) / (1 - w**N)**3
    Xi = nsum(psi, [1, inf])
    S = lambda a: sum(psi(N) for N in range(1, a + 1))
    alpha = lambda k: rho * w**k
    nu = lambda k: k*(k+1)*alpha(k)/(1-alpha(k))
    nodes = [w**(-a) for a in range(1, K+1)]
    def Fd(x):  # F'(x) at node x
        p = mpf(1)
        for y in nodes:
            if y != x: p *= (x - y)
        return p
    # polynomial quotient X^k // F: coefficients via long division
    Fc = [mpf(1)]
    for y in nodes:  # multiply by (X - y), coefficients high->low
        Fc = [a - (y * b if i > 0 else 0) for i, (a, b) in enumerate(zip(Fc + [0], [0] + Fc))]
    def entry_formal(k):
        num = [mpf(1)] + [mpf(0)] * k  # X^k high->low
        q = []
        while len(num) >= len(Fc):
            c = num[0] / Fc[0]; q.append(c)
            num = [a - c * b for a, b in zip(num, Fc + [0] * (len(num) - len(Fc)))][1:]
        deg = len(q) - 1
        Lq = sum(c * nu(deg - i) for i, c in enumerate(q))
        res = [nodes[a-1]**k / Fd(nodes[a-1]) for a in range(1, K+1)]
        mC = Lq + 2 * sum(res[a-1] * t**a * S(a) for a in range(1, K+1))
        mL = -2 * sum(res[a-1] * t**a for a in range(1, K+1))
        AK = K*(K+1)//2
        nrm = (-1)**K / w**AK
        return nrm * (mC + Xi * mL)
    def entry_direct(k):
        D = lambda s: mp.fprod([1 - w**a * s for a in range(1, K+1)])
        h = lambda s: s**k / D(s)
        def th(x):
            return x**2 * diff(h, x, 2) + 2 * x * diff(h, x, 1)
        return nsum(lambda n: rho**n * th(w**n), [1, inf])
    err = max(abs(entry_formal(k) - entry_direct(k)) for k in range(0, 2*K + 1))
    return err

for eps in (1, -1):
    for t in (mpf('0.2'), mpf('0.45'), 1/phi):
        e = run(eps, t, 3)
        print(f"eps={eps:+d} t={float(t):.4f}  max |formal - direct| over k<=2K: {float(e):.2e}")
print("phi^-2 =", float(1/phi**2), "<= 1/2:", 1/phi**2 <= mpf(1)/2)
