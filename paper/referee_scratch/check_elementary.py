"""Referee checks: root types, totient identity, cluster constants, c_*, E_1, C_0, a_j sum."""
from fractions import Fraction as Fr
from math import gcd, ceil
import mpmath as mp

def order(x, n):
    """order of exp(2 pi i x / n)"""
    x %= n
    return n // gcd(x, n)

def types(Q, d):
    # work with exponents mod 2d: zeta = exp(2 pi i *2/(2d)), -1 = exp(2 pi i * d/(2d))
    n = 2 * d
    z = 2
    q = d if Q == -1 else 0
    w = (q + 2 * z) % n
    e = order(w, n)
    kmin = None
    for k in range(1, 10 * d + 10):
        if ((k + 1) * q + (2 * k + 1) * z) % n == 0:
            kmin = k
            break
    return e, kmin

def paper_types(Q, d):
    if Q == -1:
        if d % 2 == 1: e = 2 * d
        elif d % 4 == 2: e = d
        elif d % 8 == 4: e = d // 4
        else: e = d // 2
        if d % 4 == 3: k = (d - 1) // 2
        elif d % 4 == 1: k = (3 * d - 1) // 2
        elif d == 2: k = 2
        elif d % 8 == 2: k = (d - 2) // 4
        elif d % 8 == 6: k = (3 * d - 2) // 4
        else: k = None
    else:
        e = d if d % 2 == 1 else d // 2
        if d % 2 == 0: k = None
        elif d == 1: k = 1
        else: k = (d - 1) // 2
    return e, k

bad = []
for Q in (-1, 1):
    for d in range(1, 400):
        if types(Q, d) != paper_types(Q, d):
            bad.append((Q, d, types(Q, d), paper_types(Q, d)))
print("root-type mismatches:", bad[:10], len(bad))

def phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)

ok = True
for Q in (-1, 1):
    for e in range(1, 150):
        s = sum(phi(d) for d in range(1, 4 * e + 1) if paper_types(Q, d)[0] == e)
        if s != 2 * phi(e): ok = False; print("totient fail", Q, e, s)
print("sum_{e(d)=e} phi(d) = 2 phi(e):", ok)

# alpha-count: #{zeta : alpha_j(zeta)=1} = 2j+1 for both signs; check by counting d with d | ... via types
for Q in (-1, 1):
    for j in range(1, 60):
        cnt = 0
        for d in range(1, 4 * j + 3):
            n = 2 * d; q = d if Q == -1 else 0
            # primitive d-th roots zeta^m, m coprime to d; alpha_j(zeta^m)=1 iff ...; types depend only on d
            if ((j + 1) * q + (2 * j + 1) * 2) % n == 0:
                cnt += phi(d)
        assert cnt == 2 * j + 1, (Q, j, cnt)
print("alpha_j count = 2j+1: ok")

# c(m), c'(m)
def c(m): return 2 * sum(max(Fr(0), Fr(m + 2, 2) - j) for j in range(0, m - 1))
def cp(m): return 2 * sum(max(Fr(0), Fr(m + 2, 2) - j) for j in range(0, m))
assert c(1) == 0 and cp(1) == 3
for m in range(1, 300):
    if m <= 6: assert c(m) == 4 * (m - 1)
    assert c(m) <= Fr((m + 3) ** 2, 4)
    assert 0 <= cp(m) - c(m) <= 3
    delta = c(m) - 4 * (m - 1)
    assert 0 <= delta <= Fr(max(0, m - 5) ** 2, 4), m
print("c, c' claims ok")

# W-part cluster inequality
for K in range(2, 120):
    for e in range(1, K + 1):
        ms = [len([a for a in range(1, K + 1) if (a - r) % e == 0]) for r in range(1, e + 1)]
        lhs = sum(c(m) for m in ms[:-1]) + cp(ms[-1])
        rhs = 4 * (K - e) + Fr(max(0, K - 4 * e) ** 2, 4 * e) + 3
        assert lhs <= rhs, (K, e, lhs, rhs)
print("cluster inequality ok to K=119")

# a_j formula
for K in range(2, 300):
    a = lambda j: sum(ceil(u / 3) for u in range(1, j + 1))
    lhs = 2 * sum(a(j) for j in range(K))
    iota = {0: 0, 1: 4, 2: 2}[K % 3]
    assert 9 * lhs == K ** 3 + 3 * K ** 2 - iota, (K, lhs)
print("2 sum a_j formula ok")

beta7 = Fr(3, 4) * Fr(8, 9) * Fr(24, 25) * Fr(48, 49)
cstar = Fr(11, 8) * beta7 + Fr(1, 3)
print("beta7", beta7, "c*", cstar, float(cstar), "c*-11/9", float(cstar - Fr(11, 9)), "121/100 check", cstar < Fr(121, 100) < Fr(11, 9))
# mean of g7 over period 210
g7 = lambda e: __import__('math').prod([(1 - Fr(1, p)) for p in (2, 3, 5, 7) if e % p == 0])
print("mean g7", sum(g7(e) for e in range(1, 211)) / 210 == beta7)
# integral of f_K / K^3
print("int f_K/K^3 -> 4/3+1/24 =", Fr(4, 3) + Fr(1, 24))

mp.mp.dps = 30
phi_g = (1 + mp.sqrt(5)) / 2
E1 = mp.nsum(lambda a: -mp.log(1 - phi_g ** (-a)), [1, mp.inf])
C0 = mp.nprod(lambda i: 1 / (1 - phi_g ** (-2 * i)), [1, mp.inf])
print("E1", E1, "C0", C0)
t = 1 / phi_g
print("2t^3/(1-t^2)^3", 2 * t ** 3 / (1 - t ** 2) ** 3, "1/(1-t^3)", 1 / (1 - t ** 3), "phi^2/2", phi_g ** 2 / 2)
I_hi = mp.mpf('0.6831236')
print("sharp Q=-1", (12 * I_hi + mp.mpf(80) / 27) / mp.pi ** 2, "Q=1", (12 * I_hi + mp.mpf(8) / 3) / mp.pi ** 2)
print("margins", mp.mpf(11) / 9 - (12 * I_hi + mp.mpf(80) / 27) / mp.pi ** 2, mp.mpf(11) / 9 - (12 * I_hi + mp.mpf(8) / 3) / mp.pi ** 2)

# odd-d alpha contribution for Q=1, sharp: sum_{d odd, (d-1)/2<=K-2} (K-1-(d-1)/2) phi(d) / K^3 -> 8/(3 pi^2)?
for K in (100, 300, 600):
    s = 0
    for d in range(1, 2 * K + 1, 2):
        km = 1 if d == 1 else (d - 1) // 2
        s += max(0, K - 1 - km) * phi(d)
    print("Q=1 alpha part /K^3", K, s / K ** 3, float(8 / (3 * mp.pi ** 2)))
