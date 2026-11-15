"""Exact check of the crude cost count for both signs eps = +1, -1 (LucasU/Cost).

Root data at zeta = exp(2 pi i/d), in exact rational exponents (angles mod 1):
  w(zeta) = eps zeta^2 has angle (0 or 1/2) + 2/d;  alpha_k = eps^{k+1} zeta^{2k+1}.
Checks, for d <= 4K:
  (a) sum_{e(d)=e} phi(d) <= 2 phi(e);  (b) #{d : e(d)=e} <= 8;
  (c) sum_{alpha_j(zeta_d)=1} phi(d) <= 2j+1;
  (d) sum_d n_d phi(d) <= (4393/3675) K^3 + 6610008 K^2 and the ratio to K^3.
"""
from fractions import Fraction as Fr
from math import gcd
from sympy import totient

def order(angle):  # angle a Fraction mod 1
    return (angle % 1).denominator

def eW(eps, d):
    return order((Fr(0) if eps == 1 else Fr(1, 2)) + Fr(2, d))

def isAlpha(eps, d, k):
    return ((Fr(0) if eps == 1 or (k + 1) % 2 == 0 else Fr(1, 2)) + Fr(2 * k + 1, d)) % 1 == 0

def cW(m): return sum(m + 2 - 2 * j for j in range(max(m - 1, 0)))
def cWp(m): return sum(m + 2 - 2 * j for j in range(m))
def cl(K, e, r): return sum(1 for a in range(1, K + 1) if a % e == r % e)

def nW(eps, K, d):
    e = eW(eps, d)
    if 1 <= e <= K:
        return sum(cW(cl(K, e, r)) for r in range(1, e)) + cWp(cl(K, e, e))
    return 0

def nAlpha(eps, K, d):
    for k in range(1, K - 1):
        if isAlpha(eps, d, k):
            return K - 1 - k
    return 0

phi = {}
for eps in (1, -1):
    for K in [1, 2, 3, 5, 10, 20, 40, 80, 120]:
        N = 4 * K
        fib = {}
        for d in range(1, N + 1):
            fib.setdefault(eW(eps, d), []).append(d)
        for e, ds in fib.items():
            assert sum(int(totient(d)) for d in ds) <= 2 * int(totient(e)), (eps, e)
            assert len(ds) <= 8
        for j in range(1, K):
            assert sum(int(totient(d)) for d in range(1, N + 1) if isAlpha(eps, d, j)) <= 2 * j + 1
        sW = sum(nW(eps, K, d) * int(totient(d)) for d in range(1, N + 1))
        sA = sum(nAlpha(eps, K, d) * int(totient(d)) for d in range(1, N + 1))
        tot = sW + sA
        assert Fr(tot) <= Fr(4393, 3675) * K**3 + 6610008 * K**2
        print(f"eps={eps:+d} K={K:4d}  W/K^3={sW/K**3:.4f}  alpha/K^3={sA/K**3:.4f}  total/K^3={tot/K**3:.4f}")
print("all checks passed; crude bound 4393/3675 =", 4393 / 3675, "<= 1.21")
