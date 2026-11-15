"""Referee check: exact cyclotomic multiplicities in the denominators of Delta_{K,tau}(X) versus the paper's b_{K,d}.

Exact arithmetic in Q(tau) with python-flint fmpq_poly.  Usage: python check_local_bounds.py Q Kmax
"""
import sys, json
from fractions import Fraction as Fr
from flint import fmpq_poly, fmpz_poly, fmpq

class RF:
    __slots__ = ("n", "d")
    def __init__(self, n, d=None, norm=True):
        if not isinstance(n, fmpq_poly): n = fmpq_poly([n]) if not isinstance(n, list) else fmpq_poly(n)
        if d is None: d = fmpq_poly([1])
        if norm and not n.is_zero():
            g = n.gcd(d)
            if g.degree() > 0:
                n = n // g; d = d // g
            lc = d.leading_coefficient()
            n = n / lc; d = d / lc
        elif n.is_zero():
            d = fmpq_poly([1])
        self.n, self.d = n, d
    def __add__(s, o):
        if not isinstance(o, RF): o = RF(o)
        if s.d == o.d: return RF(s.n + o.n, s.d)
        return RF(s.n * o.d + o.n * s.d, s.d * o.d)
    __radd__ = __add__
    def __neg__(s): return RF(-s.n, s.d, norm=False)
    def __sub__(s, o): return s + (-o if isinstance(o, RF) else RF(-o))
    def __rsub__(s, o): return RF(o) - s
    def __mul__(s, o):
        if not isinstance(o, RF): o = RF(o)
        return RF(s.n * o.n, s.d * o.d)
    __rmul__ = __mul__
    def inv(s): return RF(s.d, s.n)
    def __truediv__(s, o):
        if not isinstance(o, RF): o = RF(o)
        return s * o.inv()
    def iszero(s): return s.n.is_zero()
    def __pow__(s, k):
        if k < 0: return s.inv() ** (-k)
        return RF(s.n ** k, s.d ** k, norm=False)

TAU = RF(fmpq_poly([0, 1]))
ONE = RF(1)

def build(Q, K):
    w = TAU * TAU * Q
    wp = {0: ONE}
    for a in range(1, 2 * K + 2):
        wp[a] = wp[a - 1] * w
        wp[-a] = wp[a].inv()
    alpha = lambda k: RF(Q ** (k + 1)) * TAU ** (2 * k + 1)
    nu = [ (alpha(k) * (k * (k + 1)) / (ONE - alpha(k))) if k > 0 else RF(0) for k in range(2 * K)]
    lam = {a: RF(2 * Q ** a) * TAU ** (-a) for a in range(1, K + 1)}
    psi = {N: TAU ** (3 * N) / (ONE - wp[N]) ** 3 for N in range(1, K + 1)}
    S = {}
    acc = RF(0)
    for a in range(1, K + 1):
        acc = acc + psi[a]; S[a] = acc
    # D_K(s) coefficients (list in s, low to high)
    DK = [ONE]
    for a in range(1, K + 1):
        new = [RF(0)] * (len(DK) + 1)
        for i, cf in enumerate(DK):
            new[i] = new[i] + cf
            new[i + 1] = new[i + 1] - cf * wp[a]
        DK = new
    # residues denominators
    den_a = {}
    for a in range(1, K + 1):
        p = ONE
        for b in range(1, K + 1):
            if b != a: p = p * (ONE - wp[b - a])
        den_a[a] = p
    A, B = [], []
    for k in range(0, 2 * K - 1):
        # polynomial quotient of s^k by D_K
        num = [RF(0)] * k + [ONE]
        quot = [RF(0)] * max(0, k - K + 1)
        lead = DK[K]
        for i in range(k, K - 1, -1):
            cf = num[i]
            if cf.iszero(): continue
            qq = cf / lead
            quot[i - K] = qq
            for j in range(K + 1):
                num[i - K + j] = num[i - K + j] - qq * DK[j]
        a_k = RF(0)
        for j, qq in enumerate(quot):
            if not qq.iszero(): a_k = a_k + qq * nu[j]
        b_k = RF(0)
        for a in range(1, K + 1):
            res = wp[-a] ** 1  # x_a
            res = (wp[-a] ** k) / den_a[a]
            b_k = b_k + res * lam[a]
            a_k = a_k - res * lam[a] * S[a]
        A.append(a_k); B.append(b_k)
    return A, B

def det(M):
    M = [row[:] for row in M]
    n = len(M); sign = 1; d = ONE
    for c in range(n):
        piv = None
        for r in range(c, n):
            if not M[r][c].iszero(): piv = r; break
        if piv is None: return RF(0)
        if piv != c: M[c], M[piv] = M[piv], M[c]; sign = -sign
        p = M[c][c]; d = d * p
        pinv = p.inv()
        for r in range(c + 1, n):
            if M[r][c].iszero(): continue
            f = M[r][c] * pinv
            for cc in range(c + 1, n):
                M[r][cc] = M[r][cc] - f * M[c][cc]
    return d * sign

def mult(poly_q, cyc):
    """multiplicity of cyc (fmpz_poly) in fmpq_poly poly_q"""
    p = poly_q; m = 0
    c = fmpq_poly(cyc.coeffs())
    while p.degree() >= c.degree():
        qq, rr = divmod(p, c)
        if not rr.is_zero(): break
        p = qq; m += 1
    return m

from math import gcd
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

def c(m): return 2 * sum(max(Fr(0), Fr(m + 2, 2) - j) for j in range(0, m - 1))
def cp(m): return 2 * sum(max(Fr(0), Fr(m + 2, 2) - j) for j in range(0, m))

def bound(Q, K, d):
    e, k = paper_types(Q, d)
    alpha = k is not None and k <= K - 2
    if e <= K:
        ms = [len([a for a in range(1, K + 1) if (a - r) % e == 0]) for r in range(1, e + 1)]
        b = sum(c(m) for m in ms[:-1]) + cp(ms[-1])
        if alpha: b += max(0, K - 1 - k)
        return b
    if alpha: return max(0, K - 1 - k)
    return 0

if __name__ == "__main__":
    Q = int(sys.argv[1]); Kmax = int(sys.argv[2]); Kmin = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    out = {}
    for K in range(Kmin, Kmax + 1):
        A, B = build(Q, K)
        exact = {}
        integral_ok = True
        CK = fmpq_poly([1])
        for d in range(1, 4 * K + 1):
            b = bound(Q, K, d)
            if b: CK = CK * fmpq_poly(fmpz_poly.cyclotomic(d).coeffs()) ** int(b)
        for X0 in range(0, K + 1):
            M = [[A[i + j] + B[i + j] * X0 for j in range(K)] for i in range(K)]
            D = det(M)
            for d in range(1, 4 * K + 1):
                m = mult(D.d, fmpz_poly.cyclotomic(d))
                exact[d] = max(exact.get(d, 0), m)
            # check C_K * D is Laurent poly with integer coefficients
            prod = D * RF(CK)
            dd = prod.d
            # dd should be a monomial tau^n (monic)
            if any(dd.coeffs()[i] != 0 for i in range(dd.degree())):
                integral_ok = False
            if any(fmpq(cf).q != 1 for cf in prod.n.coeffs()):
                integral_ok = False
        rows = []
        worse = []
        for d in range(1, 4 * K + 1):
            b = bound(Q, K, d)
            if exact.get(d, 0) or b:
                rows.append((d, exact.get(d, 0), float(b)))
                if exact.get(d, 0) > b: worse.append(d)
        eq = sum(1 for r in rows if r[1] == r[2])
        print(f"Q={Q} K={K}: integral(C_K*Delta in Z[tau^+-1])={integral_ok}; exceed bound at d={worse}; "
              f"equality {eq}/{len(rows)}; (d, exact, bound): {rows}", flush=True)
        out[K] = {"integral": integral_ok, "worse": worse, "rows": rows}
        with open(f"local_bounds_Q{Q}.json", "w") as f: json.dump(out, f)
