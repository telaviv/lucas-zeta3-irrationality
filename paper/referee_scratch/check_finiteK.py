"""Referee check of the closing remark: (log|N C_K(t)| + log|Delta_K(Xi)| + log|sigma Delta_K(-Xi)|)/(K^3 log eta).
Usage: python check_finiteK.py P Q K dps
"""
import sys
import mpmath as mp
from flint import fmpz_poly
from check_analytic import entries
from check_local_bounds import bound

P, Q, K, dps = map(int, sys.argv[1:5])
mp.mp.dps = dps
D = P * P - 4 * Q
eta = (P + mp.sqrt(D)) / 2
t = 1 / eta; st = Q / t; w = Q * t ** 2
Xi = mp.nsum(lambda N: t ** (3 * N) / (1 - w ** N) ** 3, [1, mp.inf])
Y, _ = entries(P, Q, t, K, Xi)
dR = mp.det(mp.matrix([[Y[i + j] for j in range(K)] for i in range(K)]))
Ys, _ = entries(P, Q, st, K, -Xi)
dC = mp.det(mp.matrix([[Ys[i + j] for j in range(K)] for i in range(K)]))
logNC = mp.mpf(0); costsum = 0
for d in range(1, 4 * K + 1):
    b = bound(Q, K, d)
    if b:
        cf = [int(c) for c in fmpz_poly.cyclotomic(d).coeffs()][::-1]
        logNC += float(b) * (mp.log(abs(mp.polyval(cf, t))) + mp.log(abs(mp.polyval(cf, st))))
L = mp.log(eta)
print(f"(P,Q)=({P},{Q}) K={K} dps={dps}: logNC/K^3logeta={mp.nstr(logNC/(K**3*L),6)} "
      f"log|Delta|/..={mp.nstr(mp.log(abs(dR))/(K**3*L),8)} log|sDelta|/..={mp.nstr(mp.log(abs(dC))/(K**3*L),8)} "
      f"TOTAL={mp.nstr((logNC+mp.log(abs(dR))+mp.log(abs(dC)))/(K**3*L),6)}")
