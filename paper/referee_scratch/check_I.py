"""I = int_0^1 x l(x) dx, l piecewise linear with l(1/m) = c(m)/m."""
from fractions import Fraction as Fr
def c(m): return 2*sum(max(Fr(0), Fr(m+2,2)-j) for j in range(0, m-1))
I = Fr(0); M = 4000
for m in range(1, M):
    a, b = Fr(1, m+1), Fr(1, m)          # interval [a,b]
    la, lb = c(m+1)/(m+1), c(m)/m
    # l(x) = la + (lb-la)(x-a)/(b-a); integrate x*l(x)
    s = (lb-la)/(b-a)
    F = lambda x: la*x*x/2 + s*(x**3/3 - a*x*x/2)
    I += F(b) - F(a)
# tail [0, 1/M]: x l(x) between 1/4*(1 - ...) ; x*l(x) = x*c/m ~ (m+3)^2/(4m^2)... bounded by ~1/4+; add bounds
lo = I + Fr(0); hi = I + Fr(1, M)* Fr(1,4)*Fr((M+3)**2, M**2)
print(float(lo), float(hi))
