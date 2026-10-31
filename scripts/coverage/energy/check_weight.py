"""Check, mod the prime P=2^31-1 with random inputs: Semaev S_n (S_n(x1..xn)=Res_u(S_{n-1}(x1..x_{n-2},u), S_3(x_{n-1},x_n,u)))
has degree 2^(n-2) in its last variable and satisfies S_n(l^2 x; l^4 A, l^6 B) = l^(w_n) S_n(x;A,B), w_n=(n-1)2^(n-1), n=3..6."""
import random
P = 2**31-1
def S3(a, b, c, A, B):
    return ((a-b)**2*c*c - 2*((a+b)*(a*b+A)+2*B)*c + (a*b-A)**2 - 4*B*(a+b)) % P
def det(M):
    n = len(M); M = [r[:] for r in M]; d = 1
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] % P), None)
        if piv is None: return 0
        if piv != i: M[i], M[piv] = M[piv], M[i]; d = -d
        d = d*M[i][i] % P; inv = pow(M[i][i], -1, P)
        for r in range(i+1, n):
            f = M[r][i]*inv % P
            for c in range(i, n): M[r][c] = (M[r][c]-f*M[i][c]) % P
    return d % P
def res(f, g):  # coefficient lists, highest degree first, formal degrees = len-1
    m, n = len(f)-1, len(g)-1; N = m+n; M = []
    for i in range(n): M.append([0]*i + f + [0]*(N-m-i))
    for i in range(m): M.append([0]*i + g + [0]*(N-n-i))
    return det(M)
def interp(vals, pts):  # Lagrange -> coeff list highest first
    n = len(pts); coef = [0]*n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = [( (num[k-1] if k > 0 else 0) - pts[j]*(num[k] if k < len(num) else 0)) % P for k in range(len(num)+1)] if False else None
    return None
def polymul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] = (r[i+j]+x*y) % P
    return r
def lagrange(pts, vals):  # coeffs low->high
    n = len(pts); out = [0]*n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = polymul(num, [-pts[j] % P, 1]); den = den*(pts[i]-pts[j]) % P
        c = vals[i]*pow(den, -1, P) % P
        for k in range(n): out[k] = (out[k]+c*num[k]) % P
    return out
def S(xs, A, B):
    n = len(xs)
    if n == 3: return S3(xs[0], xs[1], xs[2], A, B)
    d = 2**(n-3)                       # z-degree of S_{n-1}
    pts = list(range(1, d+2)); vals = [S(xs[:n-2]+[t], A, B) for t in pts]
    f = lagrange(pts, vals)[::-1]      # highest first, formal degree d
    g = [(xs[n-2]-xs[n-1])**2 % P, (-2*((xs[n-2]+xs[n-1])*(xs[n-2]*xs[n-1]+A)+2*B)) % P, ((xs[n-2]*xs[n-1]-A)**2-4*B*(xs[n-2]+xs[n-1])) % P]
    return res(f, g)
random.seed(5); ok = True
for n in range(3, 7):
    xs = [random.randrange(P) for _ in range(n)]; A, B = random.randrange(P), random.randrange(P)
    lam = 2; w = (n-1)*2**(n-1)
    s1 = S(xs, A, B); s2 = S([x*lam**2 % P for x in xs], A*lam**4 % P, B*lam**6 % P)
    good = s2 == s1*pow(lam, w, P) % P
    # degree in last variable: leading behaviour via interpolation of S_n(xs[:-1], t)
    d = 2**(n-2); pts = list(range(1, d+4)); vals = [S(xs[:-1]+[t], A, B) for t in pts]
    co = lagrange(pts, vals); deg = max(i for i, c in enumerate(co) if c)
    print(f"n={n} weight w_n={w} homogeneity {'OK' if good else 'FAIL'}; deg_z={deg} (expected {d})")
    ok &= good and deg == d
print("PASS semaev_weight" if ok else "FAIL semaev_weight")
