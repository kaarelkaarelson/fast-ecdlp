"""Plain, independent brute force for point decompositions (no network code)."""
import itertools

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def next_prime(n):
    while not is_prime(n): n += 1
    return n

def ceil_root(p, m):
    B = 1
    while B ** m < p: B += 1
    return B

def curve_points(p, a, b):
    sq = {}
    for y in range(p): sq.setdefault(y * y % p, []).append(y)
    pts = []
    for x in range(p):
        for y in sq.get((x ** 3 + a * x + b) % p, []): pts.append((x, y))
    return pts

def add(P, Q, p, a):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1 + a) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)

def factor_base(p, a, b, m):
    B = ceil_root(p, m)
    return B, [P for P in curve_points(p, a, b) if P[0] < B]

def xbits(x, ell): return format(x, '0%db' % ell)

def distribution(p, a, b, m):
    """dict R -> (full_tuples, generic_tuples) where each value is a list of tuples (ordered)."""
    B, F = factor_base(p, a, b, m)
    full, gen = {}, {}
    for tup in itertools.product(F, repeat=m):
        S = None; generic = True
        for k, P in enumerate(tup):
            if k >= 1 and (S is None or S[0] == P[0]): generic = False
            S = add(S, P, p, a)
        if S is None: continue
        full.setdefault(S, []).append(tup)
        if generic: gen.setdefault(S, []).append(tup)
    return B, F, full, gen

def count(tuples, ell, prefix):
    return sum(1 for t in tuples if ''.join(xbits(P[0], ell) for P in t).startswith(prefix))
