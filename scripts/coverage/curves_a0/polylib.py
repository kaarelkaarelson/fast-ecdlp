# minimal univariate polynomial arithmetic over F_p (lists, low degree first)
def trim(a):
    while a and a[-1]==0: a.pop()
    return a
def pmul(a,b,p):
    if not a or not b: return []
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    return trim(r)
def pdivmod(a,b,p):
    a=a[:]; q=[0]*max(0,len(a)-len(b)+1); inv=pow(b[-1],-1,p)
    while len(a)>=len(b) and a:
        c=a[-1]*inv%p; d=len(a)-len(b); q[d]=c
        for i,y in enumerate(b): a[i+d]=(a[i+d]-c*y)%p
        trim(a)
    return trim(q),a
def pgcd(a,b,p):
    a=trim(a[:]); b=trim(b[:])
    while b:
        a,b=b,pdivmod(a,b,p)[1]
    return a
def pder(a,p): return trim([(i*a[i])%p for i in range(1,len(a))])
def is_const_times_square(h,p):
    """h nonzero poly, deg < p. True iff h = c*g^2 over Fbar_p."""
    d=pder(h,p)
    if not d: return True
    g=pgcd(h,d,p)           # g = prod f^(e-1)
    # h = c*sq iff every multiplicity e_i is even; peel multiplicities with repeated radicals:
    rad=pdivmod(h,g,p)[0]
    cur=h; 
    # s1=rad(h); h2=h/s1 ; s2=rad(h2)=prod_{e_i>=2} f ; ... odd part = s1/s2*s3/s4...
    ss=[]; c=h
    while len(c)>1:
        dd=pder(c,p)
        gg=pgcd(c,dd,p) if dd else c  # if c'=0 (deg<p so only const) 
        r=pdivmod(c,gg,p)[0]; ss.append(r); c=gg
        if len(ss)>60: break
    # odd part degree = deg s1 - deg s2 + deg s3 - ...
    od=sum((len(s)-1)*(1 if i%2==0 else -1) for i,s in enumerate(ss))
    return od==0
