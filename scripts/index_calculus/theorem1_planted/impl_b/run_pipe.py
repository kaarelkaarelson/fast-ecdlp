#!/usr/bin/env python3
"""Planted-diagonal pipeline vs vanilla; counts. usage: run_pipe.py kind l rounds seed policy [f m]"""
import sys, random, math, time
from pl import *

def generates(G,B1,B2,l):
    if isinstance(G,AbGroup):
        vecs=[(B1[0]%l,B1[1]%l if G.n2>1 else 0),(B2[0]%l,B2[1]%l if G.n2>1 else 0)]
        r=2 if G.n2>1 else 1
        if r==1: return any(v[0] for v in vecs)
        det=(vecs[0][0]*vecs[1][1]-vecs[0][1]*vecs[1][0])%l
        return det!=0
    seen={G.O};frontier=[G.O]
    while frontier:
        nf=[]
        for P in frontier:
            for B in (B1,B2):
                Q=G.add(P,B)
                if Q not in seen: seen.add(Q);nf.append(Q)
        frontier=nf
    return len(seen)==G.N

def setup(kind,l,rng):
    if kind=='cyc': return AbGroup(l*l),2
    if kind=='rank2': return AbGroup(l,l),1
    if kind=='l3': return AbGroup(l*l,l),3
    if kind.startswith('curve'):
        _,p,A,B=kind.split(':'); return Curve(int(p),int(A),int(B)),2
    raise ValueError

def one_round(G,l,v,f,m,orc,X,P,Q,d,rng,M0,planted,Fpts,stats):
    N=G.N
    def draw(i,M):
        for _ in range(100000):
            a=[rng.randrange(N) for _ in range(4)]
            R=G.O
            for aj,Xj in zip(a,X): R=G.add(R,G.mul(aj,Xj))
            if i is not None: R=G.add(R,G.mul(M,Fpts[i]))
            stats['calls']+=1
            c=orc.D(R)
            if c is not None: return a,list(c),R
        raise RuntimeError
    rows=[];tags=[];M=0
    if planted:
        M=rng.randrange(M0)
        for i in range(f):
            a,c,R=draw(i,M); c[i]-=M; rows.append(c);tags.append(a)
    ext=12 if planted else 12
    for _ in range(ext + (0 if planted else f)):
        a,c,R=draw(None,0); rows.append(c);tags.append(a)
    return rows,tags,M

def run(kind,l,rounds,seed,policy,f=4,m=80,dump=None):
    rng=random.Random(seed)
    G,v=setup(kind,l,rng); mod=l**v
    M0=max(8*f*1,4*f*f)
    if l<=M0:
        M0=l; print('# SMALL-l regime (l<=L0): M uniform in [0,l); outside Lemma P2 regime')
    res=dict(ok=0,singB=0,gen_fail=0,wrong=0,vanilla_tors=0,vanilla_n=0,rounds=0,calls=0,recov_vanilla_lift=0)
    tors_hist={}
    # fixed factor base & oracle per instance
    F=[G.rand(rng) for _ in range(f)]
    chi=[rng.randrange(l) for _ in range(f)]
    orc=Oracle(G,F,m,policy=policy,chi=chi,l=l)
    print(f"# {kind} l={l} N={G.N} f={f} m={m} policy={policy} cover={orc.cover:.3f} avgdec={orc.avgdec:.2f} L0={M0}",flush=True)
    for r in range(rounds):
        # X
        while True:
            B1,B2,P=G.rand(rng),G.rand(rng),G.rand(rng)
            if generates(G,B1,B2,l) and G.order(P)>1: break
        op=G.order(P); d=rng.randrange(op); Q=G.mul(d,P); X=[B1,B2,P,Q]
        stats=dict(calls=0)
        # vanilla delta
        orc.state=0
        rows,tags,_=one_round(G,l,v,f,m,orc,X,P,Q,d,rng,M0,False,F,stats)
        vals=smith_val_counts(rows,l,v)
        t=sum(1 for x in vals if 0<x<v); res['vanilla_tors']+= (t>0); res['vanilla_n']+=1
        tors_hist[t]=tors_hist.get(t,0)+1
        # planted
        orc.state=0
        rows,tags,M=one_round(G,l,v,f,m,orc,X,P,Q,d,rng,M0,True,F,stats)
        res['calls']+=stats['calls']; res['rounds']+=1
        Bm=[rows[i] for i in range(f)]
        Xinv=inv_mat_lv(Bm,l,v)
        if Xinv is None: res['singB']+=1; continue
        mus=[]
        for k in range(12):
            rk=rows[f+k]
            x=[(-sum(rk[j]*Xinv[j][i] for j in range(f)))%mod for i in range(f)]
            lam=x+[0]*12; lam[f+k]=1
            # check lambda E = 0 mod l^v
            for j in range(f):
                assert sum(lam[i]*rows[i][j] for i in range(f+12))%mod==0
            mu=[sum(lam[i]*tags[i][c] for i in range(f+12))%mod for c in range(4)]
            # Lemma 1: mu in K_l
            S=G.O
            for mj,Xj in zip(mu,X): S=G.add(S,G.mul(mj,Xj))
            assert S==G.O,"Lemma1 violated"
            mus.append(mu)
        dd=howell_d(mus,l,v)
        if dd is None: res['gen_fail']+=1; continue
        if G.mul(dd,P)==Q: res['ok']+=1
        else: res['wrong']+=1
    print(f"RESULT {kind} l={l} policy={policy} f={f} m={m}: rounds={res['rounds']} ok={res['ok']} singular_B={res['singB']} (rate {res['singB']/res['rounds']:.3f}, bound f/M0={f/M0:.3f}) howell_fail={res['gen_fail']} wrong={res['wrong']} | vanilla torsion>0 in {res['vanilla_tors']}/{res['vanilla_n']} hist={dict(sorted(tors_hist.items()))} | oracle calls/round={res['calls']/res['rounds']:.1f}",flush=True)
    return res

if __name__=='__main__':
    kind,l,rounds,seed,policy=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
    f=int(sys.argv[6]) if len(sys.argv)>6 else 4
    m=int(sys.argv[7]) if len(sys.argv)>7 else 80
    run(kind,l,rounds,seed,policy,f,m)
