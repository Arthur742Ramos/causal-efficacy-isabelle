#!/usr/bin/env python3
"""Independent exhaustive finite checks; not a proof for infinite carriers.
All labelled dependency graphs (loops allowed), n <= 3, every normalized
monotone local profile and every root assignment. Also test constructive
fully relevant endpoint witnesses and the unrestricted uniform forest copy.
"""
from itertools import product

def tables(k):
    if k == 0: return [(1,)]
    return [t for middle in product((0, 1), repeat=(1 << k)-2)
            for t in [(0,) + middle + (1,)]
            if all(t[s] <= t[s | (1 << i)] for s in range(1 << k) for i in range(k))]

def relevant(t,k):
    return all(any(not t[s] and t[s | (1 << i)] for s in range(1 << k)
                   if not s & (1 << i)) for i in range(k))

def step(ps,fs,U,s):
    return U | sum(1 << x for x,p in enumerate(ps) if p and
                  fs[x][sum(((s >> y)&1) << i for i,y in enumerate(p))])

def limits(ps,fs,U):
    n=len(ps); low=0; high=(1 << n)-1
    while (nxt:=step(ps,fs,U,low)) != low:
        assert low & ~nxt == 0
        low=nxt
    while (nxt:=step(ps,fs,U,high)) != high:
        assert nxt & ~high == 0
        high=nxt
    return low,high

def solve(ps,fs,U):
    top=(1 << len(ps))-1
    mu,nu=limits(ps,fs,U)
    sols=[s for s in range(top+1) if step(ps,fs,U,s)==s]
    assert mu in sols and nu in sols
    assert all(mu & ~s == 0 and s & ~nu == 0 for s in sols)
    K=mu | (top ^ nu)
    assert (K==top)==(len(sols)==1)
    for x in range(len(ps)):
        assert bool(K & (1 << x)) == (len({bool(s & (1 << x)) for s in sols})==1)
    return K

counts=dict(graphs=0,graph_contexts=0,profile_contexts=0,endpoint_witnesses=0,forest_contexts=0)
for n in range(4):
    top=(1 << n)-1; tabs={k:tables(k) for k in range(n+1)}
    for edges in range(1 << (n*n)):
        counts['graphs']+=1
        ps=[[y for y in range(n) if edges >> (x*n+y)&1] for x in range(n)]
        roots=sum(1 << x for x,p in enumerate(ps) if not p)
        AND=tuple(tuple(int(s==(1 << len(p))-1) for s in range(1 << len(p))) for p in ps)
        OR=tuple(tuple(int(not p or s!=0) for s in range(1 << len(p))) for p in ps)
        W=limits(ps,AND,roots)[0]; R=limits(ps,OR,roots)[0]
        # Select one smaller-distance parent once, independently of root context.
        dist={x:0 for x,p in enumerate(ps) if not p}
        for _ in range(n):
            for x,p in enumerate(ps):
                if x not in dist and any(y in dist for y in p):
                    dist[x]=1+min(dist[y] for y in p if y in dist)
        forest=[]
        if R==top:
            for x,p in enumerate(ps):
                if not p: forest.append((1,)); continue
                i=next(i for i,y in enumerate(p) if dist[y]<dist[x])
                forest.append(tuple(int(bool(s & (1 << i))) for s in range(1 << len(p))))
        for U in range(top+1):
            if U & ~roots: continue
            counts['graph_contexts']+=1
            union=0; intersection=top
            for fs in product(*(tabs[len(p)] for p in ps)):
                counts['profile_contexts']+=1
                K=solve(ps,fs,U)
                assert W & ~K == 0 and K & ~R == 0
                union |= K; intersection &= K
            assert union==R and intersection==W
            v=limits(ps,OR,U)[0]
            upper=tuple(OR[x] if v & (1 << x) else AND[x] for x in range(n))
            assert all(relevant(t,len(p)) for p,t in zip(ps,upper))
            assert solve(ps,upper,U)==R
            v=limits(ps,AND,U)[0]
            assert v & ~W == 0
            lower=[]
            for x,p in enumerate(ps):
                if W & (1 << x): lower.append(AND[x]); continue
                I={i for i,y in enumerate(p) if not W & (1 << y)}
                A={i for i,y in enumerate(p) if v & (1 << y)}
                B={i for i,y in enumerate(p) if W & (1 << y) and not v & (1 << y)}
                assert I
                lower.append(tuple(int((any(s & (1 << i) for i in I) and all(s & (1 << i) for i in A))
                                       or any(s & (1 << i) for i in B)) for s in range(1 << len(p))))
            assert all(relevant(t,len(p)) for p,t in zip(ps,lower))
            assert solve(ps,lower,U)==W
            counts['endpoint_witnesses']+=2
            if R==top:
                assert solve(ps,forest,U)==top
                counts['forest_contexts']+=1
print('PASS',counts)
print('Every context checked; both endpoints fully relevant; forest fixed across contexts.')
print('Finite regression only: arbitrary-carrier results require the Isabelle proofs.')
