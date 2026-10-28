#!/usr/bin/env python3
"""Independent exhaustive finite checks; not a proof for infinite carriers.
All labelled dependency graphs (loops allowed), n <= 3, every normalized
monotone local profile and every root assignment. Test exact three-status
realization, explicit relevant witnesses, context-independent K families,
and the positive activity/determination identity in every solution.
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

# Independent exact three-status classification. All labelled graphs, n=0..3.
def reach_inside(ps,seeds,region):
    r=seeds & region
    while True:
        t=r | sum(1<<x for x,p in enumerate(ps) if region & (1<<x) and any(r & (1<<y) for y in p))
        if t==r:return r
        r=t

def pattern_ok(ps,U,L,Z):
    top=(1<<len(ps))-1;roots=sum(1<<x for x,p in enumerate(ps) if not p)
    Q=top ^ (L|Z)
    return not(L&Z) and not(U&~L) and not((roots^U)&~Z) and reach_inside(ps,U,L)==L and reach_inside(ps,roots^U,Z)==Z and all(any(Q&(1<<y) for y in ps[x]) for x in range(len(ps)) if Q&(1<<x))

def region_ok(ps,K):
    top=(1<<len(ps))-1;roots=sum(1<<x for x,p in enumerate(ps) if not p);Q=top^K
    return not(roots&~K) and reach_inside(ps,roots,K)==K and all(any(Q&(1<<y) for y in ps[x]) for x in range(len(ps)) if Q&(1<<x))

counts=dict(graphs=0,graph_contexts=0,profile_contexts=0,relevant_profile_contexts=0,partition_tests=0,realizable_patterns=0,relevant_witnesses=0,region_tests=0)
for n in range(4):
    top=(1<<n)-1;tabs={k:tables(k) for k in range(n+1)}
    for edges in range(1<<(n*n)):
        counts['graphs']+=1
        ps=[[y for y in range(n) if edges>>(x*n+y)&1] for x in range(n)]
        roots=sum(1<<x for x,p in enumerate(ps) if not p)
        predictedK={K for K in range(top+1) if region_ok(ps,K)}
        counts['region_tests']+=top+1
        for U in range(top+1):
            if U&~roots:continue
            counts['graph_contexts']+=1
            actual=set();relevant_actual=set()
            for fs in product(*(tabs[len(p)] for p in ps)):
                counts['profile_contexts']+=1
                mu,nu=limits(ps,fs,U)
                sols=[s for s in range(top+1) if step(ps,fs,U,s)==s]
                assert sols and mu in sols and nu in sols
                assert all(mu&~s==0 and s&~nu==0 for s in sols)
                for s in sols:
                    K=mu|(top^nu)
                    assert s&K==mu # exact positive determined-target identity
                actual.add((mu,top^nu))
                if all(relevant(t,len(p)) for t,p in zip(fs,ps)):
                    counts['relevant_profile_contexts']+=1;relevant_actual.add((mu,top^nu))
            predicted=set()
            for colors in product(range(3),repeat=n):
                counts['partition_tests']+=1
                L=sum(1<<x for x,v in enumerate(colors) if v==0)
                Z=sum(1<<x for x,v in enumerate(colors) if v==1)
                if not pattern_ok(ps,U,L,Z):continue
                predicted.add((L,Z));counts['realizable_patterns']+=1
                Q=top^(L|Z);w=[]
                for x,p in enumerate(ps):
                    if not p:w.append((1,));continue
                    if L&(1<<x):w.append(tuple(int(s!=0) for s in range(1<<len(p))));continue
                    if Z&(1<<x):w.append(tuple(int(s==(1<<len(p))-1) for s in range(1<<len(p))));continue
                    I=[i for i,y in enumerate(p) if Q&(1<<y)]
                    A=[i for i,y in enumerate(p) if L&(1<<y)]
                    B=[i for i,y in enumerate(p) if Z&(1<<y)]
                    w.append(tuple(int((any(s&(1<<i) for i in I) and all(s&(1<<i) for i in A)) or any(s&(1<<i) for i in B)) for s in range(1<<len(p))))
                assert all(t in tabs[len(p)] for t,p in zip(w,ps))
                assert all(relevant(t,len(p)) for t,p in zip(w,ps))
                mu,nu=limits(ps,w,U);assert (mu,top^nu)==(L,Z)
                counts['relevant_witnesses']+=1
            assert actual==predicted==relevant_actual,(n,edges,U,actual,predicted,relevant_actual)
            assert {L|Z for L,Z in actual}==predictedK
print('PASS',counts)
print('All realized least/greatest pairs equal predicted patterns; every pattern has explicit fully relevant witness.')
print('Attainable K family matches its context-free criterion at every root context. Positive activity/determination identity checked in every solution.')
print('Bounds n=0..3; finite regression is not proof of arbitrary-carrier theorems or novelty.')
