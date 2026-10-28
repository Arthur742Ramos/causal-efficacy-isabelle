#!/usr/bin/env python3
"""Exhaustive finite sanity check, independent of Isabelle; not a proof.
Checks all labelled graphs on 0..3 nodes (self-loops allowed) and all
monotone normalized local Boolean functions whose listed inputs are relevant.
No numerical approximation or external libraries.
"""
from itertools import product

def relevant_monotone_tables(k):
    if k == 0:
        return [(1,)]
    ans=[]
    for middle in product((0,1), repeat=(1<<k)-2):
        t=(0,)+middle+(1,)
        if all(t[((1<<k)-1) ^ (1<<i)] == 0 for i in range(k)):
            if all(t[s] <= t[s|1<<i] for s in range(1<<k) for i in range(k)):
                assert t == (0,)*((1<<k)-1)+(1,)
        if any(t[s]>t[s|1<<i] for s in range(1<<k) for i in range(k)):
            continue
        if any(not any(t[s] != t[s|1<<i] for s in range(1<<k) if not s>>i&1)
               for i in range(k)):
            continue
        ans.append(t)
    return ans

def least_fixed(parents, profile, n):
    state=0
    while True:
        new=0
        for x in range(n):
            inp=sum(((state>>y)&1)<<i for i,y in enumerate(parents[x]))
            if profile[x][inp]: new |= 1<<x
        assert state & ~new == 0
        if new==state: return state
        state=new

def reachable(parents,n):
    state=sum((1<<x) for x in range(n) if not parents[x])
    while True:
        new=state | sum(1<<x for x in range(n)
                        if any(state>>y&1 for y in parents[x]))
        if new==state: return state
        state=new

def accessible(parents,n):
    state=0
    while True:
        new=sum(1<<x for x in range(n) if all(state>>y&1 for y in parents[x]))
        if new==state: return state
        state=new

counts=[]
for n in range(4):
    tables={k:relevant_monotone_tables(k) for k in range(n+1)}
    graph_count=profile_count=target_checks=0
    for edges in range(1<<(n*n)):
        graph_count+=1
        parents=[[y for y in range(n) if edges>>(x*n+y)&1] for x in range(n)]
        reach=reachable(parents,n)
        acc=accessible(parents,n)
        closures=[]
        for profile in product(*(tables[len(ps)] for ps in parents)):
            profile_count+=1
            lfp=least_fixed(parents,profile,n)
            assert acc & ~lfp == 0 and lfp & ~reach == 0
            all_on=sum(1<<x for x in range(n) if profile[x][-1])
            assert all_on==(1<<n)-1
            closures.append(lfp)
        for target in range(1<<n):
            target_checks+=1
            assert any(target & ~s == 0 for s in closures)==(target & ~reach == 0)
            assert all(target & ~s == 0 for s in closures)==(target & ~acc == 0)
    counts.append((n,graph_count,profile_count,target_checks))
print('PASS: exhaustive exact finite-mechanism sanity checks')
print('n graphs mechanism_profiles target_set_classifications')
for row in counts: print(*row)
print('Also checked: monotone all-on indispensability forces AND.')
print('This finite experiment does not verify the infinite-carrier theorems.')
