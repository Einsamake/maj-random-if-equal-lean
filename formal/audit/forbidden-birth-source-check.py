"""Exact finite computation; it is not a Lean proof or a literature claim."""
from fractions import Fraction
import json

def neighbours(v):
    x,y=v
    return ((x+1,y),(x-1,y),(x,y+1),(x,y-1))

def cleanup(s):
    s=set(s)
    while True:
        t={v for v in s if sum(u in s for u in neighbours(v))>=2}
        if t==s:
            return s
        s=t

rows=[]
for L in [2,3,4,10,40]:
    E={(x,y) for x in range(-L,L+1) for y in range(-L,L+1)}
    D={v for v in E if abs(v[0])+abs(v[1])<=L+1}
    corners=[v for v in D if sum(u in D for u in neighbours(v))==2]
    outside=[v for v in E-D if sum(u in D for u in neighbours(v))>=2]
    raw=sum(Fraction(1,2) if sum(u in D for u in neighbours(v))==2 else Fraction(1) if sum(u in D for u in neighbours(v))<2 else 0 for v in D)
    losses=[len((D-{v})-cleanup(D-{v})) for v in corners]
    weights=[L+2-abs(v[0])-abs(v[1]) for v in outside]
    assert all(x==0 for x in losses) and all(x==0 for x in weights)
    assert len(corners)==4*L and len(outside)==4*(L-1) and raw==2*L
    rows.append({'L':L,'domain_sites':len(D),'occupied_degree_two':len(corners),'inside_vacant_sites':0,'cleanup_loss_after_each_corner_deletion':0,'masked_raw_rate':str(raw),'outside_two_neighbour_sites':len(outside),'expanded_raw_rate':str(raw-Fraction(len(outside),2)),'all_forbidden_birth_weights_zero':True})
print(json.dumps(rows,indent=2))
