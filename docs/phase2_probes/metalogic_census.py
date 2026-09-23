"""Census of what the proof layer ACTUALLY contains, corpus-wide.

Tests §7's claim that the gap is "exactly four constructs", which was derived
before any theory but ZF.pair had been read.

CRITICAL: the proof and term tag spaces OVERLAP (§8). A traversal must know
which subtree it is in, per node:
    ZAbsp(3) = [prop TERM, proof]      -- descend child 1 only
    ZAbst(2) = [type/sort, proof]      -- descend last only
    ZAppt(4) = [proof, TERM]           -- descend child 0 only
    ZAppp(5) = [proof, proof]          -- descend both
    ZThm(10), ZAxiom(7), BoundP(1), Hyp(6) -- leaves in proof space
Descending blindly counts Const(0)/App(5)/Free(1) from term space as proof
nodes -- which is exactly what a first pass here did.

Sizing, not a premise (FOUNDATION §5).
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf_pair_e2e_decode import parse, proof_parts

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'data', 'zf_export')
# Isabelle Proofterm encoding order: MinProof0 PBound1 Abst2 AbsP3 Appt4
# AppP5 Hyp6 PAxm7 OfClass8 Oracle9 PThm10
KNOWN = {'0': 'MinProof', '1': 'BoundP', '2': 'ZAbst', '3': 'ZAbsp', '4': 'ZAppt',
         '5': 'ZAppp', '6': 'Hyp?', '7': 'ZAxiom', '8': 'OfClass?', '9': 'Oracle?',
         '10': 'ZThm'}
PROOF_CHILDREN = {'3': [1], '2': [-1], '4': [0], '5': [0, 1]}


def kids(n):
    out = []
    for k in n['kids']:
        if k['tag'] == ':':
            out.extend(x for x in k['kids'] if x['tag'] != '')
        elif k['tag'] != '':
            out.append(k)
    return out


def attr(n, i=0):
    return n['attrs'][i].split('=', 1)[-1] if len(n['attrs']) > i else '?'


def walk(n, st):
    t = n['tag']
    st['tags'][t] += 1
    if t == '7':
        st['axioms'][attr(n)] += 1
    elif t == '10':
        st['cites'][attr(n, 1)] += 1
        st['serials'][attr(n, 1)].add(attr(n, 0))
    elif t == '6':
        st['hyp_shapes'][len(kids(n))] += 1
    e = kids(n)
    if t == ':':                     # the root handed back by proof_parts is a ':' group
        for k in e:
            walk(k, st)
        return
    sel = PROOF_CHILDREN.get(t)
    if sel is None:
        return                       # leaf in proof space
    for i in sel:
        if -len(e) <= i < len(e):
            walk(e[i], st)


def main():
    st = {'tags': collections.Counter(), 'axioms': collections.Counter(),
          'cites': collections.Counter(), 'serials': collections.defaultdict(set),
          'hyp_shapes': collections.Counter()}
    files = 0
    for th in sorted(os.listdir(ROOT)):
        pdir = os.path.join(ROOT, th, 'proofs')
        if not os.path.isdir(pdir):
            continue
        for fn in os.listdir(pdir):
            files += 1
            with open(os.path.join(pdir, fn), encoding='utf-8', errors='replace') as f:
                stmt, prf = proof_parts(parse(f.read()))
            if prf is not None:
                walk(prf, st)

    print('files scanned : %d' % files)
    print()
    print('--- tags in PROOF position (term space excluded) ---')
    for t, c in sorted(st['tags'].items(), key=lambda kv: -kv[1]):
        print('  %-4s %-12s %d' % (t, KNOWN.get(t, '*** UNKNOWN ***'), c))
    if st['hyp_shapes']:
        print('  tag 6 child-counts: %s' % dict(st['hyp_shapes']))
    print()
    print('--- Pure ZAxioms (tier 7 claims exactly 7 rules) ---')
    pure = {a: c for a, c in st['axioms'].items() if a.startswith('Pure.')}
    for a, c in sorted(pure.items(), key=lambda kv: -kv[1]):
        print('  %-30s %d' % (a, c))
    print()
    print('--- non-Pure ZAxioms, grouped ---')
    grp = collections.Counter()
    for a, c in st['axioms'].items():
        if a.startswith('Pure.'):
            continue
        grp['%s_def_raw (constant defs)' % a.split('.')[0] if a.endswith('_def_raw')
            else ('DATATYPE/INDUCTIVE pkg' if a.count('.') >= 2 else 'ZF axiom / other')] += c
    for g, c in sorted(grp.items(), key=lambda kv: -kv[1]):
        print('  %-34s %d' % (g, c))
    print('  (datatype/inductive pkg members: %s)' % sorted(
        a for a in st['axioms'] if a.count('.') >= 2 and not a.startswith('Pure.')))
    print()
    print('--- DISTINCT cited theorems per theory  <- this sizes the kernel library ---')
    tot = 0
    for th, ss in sorted(st['serials'].items(), key=lambda kv: -len(kv[1]))[:12]:
        print('  %-22s distinct=%-6d calls=%d' % (th, len(ss), st['cites'][th]))
        tot += len(ss)
    print('  ...')
    print('  LOGIC LAYER distinct (IFOL+FOL+Pure) = %d' % sum(
        len(st['serials'][t]) for t in ('IFOL', 'FOL', 'Pure')))
    print('  ALL distinct cited theorems          = %d' % sum(
        len(v) for v in st['serials'].values()))


main()
