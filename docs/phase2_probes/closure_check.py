"""Premises of §10's completeness argument, measured rather than assumed.

The argument is a structural induction on the proof term. It needs:

  (I)   the CITATION GRAPH IS ACYCLIC -- a ZThm leaf recurses into another proof,
        so the induction terminates only if serial -> cited-serial is well-founded.
  (III) every citation RESOLVES -- a dangling citation is a leaf with no rule and
        no proof to recurse into.

CRITICAL, and the reason this script exists in this form: SERIALS ARE NOT GLOBALLY
UNIQUE. 760 serials occur in two theories with DIFFERENT content -- ZF.Arith/14846
is Arith.pred, ZF.QUniv/14846 is QUniv.quniv. Keying by serial alone silently
merges 760 distinct theorems and yields a corrupted graph (it reported 1 dangling
citation instead of 53). The key is (theory, serial); the resolution rule is exact
match, then a unique-serial fallback.
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf_pair_e2e_decode import parse, proof_parts

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..',
                    'data', 'zf_export')
PC = {'3': [1], '2': [-1], '4': [0], '5': [0, 1]}


def kids(n):
    out = []
    for k in n['kids']:
        if k['tag'] == ':':
            out.extend(x for x in k['kids'] if x['tag'] != '')
        elif k['tag'] != '':
            out.append(k)
    return out


def at(n, i=0):
    return n['attrs'][i].split('=', 1)[-1] if len(n['attrs']) > i else '?'


def cites(n, out):
    t = n['tag']
    if t == '10':
        out.add((at(n, 1), at(n, 0)))          # (theory, serial) -- the real key
    e = kids(n)
    if t == ':':
        for k in e:
            cites(k, out)
        return
    for i in PC.get(t, []):
        if -len(e) <= i < len(e):
            cites(e[i], out)


def main():
    byserial = collections.defaultdict(set)
    for th in sorted(os.listdir(ROOT)):
        d = os.path.join(ROOT, th, 'proofs')
        if os.path.isdir(d):
            for fn in os.listdir(d):
                byserial[fn].add(th)

    graph = {}
    for th in sorted(os.listdir(ROOT)):
        d = os.path.join(ROOT, th, 'proofs')
        if not os.path.isdir(d):
            continue
        for fn in os.listdir(d):
            with open(os.path.join(d, fn), encoding='utf-8', errors='replace') as f:
                _, prf = proof_parts(parse(f.read()))
            c = set()
            if prf is not None:
                cites(prf, c)
            graph[(th, fn)] = c

    present = set(graph)
    allc = set().union(*graph.values()) if graph else set()
    dang = allc - present
    fallback = [x for x in dang if len(byserial.get(x[1], ())) == 1]
    ambig = [x for x in dang if len(byserial.get(x[1], ())) > 1]
    nowhere = [x for x in dang if x[1] not in byserial]

    print('nodes (theory, serial)          : %d' % len(graph))
    print('distinct citations              : %d' % len(allc))
    print('  resolve exactly               : %d' % (len(allc) - len(dang)))
    print('  via unique-serial fallback    : %d' % len(fallback))
    print('  AMBIGUOUS (needs a rule)      : %d' % len(ambig))
    print('  genuinely absent              : %d  %s' % (len(nowhere), nowhere))

    colliding = {s for s, t in byserial.items() if len(t) > 1}
    into = {x for x in allc if x[1] in colliding}
    print()
    print('serials in >1 theory            : %d' % len(colliding))
    print('citations into one              : %d ; all resolve exactly: %s'
          % (len(into), all(x in present for x in into)))

    # (I) cycle detection
    colour = collections.defaultdict(int)
    cycles = []
    for root in graph:
        if colour[root]:
            continue
        colour[root] = 1
        stack = [(root, iter(sorted(graph[root])))]
        path = [root]
        while stack:
            node, it = stack[-1]
            adv = False
            for nxt in it:
                if nxt not in graph:
                    continue
                if colour[nxt] == 1:
                    cycles.append(path[path.index(nxt):] + [nxt])
                elif colour[nxt] == 0:
                    colour[nxt] = 1
                    path.append(nxt)
                    stack.append((nxt, iter(sorted(graph[nxt]))))
                    adv = True
                    break
            if not adv:
                colour[node] = 2
                stack.pop()
                path.pop()
    print()
    print('CYCLES in the citation graph    : %d   <- must be 0 for the induction'
          % len(cycles))
    for c in cycles[:5]:
        print('   %s' % ' -> '.join('%s/%s' % x for x in c))


main()
