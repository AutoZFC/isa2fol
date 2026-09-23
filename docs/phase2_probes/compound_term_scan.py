"""Scan the export for ZAppt nodes instantiating at a COMPOUND i-term.

Per FOUNDATION_TO_FOLZFC.md §10 item 2: the `appt_complex` materialisation path
is still unexercised against real data. Find a real proof that needs it.

Two structural facts the tree forces (both cost me a wrong first pass):
  * every child list is wrapped in ':' nodes -- unwrap before indexing.
  * ZAppt is overloaded (doc §8): an arg headed by a logical constant
    (IFOL.*/FOL.*/Pure.*) is a PROPOSITION -> schema_inst, not a term.
    Only a non-logical head in applied position is a compound i-term.
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf_pair_e2e_decode import parse, proof_parts

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'data', 'zf_export')
LOGIC_PREFIX = ('IFOL.', 'FOL.', 'Pure.', 'HOL.')


def kids(n):
    """Real children: unwrap the ':' grouping nodes."""
    out = []
    for k in n['kids']:
        if k['tag'] == ':':
            out.extend(x for x in k['kids'] if x['tag'] != '')
        elif k['tag'] != '':
            out.append(k)
    return out


def name(n):
    return n['attrs'][0].split('=', 1)[-1] if n['attrs'] else '?'


def head(n):
    """Head symbol of an application spine."""
    while n['tag'] == '5' and kids(n):
        n = kids(n)[0]
    return n


def term_str(n):
    t, e = n['tag'], kids(n)
    if t == '0':
        return name(n)
    if t == '1':
        return name(n)
    if t == '2':
        return '?' + name(n)
    if t == '3':
        return 'B' + name(n)
    if t == '4':
        return '(%%. %s)' % (term_str(e[-1]) if e else '?')
    if t == '5':
        # print spine head with all args
        args, cur = [], n
        while cur['tag'] == '5' and len(kids(cur)) >= 2:
            k = kids(cur)
            args.append(k[1])
            cur = k[0]
        return '%s(%s)' % (term_str(cur), ','.join(term_str(a) for a in reversed(args)))
    return 't' + t


def is_compound_term(arg):
    """Applied, and headed by a non-logical constant -> a real i-term."""
    if arg['tag'] != '5':
        return False
    h = head(arg)
    if h['tag'] != '0':                       # not a constant head
        return True                            # applied Free/Var: still compound
    return not name(h).startswith(LOGIC_PREFIX)


def walk(n, hits):
    if n['tag'] == '4':                        # ZAppt: [proof, term]
        e = kids(n)
        if len(e) >= 2 and is_compound_term(e[1]):
            hits.append(e[1])
    for k in kids(n):
        walk(k, hits)


def cited_thms(n, out):
    if n['tag'] == '10':
        out.append(tuple(name_at(n, i) for i in range(2)))
    for k in kids(n):
        cited_thms(k, out)


def name_at(n, i):
    return n['attrs'][i].split('=', 1)[-1] if len(n['attrs']) > i else '?'


def proof_of(root):
    """root -> (statement, proof).

    NB: use the decoder's own two-level split. Flattening ':' here instead
    merges the outer group with the (stmt, proof) pair and silently hands
    back the STATEMENT as the proof -- which reports zero ZAppt everywhere.
    """
    return proof_parts(root)


def main():
    theories = sys.argv[1:] or ['ZF.pair']
    tally = collections.Counter()
    for th in theories:
        pdir = os.path.join(ROOT, th, 'proofs')
        if not os.path.isdir(pdir):
            continue
        for fn in sorted(os.listdir(pdir), key=lambda s: int(s) if s.isdigit() else 0):
            with open(os.path.join(pdir, fn), encoding='utf-8', errors='replace') as f:
                root = parse(f.read())
            stmt, prf = proof_of(root)
            if prf is None:
                continue
            hits = []
            walk(prf, hits)
            if hits:
                tally[th] += 1
                shapes = sorted({term_str(h) for h in hits})
                cites = []
                cited_thms(prf, cites)
                print('%-12s %-6s %2d hit(s) | %s | cites %s'
                      % (th, fn, len(hits), '  '.join(shapes[:3]),
                         ' '.join('%s/%s' % c for c in cites[:4])))
    print('--- files with a compound-i-term ZAppt ---')
    for th, c in sorted(tally.items()):
        print('%-14s %d' % (th, c))


main()
