# Decoder used to read the Isabelle proof terms this probe renders.
# Usage: from zf_pair_e2e_decode import parse, proof_parts, show
X,Y = '\x05','\x06'
def parse(s):
    root={'tag':'','attrs':[],'kids':[]}; stack=[root]; i=0
    while i < len(s):
        j = s.find(X, i)
        if j < 0: chunk, i = s[i:], len(s)
        else:     chunk, i = s[i:j], j+1
        if chunk.startswith(Y):
            f = chunk[1:].split(Y)
            if f[0]=='':                      # Y X  -> close
                if len(stack)>1: stack.pop()
            else:
                n={'tag':f[0],'attrs':f[1:],'kids':[]}
                stack[-1]['kids'].append(n); stack.append(n)
        elif chunk:
            stack[-1]['kids'].append({'tag':'','text':chunk,'attrs':[],'kids':[]})
    return root
PROOF={'1':'BoundP','2':'ZAbst','3':'ZAbsp','4':'ZAppt','5':'ZAppp','7':'ZAxiom','10':'ZThm'}
TERM ={'0':'Const','1':'Free','2':'Var','3':'Bound','4':'Abs','5':'App','6':'Sort'}
def show(n,d=0,mode='proof',out=None):
    if out is None: out=[]
    if n['tag']=='':
        if n.get('text','').strip(): out.append('  '*d+'text '+repr(n['text']))
    else:
        tbl = PROOF if mode=='proof' else TERM
        nm  = tbl.get(n['tag'], n['tag'])
        a   = ' '.join(n['attrs'])
        out.append('  '*d+f"<{n['tag']}={nm}> {a}")
    for k in n['kids']: show(k,d+1,mode,out)
    return out

def elems(n): return [k for k in n['kids'] if k['tag']!='']
def proof_parts(root):
    pairs=[k for k in root['kids'] if k['tag']==':']
    if len(pairs)<2: return None,None
    pp=pairs[1]; e=elems(pp)
    if len(e)<2: return None,None
    pap=elems(e[1])
    if len(pap)<2: return None,None
    return pap[0], pap[1]
