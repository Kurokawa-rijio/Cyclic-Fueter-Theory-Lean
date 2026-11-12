"""Coverage check: every Lean theorem must be covered by some \\chk{...} line.
usage: coverage.py [chapter-file-stem]   (e.g. ch05) -> also report plan for that chapter"""
import json, re, sys, pathlib, fnmatch
T = pathlib.Path(__file__).resolve().parents[1]
decls = json.loads((T/'map/theorems.json').read_text())
key = lambda d: d['module'].replace('CFT.', '') + ':' + d['name']
allkeys = [key(d) for d in decls]
plan = {}
for L in (T/'map/plan.tsv').read_text().splitlines():
    if L.strip() and not L.startswith('#'):
        m, c = L.split('\t')[:2]; plan[m] = c
moves = {}
mp = T/'map/moves.tsv'
if mp.exists():
    for L in mp.read_text().splitlines():
        if L.strip() and not L.startswith('#'):
            k, c = L.split('\t')[:2]; moves[k] = c
def planned(k): return moves.get(k, plan.get(k.split(':')[0]))
def chk_keys(text):
    out = []
    for m in re.finditer(r'\\chk\{([^}]*)\}', text):
        for p in m.group(1).split(','):
            p = p.strip()
            if p: out.append(p)
    return out
covered = {}
bad = []
for f in sorted((T/'chapters').glob('*.tex')):
    for p in chk_keys(f.read_text()):
        hits = fnmatch.filter(allkeys, p) if any(ch in p for ch in '*?[') else ([p] if p in allkeys else [])
        if not hits: bad.append((f.stem, p))
        for h in hits: covered.setdefault(h, []).append(f.stem)
cnt = {}
for k, v in covered.items():
    for s in set(v): cnt[s] = cnt.get(s, 0) + 1
def lab(s): return str(int(s[2:])) if s.startswith('ch') else s[3:]
(T/'map/counts.tex').write_text(''.join(f'\\expandafter\\def\\csname chkcount{lab(s)}\\endcsname{{{n}}}\n' for s, n in sorted(cnt.items()))
                                     + f'\\def\\chkcounttotal{{{len(allkeys)}}}\n')
dups = {k: v for k, v in covered.items() if len(v) > 1}
print(f'covered {len(covered)}/{len(allkeys)}')
if bad: print('UNKNOWN keys:', bad)
if dups: print('DUPLICATES:', dups)
if len(sys.argv) > 1:
    ch = sys.argv[1]
    miss = [k for k in allkeys if planned(k) == ch and k not in covered]
    print(f'{ch}: planned but uncovered {len(miss)}')
    for k in miss: print('  ', k)
    n = sum(1 for k, v in covered.items() if ch in v)
    print(f'{ch}: covers {n}')
sys.exit(1 if bad or dups else 0)
