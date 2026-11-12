"""Print module headers and theorem statements. usage: dump.py MOD [MOD...] [--short]"""
import json, sys, re, pathlib
T = pathlib.Path(__file__).resolve().parents[1]
d = json.loads((T/'map/theorems.json').read_text())
short = '--short' in sys.argv
for m in [a for a in sys.argv[1:] if not a.startswith('--')]:
    f = T.parent/('CFT/' + m.replace('.', '/') + '.lean')
    txt = f.read_text()
    h = re.search(r'/-!(.*?)-/', txt, re.S)
    print(f'##### {m}'); 
    if h and not short: print(h.group(1).strip()[:2500])
    for x in d:
        if x['module'] == 'CFT.' + m:
            s = x['stmt']; s = s[s.find(x['name'])+len(x['name']):].strip()
            print(f"- {x['name']}: {s[:400]}")
            if x['doc'] and not short: print('    doc:', x['doc'].replace('\n', ' ')[:300])
