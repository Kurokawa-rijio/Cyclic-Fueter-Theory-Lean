"""Extract every theorem/lemma from CFT/**/*.lean into map/theorems.json."""
import re, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[2]
out = []
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+([^\s:({\[]+)')
for f in sorted((root/'CFT').rglob('*.lean')):
    mod = str(f.relative_to(root)).replace('/', '.')[:-5]
    lines = f.read_text().splitlines()
    doc = None; i = 0
    while i < len(lines):
        L = lines[i]
        if L.lstrip().startswith('/--'):
            buf = [L]; j = i
            while '-/' not in lines[j]:
                j += 1; buf.append(lines[j])
            doc = '\n'.join(buf).strip()[3:-2].strip(); i = j + 1; continue
        m = decl.match(L.strip())
        if m:
            stmt = [L]; j = i
            while ':=' not in lines[j] and j + 1 < len(lines) and j - i < 40:
                j += 1; stmt.append(lines[j])
            s = '\n'.join(stmt); s = s.split(':=')[0]
            out.append(dict(module=mod, name=m.group(2), kind=m.group(1), line=i+1,
                            stmt=re.sub(r'\s+', ' ', s).strip(), doc=doc))
            doc = None
        elif L.strip() and not L.strip().startswith('--'):
            if not L.startswith(' '): doc = None if not L.strip().startswith('@[') else doc
        i += 1
(root/'textbook/map/theorems.json').write_text(json.dumps(out, ensure_ascii=False, indent=0))
from collections import Counter
c = Counter(d['module'] for d in out)
print(len(out), len(c))
