"""Terminology lint: words coined in development must not appear in the book text."""
import re, sys, pathlib
T = pathlib.Path(__file__).resolve().parents[1]
FORBID = [r'dumbbell', r'\bcaps?\b', r'\bnecks?\b', r'quantum (hemi)?spheres?', r'cyclic[ -]fueter', r'kurokawa',
          r'\bU21', r"\bZ\d+[a-z]?\b", r'\bpillars?\b', r'\bstage \d', r'\bbridges?\b', r'realline', r'\bledger',
          r'α-|\\alpha-[IVX]', r'\bA_\{?[WF]\}?\b', r'three phases', r'\bphase [IVX]+\b', r'\bFable\b', r'\bClaude\b',
          r'quantum gravity geometry', r'\bshape theorem\b']
ALLOW_DUMBBELL = 1
def strip(text):
    text = re.sub(r'(?m)%.*$', '', text)
    text = re.sub(r'\\(chk|covers)\{[^}]*\}', '', text)
    text = re.sub(r'\\[a-zA-Z]+', ' ', text)
    return text
total_db = 0; bad = 0
for f in sorted((T/'chapters').glob('*.tex')):
    lines = strip(f.read_text()).splitlines()
    for n, L in enumerate(lines, 1):
        for pat in FORBID:
            for m in re.finditer(pat, L, re.I):
                if pat == 'dumbbell': total_db += 1; continue
                if pat == 'kurokawa' and f.stem == 'front': continue
                print(f'{f.name}:{n}: "{m.group(0)}"  | {L.strip()[:100]}'); bad += 1
if total_db > ALLOW_DUMBBELL: print(f'"dumbbell" used {total_db} times (allowed {ALLOW_DUMBBELL})'); bad += 1
print('lint:', 'OK' if not bad else f'{bad} problems'); sys.exit(1 if bad else 0)
