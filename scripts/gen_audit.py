import re,glob,os
root='/home/claude/lean/CFT'
mods=sorted(os.path.relpath(f,root+'/CFT')[:-5].replace('/','.') for f in glob.glob(root+'/CFT/**/*.lean',recursive=True) if not f.endswith('CFT/Basic.lean'))
lines=[f"import CFT.{m}" for m in mods]+[""]
for m in mods:
    stack=[]
    for ln in open(f"{root}/CFT/{m.replace('.','/')}.lean"):
        mm=re.match(r"^namespace\s+(\S+)",ln)
        if mm: stack.append(mm.group(1)); continue
        if re.match(r"^(noncomputable\s+)?section\b",ln): stack.append(None); continue
        if re.match(r"^end\b",ln):
            if stack: stack.pop()
            continue
        t=re.match(r"^(?:theorem|lemma|alias)\s+([^\s(:]+)",ln)
        if t:
            ns=".".join(x for x in stack if x)
            lines.append(f"#print axioms {ns}.{t.group(1)}")
open(root+'/Audit.lean','w').write("\n".join(lines)+"\n")
open(root+'/CFT.lean','w').write("import CFT.Basic\n"+"\n".join(f"import CFT.{m}" for m in mods)+"\n")
print(len([l for l in lines if l.startswith('#print')]),mods)
