#!/usr/bin/env python3
"""Write the compass figure (the chain of fourteen questions) and the
compass strip used on part openers."""
import os
OUT = os.path.join(os.path.dirname(__file__), '..', 'generated')

Q = [  # (part, question, answer)
    ('I', 'Why could Hamilton build numbers in four dimensions but not in three?',
     r'multiplication that keeps length: $q\bar q=|q|^2$; only dimensions 1, 2, 4, 8'),
    ('I', 'What does a unit quaternion do?',
     'rotations of space (covered twice), the sphere of imaginary units, Hopf circles'),
    ('I', 'How do we compute with numbers that do not commute?',
     'left and right matrices; complexifying brings nonzero elements of length zero'),
    ('II', 'Can complex analysis be carried to four dimensions?',
     r'the Fueter operator $D$, with $\bar D D=\Delta$'),
    ('II', 'What happens if the coefficients $1,i,j,k$ are cycled?',
     'a common linear solution appears: the coefficient matrix $C$ is singular (rank 3)'),
    ('III', 'Is that singularity an accident?',
     'no: the DFT eigenvalues are paravectors of length zero (nullity theorem)'),
    ('IV', 'Which algebra hides in the orderings and coefficients?',
     r'$S_4$ and the Klein group, Clifford systems, octonions'),
    ('V', 'What shape does the set of singular configurations have?',
     'rank geometry: two mechanisms by handedness; odd rank 7 after complexifying'),
    ('VI', 'Why does one formula have two real forms?',
     r'$t^2+|\mathbf x|^2$ and $t^2-|\mathbf x|^2$; on the Lorentz side rank 7 is a shared light ray'),
    ('VII', 'What does length zero mean in quantum theory?',
     r'$\det\rho=0$: pure states; entanglement of two qubits'),
    ('VIII', 'What does length zero mean in relativity?',
     'light rays = rank one = spinors; mass is measured from the equator'),
    ('IX', 'What survives when states and spacetime move?',
     'Berry phase, Thomas--Wigner rotation, curved space'),
    ('X--XI', 'Kinematics is complete. What drives it?',
     'the action principle: Maxwell, gravity, throats, collapse, quantisation'),
    ('Epilogue', 'What do we still not know?',
     r'open problems; the fine-structure constant $\alpha$ is not derived'),
]
VOL = [(1, 0, 5, 'Numbers and', 'Equations'), (2, 6, 8, 'Algebra and', 'Rank'),
       (3, 9, 11, 'States and', 'Spacetime'), (4, 12, 13, 'Action and', 'Dynamics')]


def full():
    L = []
    bx, bw, bh, step = 25, 110, 10.6, 12.4
    vgap = 3.0
    ys = []
    y = 0
    for n in range(14):
        if n in (6, 9, 12):
            y -= vgap
        ys.append(y)
        y -= step
    L.append(r'\begin{tikzpicture}[x=1mm,y=1mm,font=\sffamily]')
    for (v, a, b, t1, t2) in VOL:
        top, bot = ys[a] + bh / 2 + 1.8, ys[b] - bh / 2 - 1.8
        L.append(rf'\fill[accentlight,rounded corners=2pt] (0,{bot:.1f}) rectangle (136,{top:.1f});')
        L.append(rf'\node[anchor=north west,font=\sffamily\bfseries\footnotesize,text=accent] at (1.5,{top-1.5:.1f}) {{Vol.\,{v}}};')
        L.append(rf'\node[anchor=north west,font=\sffamily\scriptsize,text=quiet,align=left] at (1.5,{top-5.8:.1f}) {{{t1}\\{t2}}};')
    for n, (part, q, a) in enumerate(Q):
        y = ys[n]
        axis = (n == 7)
        style = 'draw=accent,line width=1.1pt,fill=accent!12' if axis else 'draw=black!55,line width=0.5pt,fill=white'
        L.append(rf'\draw[{style},rounded corners=2pt] ({bx},{y-bh/2:.1f}) rectangle ({bx+bw},{y+bh/2:.1f});')
        L.append(rf'\node[anchor=west,font=\sffamily\bfseries\scriptsize] at ({bx+1.8},{y+2.3:.1f}) {{{n+1}.\ {q}}};')
        L.append(rf'\node[anchor=west,font=\sffamily\scriptsize,text=quiet] at ({bx+1.8},{y-2.4:.1f}) {{$\to$ {a}}};')
        L.append(rf'\node[anchor=east,font=\sffamily\tiny,text=accent] at ({bx+bw-1.2},{y+2.3:.1f}) {{Part {part}}};')
        if n < 13:
            L.append(rf'\draw[-{{Stealth[length=1.6mm]}},black!55] ({bx+bw/2},{y-bh/2:.1f}) -- ({bx+bw/2},{ys[n+1]+bh/2:.1f});')
    L.append(r'\end{tikzpicture}')
    return '\n'.join(L)


def strip():
    # \compassstrip{a}{b}: highlight questions a..b
    L = [r'\newcommand{\compassstrip}[2]{%',
         r'\begin{tikzpicture}[x=1mm,y=1mm,font=\sffamily\scriptsize]']
    x = 0
    xs = []
    for n in range(14):
        if n in (6, 9, 12):
            x += 4
        xs.append(x)
        x += 8.1
    for (v, a, b, t1, t2) in VOL:
        L.append(rf'\draw[accent!50,line width=0.6pt] ({xs[a]-3},-5) -- ({xs[b]+3},-5);')
        L.append(rf'\node[text=accent,font=\sffamily\tiny] at ({(xs[a]+xs[b])/2:.1f},-8) {{Vol.\,{v}}};')
    for n in range(14):
        if n < 13:
            L.append(rf'\draw[black!40] ({xs[n]+3},0) -- ({xs[n+1]-3},0);')
        L.append(rf'\pgfmathsetmacro\on{{(#1<={n+1})&&({n+1}<=#2)}}')
        L.append(rf'\ifdim\on pt>0.5pt\node[circle,fill=accent,text=white,inner sep=0pt,minimum size=5.4mm] at ({xs[n]},0) {{{n+1}}};'
                 rf'\else\node[circle,draw=black!45,text=black!60,inner sep=0pt,minimum size=5.4mm] at ({xs[n]},0) {{{n+1}}};\fi')
    L.append(r'\end{tikzpicture}}')
    return '\n'.join(L)


if __name__ == '__main__':
    with open(os.path.join(OUT, 'compass.tex'), 'w') as f:
        f.write('% generated by tools/compass.py\n' + full() + '\n')
    with open(os.path.join(OUT, 'compassstrip.tex'), 'w') as f:
        f.write('% generated by tools/compass.py\n' + strip() + '\n')
    print('ok')
