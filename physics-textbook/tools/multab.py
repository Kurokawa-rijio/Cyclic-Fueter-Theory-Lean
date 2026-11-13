#!/usr/bin/env python3
"""Generate the book's multiplication tables.

Every cell is computed here from Hamilton's rules; nothing in a table is
typed by hand.  A table has row headers (left factor) and column headers
(right factor).  Each header carries a unit (1, i, j, k), an optional
commuting imaginary unit iota (iota^2 = -1), a numerical coefficient and a
symbol.  A cell holds

    (row coefficient)(column coefficient)(row unit)(column unit)  x  term

and is coloured by the unit of the result.  Below the table the cells of
each colour are added up ("reading").  Pairs of cells whose terms cancel
are marked with the same small letter.

Usage:  python3 tools/multab.py   (writes generated/*.tex)
"""
from fractions import Fraction
from collections import OrderedDict
import os

UNITS = ['1', 'i', 'j', 'k']
COLOR = ['uone', 'ui', 'uj', 'uk']
STYLE = ['uonestyle', 'uistyle', 'ujstyle', 'ukstyle']

# Hamilton: e_a e_b = sign * e_c
T = {(0, 0): (1, 0), (0, 1): (1, 1), (0, 2): (1, 2), (0, 3): (1, 3),
     (1, 0): (1, 1), (1, 1): (-1, 0), (1, 2): (1, 3), (1, 3): (-1, 2),
     (2, 0): (1, 2), (2, 1): (-1, 3), (2, 2): (-1, 0), (2, 3): (1, 1),
     (3, 0): (1, 3), (3, 1): (1, 2), (3, 2): (-1, 1), (3, 3): (-1, 0)}


def check_rules():
    """i^2 = j^2 = k^2 = ijk = -1 and associativity on all 64 triples."""
    def mul(x, y):
        s1, a = x
        s2, b = y
        s, c = T[(a, b)]
        return (s1 * s2 * s, c)
    for a in range(4):
        for b in range(4):
            for c in range(4):
                assert mul(mul((1, a), (1, b)), (1, c)) == mul((1, a), mul((1, b), (1, c)))
    assert mul(mul((1, 1), (1, 2)), (1, 3)) == (-1, 0)
    for a in (1, 2, 3):
        assert mul((1, a), (1, a)) == (-1, 0)


class H:
    """A header entry: coef * iota^iota * unit, with a symbol."""
    def __init__(self, label, unit, sym, coef=1, iota=0):
        self.label, self.unit, self.sym = label, unit, sym
        self.coef, self.iota = Fraction(coef), iota


def term(row, col, mode):
    """Return (key, tex) for the product of the two symbols."""
    if mode == 'commute':          # commuting real symbols: a*b = b*a
        a, b = sorted([row.sym, col.sym])
        if a == b:
            return (a, a), f'{a}^2'
        return (a, b), f'{a}{b}' if len(a) == 1 and len(b) == 1 else f'{a}\\,{b}'
    if mode == 'apply':            # an operator applied to a component
        return (row.sym, col.sym), f'{row.sym} {col.sym}'
    if mode == 'second':           # two commuting derivatives
        a, b = sorted([row.sym, col.sym])
        if a == b:
            return (a, a), f'{a}^2'
        return (a, b), f'{a}{b}'
    if mode == 'number':
        return ('',), ''
    raise ValueError(mode)


def fmt_coef(c, first, unit_tex, body, iota):
    """Format sign * |c| * iota * unit * body."""
    sign = '-' if c < 0 else ('' if first else '+')
    a = abs(c)
    num = '' if (a == 1 and (body or unit_tex or iota)) else (str(a) if a.denominator == 1 else f'\\tfrac{{{a.numerator}}}{{{a.denominator}}}')
    parts = [p for p in [num, '\\iota' if iota else '', unit_tex, body] if p]
    s = '\\,'.join(parts) if parts else '1'
    return sign + s


def build(name, rows, cols, mode, title_tex, reading_title=None, show_one=True, cell_w=24, hdr_w=20):
    cells = []          # (r, c, coef, iota, unit, key, tex)
    groups = OrderedDict()
    for r_i, row in enumerate(rows):
        for c_i, col in enumerate(cols):
            s, u = T[(row.unit, col.unit)]
            coef = row.coef * col.coef * s
            io = row.iota + col.iota
            if io == 2:
                coef, io = -coef, 0
            key, tex = term(row, col, mode)
            cells.append((r_i, c_i, coef, io, u, key, tex))
            g = groups.setdefault((u, io), OrderedDict())
            g.setdefault(key, []).append((r_i, c_i, coef, tex))
    # cancellation letters
    letters = 'abcdefghjkmnpqrstuvwxyz'
    mark = {}
    li = 0
    for (u, io), g in sorted(groups.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        for key, lst in g.items():
            if sum(x[2] for x in lst) == 0 and len(lst) >= 2:
                for (r_i, c_i, _, _) in lst:
                    mark[(r_i, c_i)] = letters[li]
                li += 1

    out = []
    W, Hh = cell_w, 9.5     # mm
    gap = 1.4
    out.append('\\begin{tikzpicture}[x=1mm,y=1mm,font=\\small]')
    # corner + column headers
    out.append(f'\\node[mtcorner] at ({hdr_w/2},0) {{{title_tex}}};')
    for c_i, col in enumerate(cols):
        x = hdr_w + gap + c_i * (W + gap) + W / 2
        out.append(f'\\node[mthead] at ({x:.1f},0) {{{col.label}}};')
    for r_i, row in enumerate(rows):
        y = -(Hh + gap) * (r_i + 1)
        out.append(f'\\node[mthead] at ({hdr_w/2},{y:.1f}) {{{row.label}}};')
    for (r_i, c_i, coef, io, u, key, tex) in cells:
        x0 = hdr_w + gap + c_i * (W + gap)
        y = -(Hh + gap) * (r_i + 1)
        unit_tex = '' if u == 0 else UNITS[u]
        if mode == 'number':
            body = ''
            if u == 0 and coef != 0 and abs(coef) != 1:
                pass
            txt = fmt_coef(coef, True, unit_tex, body, io)
            if txt in ('1', '-1') and u == 0:
                txt = txt
        else:
            unit_disp = '1' if (u == 0 and show_one) else unit_tex
            # show the unit explicitly for clarity: +1 . a^2
            if u == 0 and show_one:
                lead = ('-' if coef < 0 else '+') + (str(abs(coef)) if abs(coef) != 1 else '1')
                lead += '\\,\\iota' if io else ''
                txt = lead + '\\cdot ' + tex
            else:
                txt = fmt_coef(coef, False, unit_tex, '', io) + '\\cdot ' + tex
                if not txt.startswith('-') and not txt.startswith('+'):
                    txt = '+' + txt
        style = STYLE[u]
        out.append(f'\\draw[{style}] ({x0:.1f},{y - Hh/2:.1f}) rectangle ({x0 + W:.1f},{y + Hh/2:.1f});')
        out.append(f'\\node at ({x0 + W/2:.1f},{y:.1f}) {{${txt}$}};')
        if (r_i, c_i) in mark:
            out.append(f'\\node[mtmark] at ({x0 + W - 2.2:.1f},{y + Hh/2 - 2.2:.1f}) {{{mark[(r_i, c_i)]}}};')
    out.append('\\end{tikzpicture}')
    pic = '\n'.join(out)

    # reading
    rd = []
    for (u, io), g in sorted(groups.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        pieces = []
        cancelled = []
        for key, lst in g.items():
            c = sum(x[2] for x in lst)
            if c == 0:
                cancelled.append(mark[(lst[0][0], lst[0][1])])
                continue
            tex = lst[0][3]
            if mode == 'number':
                pieces.append((c, ''))
            else:
                pieces.append((c, tex))
        if pieces:
            expr = ''
            for n, (c, tex) in enumerate(pieces):
                sign = '-' if c < 0 else ('' if n == 0 else '+')
                a = abs(c)
                coeftxt = '' if (a == 1 and tex) else str(a)
                expr += f' {sign} {coeftxt}{tex}'
            expr = expr.strip()
        else:
            expr = '0'
        unit_name = '1' if u == 0 else UNITS[u]
        if io:
            unit_name = '\\iota' + ('' if u == 0 else '\\,' + UNITS[u])
        note = ''
        if cancelled:
            lab = ', '.join(f'\\textsf{{{x}}}' for x in cancelled)
            note = ('\\quad\\text{(pair ' + lab + ' cancels)}') if len(cancelled) == 1 else ('\\quad\\text{(pairs ' + lab + ' cancel)}')
        rd.append(f'\\mtswatch{{{STYLE[u]}}} & ${unit_name}$: & ${expr}{note}$ \\\\')
    reading = '\\begin{tabular}{@{}c@{\\ }r@{\\ }l@{}}\n' + '\n'.join(rd) + '\n\\end{tabular}'
    with open(os.path.join(OUT, name + '.tex'), 'w') as f:
        f.write('% generated by tools/multab.py -- do not edit\n')
        f.write('\\begin{center}\n' + pic + '\n\\par\\medskip\n' + reading + '\n\\end{center}\n')
    return groups


OUT = os.path.join(os.path.dirname(__file__), '..', 'generated')

if __name__ == '__main__':
    check_rules()
    one, i, j, k = 0, 1, 2, 3
    # 1. the unit table
    U = [H('$1$', one, '1'), H('$i$', i, '1'), H('$j$', j, '1'), H('$k$', k, '1')]
    out = []
    W, Hh, gap, hw = 17, 9.5, 1.4, 12
    out.append('\\begin{tikzpicture}[x=1mm,y=1mm]')
    out.append(f'\\node[mtcorner] at ({hw/2},0) {{$\\times$}};')
    for c in range(4):
        out.append(f'\\node[mthead] at ({hw + gap + c*(W+gap) + W/2:.1f},0) {{${UNITS[c]}$}};')
    for r in range(4):
        y = -(Hh + gap) * (r + 1)
        out.append(f'\\node[mthead] at ({hw/2},{y:.1f}) {{${UNITS[r]}$}};')
        for c in range(4):
            s, u = T[(r, c)]
            x0 = hw + gap + c * (W + gap)
            out.append(f'\\draw[{STYLE[u]}] ({x0:.1f},{y-Hh/2:.1f}) rectangle ({x0+W:.1f},{y+Hh/2:.1f});')
            out.append(f'\\node at ({x0+W/2:.1f},{y:.1f}) {{\\large ${"-" if s < 0 else ""}{UNITS[u]}$}};')
    out.append('\\end{tikzpicture}')
    with open(os.path.join(OUT, 'units.tex'), 'w') as f:
        f.write('% generated by tools/multab.py -- do not edit\n\\begin{center}\n' + '\n'.join(out) + '\n\\end{center}\n')

    # 2. p q, general
    P = [H('$p_0$', one, 'p_0'), H('$p_1\\,i$', i, 'p_1'), H('$p_2\\,j$', j, 'p_2'), H('$p_3\\,k$', k, 'p_3')]
    Q = [H('$q_0$', one, 'q_0'), H('$q_1\\,i$', i, 'q_1'), H('$q_2\\,j$', j, 'q_2'), H('$q_3\\,k$', k, 'q_3')]
    build('pq', P, Q, 'apply', '$p\\,q$', cell_w=24)

    # 3. q qbar (Euclidean)
    Qr = [H('$a$', one, 'a'), H('$b\\,i$', i, 'b'), H('$c\\,j$', j, 'c'), H('$d\\,k$', k, 'd')]
    Qc = [H('$a$', one, 'a'), H('$-b\\,i$', i, 'b', -1), H('$-c\\,j$', j, 'c', -1), H('$-d\\,k$', k, 'd', -1)]
    build('qqbar', Qr, Qc, 'commute', '$q\\,\\bar q$', cell_w=24)

    # 4. Dbar D = Laplacian
    Dr = [H('$\\partial_t$', one, '\\partial_t'), H('$-i\\,\\partial_x$', i, '\\partial_x', -1),
          H('$-j\\,\\partial_y$', j, '\\partial_y', -1), H('$-k\\,\\partial_z$', k, '\\partial_z', -1)]
    Dc = [H('$\\partial_t$', one, '\\partial_t'), H('$i\\,\\partial_x$', i, '\\partial_x'),
          H('$j\\,\\partial_y$', j, '\\partial_y'), H('$k\\,\\partial_z$', k, '\\partial_z')]
    build('dbard', Dr, Dc, 'second', '$\\bar D D$', cell_w=24)

    # 5. Minkowski: X Xbar with X = t + iota (x i + y j + z k)
    Mr = [H('$t$', one, 't'), H('$\\iota x\\,i$', i, 'x', 1, 1), H('$\\iota y\\,j$', j, 'y', 1, 1), H('$\\iota z\\,k$', k, 'z', 1, 1)]
    Mc = [H('$t$', one, 't'), H('$-\\iota x\\,i$', i, 'x', -1, 1), H('$-\\iota y\\,j$', j, 'y', -1, 1), H('$-\\iota z\\,k$', k, 'z', -1, 1)]
    build('minkowski', Mr, Mc, 'commute', '$X\\bar X$', cell_w=24)

    # 6. D q
    Fr = [H('$\\partial_t$', one, '\\partial_t'), H('$i\\,\\partial_x$', i, '\\partial_x'),
          H('$j\\,\\partial_y$', j, '\\partial_y'), H('$k\\,\\partial_z$', k, '\\partial_z')]
    Fc = [H('$q_t$', one, 'q_t'), H('$q_x\\,i$', i, 'q_x'), H('$q_y\\,j$', j, 'q_y'), H('$q_z\\,k$', k, 'q_z')]
    build('dq', Fr, Fc, 'apply', '$D\\,q$', cell_w=24)

    # 7. numerical example (1 + i + j)(2 + i)
    Nr = [H('$1$', one, '1', 1), H('$i$', i, '1', 1), H('$j$', j, '1', 1)]
    Nc = [H('$2$', one, '1', 2), H('$i$', i, '1', 1)]
    g = build('numeric', Nr, Nc, 'number', '$(1+i+j)(2+i)$', cell_w=22, hdr_w=24)

    # 8. pure quaternions u v
    Ur = [H('$u_1\\,i$', i, 'u_1'), H('$u_2\\,j$', j, 'u_2'), H('$u_3\\,k$', k, 'u_3')]
    Vc = [H('$v_1\\,i$', i, 'v_1'), H('$v_2\\,j$', j, 'v_2'), H('$v_3\\,k$', k, 'v_3')]
    build('uv', Ur, Vc, 'apply', '$u\\,v$', cell_w=24)
    print('tables written to', os.path.abspath(OUT))
