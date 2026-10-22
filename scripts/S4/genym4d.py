import sympy as sp, pickle
exec(open('gen4d.py').read().split("# substitute N=1")[0])
from gen3 import setup as _s
# rebuild NF of YM components with N=1 using genYMDall pickled strings? recompute directly
import importlib
from sympy import LeviCivita
funs2=['N','A','R','W']
J2,inv2,sc2,D2,_,_=_s(funs2)
