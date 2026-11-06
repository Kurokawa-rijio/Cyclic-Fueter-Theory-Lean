import numpy as np
from bmS3 import cls, bis, run
bs=[0.453716257503256,0.651725501081946,0.697040022536808,0.704878467049758,0.7061686556741109]
for lo,hi in [(0.706378,0.70638),(0.706412,0.706414),(0.706418,0.70642)]:
    bs.append(bis(lo,hi)); print(len(bs),repr(bs[-1]),flush=True)
np.save('bn.npy',np.array(bs))
