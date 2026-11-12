#!/bin/bash
# usage: tools/sheet.sh chNN [dpi]  -> out/sheet.png
cd "$(dirname "$0")/../out"; rm -f q-*.png
pdftoppm -r ${2:-45} -png $1.pdf q
python3 -c "
import glob
from PIL import Image
fs=sorted(glob.glob('q-*.png'),key=lambda s:int(s[2:-4])); ims=[Image.open(f) for f in fs]
w,h=ims[0].size; n=len(ims); cols=min(n,4); rows=(n+cols-1)//cols
c=Image.new('RGB',(w*cols,h*rows),'white')
for k,im in enumerate(ims): c.paste(im,((k%cols)*w,(k//cols)*h))
c.save('sheet.png')"
