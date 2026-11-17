from pathlib import Path
import json,hashlib
from PIL import Image,ImageDraw,ImageFont

ROOT=Path(__file__).resolve().parents[1]
W,H=1800,1150
im=Image.new('RGB',(W,H),'white');d=ImageDraw.Draw(im)
regular=Path('C:/Windows/Fonts/arial.ttf');bold=Path('C:/Windows/Fonts/arialbd.ttf')
font=lambda n,b=False:ImageFont.truetype(str(bold if b else regular),n)
ink='#1c2b33';blue='#246c9a';green='#2f8069';orange='#b96a18';amber='#fff0d8';grid='#d4dde4';red='#bd3535'
def txt(x,y,t,n=27,fill=ink,b=False,anchor=None):d.text((x,y),t,font=font(n,b),fill=fill,anchor=anchor)
txt(60,25,'A vacant quadrant forces cubic weighted loss',43,b=True)
txt(60,88,'Static example: L = 80, q = (72,1), and w(x,y) = 82 - |x| - |y|.',29)
txt(115,160,'Clipped domain and protected set',29,b=True)
txt(1015,160,'The full vacant block: m = floor(L/20) = 4',29,b=True)
cx,cy,scale=450,570,4.0
pt=lambda x,y:(cx+scale*x,cy-scale*y)
poly=[(80,1),(1,80),(-1,80),(-80,1),(-80,-1),(-1,-80),(1,-80),(80,-1)]
d.polygon([pt(*p) for p in poly],fill='#e9f1f7')
d.polygon([pt(-73,0),pt(0,-73),pt(0,73),pt(73,0)],fill='#e8f3ee')
# The visible southwest part of the empty quadrant, clipped to the domain.
sw=[(-80,-1),(-1,-80),(1,-80),(72,-9),(72,1),(-80,1)]
d.polygon([pt(*p) for p in sw],fill=amber)
for v in range(-80,81,20):
    x,y=pt(v,0);d.line((x,250,x,890),fill=grid,width=1);txt(x,905,str(v),22,anchor='ma')
    x,y=pt(0,v);d.line((130,y,770,y),fill=grid,width=1);txt(115,y,str(v),22,anchor='rm')
d.line((115,570,790,570),fill='#9ba9b2',width=2);d.line((450,235,450,905),fill='#9ba9b2',width=2)
d.line([pt(*p) for p in poly]+[pt(*poly[0])],fill=blue,width=3)
d.line([pt(-73,0),pt(0,-73),pt(73,0),pt(0,73),pt(-73,0)],fill=green,width=3)
qx,qy=pt(72,1);d.ellipse((qx-6,qy-6,qx+6,qy+6),outline=red,width=2)
txt(qx-6,qy+14,'q',25,red,b=True)
txt(300,735,'empty southwest quadrant',25,orange)
txt(180,960,'D: |x|,|y| <= 80 and |x|+|y| <= 81',24,blue)
txt(240,1000,'P: |x|+|y| <= 73',24,green)

# Grid cell labels are mathematical coordinates at cell centres.
left,top,size=1030,290,58
xlo,xhi,ylo,yhi=67,74,-4,4
xy=lambda x,y:(left+(x-xlo)*size,top+(yhi-y)*size)
occupied={(73,1),(72,2),(73,2)}
block={(72-i,1-j) for i in range(1,5) for j in range(1,5)}
weights={p:82-abs(p[0])-abs(p[1]) for p in block}
assert sum(weights.values())==176
for y in range(ylo,yhi+1):
  for x in range(xlo,xhi+1):
    px,py=xy(x,y)
    fill=ink if (x,y) in occupied else amber if (x,y) in block else 'white'
    d.rectangle((px,py,px+size,py+size),fill=fill,outline=grid,width=1)
    if (x,y) in occupied:txt(px+size/2,py+size/2,'S',24,'white',True,'mm')
    if (x,y) in block:txt(px+size/2,py+size/2,str(weights[(x,y)]),24,orange,True,'mm')
    if (x,y)==(72,1):
      d.ellipse((px+9,py+9,px+size-9,py+size-9),outline=red,width=2)
      txt(px+size/2,py+size/2,'q',25,red,True,'mm')
for x in range(xlo,xhi+1):txt(xy(x,ylo)[0]+size/2,top+(yhi-ylo+1)*size+16,str(x),22,anchor='ma')
for y in range(ylo,yhi+1):txt(left-20,xy(xlo,y)[1]+size/2,str(y),22,anchor='rm')
txt(1025,220,'Occupied S = {(73,1), (72,2), (73,2)}',25)
txt(1025,880,'Sixteen missing sites: q - (i,j), 1 <= i,j <= 4',25,orange)
txt(1025,925,'Exact sum = 50 + 46 + 42 + 38 = 176',26,orange,b=True)
txt(1025,970,'Affine lower sum: 16(8 - 4) = 64',26)
txt(1025,1015,'Cubic threshold: 80^3 / 12500 = 40.96',26)
txt(60,1080,'S is row- and column-convex and connected by nearest-neighbour steps.',26)
txt(60,1120,'Static geometry only; no reachable or stable clock state is asserted.',23,'#596d79')
out=ROOT/'images/static-protected-geometry.png';im.save(out)
data={'L':80,'q':[72,1],'m':4,'weights':{f'{x},{y}':w for (x,y),w in sorted(weights.items())},
      'sum':sum(weights.values()),'affine_lower':64,'threshold':'40.96',
      'image_sha256':hashlib.sha256(out.read_bytes()).hexdigest()}
(ROOT/'review/static-figure-data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'output':str(out),'sum':176,'image_sha256':data['image_sha256']}))
