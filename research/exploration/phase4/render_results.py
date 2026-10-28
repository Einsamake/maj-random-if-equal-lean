"""Reproducible analytic plots and the gap-equation diagram."""
from pathlib import Path
from math import exp,log
from fractions import Fraction as F
from PIL import Image,ImageDraw,ImageFont
import json,hashlib
R=Path(__file__).resolve().parent;O=R/'images';O.mkdir(exist_ok=True)
INK='#25354a';GRAY='#55677b';BLUE='#1e6ba7';ORANGE='#ad581d';GREEN='#18735a';BG='#f7f9fc';GRID='#dce4ed'
def font(n,b=False):return ImageFont.truetype('C:/Windows/Fonts/msyhbd.ttc' if b else 'C:/Windows/Fonts/msyh.ttc',n)
def text(d,x,y,s,n=25,c=INK,b=False):d.text((x,y),s,font=font(n,b),fill=c)
def center(d,x,y,s,n=24,c=INK,b=False):
 bb=d.textbbox((0,0),s,font=font(n,b));text(d,x-(bb[2]-bb[0])/2,y,s,n,c,b)
def base(title,subtitle):
 im=Image.new('RGB',(1600,1040),BG);d=ImageDraw.Draw(im)
 text(d,48,27,title,34,b=True);text(d,48,90,subtitle,25,GRAY);return im,d
def low(t):
 r=exp(-t/2);return 1-r*r-r/2+r**5/2
def high(t):
 r=exp(-t/2);return 1-r*r/2-.8*r+.3*r**6
def middle(t):return (1-exp(-t/2))**2
T=2*log(2)
assert abs(low(T)-float(F(33,64)))<1e-13
assert abs(high(T)-float(F(307,640)))<1e-13
assert F(33,64)-F(307,640)==F(23,640)
im,d=base('同样的恒定入口，连接加快，出口浓度反而降低',
 '零初态，u=1；a=1、b=0.5、e=2保持不变，只把f从0.5改成1。所有速率都严格为正。')
text(d,140,158,'浓度（入口上限为1）',25)
for x,col,label in [(150,BLUE,'f=0.5的出口'),(620,ORANGE,'f=1的出口'),(1110,GRAY,'共同第1箱')]:
 d.line((x,219,x+45,219),fill=col,width=5);text(d,x+57,198,label,24,col)
gx,gy,w,h=150,800,1290,490
def xy(t,y):return gx+t/2*w,gy-y/.8*h
for y in [0,.2,.4,.6,.8]:
 py=xy(0,y)[1];d.line((gx,py,gx+w,py),fill=GRID);text(d,78,py-15,f'{y:.1f}',23,GRAY)
for t in [0,.5,1,1.5,2]:
 px=xy(t,0)[0];center(d,px,gy+17,f'{t:g}',23,GRAY)
for col,fun in [(BLUE,low),(ORANGE,high),(GRAY,middle)]:
 d.line([xy(2*i/800,fun(2*i/800)) for i in range(801)],fill=col,width=5)
px=xy(T,0)[0]
for yy in range(310,gy,18):d.line((px,yy,px,min(yy+9,gy)),fill=GRAY,width=2)
for col,fun in [(BLUE,low),(ORANGE,high),(GRAY,middle)]:
 xx,yy=xy(T,fun(T));d.ellipse((xx-7,yy-7,xx+7,yy+7),fill=col)
d.rounded_rectangle((180,320,855,515),radius=12,fill='white',outline=GRID,width=2)
text(d,205,335,'同一时刻 T=2ln2 ≈1.386',27,b=True)
text(d,205,383,'f=0.5：33/64 =0.515625',26,BLUE,b=True)
text(d,205,426,'f=1：307/640 =0.4796875',26,ORANGE,b=True)
text(d,205,469,'较大f的出口少23/640 =0.0359375',25)
text(d,1270,850,'归一化时间 t',24)
text(d,60,920,'严格结论：这两个实际模型足以否定“把f取最大就一定最坏”。',26,b=True)
text(d,60,980,'没有据此证明全f区间的单调性或真正最大值。曲线来自解析公式，指定时刻的不等式有Lean证明。',23,GRAY)
im.save(O/'constant-inlet-counterexample.png')

im,d=base('把浓度差当作变量：先检查这条正向驱动链',
 '上端真实方程，入口1，零初态；A、B、E、F≥0。充分条件B≥E使三个差保持非负。')
names=['g0=1−Y0','g1=Y0−Y1','g2=Y1−Y2'];xs=[285,800,1315]
for x,n,initial in zip(xs,names,[1,0,0]):
 d.rounded_rectangle((x-160,285,x+160,480),radius=16,fill='white',outline=GREEN,width=3)
 center(d,x,325,n,31,GREEN,b=True)
 center(d,x,401,f'初值 {initial}',27)
def arrow(x1,x2,y,label):
 d.line((x1,y,x2,y),fill=GREEN,width=5)
 d.polygon([(x2,y),(x2-17,y-10),(x2-17,y+10)],fill=GREEN)
 center(d,(x1+x2)/2,y-55,label,27,GREEN,b=True)
arrow(450,635,385,'A ≥0')
arrow(965,1150,385,'B−E ≥0')
text(d,100,550,'差变量的真实方程',29,b=True)
text(d,150,615,"g0' = −A g0",30)
text(d,150,680,"g1' = A g0 − B g1",30)
text(d,150,745,"g2' = (B−E)g1 − (E+F)g2",30)
text(d,980,605,'顺次用积分因子：',27,GREEN,b=True)
text(d,980,663,'非负初值 + 非负驱动',26,GREEN)
text(d,980,715,'→ 差变量不会变负',27,GREEN,b=True)
text(d,100,856,'得到 1≥Y0≥Y1≥Y2，再由非负残差把所有允许模型压在Y之下。',27,b=True)
text(d,100,922,'该条件针对上端解的排序；没有要求所有实际参数的轨迹都保持同样顺序。',24,GRAY)
text(d,100,980,'B≥E是已证的充分条件，本轮没有证明它是必要条件或给出完整分类。',24,GRAY)
im.save(O/'ordered-gaps.png')
record={'kind':'analytic formulas and a gap-equation schematic; no physical experiment',
 'inlet':'constant1','a':'1','b':'1/2','e':'2','f_pair':['1/2','1'],
 'time':'2log2','outlets':['33/64','307/640'],'difference':'23/640','all_rates_strictly_positive':True,
 'not_claimed':['interior_beats_both_endpoints','whole_f_monotonicity','global_f_maximum','necessity_of_B_ge_E'],
 'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.glob('*.png'))}}
(R/'figure-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,ensure_ascii=True))

