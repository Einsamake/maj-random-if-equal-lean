"""Draw explanatory diagrams from the displayed analytic formulas.

No trajectories in these figures replace the separate formal comparison proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import exp, log
from PIL import Image, ImageDraw, ImageFont
import hashlib, json

R=Path(__file__).resolve().parent
O=R/'images'; O.mkdir(exist_ok=True)
INK='#25354a'; GRAY='#55677b'; BLUE='#1e6ba7'; PURPLE='#7946a2'; GREEN='#18735a'
BG='#f7f9fc'; GRID='#dce4ed'; RED='#ac4444'
def font(n,b=False):
    return ImageFont.truetype('C:/Windows/Fonts/msyhbd.ttc' if b else 'C:/Windows/Fonts/msyh.ttc',n)
def text(d,x,y,s,n=25,c=INK,b=False): d.text((x,y),s,font=font(n,b),fill=c)
def center(d,x,y,s,n=24,c=INK,b=False):
    bb=d.textbbox((0,0),s,font=font(n,b)); text(d,x-(bb[2]-bb[0])/2,y,s,n,c,b)
def canvas(title,subtitle):
    im=Image.new('RGB',(1600,1040),BG); d=ImageDraw.Draw(im)
    text(d,48,26,title,35,b=True); text(d,48,88,subtitle,25,c=GRAY)
    return im,d
def response(q): return 1-7*q/3+1.5*q*q-q**4/6
def nominal(t): return response(exp(-t))
def endpoint(t): return response(exp(-1.05*t))
def old(t):
    q=exp(-.95*t); rho=21/19
    return rho*rho*(.25-q/3+q**4/12)+rho**3*(.75-2*q+1.5*q*q-q**4/4)
T=20*log(2)/19
old_exact=F(28077,109744)
rational=F(7425545410773,32000000000000)
assert abs(old(T)-float(old_exact))<1e-13
assert endpoint(T)<float(rational)<.233<.24<float(old_exact)

im,d=canvas('能否保证出口低于0.24？新的最大曲线给出肯定答案',
    '三箱零初态；入口0≤u(t)≤1；四个固定方程速率各有±5%范围。时间与浓度均已归一化。')
text(d,130,157,'出口浓度 x2',25)
for x,col,label in [(150,PURPLE,'旧：保守上界'),(620,GREEN,'新：实际可达的最大曲线'),(1170,BLUE,'名义模型，入口1')]:
    d.line((x,214,x+48,214),fill=col,width=5); text(d,x+58,192,label,23,col)
gx,gy,w,h=150,790,1290,480
def xy(t,y): return gx+t/1.2*w,gy-y/.6*h
for y in [0,.1,.2,.3,.4,.5,.6]:
    py=xy(0,y)[1];d.line((gx,py,gx+w,py),fill=GRID);text(d,80,py-15,f'{y:.1f}',23,GRAY)
for t in [0,.2,.4,.6,.8,1,1.2]:
    px=xy(t,0)[0];d.line((px,gy,px,gy+7),fill=GRAY,width=2);center(d,px,gy+15,f'{t:g}',23,GRAY)
text(d,1280,846,'归一化时间 t',23)
for col,func in [(BLUE,nominal),(GREEN,endpoint),(PURPLE,old)]:
    d.line([xy(1.2*i/800,func(1.2*i/800)) for i in range(801)],fill=col,width=5)
threshold=xy(0,.24)[1]
for x in range(gx,gx+w,22):d.line((x,threshold,min(x+10,gx+w),threshold),fill=RED,width=2)
text(d,160,threshold-36,'判断门槛0.24',23,RED)
px=xy(T,0)[0]
for y in range(305,gy,18): d.line((px,y,px,min(y+9,gy)),fill=GRAY,width=2)
for col,fun in [(GREEN,endpoint),(PURPLE,old)]:
    xx,yy=xy(T,fun(T)); d.ellipse((xx-7,yy-7,xx+7,yy+7),fill=col)
d.rounded_rectangle((175,305,725,455),radius=12,fill='white',outline=GRID,width=2)
text(d,198,319,'同一观察时刻 t*=(20/19)ln2',25,b=True)
text(d,198,366,'旧保证 ≤0.255841',25,PURPLE)
text(d,198,407,'新最大值 ≈0.231729',25,GREEN,b=True)
center(d,px,875,'t*≈0.730',25,GRAY)
text(d,60,930,'严格保证：x2(t*) ≤7425545410773/32000000000000 <0.233 <0.24。',25,b=True)
text(d,60,983,'曲线来自解析式；全部模型均被包含的结论另有证明。0.24是本例门槛，不是实测安全标准。',23,GRAY)
im.save(O/'endpoint-certificate.png')

im,d=canvas('同一条候选轨迹上的浓度顺序，决定比较的方向',
    '候选：入口恒为1；速率(a,b,e,f)=(1.05,2.1,1.05,3.15)。图画t*，正文证明所有t≥0。')
q=exp(-1.05*T); values=[1-q,(1-q)**2,response(q)]
assert values[0]>=values[1]>=values[2]>=0
text(d,65,161,'箭头表示方程中的浓度耦合；5%直接针对速率系数。',24,GRAY)
text(d,65,195,'色块高度代表浓度，容器仅作示意。',23,GRAY)
def arrow(points,color=GRAY,width=4):
    d.line(points,fill=color,width=width)
    x,y=points[-1]; x0,y0=points[-2]
    if x>x0:d.polygon([(x,y),(x-17,y-9),(x-17,y+9)],fill=color)
    elif x<x0:d.polygon([(x,y),(x+17,y-9),(x+17,y+9)],fill=color)
    elif y>y0:d.polygon([(x,y),(x-9,y-17),(x+9,y-17)],fill=color)
    else:d.polygon([(x,y),(x-9,y+17),(x+9,y+17)],fill=color)
xs=[375,815,1255]
for i,(x,v) in enumerate(zip(xs,values)):
    left=x-86; right=x+86; top=410; bottom=685
    d.rounded_rectangle((left,top,right,bottom),radius=10,outline=GREEN,width=4,fill='white')
    level=bottom-260*v
    d.rectangle((left+5,level,right-5,bottom-5),fill='#a9d7c9')
    center(d,x,350,f'第{i}箱  Y{i}',29,b=True)
    center(d,x,710,f'{v:.4f}',29,GREEN,b=True)
    center(d,x,757,'浓度',23,GRAY)
arrow([(80,480),(282,480)]);text(d,70,427,'入口1',26,b=True)
arrow([(465,475),(722,475)]);center(d,595,427,'b=2.1',25)
arrow([(905,475),(1162,475)]);center(d,1030,427,'f=3.15',25)
arrow([(465,420),(505,420),(505,270),(1125,270),(1125,420),(1162,420)])
center(d,810,222,'e=1.05：第0箱也直接影响第2箱',25)
text(d,120,520,'a=1.05',25)
text(d,70,833,'令 q=exp(−1.05t)，三个基本差始终非负：',26,b=True)
text(d,95,894,'1−Y0=q',27,GREEN)
text(d,535,894,'Y0−Y1=q(1−q)',27,GREEN)
text(d,1020,894,'Y1−Y2=q(1−q)²(q+2)/6',25,GREEN)
text(d,70,978,'速率差 ≥0 × 浓度差 ≥0 → 候选在同一状态下的变化率足够大 → 比较原理给出全程上界。',23,GRAY)
im.save(O/'why-endpoint-works.png')

record={'kind':'analytic-curve samples and a concentration-coupling schematic; no simulation certificate',
    'time':'(20/19)log2','time_float':T,'nominal_value':nominal(T),'endpoint_value_numeric':endpoint(T),
    'old_bound':'28077/109744','new_rational_bound':'7425545410773/32000000000000',
    'rate_box_percent':5,'coefficients_fixed':True,'all_input_range':[0,1],
    'q_half_example':{'Y0':'1/2','Y1':'1/4','Y2':'19/96','Y1_minus_Y2':'5/96'},
    'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.glob('*.png'))}}
(R/'figure-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,ensure_ascii=True))
