"""Exact-formula illustrations, not measurements or interval certificates."""
from pathlib import Path
from math import exp,log
from fractions import Fraction as F
from PIL import Image,ImageDraw,ImageFont
import hashlib,json
R=Path(__file__).resolve().parent;O=R/'images';O.mkdir(exist_ok=True)
def font(n,b=False):return ImageFont.truetype('C:/Windows/Fonts/msyhbd.ttc' if b else 'C:/Windows/Fonts/msyh.ttc',n)
INK='#25354a';GRAY='#55677b';BLUE='#1e6ba7';PURPLE='#7946a2';RED='#ac4444'
def text(d,x,y,s,n=25,c=INK,b=False):d.text((x,y),s,font=font(n,b),fill=c)
def center(d,x,y,s,n=24,c=INK,b=False):
    z=d.textbbox((0,0),s,font=font(n,b));text(d,x-(z[2]-z[0])/2,y,s,n,c,b)
def base(title,subtitle):
    im=Image.new('RGB',(1600,1000),'#f7f9fc');d=ImageDraw.Draw(im)
    text(d,48,28,title,35,b=True);text(d,48,90,subtitle,25,c=GRAY)
    return im,d
T=log(4)
def response(k):return T*exp(-T) if abs(k-1)<1e-10 else k/(k-1)*(exp(-T)-exp(-k*T))
checks=[(.5,F(1,4)),(2,F(3,8)),(4,F(21,64))]
assert all(abs(response(k)-float(v))<1e-14 for k,v in checks)
assert F(3,8)-max(F(1,4),F(21,64))==F(3,64)
im,d=base('只试参数两端，会漏掉更大的响应','同一个平滑入口 u(t)=exp(−t)，零初态；比较时刻固定为 T=ln4。')
gx,gy,w,h=150,745,1280,490
def xy(k,y):return gx+(k-.5)/3.5*w,gy-(y-.2)/.2*h
for y in (.2,.25,.3,.35,.4):
    py=xy(.5,y)[1];d.line((gx,py,gx+w,py),fill='#dce4ed');text(d,76,py-15,f'{y:.2f}',22,c=GRAY)
for k in (.5,1,2,3,4):
    px=xy(k,.2)[0];d.line((px,gy,px,gy+7),fill=GRAY,width=2);center(d,px,gy+15,str(k),22,c=GRAY)
d.line((gx,gy,gx+w+15,gy),fill=GRAY,width=2)
text(d,60,188,'固定时刻的浓度 x_k(T)',25)
text(d,1070,804,'混合速率 k（归一化单位）',24)
d.line([xy(.5+3.5*i/700,response(.5+3.5*i/700)) for i in range(701)],fill=BLUE,width=5)
py=xy(.5,float(F(21,64)))[1]
for x in range(gx,gx+w,20):d.line((x,py,min(x+10,gx+w),py),fill=RED,width=2)
text(d,880,py+13,'两个端点中的较大值：21/64',24,c=RED)
for k,value in checks:
    px,py=xy(k,float(value));d.ellipse((px-7,py-7,px+7,py+7),fill=PURPLE)
    label=f'k={k:g}：{value}'
    if k==2:center(d,px,py-62,label,27,c=PURPLE,b=True)
    elif k==.5:text(d,px+17,py+17,label,25,c=PURPLE,b=True)
    else:text(d,px-210,py-60,label,25,c=PURPLE,b=True)
text(d,60,875,'内点 k=2 比两个端点都大；这反驳“端点一定最坏”，不宣称 k=2 是全局最大。',24,b=True)
text(d,60,930,'曲线是解析函数的采样绘图；三个精确值及反例关系另有 Lean 证明。',24,c=GRAY)
im.save(O/'parameter-counterexample.png')

rho=F(21,19);rr=F(19,20);tstar=float(F(20,19))*log(2)
bound=F(28077,109744)
def nominal(t):return 1-F(7,3)*exp(-t)+F(3,2)*exp(-2*t)-F(1,6)*exp(-4*t)
def robust(t):
    q=exp(-float(rr)*t)
    return float(rho**2)*(.25-q/3+q**4/12)+float(rho**3)*(.75-2*q+1.5*q*q-q**4/4)
assert abs(robust(tstar)-float(bound))<1e-14
assert bound<F(13,50)
im,d=base('模型系数也不精确：使用保守包络，而不是只跑几个模型','零初态、0≤u(t)≤1。蓝：名义模型；紫：指定方程系数各有±5%范围时的上比较解。')
gx,gy,w,h=145,750,1290,485
def xy2(t,y):return gx+t/1.5*w,gy-y/.8*h
for y in (0,.2,.4,.6,.8):
    py=xy2(0,y)[1];d.line((gx,py,gx+w,py),fill='#dce4ed');text(d,72,py-15,f'{y:.1f}',22,c=GRAY)
for t in (0,.5,1,1.5):
    px=xy2(t,0)[0];center(d,px,gy+15,str(t),22,c=GRAY)
d.line((gx,gy,gx+w+15,gy),fill=GRAY,width=2)
text(d,60,203,'出口浓度（入口上限归一化为1）',25)
text(d,1160,808,'归一化时间 t',24)
for name,c,f in [('名义上界',BLUE,nominal),('不确定系数的保守上界',PURPLE,robust)]:
    d.line([xy2(1.5*i/600,float(f(1.5*i/600))) for i in range(601)],fill=c,width=5)
text(d,170,153,'蓝：名义模型',24,c=BLUE);text(d,650,153,'紫：区间上比较系统',24,c=PURPLE)
px,py=xy2(tstar,float(bound));d.ellipse((px-7,py-7,px+7,py+7),fill=PURPLE)
d.line((px,gy,px,py),fill=PURPLE,width=2)
d.rounded_rectangle((185,285,940,445),12,fill='white',outline='#cdbedb',width=2)
text(d,205,300,'t*=(20/19)ln2 ≈0.730',25,c=PURPLE,b=True)
text(d,205,346,'所有允许系数和输入：',24,c=PURPLE,b=True)
text(d,205,392,'x2(t*) ≤28077/109744 ≈0.255841 <0.26',24,c=PURPLE,b=True)
d.line((940,446,px+10,py-13),fill=PURPLE,width=2)
text(d,60,867,'±5%指方程中指定的四个系数，不是体积和水流量各自独立±5%。',25)
text(d,60,922,'紫线是保证包含的上界，不声称实际可达，也不等于模拟观察到的最坏曲线。',24,c=GRAY)
im.save(O/'robust-envelope.png')
record={'kind':'deterministic exact-formula teaching figures','parameter_check':{'T':'log4','values':{'1/2':'1/4','2':'3/8','4':'21/64'},'interior_minus_endpoint_max':'3/64'},
        'robust_check':{'time':'(20/19)log2','bound':'28077/109744','bound_float':float(bound),'not_claimed_sharp':True},
        'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.glob('*.png'))}}
(R/'figure-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,ensure_ascii=True))
