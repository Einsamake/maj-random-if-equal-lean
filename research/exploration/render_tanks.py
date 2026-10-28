"""Deterministic ideal-model illustrations; RK4 curves are not certificates.
All exact theorem claims are separately tied to the Lean source and audit.
"""
from pathlib import Path
from fractions import Fraction as F
from math import exp, log, sin, cos, atan2
from PIL import Image, ImageDraw, ImageFont
import json, hashlib

R=Path(__file__).resolve().parent
O=R/'images'; O.mkdir(exist_ok=True)
FONT='C:/Windows/Fonts/msyh.ttc'; BOLD='C:/Windows/Fonts/msyhbd.ttc'
INK='#25354a'; BLUE='#1b68a7'; GREEN='#237b63'; ORANGE='#ad650e'; GRAY='#526579'
def f(n,b=False): return ImageFont.truetype(BOLD if b else FONT,n)
def text(d,x,y,s,n=26,c=INK,b=False): d.text((x,y),s,font=f(n,b),fill=c)
def center(d,x,y,s,n=26,c=INK,b=False):
    z=d.textbbox((0,0),s,font=f(n,b)); text(d,x-(z[2]-z[0])/2,y,s,n,c,b)
def arrow(d,a,b,c=BLUE,width=5):
    d.line((a,b),fill=c,width=width)
    angle=atan2(b[1]-a[1],b[0]-a[0]); length=17
    p1=(b[0]-length*cos(angle-.48),b[1]-length*sin(angle-.48))
    p2=(b[0]-length*cos(angle+.48),b[1]-length*sin(angle+.48))
    d.polygon([b,p1,p2],fill=c)
def base(title,subtitle,h=960):
    im=Image.new('RGB',(1600,h),'#f7f9fc'); d=ImageDraw.Draw(im)
    text(d,48,28,title,36,b=True); text(d,48,93,subtitle,25,c=GRAY)
    return im,d

im,d=base('证明工具的一个用途：给未知输入画一条严格上界','三个恒定体积、完全混合的理想水箱；每条水流都标明方向与流量，单位 L/s。')
boxes=[(205,225,485,525),(650,225,930,525),(1095,225,1375,525)]
for i,(left,top,right,bottom) in enumerate(boxes):
    d.rounded_rectangle((left,top,right,bottom),20,fill='#dcecf8',outline=BLUE,width=3)
    center(d,(left+right)/2,250,f'水箱 {i}',31,b=True)
    center(d,(left+right)/2,314,f'体积 {(8,3,2)[i]} L',28)
    center(d,(left+right)/2,389,f'浓度 x{i}(t)',28,c=BLUE,b=True)
arrow(d,(33,355),(202,355)); center(d,110,276,'流入 8',23)
center(d,108,405,'浓度 u(t)',22)
arrow(d,(488,355),(647,355)); center(d,568,285,'6',26)
arrow(d,(933,355),(1092,355)); center(d,1014,285,'6',26)
arrow(d,(1378,355),(1557,355)); center(d,1470,285,'排出 8',23)
center(d,1470,405,'浓度 x2(t)',22)
d.line((345,526,345,652,1235,652,1235,555),fill=BLUE,width=5)
arrow(d,(1235,555),(1235,527))
center(d,790,593,'从水箱0直接流向水箱2：2 L/s',26,c=BLUE)
text(d,80,733,'体积不变：水箱0流入8、流出6+2；水箱1流入流出均6；水箱2均8。',25)
text(d,80,791,'问题：初始浓度均为0，只知道每时每刻 0≤u(t)≤1，出口最多能有多浓？',26,b=True)
text(d,80,872,'水流量固定，不代表污染物质量守恒；污染物随入口进入、随出口排出。',24,c=GRAY)
im.save(O/'three-tanks.png')

def envelope(t):
    return [1-exp(-t),1-2*exp(-t)+exp(-2*t),
            1-(7/3)*exp(-t)+(3/2)*exp(-2*t)-(1/6)*exp(-4*t)]
def vector_field(t,x,u):
    return [-x[0]+u(t),2*(x[0]-x[1]),x[0]+3*x[1]-4*x[2]]
def simulate(u,h=.002,T=2.0):
    x=[0.,0.,0.]; series=[(0.,*x)]
    for n in range(round(T/h)):
        t=n*h
        k1=vector_field(t,x,u)
        k2=vector_field(t+h/2,[v+h*k/2 for v,k in zip(x,k1)],u)
        k3=vector_field(t+h/2,[v+h*k/2 for v,k in zip(x,k2)],u)
        k4=vector_field(t+h,[v+h*k for v,k in zip(x,k3)],u)
        x=[v+h*(a+2*b+2*c+e)/6 for v,a,b,c,e in zip(x,k1,k2,k3,k4)]
        series.append(((n+1)*h,*x))
    return series

profiles=[('平滑波动输入',lambda t:.5+.4*sin(6*t),BLUE),
          ('持续低输入0.2',lambda t:.2,GREEN)]
samples=[(name,simulate(u),color) for name,u,color in profiles]
const=simulate(lambda _:1.)
max_error=max(abs(row[i+1]-envelope(row[0])[i]) for row in const for i in range(3))
assert max_error<1e-8
for _,rows,_ in samples:
    assert min(row[3] for row in rows)>-1e-10
    assert max(row[3]-envelope(row[0])[2] for row in rows)<1e-8
assert F(19,96)<F(1,5)
tstar=log(2); bound=F(19,96)
assert abs(envelope(tstar)[2]-float(bound))<1e-14
im,d=base('不用猜入口曲线：始终输入上限1，得到最坏上包络','紫色是解析上包络；蓝、绿是两条允许输入的数值演示，不是证明。',1000)
gx,gy,w,h=130,740,1310,510
def xy(t,value): return gx+t/2*w,gy-value/.8*h
for value in (0,.2,.4,.6,.8):
    py=xy(0,value)[1]
    d.line((gx,py,gx+w,py),fill='#dfe5ec',width=1)
    text(d,66,py-14,f'{value:.1f}',22,c=GRAY)
for t in (0,.5,1.,1.5,2.):
    px=xy(t,0)[0]
    d.line((px,gy,px,gy+7),fill=GRAY,width=2)
    center(d,px,gy+16,str(t),22,c=GRAY)
d.line((gx,gy,gx+w+15,gy),fill=GRAY,width=2)
d.line((gx,gy,gx,gy-h-15),fill=GRAY,width=2)
text(d,55,197,'出口浓度（以输入上限1归一化）',25)
text(d,1260,801,'时间 t（秒）',24)
d.line([xy(i/500*2,envelope(i/500*2)[2]) for i in range(501)],fill='#7945a6',width=6)
for _,rows,color in samples:
    d.line([xy(row[0],row[3]) for row in rows],fill=color,width=4)
for x,name,c in ((180,'入口1时的出口','#7945a6'),(650,'波动输入下的出口',BLUE),(1070,'入口0.2时的出口',GREEN)):
    d.line((x,164,x+47,164),fill=c,width=5); text(d,x+60,148,name,24,c=c)
px,py=xy(tstar,float(bound))
d.line((px,gy,px,py),fill='#7945a6',width=2)
d.ellipse((px-7,py-7,px+7,py+7),fill='#7945a6')
d.rounded_rectangle((170,270,820,383),12,fill='white',outline='#cfc1dc',width=2)
text(d,192,286,'t=ln 2 ≈0.693秒',25,c='#7945a6',b=True)
text(d,192,330,'所有允许输入：x2(t)≤19/96≈0.198',25,c='#7945a6',b=True)
d.line((800,384,px+8,py-12),fill='#7945a6',width=2)
text(d,60,872,'严格证书针对：固定流量、完全混合、初始全零、给定满足方程的解及点态输入界。',24)
text(d,60,925,'这是理想模型的证明与数值示意，尚未用真实装置的实测数据检验。',23,c=GRAY)
im.save(O/'outlet-envelope.png')

record={'kind':'ideal deterministic model and numerical illustration, not empirical data',
        'volumes_litre':[8,3,2], 'internal_flows_litre_per_second':[[0,1,6],[0,2,2],[1,2,6]],
        'external_inlet_and_outlet_flow':8,'initial_state':[0,0,0],
        'inlet_bounds':[0,1], 'time_point':'log(2)','exact_outlet_bound':'19/96',
        'numerics':{'method':'RK4','step':.002,'end_time':2,'max_unit_step_analytic_error':max_error},
        'profiles':[{'name':name,'rows':rows} for name,rows,_ in samples],
        'image_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.glob('*.png'))}}
(R/'tank-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='profiles'},ensure_ascii=True))
