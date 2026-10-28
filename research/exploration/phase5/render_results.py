from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
import math,json,hashlib
R=Path(__file__).resolve().parent
W,H=1600,1040
font='C:/Windows/Fonts/msyh.ttc';bold='C:/Windows/Fonts/msyhbd.ttc'
def F(n,b=False):return ImageFont.truetype(bold if b else font,n)
ink='#183345';blue='#1665ab';orange='#bb5a1d';muted='#53677a';gray='#e5ebf0'
def base(title,sub):
 im=Image.new('RGB',(W,H),'#ffffff');d=ImageDraw.Draw(im)
 d.text((55,30),title,font=F(43,True),fill=ink);d.text((55,99),sub,font=F(24),fill=muted)
 return im,d
def arrow(d,p,q,color=ink,width=5):
 d.line([p,q],fill=color,width=width);a=math.atan2(q[1]-p[1],q[0]-p[0]);l=19
 d.polygon([q,(q[0]-l*math.cos(a-.45),q[1]-l*math.sin(a-.45)),(q[0]-l*math.cos(a+.45),q[1]-l*math.sin(a+.45))],fill=color)
def node(d,box,label,wait,mean):
 d.rounded_rectangle(box,radius=16,fill='#eff6fb',outline=blue,width=3)
 x,y=box[0]+22,box[1]+16
 for txt,sz,weight in [(label,30,True),(wait,25,False),(mean,23,False)]:
  d.text((x,y),txt,font=F(sz,weight),fill=ink);y+=44
im,d=base('一条明确的随机路线，解释三箱响应','所有等待和分支独立；路线沿方程依赖关系逆向构造，不是水滴倒流。')
node(d,(55,300,415,460),'从节点 2 出发','等待 Wc ~ Exp(e+f)','平均等待 1/(e+f)')
node(d,(620,170,980,330),'绕经节点 1','等待 Wb ~ Exp(b)','平均等待 1/b')
node(d,(1185,300,1545,460),'到达节点 0','等待 Wa ~ Exp(a)','平均等待 1/a')
arrow(d,(415,310),(620,250));arrow(d,(980,250),(1185,310))
d.text((415,180),'概率 p = f/(e+f)',font=F(25),fill=ink)
arrow(d,(415,410),(1185,410));d.text((565,435),'概率 1-p = e/(e+f)：直接走',font=F(25),fill=ink)
arrow(d,(1360,460),(1360,570));d.rounded_rectangle((1260,580,1460,642),radius=20,fill='#dfefe4')
d.text((1300,592),'结束',font=F(30,True),fill=ink)
d.text((60,565),'总等待 S = Wc + Wa + J Wb',font=F(34,True),fill=ink)
d.text((60,620),'J=1 时绕路，J=0 时不绕路。预先抽取的 Wb 在直达路线中不使用。',font=F(24),fill=muted)
d.line((55,690,1545,690),fill=gray,width=3)
d.text((55,720),'例：a=1，b=1/2，e=2；只改变 f',font=F(29,True),fill=ink)
d.text((55,775),'f',font=F(24),fill=ink)
for x,txt in [(260,'起点等待'),(565,'绕路对均值的贡献'),(925,'最后等待'),(1260,'平均总等待')]:d.text((x,775),txt,font=F(24),fill=ink)
for y,vals,c in [(835,['1/2','2/5','(1/5) × 2 = 2/5','1','9/5 = 1.8'],blue),(910,['1','1/3','(1/3) × 2 = 2/3','1','2'],orange)]:
 for x,txt in zip([55,260,565,925,1260],vals):d.text((x,y),txt,font=F(28,True),fill=c)
d.text((55,985),'增大 f：起点等得更短，但更容易绕路；两种影响不能只看其中一种。',font=F(25),fill=muted)
im.save(R/'images/waiting-route.png')

def low(t):
 r=math.exp(-t/2);return 1-r*r-r/2+r**5/2
def high(t):
 r=math.exp(-t/2);return 1-r*r/2-4*r/5+3*r**6/10
T=2*math.log(2)
assert abs(low(T)-33/64)<1e-14 and abs(high(T)-307/640)<1e-14
im,d=base('同一条曲线：出口浓度 = 此前已经结束的概率','初始浓度 0，入口恒为 1；a=1，b=1/2，e=2。全时刻等式只展示已核验的两组 f。')
x0,y0,x1,y1=150,290,1500,800
px=lambda t:x0+t/5*(x1-x0)
py=lambda v:y1-v*(y1-y0)
for v in [0,.25,.5,.75,1]:
 y=py(v);d.line((x0,y,x1,y),fill=gray,width=2);d.text((65,y-18),f'{v:g}',font=F(24),fill=muted)
for t in range(6):
 x=px(t);d.line((x,y0,x,y1),fill=gray,width=2);d.text((x-8,y1+18),str(t),font=F(24),fill=muted)
d.text((55,245),'浓度 / 概率',font=F(26,True),fill=ink)
d.text((1290,852),'归一化时间 t',font=F(26),fill=ink)
for fn,c in [(low,blue),(high,orange)]:d.line([(px(i/200),py(fn(i/200))) for i in range(1001)],fill=c,width=5)
x=px(T);d.line((x,y0,x,y1),fill='#8995a0',width=3)
for fn,c in [(low,blue),(high,orange)]:
 y=py(fn(T));d.ellipse((x-8,y-8,x+8,y+8),fill=c)
d.text((260,157),'f = 1/2：F(T) = 33/64 ≈ 0.515625',font=F(29,True),fill=blue)
d.text((260,206),'f = 1：   F(T) = 307/640 ≈ 0.479688',font=F(29,True),fill=orange)
d.text((x0+10,865),'T = 2 ln 2 ≈ 1.3863',font=F(26),fill=ink)
d.text((55,920),'F(t) = P(S ≤ t)。在 T 时，f=1 的结束概率少 23/640，平均总等待反而更长。',font=F(26),fill=ink)
d.text((55,977),'曲线来自已证明的解析式；没有用随机模拟替代概率证明，也没有从均值排序推出曲线排序。',font=F(23),fill=muted)
im.save(R/'images/cdf-response.png')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(R/'figure-data.json').write_text(json.dumps({'method':'Pillow, exact accepted analytic formulas; not Monte Carlo','time_range':[0,5],'normalization':'dimensionless time and concentration','at_T':{'T':'2 log 2','low':'33/64','high':'307/640','difference':'23/640'},'means':{'f_half':'9/5','f_one':'2'},'images':{p.name:sha(p) for p in sorted((R/'images').glob('*.png'))}},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
