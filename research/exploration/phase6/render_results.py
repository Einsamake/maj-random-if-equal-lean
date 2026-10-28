from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction
import json,math,hashlib
R=Path(__file__).resolve().parent;W,H=1800,1120
font='C:/Windows/Fonts/msyh.ttc';bold='C:/Windows/Fonts/msyhbd.ttc'
def F(n,b=False):return ImageFont.truetype(bold if b else font,n)
ink='#173445';muted='#52687a';blue='#1768ad';orange='#ba591c';gray='#e3ebf0'
def base(title,sub):
 im=Image.new('RGB',(W,H),'white');d=ImageDraw.Draw(im)
 d.text((55,32),title,font=F(43,True),fill=ink);d.text((55,100),sub,font=F(25),fill=muted)
 return im,d

def solve(b,e,f,n=10000,T=5):
 dt=T/n;x=(0.,0.,0.);out=[x[2]]
 def V(x):return (1-x[0],b*(x[0]-x[1]),e*(x[0]-x[2])+f*(x[1]-x[2]))
 def plus(x,k,c):return tuple(x[i]+c*k[i] for i in range(3))
 for j in range(n):
  k1=V(x);k2=V(plus(x,k1,dt/2));k3=V(plus(x,k2,dt/2));k4=V(plus(x,k3,dt))
  x=tuple(x[i]+dt*(k1[i]+2*k2[i]+2*k3[i]+k4[i])/6 for i in range(3));out.append(x[2])
 return out
cases=[('b > e：偏向绕路更有利',2,1,'b=2 > e=1','增强 f：完成概率不下降','11/6 → 7/4'),('b < e：偏向直达更有利',.5,2,'b=1/2 < e=2','增强 f：完成概率不上升','9/5 → 2'),('b = e：两种支路速率相等',1,1,'b=e=1','增强 f：整条曲线不变','2 → 2')]
curves={};checks={}
for title,b,e,tag,rule,mean in cases:
 rows=[]
 for f in [.5,1]:
  fine=solve(b,e,f);coarse=solve(b,e,f,5000)
  err=max(abs(coarse[i]-fine[2*i]) for i in range(5001));assert err<1e-10
  assert all(-1e-12<=v<=1+1e-12 for v in fine)
  rows.append(fine);checks[str((b,e,f))]=err
 curves[(b,e)]=rows
 if b>e:assert min(y-x for x,y in zip(*rows))>=-1e-12
 if b<e:assert max(y-x for x,y in zip(*rows))<=1e-12
 if b==e:
  assert max(abs(x-y) for x,y in zip(*rows))<1e-12
  assert max(abs(v-(1-(1+5*i/10000)*math.exp(-5*i/10000))) for i,v in enumerate(rows[0]))<1e-11
im,d=base('连接变快，整体何时更快、何时更慢？','初态 0，入口恒为 1；a=1，蓝色 f=1/2，橙色 f=1。纵轴都是截止前完成概率 F(t)。')
d.text((55,145),'e 是直达支路的竞争速率；当 e>0 时，即使已知走直达，起点等待仍是 Exp(e+f)。',font=F(23),fill=muted)
for j,(title,b,e,tag,rule,mean) in enumerate(cases):
 left=65+j*590;x0=left+55;x1=left+515;y0=290;y1=745
 d.text((left,195),title,font=F(32,True),fill=ink);d.text((left,245),tag,font=F(28),fill=muted)
 px=lambda t:x0+t/5*(x1-x0);py=lambda v:y1-v*(y1-y0)
 for v in [0,.5,1]:
  y=py(v);d.line((x0,y,x1,y),fill=gray,width=2);d.text((left+1,y-16),f'{v:g}',font=F(22),fill=muted)
 for t in [0,2.5,5]:
  x=px(t);d.line((x,y0,x,y1),fill=gray,width=2);d.text((x-10,y1+12),f'{t:g}',font=F(22),fill=muted)
 rows=curves[(b,e)]
 for k,c in [(0,blue),(1,orange)]:
  points=[(px(5*i/10000),py(rows[k][i])) for i in range(0,10001,10)]
  if b==e and k==1:
   for m in range(0,len(points)-8,16):d.line(points[m:m+8],fill=c,width=5)
  else:d.line(points,fill=c,width=5)
 d.text((left,820),rule,font=F(29,True),fill=ink)
 d.text((left,885),'平均总等待：'+mean,font=F(28),fill=muted)
 d.text((x1-110,785),'时间 t',font=F(23),fill=muted)
d.text((55,975),'规则对每个截止时间都成立；它来自实际概率与保号积分的证明，不能只凭均值判断。',font=F(27),fill=ink)
d.text((55,1040),'曲线为 ODE 的 RK4 数值示意，已作步长减半检查；数学结论另由标准 Lean 内核验证。',font=F(24),fill=muted)
im.save(R/'images/rate-order.png')

im,d=base('完成时间一样，内部路线可以很不一样','固定 a=b=e=1；总等待的整个分布相同，但绕路概率从 1/3 变成 1/2。')
for x,tag,p,wait,c in [(65,'f=1/2','1/3','2/3',blue),(940,'f=1','1/2','1/2',orange)]:
 d.rounded_rectangle((x,175,x+790,680),radius=20,fill='#f5f8fa',outline=c,width=3)
 d.text((x+30,205),tag,font=F(35,True),fill=c)
 d.text((x+30,280),'起点平均等待：'+wait,font=F(28),fill=ink)
 d.text((x+30,345),'绕经节点 1 的概率：'+p,font=F(28,True),fill=c)
 d.text((x+30,410),'绕路后平均多等：1',font=F(28),fill=ink)
 d.text((x+30,475),'最后平均等待：1',font=F(28),fill=ink)
 d.text((x+30,550),'平均总等待：'+wait+' + '+p+' × 1 + 1 = 2',font=F(27),fill=ink)
 d.text((x+30,610),'不只是均值相同：整个完成时间分布相同。',font=F(24),fill=muted)
d.text((80,735),'若只记录每次完成用了多久，观测到的分布无法区分这两种隐藏路线。',font=F(34,True),fill=ink)
d.text((80,805),'若还能记录是否绕路，两组概率分别是 1/3 与 1/2，便有可区分的统计信息。',font=F(30),fill=ink)
d.line((65,890,1730,890),fill=gray,width=3)
d.text((80,930),'相同的是输出 S 的分布；四个内部随机量的联合分布并不相同。',font=F(29),fill=muted)
d.text((80,1005),'这里展示一个具体的参数不可辨识例子；没有声称所有网络都不可辨识。',font=F(27),fill=muted)
im.save(R/'images/hidden-branch.png')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(R/'figure-data.json').write_text(json.dumps({'method':'Deterministic RK4 numerical illustration, exact rational means and branch probabilities; proofs separate.','RK4_fine_steps':10000,'RK4_coarse_steps':5000,'max_halving_discrepancy':max(checks.values()),'normalization':'dimensionless time, concentration and probability','means':{'b2_e1':['11/6','7/4'],'bhalf_e2':['9/5','2'],'b1_e1':['2','2']},'branch_probabilities':['1/3','1/2'],'images':{p.name:sha(p) for p in sorted((R/'images').glob('*.png'))}},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
