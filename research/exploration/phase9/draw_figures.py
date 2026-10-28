from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction as Q
import json,hashlib
R=Path(__file__).resolve().parent;F='C:/Windows/Fonts/msyh.ttc';FB='C:/Windows/Fonts/msyhbd.ttc'
font=lambda n,b=False:ImageFont.truetype(FB if b else F,n)
INK='#182735';MUT='#51616e';BLUE='#225a97';GREEN='#227764';BG='#f7f9fc'
def text(d,p,s,n=30,fill=INK,b=False):d.text(p,s,font=font(n,b),fill=fill)
def box(d,r,fill):d.rounded_rectangle(r,22,fill)
im=Image.new('RGB',(1680,1090),BG);d=ImageDraw.Draw(im)
text(d,(64,37),'内部路线差固定，所有截止时间的概率差上界却能缩小',42,b=True)
text(d,(64,112),'a = e = 1，b = 1 + ε，ε > 0；比较固定 f = 1/2 与 f = 1 的两个模型。',30,fill=MUT)
box(d,(64,185,1616,294),'#e9eef5')
text(d,(94,207),'总完成时间 S = Wc + Wa + J Wb；四个随机量相互独立。',32,b=True)
text(d,(94,256),'Wa ~ Exp(1)，Wb ~ Exp(1 + ε)，Wc ~ Exp(1 + f)，P(J = 1) = f/(1 + f)。',27,fill=MUT)
box(d,(64,334,798,878),'#e9f2fc');box(d,(828,334,1616,878),'#e8f5f0')
text(d,(96,361),'内部观测：是否绕路？',34,BLUE,True)
text(d,(96,414),'绕路概率与 ε 无关',29,fill=MUT)
x0,x1=200,730;y=685;w=x1-x0
for v in [0,.5,1]:
 x=x0+v*w;d.line((x,494,x,718),fill='#c4d2e1',width=2);text(d,(x-15,732),str(v).rstrip('0').rstrip('.') if v else '0',23,fill=MUT)
text(d,(98,516),'f = 1/2',27);text(d,(98,611),'f = 1',27)
d.rounded_rectangle((x0,516,x0+w/3,563),9,BLUE);d.rounded_rectangle((x0,611,x0+w/2,658),9,GREEN)
text(d,(x0+w/3+15,516),'1/3',29,BLUE,True);text(d,(x0+w/2+15,611),'1/2',29,GREEN,True)
text(d,(98,804),'差一直是 1/6 ≈ 16.67 个百分点',29,b=True)
text(d,(860,361),'外部观测：是否在 t 之前完成？',33,GREEN,True)
text(d,(860,414),'每一个实数 t，都有 0 ≤ FH(t) − FL(t) ≤ ε/6',27,fill=MUT)
text(d,(875,492),'ε',30,b=True);text(d,(1080,492),'全时间概率差上界',29,b=True)
for i,(ep,bound) in enumerate([(Q(1,10),Q(1,60)),(Q(1,100),Q(1,600)),(Q(1,1000),Q(1,6000))]):
 yy=557+i*83;text(d,(875,yy),str(ep),32);text(d,(1080,yy),str(bound),32,b=True);text(d,(1260,yy),f'≈ {float(bound):.6f}',27,fill=MUT)
text(d,(860,804),'ε = 1/100 时，最多约 0.1667 个百分点',27,b=True)
text(d,(64,928),'FH、FL 是两个模型总等待 S 的分布函数：F(t) = P(S ≤ t)。',30,b=True)
text(d,(64,987),'右侧是证明给出的上界，不是测得的实际差；不等于任意复杂事件接近或有限样本无法区分。',27,fill=MUT)
text(d,(64,1036),'缩小 ε 会改变两个模型共同的已知速率 b；每一对模型只改变 f。',27,fill=MUT)
im.save(R/'images/hidden-route-vs-deadline.png')
assert (Q(1,2)-Q(1,3))==Q(1,6)
assert Q(1,100)/6==Q(1,600)
assert Q(1,600)*100==Q(1,6)
p=R/'images/hidden-route-vs-deadline.png'
(R/'figure-data.json').write_text(json.dumps({'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()},'type':'Exact rational illustrative table and exact branch-probability bars, no simulations','parameters':'a=e=1,b=1+eps,eps>0,fLow=1/2,fHigh=1','branch_probabilities':['1/3','1/2'],'branch_difference':'1/6','all_real_deadline_bound':'eps/6','rational_rows':[['1/10','1/60'],['1/100','1/600'],['1/1000','1/6000']],'probability_to_percentage_points':'(1/600)*100=1/6≈0.1667','checks':'fractions.Fraction exact'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('image generated')
