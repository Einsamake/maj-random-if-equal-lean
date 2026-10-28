from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction as Q
import math,json,hashlib
R=Path(__file__).resolve().parent;F='C:/Windows/Fonts/msyh.ttc';FB='C:/Windows/Fonts/msyhbd.ttc'
font=lambda n,b=False:ImageFont.truetype(FB if b else F,n)
INK='#182735';MUT='#51616e';BLUE='#225a97';GREEN='#227764';BG='#f7f9fc';GOLD='#985b14'
def text(d,p,s,n=30,fill=INK,b=False):d.text(p,s,font=font(n,b),fill=fill)
def box(d,r,fill):d.rounded_rectangle(r,20,fill)
def arrow(d,a,b,col=INK):
 d.line((a,b),fill=col,width=4);x=b[0]-a[0];y=b[1]-a[1];z=math.hypot(x,y);x/=z;y/=z;k=15;d.polygon([b,(b[0]-k*x+7*y,b[1]-k*y-7*x),(b[0]-k*x-7*y,b[1]-k*y+7*x)],fill=col)
im=Image.new('RGB',(1800,1160),BG);d=ImageDraw.Draw(im)
text(d,(60,35),'看100次完成时间，任何规则的成功率仍有上界',45,b=True)
text(d,(60,111),'本例：ε = 1/100；低模型 f = 1/2，高模型 f = 1；只观测总完成时间 S。',30,fill=MUT)
text(d,(60,189),'① 只选一次模型，各以 1/2 概率',30,b=True)
box(d,(60,258,535,365),'#dceafd');box(d,(60,419,535,526),'#dcefe7')
text(d,(91,276),'低模型：绕路概率 1/3',31,BLUE,True);text(d,(91,326),'后续100次都用这个模型',25,BLUE)
text(d,(91,437),'高模型：绕路概率 1/2',31,GREEN,True);text(d,(91,487),'后续100次都用这个模型',25,GREEN)
box(d,(655,258,1165,526),'#e9eef5');text(d,(687,283),'② 给定模型，独立重复',29,b=True);text(d,(687,345),'X = (S1, S2, …, S100)',33,b=True);text(d,(687,415),'保留全部原始完成时间',28);text(d,(687,469),'不重新抛硬币选模型',27,fill=MUT)
box(d,(1290,258,1740,526),'#fff1df');text(d,(1322,283),'③ 看完样本作二选一',28,GOLD,True);text(d,(1322,345),'X ∈ A：判高',31,b=True);text(d,(1322,403),'否则：判低',31,b=True);text(d,(1322,469),'任意可测样本集合 A',25,fill=MUT)
arrow(d,(535,312),(655,350),BLUE);arrow(d,(535,473),(655,435),GREEN);arrow(d,(1165,392),(1290,392))
box(d,(60,594,1740,1060),'#e9eef5')
text(d,(92,620),'所有这样的规则，都满足平均成功率 ≤ 353/606 ≈ 58.25%',36,b=True)
text(d,(92,685),'平均：高、低模型各占一半；这是证明给出的上界，不是已达到的算法成绩。',28,fill=MUT)
x=360;w=1210
for v in [0,.5,1]:
 xx=x+v*w;d.line((xx,758,xx,974),fill='#c1cdd8',width=2);text(d,(xx-24,984),f'{v*100:.0f}%',25,fill=MUT)
text(d,(92,775),'总是判低',29);text(d,(92,877),'经证明的上界',29,b=True)
d.rounded_rectangle((x,777,x+w/2,825),10,BLUE)
d.rounded_rectangle((x,879,x+w*float(Q(353,606)),927),10,GREEN)
text(d,(x+w/2+16,777),'50%',29,BLUE,True);text(d,(x+w*float(Q(353,606))+16,879),'约58.25%',29,GREEN,True)
text(d,(60,1094),'两个内部机制仍有固定差异；结论只针对这两个模型、独立完成时间观测、等先验和上述二选一规则。',27,fill=MUT)
im.save(R/'images/testing-experiment.png')
c=Q(605,606);delta=1-c;n=100;loose=Q(1,2)+n*delta/2;err=Q(1,2)-n*delta/2
assert loose==Q(353,606) and err==Q(253,606) and loose+err==1
assert Q(1,1)-c**n/2<=loose
p=R/'images/testing-experiment.png';(R/'figure-data.json').write_text(json.dumps({'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()},'type':'Exact rational experiment diagram and upper-bound bars; no empiricalaccuracy/algorithmexperiment','model_choice':'Onefairchoice, then100IID tasks conditionalonfixedselectedmodel','example':{'eps':'1/100','c':'605/606','delta':'1/606','n':100,'linear_success_upper':'353/606','linear_error_lower':'253/606','success_decimal':float(loose),'sharp_success_upper_expression':'1-(605/606)^100/2','sharp_success_upper_illustrative_decimal':float(1-c**n/2)},'checks':'Exactfractions.Fraction, power100computedexactly; displaydecimalsillustrative'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('image generated')
