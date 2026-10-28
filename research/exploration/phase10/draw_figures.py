from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction as Q
import json,hashlib
R=Path(__file__).resolve().parent;F='C:/Windows/Fonts/msyh.ttc';FB='C:/Windows/Fonts/msyhbd.ttc'
font=lambda n,b=False:ImageFont.truetype(FB if b else F,n)
INK='#182735';MUT='#51616e';BLUE='#225a97';GREEN='#227764';BG='#f7f9fc';ORANGE='#a85f14'
def text(d,p,s,n=30,fill=INK,b=False):d.text(p,s,font=font(n,b),fill=fill)
def box(d,r,fill):d.rounded_rectangle(r,18,fill)
im=Image.new('RGB',(1700,1110),BG);d=ImageDraw.Draw(im)
text(d,(60,38),'同一大块 + 少量剩余：控制任意完成时间事件',44,b=True)
text(d,(60,111),'b = 1 + ε，ε > 0；比较 f = 1/2 与 f = 1；四个随机量的原始定义见正文。',28,fill=MUT)
box(d,(60,185,1640,270),'#e9eef5');text(d,(88,207),'以下是总完成时间的等价新表示；原内部绕路概率仍是 1/3 与 1/2。',31,b=True)
for yy,label,right in [(324,'低 f 模型','κ * E1'),(474,'高 f 模型','κ * Eb')]:
 text(d,(60,yy+37),label,31,b=True)
 box(d,(290,yy,1415,yy+112),'#dceafd');box(d,(1415,yy,1640,yy+112),'#dcefe7')
 text(d,(650,yy+17),'共同部分 R',33,BLUE,True);text(d,(690,yy+65),'质量 5/6',28,BLUE)
 text(d,(1440,yy+17),right,33,GREEN,True);text(d,(1440,yy+65),'质量 1/6',28,GREEN)
text(d,(60,636),'E1 与 Eb 又共同包含 ρb：密度 exp(−b t)，t ≥ 0，总质量 1/b。',31,b=True)
text(d,(60,696),'所以两边都包含 γ = R + κ * ρb，质量 c = 5/6 + 1/(6b)。',31,b=True)
box(d,(60,776,1640,1018),'#fff1df')
text(d,(92,801),'ε = 1/100 的精确算例',33,ORANGE,True)
text(d,(92,864),'共同质量：605/606',34,b=True);text(d,(820,864),'各自剩余质量：1/606',34,b=True)
text(d,(92,936),'任何可测时间集合 A：|P高(S ∈ A) − P低(S ∈ A)| ≤ 1/606 ≈ 0.1650 个百分点',29)
text(d,(60,1056),'Er 是速率 r 的指数等待分布；* 表示独立等待相加；κ 质量 1/6。条形按 5/6 与 1/6 绘制。',27,fill=MUT)
im.save(R/'images/common-completion-mass.png')
b=Q(101,100);c=Q(5,6)+1/(6*b);assert c==Q(605,606) and 1-c==Q(1,606)
assert (Q(1,3)+Q(1,6))==Q(1,2)
p=R/'images/common-completion-mass.png'
(R/'figure-data.json').write_text(json.dumps({'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()},'type':'Exact positive-component mass diagram; topbars toscale5/6versus1/6, no samples','parameters':'a=e=1,b=1+eps,eps>0,fLow1/2,fHigh1','example':{'eps':'1/100','b':'101/100','commonmass':'605/606','remainingmass':'1/606','percentagepoints_approx':'0.1650'},'checks':'Exactfractions.Fraction; representation is outputlawonly, not originalroutechoice'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('image generated')
