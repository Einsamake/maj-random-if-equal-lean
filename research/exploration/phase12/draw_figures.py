from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction as Q
import json,hashlib
R=Path(__file__).resolve().parent;F='C:/Windows/Fonts/msyh.ttc';FB='C:/Windows/Fonts/msyhbd.ttc'
font=lambda n,b=False:ImageFont.truetype(FB if b else F,n)
INK='#182735';MUT='#51616e';BLUE='#225a97';GREEN='#227764';BG='#f7f9fc'
def txt(d,p,s,n=30,fill=INK,b=False):d.text(p,s,font=font(n,b),fill=fill)
def box(d,r,fill):d.rounded_rectangle(r,20,fill)
im=Image.new('RGB',(1800,1160),BG);d=ImageDraw.Draw(im)
txt(d,(60,36),'同样100次任务：观察什么，影响能保证的判断能力',43,b=True)
txt(d,(60,108),'先以各1/2概率选定一个模型，再从同一模型独立重复；完整等待模型见正文。',29,fill=MUT)
box(d,(60,185,1740,285),'#e9eef5');txt(d,(93,207),'两个模型：绕路概率 1/3 与 1/2；共同的绕路等待速率为 101/100。',31,b=True);txt(d,(93,253),'两种方案使用同一组原始随机任务，只改变实际交给判断规则的观测量。',24,fill=MUT)
box(d,(60,331,885,565),'#e9f2fc');box(d,(915,331,1740,565),'#e8f5f0')
txt(d,(92,356),'只看总完成时间 S1, …, S100',33,BLUE,True);txt(d,(92,423),'任何由样本决定结果的可测二选一规则',29);txt(d,(92,490),'成功率 ≤ 353/606 ≈ 58.25%',34,BLUE,True)
txt(d,(947,356),'直接看是否绕路 J1, …, J100',33,GREEN,True);txt(d,(947,423),'绕路比例 ≥ 5/12 判高模型，否则判低',29);txt(d,(947,490),'成功率 ≥ 33/50 = 66%',34,GREEN,True)
x=300;w=1250;y1=688;y2=819
for v in [0,.5,1]:
 xx=x+w*v;d.line((xx,637,xx,915),fill='#d1dbe4',width=2);txt(d,(xx-22,931),f'{v*100:.0f}%',24,fill=MUT)
txt(d,(60,y1+5),'时间规则上界',29,BLUE,True);txt(d,(60,y2+5),'分支规则保证',29,GREEN,True)
d.rounded_rectangle((x,y1,x+w*float(Q(353,606)),y1+49),8,BLUE)
d.rounded_rectangle((x+w*float(Q(33,50)),y2,x+w,y2+49),8,GREEN)
txt(d,(x+w*float(Q(353,606))+15,y1),'≤约58.25%',27,BLUE,True);txt(d,(x+w*float(Q(33,50))-175,y2),'至少66% →',27,GREEN,True)
box(d,(60,1000,1740,1102),'#fff1df');txt(d,(92,1018),'严格保证的成功率差：至少 587/7575，约7.75个百分点。',32,b=True);txt(d,(92,1067),'图示是上界与下界，不是实验准确率；阈值未声称最优，记录内部标记的成本未建模。',24,fill=MUT)
im.save(R/'images/observation-choice.png')
gap=Q(33,50)-Q(353,606);assert gap==Q(587,7575) and gap>0
assert (Q(32,100)+Q(36,100))/2==Q(17,50)
assert 1-Q(17,50)==Q(33,50)
p=R/'images/observation-choice.png';(R/'figure-data.json').write_text(json.dumps({'images':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()},'type':'Exact guarantee comparison on common0-100percent axes, upper/lower bounds not measuredaccuracy','actualexperiment':'Same original jointIID, fairmodelchoice once,100tasks,lowf1/2 highf1,b101/100','branch_rule':'Real count>=5*n/12, n100','exact_values':{'time_success_upper':'353/606','specified_branch_success_lower':'33/50','guaranteed_advantage':'587/7575','low_error_upper_n100':'8/25','high_error_upper_n100':'9/25','equal_prior_error_upper':'17/50'},'checks':'Exactfractions.Fraction; percentagesillustrative'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('image generated')
