from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction as Q
import json,hashlib,math
R=Path(__file__).resolve().parent
F='C:/Windows/Fonts/msyh.ttc';FB='C:/Windows/Fonts/msyhbd.ttc'
font=lambda n,b=False:ImageFont.truetype(FB if b else F,n)
INK='#182735';MUT='#51616e';BLUE='#225a97';GREEN='#227764';BG='#f7f9fc';GOLD='#995e14'
def txt(d,p,s,size=30,fill=INK,b=False):d.text(p,s,font=font(size,b),fill=fill)
def rect(d,box,fill,outline=None):d.rounded_rectangle(box,20,fill,outline,3)
def arrow(d,a,b,color=INK,w=4):
 d.line([a,b],fill=color,width=w);v=(b[0]-a[0],b[1]-a[1]);r=math.hypot(*v);u=(v[0]/r,v[1]/r);k=15;d.polygon([b,(b[0]-k*u[0]+k*.5*u[1],b[1]-k*u[1]-k*.5*u[0]),(b[0]-k*u[0]-k*.5*u[1],b[1]-k*u[1]+k*.5*u[0])],fill=color)
im=Image.new('RGB',(1600,980),BG);d=ImageDraw.Draw(im)
txt(d,(64,40),'一个角点，达到每个截止时间的最大完成概率',45,b=True)
txt(d,(64,112),'四个速率各在独立区间内；每次任务中固定。比较 P(S ≤ t)，t ≥ 0。',29,fill=MUT)
rect(d,(64,182,1536,302),'#e9eef5')
txt(d,(96,205),'a ∈ [a_min, A]     b ∈ [b_min, B]     e ∈ [e_min, E]     f ∈ [f_min, F]',31,b=True)
txt(d,(96,262),'min 表示下限；a_min,b_min > 0；e_min,f_min ≥ 0；e_min + f_min > 0。',25,fill=MUT)
rect(d,(64,343,785,855),'#e9f2fc',BLUE);rect(d,(815,343,1536,855),'#e8f5f0',GREEN)
txt(d,(96,368),'B ≥ E：f 取上限',38,BLUE,True)
txt(d,(96,435),'选择 (A, B, E, F)',38,b=True)
txt(d,(96,510),'例 1',30,BLUE,True)
for i,line in enumerate(['a ∈ [1, 2]        b ∈ [1, 3]','e ∈ [1/2, 1]     f ∈ [1/2, 2]','B = 3 > E = 1','最大完成概率角点：(2, 3, 1, 2)']):txt(d,(96,561+52*i),line,29)
txt(d,(96,792),'同一角点适用于全部 t ≥ 0',28,BLUE,True)
txt(d,(847,368),'B < E：f 取下限',38,GREEN,True)
txt(d,(847,435),'选择 (A, B, E, f_min)',38,b=True)
txt(d,(847,510),'例 2',30,GREEN,True)
for i,line in enumerate(['a ∈ [1, 2]        b ∈ [1/2, 1]','e ∈ [1, 3]        f ∈ [1/2, 2]','B = 1 < E = 3','最大完成概率角点：(2, 1, 3, 1/2)']):txt(d,(847,561+52*i),line,29)
txt(d,(847,792),'同一角点适用于全部 t ≥ 0',28,GREEN,True)
txt(d,(64,893),'每个允许组合的完成概率 ≤ 所选角点的完成概率；所选角点本身合法、可以达到。',29,b=True)
txt(d,(64,944),'这是“完成得更快”的比较。B = E 时，所选 A、B、E 下任意允许 f 都给出相同分布。',25,fill=MUT)
im.save(R/'images/rate-box-rule.png')
im=Image.new('RGB',(1600,940),BG);d=ImageDraw.Draw(im)
txt(d,(64,40),'两条路线，四个相互独立的随机量',45,b=True)
txt(d,(64,113),'总等待 S = Wc + Wa + J Wb；指数等待 Exp(k) 的平均时长为 1/k。',30,fill=MUT)
rect(d,(64,235,460,514),'#e9eef5');txt(d,(92,271),'两条路线都先等',30,b=True);txt(d,(92,336),'Wc ~ Exp(e + f)',33,b=True);txt(d,(92,407),'均值 1/(e + f)',29,fill=MUT)
rect(d,(650,211,1536,418),'#e9f2fc',BLUE);txt(d,(682,234),'直达：J = 0，概率 e/(e + f)',31,BLUE,True);txt(d,(682,295),'再等 Wa ~ Exp(a)',33,b=True);txt(d,(682,356),'总等待 Wc + Wa',28)
rect(d,(650,476,1536,708),'#e8f5f0',GREEN);txt(d,(682,499),'绕路：J = 1，概率 f/(e + f)',31,GREEN,True);txt(d,(682,563),'再等 Wb ~ Exp(b)，再等 Wa ~ Exp(a)',31,b=True);txt(d,(682,636),'总等待 Wc + Wb + Wa',28)
arrow(d,(460,342),(650,316),BLUE);arrow(d,(460,438),(650,584),GREEN)
rect(d,(64,766,1536,903),'#fff4e3')
txt(d,(94,791),'增加 f 同时改变等待速度和绕路比例',32,GOLD,True)
txt(d,(94,847),'第一段平均等待 1/(e + f) 变短；绕路概率 f/(e + f) 不减。',30)
im.save(R/'images/two-routes.png')
mean=lambda a,b,e,f:1/a+1/(e+f)+f/((e+f)*b)
assert mean(Q(2),Q(3),Q(1),Q(2))==Q(19,18)
assert mean(Q(2),Q(1),Q(3),Q(1,2))==Q(13,14)
images={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'images').glob('*.png')}
(R/'figure-data.json').write_text(json.dumps({'images':images,'type':'Exact decision diagram and probability-route diagram; no numerical sampling/curve evidence','domain':'a,b>0,e,f>=0,e+f>0; all rates fixed; independent rate intervals','examples':[{'corner':[2,3,1,2],'mean':'19/18'},{'corner':['2','1','3','1/2'],'mean':'13/14'}],'arithmetic_checked_with':'fractions.Fraction'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(images))
