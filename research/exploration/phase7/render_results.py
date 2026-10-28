from pathlib import Path
from PIL import Image,ImageDraw,ImageFont
from fractions import Fraction
import json,hashlib
R=Path(__file__).resolve().parent;W,H=1800,1100
font='C:/Windows/Fonts/msyh.ttc';bold='C:/Windows/Fonts/msyhbd.ttc'
def F(n,b=False):return ImageFont.truetype(bold if b else font,n)
ink='#173445';muted='#53697b';blue='#1768ad';orange='#ba591c';gray='#80909c'
im=Image.new('RGB',(W,H),'white');d=ImageDraw.Draw(im)
d.text((55,35),'能算回隐藏参数，也可能放大均值误差',font=F(44,True),fill=ink)
d.text((55,106),'前提：a、b、e 已知；m 是总等待 S 的真实总体均值。此图不提供有限样本估计保证。',font=F(25),fill=muted)
x0,y0,x1,y1=130,295,890,800
px=lambda f:x0+f/2*(x1-x0);py=lambda m:y1-(m-1.6)/.42*(y1-y0)
def mean(b,f):return 1+(b+f)/(b*(1+f))
for m in [1.6,1.8,2]:
 y=py(m);d.line((x0,y,x1,y),fill='#e3ebf0',width=2);d.text((60,y-18),f'{m:g}',font=F(24),fill=muted)
for f in [0,.5,1,1.5,2]:
 x=px(f);d.line((x,y0,x,y1),fill='#e3ebf0',width=2);d.text((x-10,y1+15),f'{f:g}',font=F(24),fill=muted)
d.text((55,180),'a=e=1；只改变 f',font=F(30,True),fill=ink)
d.text((55,245),'总体均值 m',font=F(25),fill=ink)
for b,c in [(1,gray),(1.01,blue),(2,orange)]:
 pts=[(px(i/400),py(mean(b,i/400))) for i in range(801)]
 if b==1:
  for j in range(0,len(pts)-5,10):d.line(pts[j:j+5],fill=c,width=4)
 else:d.line(pts,fill=c,width=5)
for y,txt,c in [(895,'b=e=1：整条均值曲线平坦',gray),(945,'b=1.01：唯一可恢复，但曲线很平',blue),(995,'b=2：均值变化更明显',orange)]:d.text((65,y),txt,font=F(27),fill=c)
d.text((760,848),'隐藏参数 f',font=F(25),fill=ink)
d.rounded_rectangle((1000,180,1740,850),radius=18,fill='#f2f7fb',outline=blue,width=3)
d.text((1030,210),'精确比较：a=e=1，b=101/100',font=F(29,True),fill=ink)
for y,fv,mv in [(310,'f = 1/2','m = 605/303 ≈ 1.996700'),(420,'f = 1','m = 403/202 ≈ 1.995050')]:
 d.text((1040,y),fv,font=F(32,True),fill=blue);d.text((1040,y+49),mv,font=F(28),fill=ink)
d.line((1030,550,1710,550),fill='#cddce7',width=3)
d.text((1040,580),'参数相差：1/2',font=F(31,True),fill=ink)
d.text((1040,640),'均值只差：1/606 ≈ 0.001650',font=F(29),fill=ink)
d.text((1040,710),'两者差值的比：303',font=F(33,True),fill=orange)
d.text((1030,785),'同一组已知速率下，不能忽略这种敏感性。',font=F(24),fill=muted)
d.text((1030,910),'b=e 时：不是误差放大，而是输出分布本就相同。',font=F(23),fill=muted)
d.text((55,1060),'曲线直接计算已证均值公式；没有从均值相近推断整个完成时间分布相近。',font=F(24),fill=muted)
im.save(R/'images/mean-recovery.png')
b=Fraction(101,100);mlo=1+(b+Fraction(1,2))/(b*Fraction(3,2));mhi=1+(b+1)/(b*2)
assert mlo==Fraction(605,303) and mhi==Fraction(403,202) and mlo-mhi==Fraction(1,606)
assert Fraction(1,2)/(mlo-mhi)==303
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(R/'figure-data.json').write_text(json.dumps({'method':'Direct evaluation of exact mean formula, not sampled data','known_a_e':1,'near_b':'101/100','f_pair':['1/2','1'],'population_means':[str(mlo),str(mhi)],'mean_gap':str(mlo-mhi),'finite_difference_ratio':303,'finite_sample_guarantee':False,'CDF_distance_inference':False,'images':{'mean-recovery.png':sha(R/'images/mean-recovery.png')}},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
