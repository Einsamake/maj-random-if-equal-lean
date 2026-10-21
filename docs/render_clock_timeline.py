"""Draw an exact arithmetic teaching example of clipped-gap occupation.
These hand-chosen gaps illustrate an identity; they are not a simulation,
a probability estimate or a claim about recovery-time bounds.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json
from PIL import Image,ImageDraw,ImageFont
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'docs/images'
FONT=Path('C:/Windows/Fonts/msyh.ttc');BOLD=Path('C:/Windows/Fonts/msyhbd.ttc')
if not FONT.exists():
    FONT=BOLD=Path('/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc')
assert FONT.exists()
gaps=[Fraction(6,10),Fraction(11,10),Fraction(9,10)]
arrivals=[];x=Fraction(0)
for g in gaps:x+=g;arrivals.append(x)
t=Fraction(11,5)
lengths=[min(g,max(Fraction(0),t-s)) for g,s in zip(gaps,[Fraction(0),*arrivals[:-1]])]
assert lengths==[Fraction(6,10),Fraction(11,10),Fraction(1,2)]
assert sum(lengths)==t and sum(a<=t for a in arrivals)==2
im=Image.new('RGB',(1280,680),'#f5f7fb');d=ImageDraw.Draw(im)
boxes=[]
def text(x,y,s,n=29,color='#1f2937',bold=False):
    ft=ImageFont.truetype(str(BOLD if bold else FONT),n)
    b=d.textbbox((x,y),s,font=ft);assert 0<=b[0]<b[2]<=1260 and b[3]<=665,(s,b)
    d.text((x,y),s,font=ft,fill=color);boxes.append([s,list(b)])
def X(a):return 100+int(float(a)*390)
text(40,24,'把一段时间切开，就能看清怎样累计响铃',36,bold=True)
text(42,84,'只看一个格点的闹钟。下面是一组人为选定的等待间隔。',27,'#536174')
colors=['#bbd0f4','#b7ded6','#f5d6a5']
starts=[Fraction(0),*arrivals[:-1]]
for i,(s,g) in enumerate(zip(starts,gaps)):
    e=s+g
    d.rectangle((X(s),190,X(min(e,t)),270),fill=colors[i])
    if e>t:
        d.rectangle((X(t),190,X(e),270),fill='#e8ecf2')
        for xx in range(X(t)+8,X(e)-4,16):d.line((xx,194,xx,266),fill='#c3cbd8',width=2)
    if s<t:
        text(X(s)+15,211,['占用 0.6','占用 1.1','占用 0.5'][i],25,bold=True)
for a,label in [(Fraction(0),'0'),*zip(arrivals,['0.6','1.7','2.6'])]:
    d.line((X(a),176,X(a),285),fill='#245dc1',width=3)
    text(X(a)-12,299,label,26,'#245dc1',True)
    if a:
        d.ellipse((X(a)-6,157,X(a)+6,169),fill='#245dc1')
for y in range(150,340,16):d.line((X(t),y,X(t),y+9),fill='#b76009',width=3)
text(X(t)-65,117,'截止：2.2',27,'#b76009',True)
text(295,350,'前两次已响',26,'#245dc1',True)
text(947,350,'这一次还没响',25,'#536174')
d.rounded_rectangle((38,412,1242,520),18,fill='white',outline='#d7dee8',width=2)
text(64,429,'这条样本经过 2.2 单位时间，响了 2 次。',30,bold=True)
text(64,474,'占用时长：0.6 + 1.1 + 0.5 = 2.2',26,'#087f73',True)
text(43,547,'换一组等待间隔，响铃次数会变；占用时长的总和仍是截止时间。',28)
text(43,601,'证明思路：用指数等待的概率规律，把平均占用时长换成平均响铃次数。',27,'#536174')
png=OUT/'09-clock-time.png';im.save(png)
rec={'kind':'hand-chosen exact arithmetic illustration, not a random simulation',
     'gaps':[str(a) for a in gaps],'arrivals':[str(a) for a in arrivals],
     'cutoff':str(t),'occupation_lengths':[str(a) for a in lengths],
     'count_before_cutoff':2,'occupation_sum':str(sum(lengths)),
     'checks':{'rational_partition_identity':True,'all_text_within_canvas':True},
     'figure':{'file':png.name,'bytes':png.stat().st_size,'sha256':hashlib.sha256(png.read_bytes()).hexdigest()},
     'text_boxes':boxes}
(OUT/'clock-time-data.json').write_text(json.dumps(rec,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({k:v for k,v in rec.items() if k!='text_boxes'},ensure_ascii=False))
