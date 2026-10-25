"""Draw a deterministic legal mixed-boundary path and its exact row encoding.
This is a teaching diagram, not a random trajectory or probability estimate.
"""
from pathlib import Path
import json,hashlib
from PIL import Image,ImageDraw,ImageFont
R=Path(__file__).resolve().parents[1];O=R/'docs/images'
M=5;positions=[list(range(M)),[0,1,2,3,5],[0,1,2,4,6]]
fonts=Path('C:/Windows/Fonts/msyh.ttc');bold=Path('C:/Windows/Fonts/msyhbd.ttc')
def f(n,b=False):return ImageFont.truetype(str(bold if b else fonts),n)
im=Image.new('RGB',(1280,730),'#f5f7fb');d=ImageDraw.Draw(im)
def text(x,y,s,n=25,c='#263342',b=False):d.text((x,y),s,font=f(n,b),fill=c)
def centered(cx,y,s,n=25,c='#263342',b=False):
 box=d.textbbox((0,0),s,font=f(n,b));text(cx-(box[2]-box[0])/2,y,s,n,c,b)
text(42,24,'辅助证明：把阶梯边界变成一维粒子',36,b=True)
text(42,82,'上：混合边界方框中的黑白格子。下：边界的粒子编码。',25)
text(42,120,'南、西外边界固定白色；北、东外边界固定黑色。每次只更新一个角点。',23,c='#536174')
rows=[]
for panel,(pos,title) in enumerate(zip(positions,['初始全黑','一个角点变白','再有两个角点变白'])):
 x=32+panel*416;cx=x+196
 d.rounded_rectangle((x,175,x+392,622),16,fill='white',outline='#d7dee8',width=2)
 centered(cx,193,title,27,b=True)
 lengths=[0]*M
 for label,slot in enumerate(pos):lengths[M-1-label]=slot-label
 assert all(0<=v<=M for v in lengths) and all(lengths[i]>=lengths[i+1] for i in range(M-1))
 rows.append(lengths)
 cell=45;gx=cx-112;gy=248
 # Border bands explicitly show the two fixed exterior colours.
 d.rectangle((gx-10,gy-10,gx+M*cell+10,gy+M*cell+10),fill='white',outline='#bcc7d5')
 d.rectangle((gx,gy-10,gx+M*cell+10,gy-1),fill='#263342')
 d.rectangle((gx+M*cell,gy-10,gx+M*cell+10,gy+M*cell),fill='#263342')
 for y in range(M):
  for xx in range(M):
   yy=M-1-y
   d.rectangle((gx+xx*cell,gy+yy*cell,gx+(xx+1)*cell,gy+(yy+1)*cell),fill='white' if xx<lengths[y] else '#263342',outline='#d7dee8',width=1)
 centered(cx,492,'对应的 5 个粒子',22,c='#245dc1')
 base=x+39;spacing=34
 d.line((base,548,base+9*spacing,548),fill='#b9c6d8',width=3)
 for slot in range(2*M):
  px=base+slot*spacing
  d.ellipse((px-10,538,px+10,558),fill='#245dc1' if slot in pos else 'white',outline='#245dc1' if slot in pos else '#a9b6c8',width=2)
  centered(px,570,str(slot),18,c='#667589')
text(42,644,'黑格数在变化，编码粒子数始终是 5；粒子不是黑格本身。',25,b=True)
text(42,685,'这是一种合法更新顺序的示意，没有指定等待时间，也不代表平均恢复速度。',22,c='#536174')
# The last panel differs from the first by three genuine single-cell corner deletions.
assert rows==[[0,0,0,0,0],[1,0,0,0,0],[2,1,0,0,0]]
im.save(O/'06-particle-encoding.png')
record={'kind':'deterministic legal path illustration, no random waiting times','side':M,'particle_positions':positions,'row_white_lengths_bottom_up':rows,'legal_adjacent_hops':[[4,5],[3,4],[5,6]],'source':'docs/render_particle_encoding.py','png_sha256':hashlib.sha256((O/'06-particle-encoding.png').read_bytes()).hexdigest()}
(O/'particle-encoding-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf8')
print('rendered particle encoding teaching diagram')
