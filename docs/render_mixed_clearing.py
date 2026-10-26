"""Draw the proved auxiliary local-clearing statement, without simulated data."""
from pathlib import Path
import json,hashlib
from PIL import Image,ImageDraw,ImageFont
root=Path(__file__).resolve().parents[1]
out=root/'docs/images/07-local-clearing.png'
im=Image.new('RGB',(1600,1030),'#f7f9fc');d=ImageDraw.Draw(im)
regular='C:/Windows/Fonts/msyh.ttc';bold='C:/Windows/Fonts/msyhbd.ttc'
def font(n,b=False):return ImageFont.truetype(bold if b else regular,n)
def text(x,y,s,n=25,color='#27364b',b=False):d.text((x,y),s,font=font(n,b),fill=color)
text(55,32,'上界证明：从辅助区域清空，接回原同步模型',42,b=True)
text(57,95,'这是一条已通过 Lean 核验的推理链；方格图是结构示意，不是模拟结果。',25)
d.rounded_rectangle((45,160,690,965),radius=20,fill='white',outline='#d8e1ec',width=2)
d.rounded_rectangle((725,160,1555,965),radius=20,fill='white',outline='#d8e1ec',width=2)
text(75,185,'1  先看一个更大的辅助方块',29,b=True)
text(75,238,'边长 8N+1；只要求左下 N×N 区域变白。',24)
x0,y0,size=107,338,500
# A drawn domain, not a sampled spin configuration.
d.rectangle((x0,y0,x0+size,y0+size),fill='#e9edf3',outline='#697b91',width=2)
for k in range(1,129):
 q=round(size*k/129)
 d.line((x0+q,y0,x0+q,y0+size),fill='#dde3ec',width=1)
 d.line((x0,y0+q,x0+size,y0+q),fill='#dde3ec',width=1)
target=size*16/129
# southwest target coordinates, y increasing upward
r=(x0,y0+size-target,x0+target,y0+size)
d.rectangle(r,fill='#dceeff',outline='#176cc0',width=4)
d.line((x0-10,y0,x0-10,y0+size),fill='#bec8d5',width=9)
d.line((x0,y0+size+10,x0+size,y0+size+10),fill='#bec8d5',width=9)
d.line((x0,y0-10,x0+size,y0-10),fill='#263343',width=9)
d.line((x0+size+10,y0,x0+size+10,y0+size),fill='#263343',width=9)
text(x0+135,y0-55,'固定黑色边界',23)
text(x0+122,y0+size+25,'固定白色边界',23)
d.line((x0+target+5,y0+size-target/2,x0+230,y0+size-95),fill='#176cc0',width=3)
text(x0+230,y0+size-125,'目标：N×N',24,'#176cc0',True)
text(76,920,'按 N=16 绘制；灰色表示未指定的区域。',22)
text(760,190,'2  到平方量级的时间，目标有较大概率全白',28,b=True)
text(765,257,'辅助时钟时刻 t = 16(8N+1)²  ≤  1296N²',26,'#1f587c',True)
text(765,312,'粒子的平均分布逐渐接近均匀。',26)
text(765,362,'右半边的平均粒子数足够多，波动也受控。',25)
d.rounded_rectangle((765,424,1510,540),radius=15,fill='#e7f3e8')
text(790,443,'N ≥ 16 时：目标区域全白的概率 ≥ 7/8。',29,'#245a2b',True)
text(790,493,'辅助过程用独立随机时钟，一格一格更新。',23,'#245a2b')
text(765,593,'3  接回原同步模型，再反复重启',28,b=True)
text(765,645,'同一组随机事件下，小方块的时钟过程',23)
text(765,682,'不比辅助区域更黑。',23)
text(765,727,'换算成同步轮数后，j 个时段的存活概率 ≤ 2^(-j)。',22)
text(765,770,'尾概率相加，给出原同步平均恢复时间上界。',23)
d.rounded_rectangle((765,815,1510,889),radius=12,fill='#fff1df')
text(789,833,'原同步平均恢复时间 ≤ 664066N²（N≥16）',25,'#955b13',True)
out.parent.mkdir(parents=True,exist_ok=True);im.save(out)
record={'kind':'drawn theorem illustration, not simulation','example_N':16,'auxiliary_side':129,'target_side':16,'time':'16(8N+1)^2 <= 1296N^2 for N>=1','probability':'auxiliary mixed local-clear failure <= 1/8 for N>=16','original_quadratic_upper_complete':True,'image_sha256':hashlib.sha256(out.read_bytes()).hexdigest()}
(root/'docs/images/local-clearing-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf8')
print(out)
