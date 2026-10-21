"""Draw the README's original-model demonstrations; no proof-source changes.
Run from any directory with Python, NumPy and Pillow. Reproducible coin fields
and all states are saved, and every parallel step is independently checked.
"""
from pathlib import Path
import json, hashlib, math
import numpy as np
from PIL import Image, ImageDraw, ImageFont
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'docs/images'
OUT.mkdir(parents=True,exist_ok=True)
FONT=Path('C:/Windows/Fonts/msyh.ttc')
BOLD=Path('C:/Windows/Fonts/msyhbd.ttc')
if not FONT.exists():
    for p in [Path('/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc'),Path('/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc')]:
        if p.exists(): FONT=BOLD=p;break
assert FONT.exists(),'Set FONT to an installed CJK font.'
BG='#f5f7fb';INK='#1f2937';MUTED='#536174';BLUE='#245dc1';TEAL='#087f73';AMBER='#b76009';LINE='#d7dee8';BLACK='#252b35'
def font(n=30,bold=False):return ImageFont.truetype(str(BOLD if bold else FONT),n)
def canvas(h):return Image.new('RGB',(1280,h),BG)
def text(d,xy,s,n=30,fill=INK,bold=False):d.text(xy,s,font=font(n,bold),fill=fill)
def center(d,x,y,s,n=30,fill=INK,bold=False):
    box=d.textbbox((0,0),s,font=font(n,bold));text(d,(int(x-(box[2]-box[0])/2),y),s,n,fill,bold)
def card(d,box,fill='white',outline=LINE):d.rounded_rectangle(box,18,fill=fill,outline=outline,width=2)
def arrow(d,a,b,color=BLUE,width=4):
    d.line([a,b],fill=color,width=width);theta=math.atan2(b[1]-a[1],b[0]-a[0]);size=13
    d.polygon([b,(b[0]-size*math.cos(theta-.5),b[1]-size*math.sin(theta-.5)),(b[0]-size*math.cos(theta+.5),b[1]-size*math.sin(theta+.5))],fill=color)
def board(d,a,x,y,cell=30,birth=None):
    for i in range(a.shape[0]):
        for j in range(a.shape[1]):
            box=(x+j*cell,y+i*cell,x+(j+1)*cell,y+(i+1)*cell)
            d.rectangle(box,fill=BLACK if a[i,j] else 'white',outline=LINE,width=1)
            if birth is not None and birth[i,j]:
                d.rectangle((box[0]+2,box[1]+2,box[2]-2,box[3]-2),outline='#ef8c27',width=3)
    d.rectangle((x,y,x+a.shape[1]*cell,y+a.shape[0]*cell),outline='#9ba8ba',width=2)
def save(im,name):im.save(OUT/name)
def counts(a):
    p=np.pad(a,1)
    return p[:-2,1:-1]+p[2:,1:-1]+p[1:-1,:-2]+p[1:-1,2:]
def parallel_step(a,coins):
    k=counts(a);return ((k>2)|((k==2)&(coins==1))).astype(np.uint8)
def scalar_step(a,coins):
    b=np.zeros_like(a)
    for i in range(a.shape[0]):
        for j in range(a.shape[1]):
            k=sum(int(a[u,v]) for u,v in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)] if 0<=u<a.shape[0] and 0<=v<a.shape[1])
            b[i,j]=int(k>2 or (k==2 and coins[i,j]==1))
    return b
def trajectory(seed):
    rng=np.random.default_rng(seed);a=np.zeros((7,7),dtype=np.uint8);a[2:5,2:5]=1
    states=[a.copy()];coins=[];birth=[]
    for t in range(1,301):
        c=rng.integers(0,2,a.shape);b=parallel_step(a,c)
        assert np.array_equal(b,scalar_step(a,c))
        assert not b[:2].any() and not b[5:].any() and not b[:,:2].any() and not b[:,5:].any()
        coins.append(c.tolist());birth.append(int(((a==0)&(b==1)).sum()));a=b;states.append(a.copy())
        if not a.any():break
    assert not a.any() and all(x.any() for x in states[:-1])
    return {'seed':seed,'T':len(states)-1,'states':[x.tolist() for x in states],'coins':coins,'birth_counts':birth}
runs=[trajectory(k) for k in [0,5,8]]
assert [r['T'] for r in runs]==[7,4,10]
# Exhaust all four-neighbour choices, both old center values and both tie marks.
for pattern in range(16):
    for old in [0,1]:
        for coin in [0,1]:
            a=np.zeros((3,3),dtype=np.uint8);a[1,1]=old
            for k,(i,j) in enumerate([(0,1),(2,1),(1,0),(1,2)]):a[i,j]=(pattern>>k)&1
            votes=pattern.bit_count();expected=int(votes>2 or (votes==2 and coin==1))
            assert parallel_step(a,np.full((3,3),coin))[1,1]==expected
# Rule: the grey diagonals never vote; the old center is deliberately unknown.
im=canvas(545);d=ImageDraw.Draw(im)
text(d,(40,24),'每个格子只问四个邻居：下一步选黑，还是选白？',35,bold=True)
for col,(vals,title,result) in enumerate([([1,1,1,0],'3 黑、1 白','下一步：黑'),([1,0,0,0],'1 黑、3 白','下一步：白'),([1,0,1,0],'2 黑、2 白','掷硬币：各一半')]):
    x=30+col*420;card(d,(x,90,x+400,465));center(d,x+200,108,title,29,bold=True)
    gx=x+105;gy=166;c=62
    for i in range(3):
        for j in range(3):
            box=(gx+j*c,gy+i*c,gx+(j+1)*c,gy+(i+1)*c)
            d.rectangle(box,fill='#edf0f5',outline='white',width=3)
    for v,(i,j) in zip(vals,[(0,1),(2,1),(1,0),(1,2)]):d.rectangle((gx+j*c,gy+i*c,gx+(j+1)*c,gy+(i+1)*c),fill=BLACK if v else 'white',outline='#9ba8ba',width=2)
    d.rectangle((gx+c,gy+c,gx+2*c,gy+2*c),fill='#fff1d6',outline=AMBER,width=3);center(d,gx+1.5*c,gy+c+8,'?',35,AMBER,True)
    center(d,x+200,378,result,28,BLUE,True)
    if col==2:center(d,x+200,423,'这次选黑，下次也可能选白',21,MUTED)
center(d,640,488,'“？”格原来的颜色不参加投票；每一轮所有格子同时更新。',27)
save(im,'01-rule.png')
# A real synchronous path: no interpolated or hand-edited state.
r0=runs[0];states=[np.array(s,dtype=np.uint8) for s in r0['states']]
im=canvas(570);d=ImageDraw.Draw(im);text(d,(38,22),'同一个 3×3 黑色方块：这一次，第 7 步变成全白',34,bold=True)
text(d,(40,76),'只画出周围的 7×7 窗口；窗口外全是白色。',26,MUTED)
for j,t in enumerate([0,1,2,7]):
    x=26+j*312;card(d,(x,128,x+302,487));center(d,x+151,146,f'第 {t} 步',30,bold=True)
    a=states[t];born=None if t==0 else ((states[t-1]==0)&(a==1))
    board(d,a,x+39,207,32,born);center(d,x+151,445,f'{int(a.sum())} 个黑格',25,MUTED)
text(d,(40,511),'橙框：刚刚重新变黑的格子。中间的完整过程见动图；这只是一条模拟轨迹。',25,AMBER)
save(im,'02-evolution.png')
frames=[]
for t,a in enumerate(states):
    im=Image.new('RGB',(800,750),BG);d=ImageDraw.Draw(im)
    center(d,400,24,'3×3 黑色小岛的一次真实同步演化',31,bold=True)
    center(d,400,82,f'第 {t} 步  ·  {int(a.sum())} 个黑格',30,BLUE,True)
    born=None if t==0 else ((states[t-1]==0)&(a==1));board(d,a,162,150,68,born)
    center(d,400,648,'橙框表示这一步新变黑的格子',25,AMBER)
    center(d,400,694,'每一步都重新掷独立硬币；这不是平均恢复速度。',23,MUTED)
    frames.append(im)
frames[0].save(OUT/'03-evolution.gif',save_all=True,append_images=frames[1:],duration=[1800]+[1100]*(len(frames)-2)+[2500],loop=0,optimize=False,disposal=2)
# Three runs illustrate samples, not a theoretical mean or asymptotic claim.
im=canvas(490);d=ImageDraw.Draw(im);text(d,(40,24),'初态完全相同，恢复时间也可能不同',35,bold=True)
text(d,(42,81),'仍然从刚才的 3×3 方块出发，只换硬币结果。',27,MUTED)
for j,rn in enumerate(runs):
    y=148+j*88;text(d,(44,y+11),f'第 {j+1} 次模拟',28)
    for k in range(rn['T']):d.rounded_rectangle((249+k*72,y,313+k*72,y+55),7,fill=['#235fbb','#3b7d72','#a16a22'][j])
    text(d,(260+rn['T']*72,y+10),f"{rn['T']} 步",28,bold=True)
text(d,(42,422),'这 3 次的平均是 7 步；它不等于所有可能结果的理论平均。',27)
save(im,'04-recovery-times.png')
# The order 'mean first, maximum over all same-diameter patterns second'.
im=canvas(650);d=ImageDraw.Draw(im);text(d,(40,24),'τ(3) 怎么来？先各自取平均，再挑最慢的图形',34,bold=True)
patterns=[np.ones((3,3),dtype=np.uint8),np.array([[1,1,1],[1,0,0],[1,0,0]],dtype=np.uint8),np.array([[1,0,0],[0,0,0],[0,0,1]],dtype=np.uint8)]
for j,a in enumerate(patterns):
    x=32+j*420;card(d,(x,99,x+392,453));center(d,x+196,117,['实心方块','L 形','两个分开的黑格'][j],28,bold=True)
    board(d,a,x+112,177,56);center(d,x+196,356,'最小方框边长都是 3',24,MUTED)
    center(d,x+196,401,f'各自的理论平均时间：{chr(65+j)}',25,BLUE,True)
    arrow(d,(x+196,466),(x+196,506))
card(d,(80,518,1200,587),fill='#e7eefc',outline='#b3c6ec')
center(d,640,531,'把尺寸为 3 的所有图形都比完，最大的平均时间叫 τ(3)。',29,BLUE,True)
center(d,640,608,'这里只画了 3 种图形；τ(N) 里的 N 是包围方框的边长，不是黑格数。',24,MUTED)
save(im,'05-worst-case.png')
# The two processes must stay visibly different: original synchronous and auxiliary clocks.
im=canvas(760);d=ImageDraw.Draw(im);text(d,(40,24),'为什么引入时钟？让“一起变化”变成“一次处理一处”',32,bold=True)
for j in range(2):
    x=32+j*624;card(d,(x,94,x+608,448));center(d,x+304,111,['原问题：所有格点同时更新','辅助过程：闹钟响到谁，更新谁'][j],28,bold=True)
    a=states[0];b=parallel_step(a,np.zeros_like(a)) if j==0 else a.copy()
    if j==1:b[2,2]=0
    board(d,a,x+35,178,30);board(d,b,x+366,178,30);arrow(d,(x+259,282),(x+349,282))
    center(d,x+304,400,['这一轮，四个角恰好都选白色','图中只演示一次响铃造成的变化'][j],23,MUTED)
center(d,640,473,'两种过程的连接工具已有证明；它们不是同一条演化轨迹。',27,BLUE)
card(d,(54,533,1226,699),fill='#fff4e5',outline='#e1b270')
center(d,640,552,'现在还缺的关键一步',31,AMBER,True)
center(d,640,603,'会算“一次更新的平均面积变化”',29)
center(d,640,648,'还要证明“在一段时间内，整个小岛平均收缩多少”。',27)
save(im,'06-current-bridge.png')
# Same past and same arrival time, flip only the still unrevealed identity-mark.
im=canvas(600);d=ImageDraw.Draw(im);text(d,(40,24),'最近证明的一件事：停下来观察，不会把未来硬币挑偏',32,bold=True)
text(d,(42,82),'只看已经发生的记录，决定什么时候停；还没用的那枚硬币此时仍未揭示。',25,MUTED)
for row in range(2):
    y=224+row*170;d.line((90,y,1190,y),fill='#8d99ab',width=4)
    for x in [150,300,440]:d.ellipse((x-10,y-10,x+10,y+10),fill=BLUE)
    d.line((615,y-60,615,y+70),fill=AMBER,width=4)
    d.ellipse((1000-23,y-23,1000+23,y+23),fill=BLACK if row==0 else 'white',outline=BLACK,width=3)
    center(d,300,y+24,'已经看到的过去：完全相同',26,BLUE)
    center(d,615,y-105,'观察时刻',27,AMBER,True)
    center(d,1000,y+36,['下一枚结果：黑','下一枚结果：白'][row],27,bold=True)
    center(d,820,y-51,'同一个下一次响铃时刻',24,MUTED)
center(d,640,532,'只翻转尚未使用的标记：过去和等待都不变，黑、白两种结果等概率。',26,TEAL,True)
save(im,'07-fresh-coin.png')
# An exact one-site calculation in the ordinary clock auxiliary rule.
im=canvas(645);d=ImageDraw.Draw(im);text(d,(40,24),'先算得出的是什么？例如：只更新这一个角',34,bold=True)
a=np.zeros((5,5),dtype=np.uint8);a[1:4,1:4]=1;b=a.copy();b[1,1]=0
assert counts(a)[1,1]==2 and int(a.sum())==9 and int(b.sum())==8
for j,q in enumerate([a,a,b]):
    x=28+j*420;card(d,(x,105,x+388,462));center(d,x+194,122,['更新前：9 个黑格','硬币选黑：仍是 9 个','硬币选白：变成 8 个'][j],26,bold=True)
    board(d,q,x+89,185,42)
    d.rectangle((x+89+42+2,185+42+2,x+89+84-2,185+84-2),outline=BLUE,width=3)
    center(d,x+194,412,['蓝框这个角：2 黑、2 白','概率 ½，黑格数变化 0','概率 ½，黑格数变化 −1'][j],25,BLUE)
center(d,640,496,'这一处更新，平均变化 = ½×0 + ½×(−1) = −½ 个黑格。',29,TEAL,True)
center(d,640,558,'但下次可能更新别处，图形也变了；不能把这一个数直接乘时间。',26)
save(im,'08-local-change.png')
record={'model':'infinite square grid; synchronous four-neighbour majority; independent fair ties; no center vote','simulation':'7x7 shown; initial 3x3 block; support checked to remain in that block','numpy_version':np.__version__,'rng':'numpy.default_rng / PCG64','runs':runs,'checks':{'all_64_local_rule_cases':True,'all_simulated_frames_match_independent_scalar_parallel_update':True,'first_hit_recorded':True,'outer_white_support_preserved':True},'figures':{p.name:{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(OUT.iterdir()) if p.suffix in {'.png','.gif'}}}
(OUT/'simulation-data.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({'runs':[(r['seed'],r['T']) for r in runs],'figures':list(record['figures']),'checks':record['checks']},ensure_ascii=False))
