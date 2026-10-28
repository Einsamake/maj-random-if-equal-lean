"""Reproducible teaching diagrams and exact finite checks, not Lean proofs.

Requires Pillow and Windows Microsoft YaHei (the project environment).
No Monte Carlo data, downloads, or changes to mathematical sources.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, permutations
import hashlib
import json
import random
from PIL import Image, ImageDraw, ImageFont

HERE = Path(__file__).resolve().parent
OUT = HERE / 'images'
OUT.mkdir(exist_ok=True)
FONT = Path('C:/Windows/Fonts/msyh.ttc')
BOLD = Path('C:/Windows/Fonts/msyhbd.ttc')
INK, MUTED, BLUE, GOLD, RED = '#243349', '#536478', '#2267ac', '#ad6b11', '#b44545'


def font(n, bold=False):
    return ImageFont.truetype(str(BOLD if bold else FONT), n)


def txt(draw, xy, s, n=25, color=INK, bold=False):
    draw.text(xy, s, fill=color, font=font(n, bold))


def center(draw, x, y, s, n=25, color=INK, bold=False):
    box = draw.textbbox((0, 0), s, font=font(n, bold))
    txt(draw, (x-(box[2]-box[0])/2, y), s, n, color, bold)


def canvas(title, subtitle, height=950):
    im = Image.new('RGB', (1600, height), '#f7f9fc')
    draw = ImageDraw.Draw(im)
    txt(draw, (45, 26), title, 37, bold=True)
    txt(draw, (45, 91), subtitle, 25, MUTED)
    return im, draw


def domain(L):
    return {(x, y) for x in range(-L, L+1) for y in range(-L, L+1)
            if abs(x)+abs(y) <= L+1}


def square(L):
    return {(x, y) for x in range(-L, L+1) for y in range(-L, L+1)}


def degree(S, v):
    x, y = v
    return sum(u in S for u in ((x+1, y), (x-1, y), (x, y+1), (x, y-1)))


def weight(L, v):
    return L+2-abs(v[0])-abs(v[1])


def loss(S, v):
    """E[old occupancy - new occupancy] for one fair marked heat-bath step."""
    d = degree(S, v)
    new = F(0) if d < 2 else F(1, 2) if d == 2 else F(1)
    return F(v in S)-new


def raw(S, E, w):
    return sum((w(v)*loss(S, v) for v in E), F(0))


counts = []
for L in (2, 3, 4, 10, 40):
    D, E = domain(L), square(L)
    outside = {v for v in E-D if degree(D, v) >= 2}
    assert all(weight(L, v) == 0 for v in outside)
    ordinary = (raw(D, D, lambda _: 1), raw(D, E, lambda _: 1))
    weighted = (raw(D, D, lambda v: weight(L, v)), raw(D, E, lambda v: weight(L, v)))
    assert ordinary == (2*L, F(2))
    assert weighted[0] == weighted[1]
    counts.append({'L': L, 'domain_sites': len(D), 'outside_birth_sites': len(outside),
                   'ordinary_masked': str(ordinary[0]), 'ordinary_expanded': str(ordinary[1]),
                   'weighted_masked': str(weighted[0]), 'weighted_expanded': str(weighted[1])})

# Test selected finite subsets; the all-state theorem is in Lean, not inferred here.
rng = random.Random(20261026)
subset_checks = 0
for L in (1, 2, 3):
    sites = sorted(domain(L))
    selections = ([{v for i, v in enumerate(sites) if (mask >> i) & 1}
                   for mask in range(1 << len(sites))] if L == 1 else
                  [{v for v in sites if rng.randrange(2)} for _ in range(200)])
    for S in selections:
        E = square(L)
        assert all(weight(L, v) == 0 for v in E-domain(L) if degree(S, v) >= 2)
        assert raw(S, domain(L), lambda v: weight(L, v)) == raw(S, E, lambda v: weight(L, v))
        subset_checks += 1

# Convex supporting inequality on a rational grid, and actual permutation flux.
grid = [F(i, 3) for i in range(-18, 19)]
for a in grid:
    for b in grid:
        assert 2*max(a, 0)*(b-a) <= max(b, 0)**2-max(a, 0)**2
flux_checks = 0
for f in ((F(2), F(-1), F(0)), (F(-1), F(-2), F(-3)), (F(1, 2), F(3), F(-4))):
    for p in permutations(range(3)):
        flux = sum((2*max(f[i], 0)*(f[p[i]]-f[i]) for i in range(3)), F(0))
        assert flux <= 0
        flux_checks += 1

# Every M-particle choice for M<=5 gives a unique monotone row profile.
encoding_checks = 0
for M in range(1, 6):
    for p in combinations(range(2*M), M):
        rows = [p[M-1-y]-(M-1-y) for y in range(M)]
        assert all(0 <= a <= M for a in rows)
        assert all(rows[i] >= rows[i+1] for i in range(M-1))
        assert tuple(r+rows[M-1-r] for r in range(M)) == p
        J = sum(v >= M for v in p)
        assert J == sum(y < rows[y] for y in range(M))
        for N in range(M+1):
            local_white = all(x < rows[y] for x in range(N) for y in range(N))
            assert local_white == (J >= N)
        encoding_checks += 1

# Figure 1: actual lattice and exact initial rates.
im, d = canvas('换一把尺子：让被禁止的出生只值零分', 'L=4：暖色格当前全黑，数字仅表示权重；蓝叉格当前白，可能变黑但被禁止。', 1030)
L = 4
D, E = domain(L), square(L)
bad = {v for v in E-D if degree(D, v) >= 2}
cell, gx, gy = 65, 86, 171
for x in range(-L, L+1):
    for y in range(-L, L+1):
        xx, yy = gx+(x+L)*cell, gy+(L-y)*cell
        v = x, y
        if v in D:
            w = weight(L, v)
            fill = (255, 244-12*w, 212-16*w)
            d.rectangle((xx, yy, xx+cell-3, yy+cell-3), fill=fill, outline='#c8b99c')
            center(d, xx+(cell-3)/2, yy+15, str(w), 26)
        elif v in bad:
            d.rectangle((xx, yy, xx+cell-3, yy+cell-3), fill='#e7f1fc', outline=BLUE, width=2)
            center(d, xx+cell/2, yy+1, '0', 26, BLUE, True)
            center(d, xx+cell/2, yy+30, '×', 25, BLUE)
        else:
            d.rectangle((xx, yy, xx+cell-3, yy+cell-3), outline='#dbe1e8')
for x in (-4, 0, 4):
    center(d, gx+(x+L+0.5)*cell, 758, str(x), 20, MUTED)
for y in (-4, 0, 4):
    txt(d, (52, gy+(L-y)*cell+15), str(y), 20, MUTED)
txt(d, (680, 759), 'x', 22)
txt(d, (53, 139), 'y', 22)
txt(d, (86, 808), '中心为(0,0)；域内权重≥1，蓝叉层权重=0。', 24)
for point, color in (((2, 4), BLUE), ((1, 4), RED)):
    x, y = point
    xx, yy = gx+(x+L)*cell, gy+(L-y)*cell
    d.rectangle((xx+3, yy+3, xx+cell-6, yy+cell-6), outline=color, width=4)
txt(d, (800, 178), '同一个初态，两种计分', 30, bold=True)
txt(d, (800, 246), '普通计数：黑变白 +1，白变黑 −1', 25)
txt(d, (822, 296), '16个黑角 × 1/2 = +8', 27, RED)
txt(d, (822, 341), '12个蓝叉 × (−1/2) = −6', 27, BLUE)
txt(d, (822, 389), '域内率8；扩域率8−6=2。', 25)
wval = raw(D, D, lambda v: weight(L, v))
txt(d, (800, 490), '加权计数：该格的权重就是分值', 25)
txt(d, (822, 544), f'域内损失率 = 扩域损失率 = {wval}', 27, BLUE, True)
txt(d, (822, 596), '差额中的每个贡献都乘以零。', 25, BLUE)
txt(d, (800, 674), '红框(1,4)：黑格可能变白。', 23, RED)
txt(d, (800, 717), '蓝框(2,4)：白格可能变黑。', 23, BLUE)
txt(d, (45, 884), '这里只算多数更新的瞬时净变化率：每格平均每单位时间响铃一次，不含后续清理。', 24)
txt(d, (45, 946), '这是有限初态精确枚举；任意支撑状态的零权结论另有证明，不从这张图外推。', 24, bold=True)
im.save(OUT/'boundary-weight.png')

# Figure 2: exact functions, no stochastic or ODE simulation.
im, d = canvas('不盯着最大值：只给超过零的部分计分', '正部在零点有折角；正部平方在零点两边的斜率都是零。', 900)
for panel in range(2):
    ox, oy, width, height = 90+panel*735, 510, 600, 300
    xmin, xmax, ymax = -2, 2, 4.5
    def mapxy(x, y):
        return ox+(x-xmin)/(xmax-xmin)*width, oy-y/ymax*height
    d.line((ox, oy, ox+width+18, oy), fill=MUTED, width=2)
    zx, _ = mapxy(0, 0)
    d.line((zx, oy+12, zx, oy-height-15), fill=MUTED, width=2)
    for k in (-2, -1, 0, 1, 2):
        px, _ = mapxy(k, 0)
        d.line((px, oy-4, px, oy+5), fill=MUTED)
        center(d, px, oy+12, str(k), 22, MUTED)
    for k in (1, 2, 3, 4):
        _, py = mapxy(0, k)
        txt(d, (zx-31, py-15), str(k), 20, MUTED)
    points = []
    for step in range(401):
        x = xmin+(xmax-xmin)*step/400
        y = max(x, 0) if panel == 0 else max(x, 0)**2
        points.append(mapxy(x, y))
    d.line(points, fill=RED if panel == 0 else BLUE, width=5)
    center(d, ox+width/2, 155, '正部 max(x,0)' if panel == 0 else '正部平方 φ(x)=max(x,0)²', 27, bold=True)
    txt(d, (ox+width+21, oy-10), 'x', 22)
    txt(d, (zx+10, oy-height-30), '值', 22)
txt(d, (70, 600), '一个置换算例：a=(2,−1,0) → (−1,0,2)', 27, bold=True)
txt(d, (70, 654), '支持不等式左边求和：−12；右边求和：(0−4)+(0−0)+(4−0)=0。', 25)
txt(d, (70, 706), '置换重新排列同一组平方分，右边相消；左边因此 ≤0。', 25, BLUE)
txt(d, (70, 808), '若能量从零开始、始终非负又不增加，便始终为零：所有坐标都不变正。', 25)
im.save(OUT/'positive-energy.png')

# Figure 3: one exact profile and its reversible encoding.
im, d = canvas('整块区域全白，怎样变成“右边有几个人”？', '辅助混合边界：南、西固定白，北、东固定黑；白格向西南闭合。')
M, rows = 5, [4, 3, 2, 1, 0]
p = [r+rows[M-1-r] for r in range(M)]
assert p == [0, 2, 4, 6, 8]
gx, gy, cell = 110, 208, 86
d.rectangle((gx-12, gy-12, gx+5*cell+12, gy+5*cell+12), fill='white', outline='#c4ccd6')
d.rectangle((gx, gy-12, gx+5*cell+12, gy-1), fill=INK)
d.rectangle((gx+5*cell, gy-12, gx+5*cell+12, gy+5*cell), fill=INK)
for y in range(M):
    for x in range(M):
        xx, yy = gx+x*cell, gy+(M-1-y)*cell
        white = x < rows[y]
        d.rectangle((xx, yy, xx+cell, yy+cell), fill='white' if white else INK, outline='#b9c5d4', width=2)
        if x == y:
            d.ellipse((xx+31, yy+31, xx+55, yy+55), fill=BLUE if white else '#a6bdd7')
    txt(d, (gx+M*cell+40, gy+(M-1-y)*cell+23), f'λ{y}={rows[y]}', 25)
# Green outline encloses exactly southwest 2x2.
d.rectangle((gx+3, gy+3*cell+3, gx+2*cell-3, gy+5*cell-3), outline='#20845e', width=5)
txt(d, (110, 691), '绿色框：左下 2×2 全白', 27, '#20845e', True)
txt(d, (110, 747), '底行 y=0 对应 r=4：p_4=4+4=8', 23)
txt(d, (800, 220), '位置 = 编号 + 对应行白格数', 29, bold=True)
txt(d, (800, 281), 'p=(0,2,4,6,8)', 28)
base, space, y = 790, 68, 430
d.rounded_rectangle((base+5*space-28, y-58, base+9*space+28, y+87), 12, fill='#e5f0fc')
center(d, base+7*space, y-105, '右半槽位：5 至 9', 25, BLUE)
d.line((base, y, base+9*space, y), fill='#b9c5d4', width=3)
for slot in range(10):
    xx = base+slot*space
    d.ellipse((xx-16, y-16, xx+16, y+16), fill=BLUE if slot in p else 'white', outline=BLUE, width=2)
    center(d, xx, y+30, str(slot), 22)
txt(d, (800, 581), '右半有 2 粒子，恰好对应 2 个白色对角格', 25, BLUE, True)
txt(d, (800, 635), '形状闭合性把对角格扩大为整块白区。', 24)
txt(d, (45, 811), '粒子数始终为 5；本图白格有 10 个。粒子编码的是边界，不是黑格或白格本身。', 25)
txt(d, (45, 870), '这是确定形状的编码示意，不指定等待时间，也不代表某个时刻的平均图形。', 24, MUTED)
im.save(OUT/'particle-count.png')

# Figure 4: conditional geometry, not a simulated full droplet trajectory.
# L=160, protected outer-layer point x=(145,0); NE block offsets 1..4.
Lbig, anchor = 160, (145, 0)
small = {(anchor[0]+a, anchor[1]+b) for a in range(1, 5) for b in range(1, 5)}
assert small <= domain(Lbig)
assert min(weight(Lbig, v) for v in small) >= F(Lbig, 20)
assert len(small) >= F(Lbig**2, 6400)
small_mass = sum(weight(Lbig, v) for v in small)
assert small_mass >= F(Lbig**3, 128000)
im, d = canvas('失守为何要积累立方分数：白格数量 × 每格分值', '条件几何示意，L=160；蓝色只标保护区，不表示格子的黑白状态。', 1000)
cx, cy, scale = 365, 450, 1.48
def pt(x,y):
    return cx+x*scale, cy-y*scale
corners = [(160,1),(1,160),(-1,160),(-160,1),(-160,-1),(-1,-160),(1,-160),(160,-1)]
d.polygon([pt(x,y) for x,y in corners], fill='#fae5c7', outline=GOLD)
d.polygon([pt(145,0),pt(0,145),pt(-145,0),pt(0,-145)], fill='#d8e8f8', outline=BLUE)
ax, ay = pt(*anchor)
d.ellipse((ax-6,ay-6,ax+6,ay+6),fill=RED)
for v in small:
    xx, yy=pt(*v)
    d.rectangle((xx-scale/2,yy-scale/2,xx+scale/2,yy+scale/2),fill='white',outline='#20845e')
txt(d,(95,164),'大裁角域 D_L：容许黑格存在',25,GOLD)
txt(d,(100,717),'蓝色：内菱形及紧邻的一圈保护格',24,BLUE)
txt(d,(100,760),'红点 x=(145,0)：一个失守位置示意',23,RED)
d.line((ax+13,ay-15,850,300),fill='#20845e',width=2)
txt(d,(860,170),'若这个方向是已证的全白小方块',27,bold=True)
txt(d,(860,217),'右图放大：4×4格，数字是分值',24,MUTED)
for a in range(1,5):
    for b in range(1,5):
        xx, yy=948+(a-1)*65,300+(4-b)*65
        d.rectangle((xx,yy,xx+65,yy+65),fill='white',outline='#20845e',width=2)
        center(d,xx+32.5,yy+15,str(weight(Lbig,(anchor[0]+a,b))),26)
txt(d,(860,601),'16格 ≥ L²/6400 = 4格',25)
txt(d,(860,648),'每格至少9分 ≥ L/20 = 8分',25)
txt(d,(860,696),f'实际总分{small_mass} ≥ L³/128000 = 32',25,BLUE,True)
txt(d,(45,853),'一般失守时：形状定理先给全白小方块；本图只解释如何把它换成分数门槛。',24)
txt(d,(45,914),'没有声称仅有一个白点就会产生大片白区，也没有构造一条完整合法演化。',24,MUTED)
im.save(OUT/'protected-threshold.png')

record = {
    'kind': 'exact finite checks and deterministic teaching diagrams; not new Lean proofs',
    'ordinary_and_weighted_initial_rates': counts,
    'selected_state_zero_boundary_checks': subset_checks,
    'state_sampling': 'all 512 subsets for L=1; 200 seeded subsets each for L=2,3; seed 20261026',
    'supporting_inequality_rational_pairs': len(grid)**2,
    'permutation_flux_checks': flux_checks,
    'exhaustive_encoding_profiles_M_1_through_5': encoding_checks,
    'particle_figure': {'M': M, 'row_lengths_bottom_up': rows, 'positions': p,
                        'right_count': 2, 'white_cells': sum(rows)},
    'protected_figure': {'L':Lbig, 'loss_point':list(anchor), 'offsets':[1,2,3,4],
                         'block_cells':len(small), 'min_weight':min(weight(Lbig,v) for v in small),
                         'block_weight':small_mass,'kind':'conditional geometry; not a trajectory'},
    'figures': {q.name: hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(OUT.glob('*.png'))},
}
(HERE/'toy-checks.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps(record, ensure_ascii=True))
