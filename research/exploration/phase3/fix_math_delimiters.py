from pathlib import Path
import re,sys,hashlib
sys.stdout.reconfigure(encoding='utf-8')
r=Path(r'C:\Users\Lenovo\Desktop\Project\Math\research\exploration\phase3')
for name in ['README.md','PROOF.md']:
 s=(r/name).read_text(encoding='utf-8')
 if name=='README.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   if line.startswith('可以自己检验一个小例子：'):
    lines[i]='可以自己检验一个小例子：在任意满足 $q=1/2$ 的时刻，上述三个公式给出 $Y_0=1/2$、$Y_1=1/4$、$Y_2=19/96$。因此 $Y_0-Y_1=1/4$、$Y_1-Y_2=5/96$。这里是在另一个简单时刻检查公式；观察时刻 $t_*$ 对应的仍是 $q_*=2^{-21/19}$。'
  s='\n'.join(lines)+'\n'
  s=s.replace('这些式子代回三个方程和初值都成立。','使用 $q\\prime=-1.05q$ 求导，这些式子代回三个方程和初值都成立。')
 else:
  needle='由于非负数的十九次幂严格递增'
  s=s.replace(needle,'这条幂比较也可以直接清除分母，检查下面的整数不等式：\n\n$$\n929^{19}\\,2^{21}\\le2000^{19}.\n$$\n\n'+needle)
 s=s.replace(r'\[','$$').replace(r'\]','$$').replace(r'\(','$').replace(r'\)','$')
 # Normalize legacy plain parentheses around inline math, preserving links,
 # existing dollar spans and displayed formulas.
 out=[]; display=False
 for line in s.splitlines():
  if line.strip()=='$$':
   display=not display;out.append(line);continue
  if display:out.append(line);continue
  buf=[];i=0;inmath=False
  while i<len(line):
   if line[i]=='$':inmath=not inmath;buf.append(line[i]);i+=1;continue
   if line[i]=='(' and not inmath and (i==0 or line[i-1]!=']'):
    depth=1;j=i+1
    while j<len(line) and depth:
     depth += (line[j]=='(')-(line[j]==')');j+=1
    inside=line[i+1:j-1]
    if depth==0 and inside and not re.search(r'[\u4e00-\u9fff$]',inside) and re.search(r'[A-Za-z0-9\\]',inside):
     buf.append('$'+inside+'$');i=j;continue
   buf.append(line[i]);i+=1
  out.append(''.join(buf))
 s='\n'.join(out)+'\n'
 (r/name).write_text(s,encoding='utf-8')
 assert not any(token in s for token in [r'\(',r'\)'])
 print(name,hashlib.sha256((r/name).read_bytes()).hexdigest())

