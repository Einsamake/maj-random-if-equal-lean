from pathlib import Path
import hashlib,json,subprocess,re,shutil,sys,os
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parents[1]
T=R/'tex';B=T/'build';O=R/'output/pdf';V=R/'review'
for p in [T,B,O]:p.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper=R/'paper.md';body=paper.read_text(encoding='utf-8');paper_hash=sha(paper)
title=body.splitlines()[0].removeprefix('# ')
conversion=V/'conversion.md';conversion.write_text(body[body.index('\n')+1:].lstrip(),encoding='utf-8',newline='\n')
filter_path=V/'pdf-links.lua'
filter_path.write_text('''function Link(el)
  if not el.target:match("^https?://") and not el.target:match("^#") then
    return el.content
  end
end
''',encoding='utf-8')
for p in (R/'images').glob('*.png'):
  (T/'images').mkdir(exist_ok=True);shutil.copy2(p,T/'images'/p.name)
commands=[]
def run(cmd,log,cwd):
    r=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
    log.write_bytes(r.stdout)
    commands.append({'command':[str(x) for x in cmd],'cwd':str(cwd),'exit_code':r.returncode,
                     'log':log.relative_to(R).as_posix(),'log_sha256':sha(log)})
    if r.returncode: print(r.stdout.decode('utf-8','replace')[-7000:]);raise SystemExit(r.returncode)
    return r
pandoc=Path('D:/Program_Files_Backup/anaconda3/Library/bin/pandoc.exe')
run([str(pandoc),str(conversion),'-f','markdown+tex_math_dollars-implicit_figures','-t','latex','-s',
 '--metadata',f'title={title}','--metadata','date=Working draft, 17 November 2026',
 '-V','geometry:margin=25.4mm','-V','fontsize=11pt','-V','papersize=a4',
 '-V','colorlinks=true','-V','linkcolor=blue','-V','urlcolor=blue',
 '--lua-filter',str(filter_path),'-o',str(T/'main.tex')],V/'pandoc.log',R)
tex=(T/'main.tex').read_text(encoding='utf-8')
# Identifiers in the source dictionary may wrap at underscores in prose.
# Escaped underscores are text; mathematical subscripts remain untouched.
tex=tex.replace('\\_','\\_\\allowbreak ')
# Keep each existing manual caption with its image, avoiding a caption split
# at a page boundary after disabling Pandoc's duplicate automatic captions.
fig_pattern=r'(?m)^(\\pandocbounded\{\\includegraphics[^\n]+\})\n\n((?:\\emph\{)?Figure [1-6]\..*?)(?=\n\n)'
def figure_block(match):
    return ('\\par\\medskip\\noindent\n\\begin{minipage}{\\linewidth}\n{\\centering\n'+
            match.group(1)+'\n\\par}\n\\smallskip\n{\\small '+match.group(2)+'}\n'+
            '\\end{minipage}\n\\par\\medskip')
tex,n_figures=re.subn(fig_pattern,figure_block,tex,flags=re.S)
assert n_figures==6,n_figures
# Typeset the two wide formulas on their own lines without changing any term.
inline=r'\(e^{-\beta H(y)}/(e^{-\beta H(x^{v,0})}+e^{-\beta H(x^{v,1})})\)'
assert tex.count(inline)==1
tex=tex.replace(inline,r'\[e^{-\beta H(y)}/(e^{-\beta H(x^{v,0})}+e^{-\beta H(x^{v,1})})\]')
wide=r'''q_S(v)=\frac{m(S)-m(\rho_{v,0}(S))
                    +m(S)-m(\rho_{v,1}(S))}{2},\qquad
Q_D(S)=\sum_{v\in D}q_S(v),\quad Q_E(S)=\sum_{v\in E}q_S(v).'''
split=r'''\begin{aligned}
q_S(v)&=\frac{m(S)-m(\rho_{v,0}(S))
                    +m(S)-m(\rho_{v,1}(S))}{2},\\
Q_D(S)&=\sum_{v\in D}q_S(v),\qquad Q_E(S)=\sum_{v\in E}q_S(v).
\end{aligned}'''
assert tex.count(wide)==1
tex=tex.replace(wide,split)
tex=tex.replace('\\setlength{\\emergencystretch}{3em}',
                '\\setlength{\\emergencystretch}{3em}\n\\widowpenalty=10000\n\\clubpenalty=10000\n\\setlength{\\abovedisplayskip}{8pt plus 2pt minus 2pt}\n\\setlength{\\belowdisplayskip}{8pt plus 2pt minus 2pt}')
(T/'main.tex').write_text(tex,encoding='utf-8',newline='\n')
engine=Path('D:/Program Files/TexLive/2026/bin/windows/xelatex.exe')
for i in [1,2]:
  run([str(engine),'-interaction=nonstopmode','-halt-on-error','-file-line-error',
       '-no-shell-escape','-synctex=1','-output-directory',str(B),str(T/'main.tex')],
       V/f'xelatex-pass-{i}.log',T)
pdf=O/'quadratic-recovery-v6.pdf';shutil.copy2(B/'main.pdf',pdf)
log=(B/'main.log').read_text(encoding='utf-8',errors='replace')
warnings={key:re.findall(pattern,log) for key,pattern in {
  'overfull':r'Overfull \\[hv]box[^\n]*',
  'missing_characters':r'Missing character:[^\n]*',
  'undefined_references':r'(?:LaTeX Warning: (?:Reference|Citation)[^\n]*|There were undefined references\.)',
  'rerun':r'[^\n]*(?:Rerun to get|Label\(s\) may have changed)[^\n]*'}.items()}
record={'paper_sha256':paper_hash,'tex_sha256':sha(T/'main.tex'),'pdf_sha256':sha(pdf),
        'pdf_bytes':pdf.stat().st_size,'commands':commands,'compiler':'native XeLaTeX 2026, two actual passes',
        'margin_mm':25.4,'internal_relative_pdf_links':'removed in TeX conversion only; Markdown links retained',
        'warnings':warnings,'pages_visual_review':'pending','images':{p.name:sha(p) for p in (R/'images').glob('*.png')}}
(V/'native-build.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
assert sha(paper)==paper_hash,'Markdown changed during compilation; rebuild needed'
print(json.dumps({'pdf':str(pdf),'bytes':pdf.stat().st_size,'pdf_sha256':record['pdf_sha256'],'warnings':warnings}))
