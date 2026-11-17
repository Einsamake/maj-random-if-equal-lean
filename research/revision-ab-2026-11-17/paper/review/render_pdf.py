from pathlib import Path
import subprocess,hashlib,json,sys,math,re
from pypdf import PdfReader
from PIL import Image,ImageDraw,ImageFont
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parents[1];V=R/'review';O=V/'rendered';O.mkdir(exist_ok=True)
pdf=R/'output/pdf/quadratic-recovery-v6.pdf'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
reader=PdfReader(pdf);texts=[p.extract_text() or '' for p in reader.pages]
(V/'pdf-text.txt').write_text('\n\n'.join(f'PAGE {i+1}\n'+t for i,t in enumerate(texts)),encoding='utf-8')
# Replace only renderer-owned image files in this explicit staging directory.
for pattern in ['page-*.png','contact-*.png']:
 for old in O.glob(pattern):
  assert old.resolve().parent==O.resolve()
  old.unlink()
poppler=Path('C:/Users/Lenovo/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/poppler/Library/bin/pdftoppm.exe')
cmd=[str(poppler),'-r','96','-png',str(pdf),str(O/'page')]
q=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
(V/'render.log').write_bytes(q.stdout);assert q.returncode==0,q.stdout.decode('utf-8','replace')
pages=sorted(O.glob('page-*.png'));assert len(pages)==len(reader.pages)
font=ImageFont.truetype('C:/Windows/Fonts/arial.ttf',21)
contacts=[];thumbw=245;thumbh=347;col=4;rows=6;cellw=265;cellh=382
for start in range(0,len(pages),col*rows):
 subset=pages[start:start+col*rows];rows_actual=math.ceil(len(subset)/col)
 sheet=Image.new('RGB',(cellw*col,cellh*rows_actual),'#dce3e9');d=ImageDraw.Draw(sheet)
 for j,p in enumerate(subset):
  im=Image.open(p).convert('RGB');im.thumbnail((thumbw,thumbh))
  x=(j%col)*cellw+(cellw-im.width)//2;y=(j//col)*cellh+28
  sheet.paste(im,(x,y));d.text(((j%col)*cellw+10,(j//col)*cellh+3),f'Page {start+j+1}',font=font,fill='#1a2530')
 out=O/f'contact-{start//24+1:02}.png';sheet.save(out);contacts.append(out)
terms=['Theorem 1','Theorem 4','retained failure','finite-state observable','From an empty quadrant',
       'Sixteen','The full vacant block','quadratic denominator','qS(v)','Formal artifact']
important={}
for term in terms:
 found=[i+1 for i,t in enumerate(texts) if term.casefold() in t.casefold()]
 if found:important[term]=found
annotations=[]
for i,page in enumerate(reader.pages):
 for ann in page.get('/Annots',[]):
  obj=ann.get_object();a=obj.get('/A')
  if a and a.get('/S')=='/URI':annotations.append({'page':i+1,'uri':str(a.get('/URI'))})
assert all(x['uri'].startswith(('http://','https://')) for x in annotations),annotations
record={'pdf_sha256':sha(pdf),'paper_sha256':sha(R/'paper.md'),'pages':len(pages),'render_command':cmd,
        'render_exit_code':q.returncode,'render_dpi':96,
        'page_images':{p.relative_to(R).as_posix():sha(p) for p in pages},
        'contact_sheets':{p.relative_to(R).as_posix():sha(p) for p in contacts},
        'important_pages_by_text':important,'external_link_annotations':annotations,
        'all_pages_rendered':True,'visual_inspection':'pending'}
record['figure_caption_pages']={str(i):[j+1 for j,t in enumerate(texts)
    if re.search(r'Figure\s+'+str(i)+r'\.',t)] for i in range(1,7)}
(V/'render-validation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pages':len(pages),'contacts':[str(x) for x in contacts],'important':important}))
