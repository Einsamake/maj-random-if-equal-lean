from pathlib import Path
import json,hashlib,re
from pypdf import PdfReader
R=Path(__file__).resolve().parents[1];V=R/'review'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pdf=R/'output/pdf/quadratic-recovery-v6.pdf';paper=R/'paper.md';tex=R/'tex/main.tex'
assert sha(pdf)=='926d5af679ec9f1b4a89bd56228bb4787dcb573ccd109098ccc878b9b5db4414'
assert sha(paper)=='88eb33dea7af3ca495d3c7dc1a0f78e4a75aa5d14d1e5e471d1a39ae1d9dffcb'
b=json.loads((V/'native-build.json').read_text());r=json.loads((V/'render-validation.json').read_text())
assert b['paper_sha256']==r['paper_sha256']==sha(paper)
assert b['pdf_sha256']==r['pdf_sha256']==sha(pdf)
assert all(not xs for xs in b['warnings'].values()),b['warnings']
assert all(c['exit_code']==0 for c in b['commands'])
assert len(r['page_images'])==r['pages']==60
for key,h in r['page_images'].items():assert sha(R/key)==h,key
for key,h in r['contact_sheets'].items():assert sha(R/key)==h,key
for i in range(1,7):assert len(r['figure_caption_pages'][str(i)])==1
assert all(sha(R/'images'/n)==sha(R/'tex/images'/n) for n in b['images'])
assert len(b['images'])==6
assert r['figure_caption_pages']=={'1':[6],'2':[13],'3':[33],'4':[39],'5':[50],'6':[54]}
whole_pages=[3,6,9,13,22,33,35,39,43,50,54,59,60]
inspection={f'review/rendered/page-{i:02}.png':sha(V/'rendered'/f'page-{i:02}.png') for i in whole_pages}
r['visual_inspection']='PASS: final three contact sheets reviewed across pages1–60; thirteen selected full-page renders reviewed.'
(V/'render-validation.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
b['pages_visual_review']='PASS; see pdf-validation.json for exact scope and bound page hashes.'
(V/'native-build.json').write_text(json.dumps(b,indent=2)+'\n',encoding='utf-8')
out={'status':'PASS','paper_sha256':sha(paper),'tex_sha256':sha(tex),'pdf_sha256':sha(pdf),
     'pdf_path':'output/pdf/quadratic-recovery-v6.pdf','pdf_bytes':pdf.stat().st_size,'pages':60,
     'all_pages_rendered':True,'all_pages_visually_inspected':True,
     'visual_inspection_method':'Every final page was inspected in three contact sheets for layout continuity, clipping, blank pages, table/figure placement and page order. Thirteen selected pages were also examined as full-page images. This is a visual layout check, not a sixty-page word-by-word mathematical referee report.',
     'contact_sheets_inspected':r['contact_sheets'],'full_page_images_inspected':inspection,
     'figure_caption_pages':r['figure_caption_pages'],'all_six_images_match_tex_copies':True,
     'native_build':'Pandoc conversion plus two actual native XeLaTeX passes, all exits0; final logs bound below.',
     'margin_mm':25.4,'warnings':b['warnings'],
     'typesetting_adjustments':['remove duplicate automatic image-alt captions while keeping all six supplied captions',
       'keep each image and its supplied caption in one unsplit minipage',
       'allow line breaks at underscores in source identifiers',
       'typeset the Gibbs conditional probability and raw-rate definition on separate lines',
       'suppress isolated paragraph first/last lines across page boundaries',
       'internal relative links become readable text in PDF; original Markdown links retained'],
     'mathematical_markdown_modified_by_pdf_task':False,'desktop_second_compile_claimed':False,
     'simulated_reader_review':'waived by explicit user instruction; none claimed',
     'build_record_sha256':sha(V/'native-build.json'),'render_record_sha256':sha(V/'render-validation.json'),
     'commands':b['commands'],'page_images':r['page_images'],
     'editable_sources':['paper.md','tex/main.tex','review/compile_paper.py','review/render_pdf.py'],
     'scope_note':'No submission, publication, external communication, source-mathematics change, or human expert review is asserted by this PDF validation.'}
(V/'pdf-validation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','pages','pdf_bytes','paper_sha256','pdf_sha256']}))
