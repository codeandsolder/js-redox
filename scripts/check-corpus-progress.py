#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, os, sqlite3, subprocess, sys, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; BUILDER=ROOT/'scripts/build-corpus-catalog.py'; SEMANTIC=ROOT/'scripts/build-corpus-semantic-index.py'; UPDATER=ROOT/'scripts/update-corpus-progress.py'; SAMPLER=ROOT/'scripts/check-corpus-classifier-sample.py'
def main():
 with tempfile.TemporaryDirectory(prefix='js-redox-progress-test-') as tmp:
  w=Path(tmp); captures=w/'captures'; cap=captures/'0001-popunder-ads-test'; (cap/'resources').mkdir(parents=True); (cap/'runtime-scripts').mkdir(); (cap/'recorder-manifest.json').write_text('{}\n')
  raw=b"while(true){switch(x){case 1:eval('x');break;}}"; sha=hashlib.sha256(raw).hexdigest(); body='resources/a.js'; (cap/body).write_bytes(raw)
  (cap/'network.json').write_text(json.dumps([{'url':'https://x.example/a.js','resourceType':'Script','mimeType':'application/javascript','body':{'sha256':sha,'path':body,'size':len(raw)}}])); (cap/'runtime-scripts.json').write_text('[]')
  db=w/'catalog.sqlite'; cand=w/'candidates'; summary=w/'summary.json'
  subprocess.run([sys.executable,str(BUILDER),'--captures',str(captures),'--database',str(db),'--candidate-dir',str(cand),'--summary',str(summary),'--jobs','1'],check=True,stdout=subprocess.PIPE,text=True)
  deob=w/'deob'; deob.write_text("""#!/usr/bin/env python3
import hashlib,json,shutil,sys
from pathlib import Path
a=sys.argv[1:]; inp=Path(a[0]); out=Path(a[1]); report=Path(a[a.index('--report')+1]); shutil.copyfile(inp,out); raw=inp.read_bytes(); sha=hashlib.sha256(raw).hexdigest(); report.write_text(json.dumps({'schema':'js-safe-deobfuscate/v1','input_sha256':sha,'output_sha256':sha,'changed':True,'iterations':2,'transforms':{'constant_fold':3}}))
"""); deob.chmod(0o755)
  sus=w/'sus'; sus.write_text("""#!/usr/bin/env python3
import json,sys
path=sys.argv[-1]; print(json.dumps({'schema':'js-sus-scan/v3','files':[{'input':path,'bytes':1,'diagnostics':0,'fatal_error':False,'signal_count':5,'signal_kinds':{'eval':2},'top_score':17,'clusters':[{'score':17}],'actionable_signal_count':3,'actionable_signal_kinds':{'dynamic_code_call':3},'actionable_top_score':15,'actionable_clusters':[{'score':15}]}]}))
"""); sus.chmod(0o755)
  semantic=subprocess.run([sys.executable,str(SEMANTIC),'--database',str(db),'--candidate-dir',str(cand),'--sus-scan',str(sus),'--chunk-size','1','--nice','0'],check=True,text=True,capture_output=True)
  sem_report=json.loads(semantic.stdout[semantic.stdout.index('{'):]); assert sem_report['newly_scanned']==1,sem_report
  assert (cand/'semantic-actionable.txt').read_text().strip()==str(cap/body)
  semantic2=subprocess.run([sys.executable,str(SEMANTIC),'--database',str(db),'--candidate-dir',str(cand),'--sus-scan',str(sus),'--chunk-size','1','--nice','0'],check=True,text=True,capture_output=True)
  assert 'semantic pending=0' in semantic2.stdout,semantic2.stdout
  paths=w/'paths.txt'; paths.write_text(str(cap/body)+'\n')
  cp=subprocess.run([sys.executable,str(UPDATER),'--database',str(db),'--candidate-dir',str(cand),'--paths-file',str(paths),'--deobfuscate-safe',str(deob),'--sus-scan',str(sus),'--pipeline-id','test-p1','--nice','0'],check=True,text=True,capture_output=True)
  report=json.loads(cp.stdout); assert report['recorded']==1,report; assert report['best_known']['residual']==1,report
  con=sqlite3.connect(db); row=con.execute('SELECT actionable_top_score,actionable_signal_count,transform_total FROM body_analysis_best WHERE sha256=?',(sha,)).fetchone(); assert row==(15,3,3),row; con.close()
  assert (cand/'known-residual.txt').read_text().strip()==str(cap/body); assert (cand/'quick-focus.txt').read_text().strip()==str(cap/body)
  sample=subprocess.run([sys.executable,str(SAMPLER),'--database',str(db),'--sus-scan',str(sus),'--sample-per-stratum','1'],check=True,text=True,capture_output=True); sampled=json.loads(sample.stdout); assert sampled['schema']=='js-redox-corpus-classifier-sample/v2',sampled
  print('PASS: corpus progress records post-deob semantic residuals and refreshes focus candidates')
if __name__=='__main__': main()
