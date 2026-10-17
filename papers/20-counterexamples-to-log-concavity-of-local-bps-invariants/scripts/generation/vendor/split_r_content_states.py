from pathlib import Path
import re,json
root=Path('Paper20/Certs/RContent36')
changed=[]
for a in range(17,1,-1):
 for p in sorted(root.glob(f'B{a:02}C*.lean')):
  src=p.read_text()
  def split(m):
   name,lit=m.group(1),m.group(2)
   rows=lit[1:-1].split(',\n')
   if len(rows)<60:return m.group(0)
   names=[f'{name}_row{i:03}' for i in range(len(rows))]
   changed.append(dict(file=str(p),name=name,rows=len(rows)))
   return '\n'.join(f'def {n} : ℕ × List ℤ := {v}' for n,v in zip(names,rows))+'\n\ndef '+name+' : State := ['+', '.join(names)+']\n\n'
  out=re.sub(r'def (v_[0-9_]+) : State := (\[.*?\])\n\n',split,src,flags=re.S)
  if out!=src:p.write_text(out)
Path('work/r-content36-state-splits.json').write_text(json.dumps(changed,indent=2)+'\n')
print('Split',len(changed),'large states in',len(set(x['file'] for x in changed)),'unbuilt files')
