import json,sys
from pathlib import Path
root=Path(__file__).resolve().parents[3]; sys.path.insert(0,str(root))
from sync import Client,json_bytes,write_atomic
c=Client(json.loads((root/'.credentials.json').read_text())['api_key'])
directory=Path(__file__).resolve().parents[1]/'Metadata'; directory.mkdir(exist_ok=True)
items={}
for name,tid in [('measure','77397b5f-f00d-4fe2-aaef-e8544eda2e28'),('openness','c13cb69f-c40b-40b3-8960-3a59f11c9123'),('parent','0347aa7b-4f24-4106-873e-c9b21fd9169f')]:
 item=c.request('/theorems/'+tid);items[name]=item; print(name,item['status'],item['mathlib_rev'])
write_atomic(directory/'external_items.json',json_bytes(items))
write_atomic(directory/'root_before.json',json_bytes(c.request('/theorems/7ea2da12-4d1b-4bbc-8257-df87d92f5a8e/graph')))
