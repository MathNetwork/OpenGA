import json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]; R=D.parents[1];sys.path.insert(0,str(R))
from sync import Client,json_bytes,write_atomic
c=Client(json.loads((R/'.credentials.json').read_text())['api_key'])
item=c.request('/theorems/fe9a0128-6fb2-494b-aba1-8436851df1e4')
write_atomic(D/'Metadata/endgame_parent.json',json_bytes(item));print(item['status'],item['theorem_name'])
