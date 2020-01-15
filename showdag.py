import sys

def supported(op):
  return (op in supported_ops) | op.startswith(("TWrite", "LiteralOp", "TRead"))

def op_s(op):
    return {
        "b(>)": "b(gt)",
        "b(>=)": "b(geq)",
        "b(<)": "b(lt)",
        "b(<=)": "b(leq)",
    }.get(op, op)

supported_ops = [
  "b(+)",
  "b(*)",
  "r(t)",
  "ba(+*)",
  "ua(+RC)"
]

f = open(sys.argv[1],"r") 

print("digraph graphname {")

for hop in f.readlines():
  h = hop.split(';')
  hid = h[1]
  hop = h[2]
  hchildren = h[3]
  hmeta=h[4].split(',')
  row, col = (hmeta[0], hmeta[1])
  # row, col = ("", "")
  nnz = int(hmeta[4])
  vol=int(row) * int(col)
  # sparsity=" "
  if (vol > 0) & (nnz > 0):
    sparsity = str(float(nnz) / float(vol))
  
  color = "\"red\""
  if supported(hop):
    color = "\"black\""
  # S [shape=record, label="{{S|6}|1000}"];
  node = hid + " [shape=record label=\"{{" + op_s(hop) + " | " + sparsity + "} | " + row + "x" + col + "}\" color=" + color + "];";
  print(node)
  for child in filter(None, hchildren.split(',')):
    # edge = child + "<-" + hid + ";"
    edge = hid + "->" + child + " [color=" + color + "];"
    print(edge)

print("}")
