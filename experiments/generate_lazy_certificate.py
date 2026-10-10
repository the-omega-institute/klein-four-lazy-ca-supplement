"""Produce candidate finite certificates. Lean, not this script, is the verifier."""
from collections import deque
from pathlib import Path
import sys

def translated(x, g):
    return sum(((x >> (h ^ g)) & 1) << h for h in range(4))

def lazy_map(S, p):
    return tuple(x ^ sum(1 << g for g in range(4)
                         if all(((translated(x, g) ^ p) & (1 << h)) == 0
                                for h in range(4) if S & (1 << h)))
                 for x in range(16))

parameters = [(S, p) for S in range(16) if S & 1
              for p in range(16) if p & ~S == 0]
generators = [lazy_map(*parameter) for parameter in parameters]
identity = tuple(range(16))
members = [identity]
indices = {identity: 0}
parents = [0]
last = [0]
queue = deque([0])
while queue:
    i = queue.popleft()
    for j, generator in enumerate(generators):
        product = tuple(generator[x] for x in members[i])
        if product not in indices:
            indices[product] = len(members)
            parents.append(i)
            last.append(j)
            queue.append(len(members))
            members.append(product)

def pack(t):
    result = t[0] // 15 + 2 * (t[15] // 15)
    for s, representative in enumerate([10, 12, 6]):
        image = t[representative]
        descriptor = {0: 0, 15: 1, representative: 2, 15-representative: 3}[image]
        result += descriptor * 2 ** (2 + 2*s)
    return result + t[1] * 256 + t[14] * 4096

codes = [pack(t) for t in members]
assert len(members) == 4007 and len(set(codes)) == 4007 and len(generators) == 54

def array(name, values):
    if len(values) > 64:
        chunks = [f'def {name}Chunk{i//64:02} : Array Nat := #[' + ', '.join(map(str, values[i:i+64])) + ']\n'
                  for i in range(0, len(values), 64)]
        def access(lo, hi):
            if hi-lo == 1:
                return f'{name}Chunk{lo:02}.getD (n % 64) 0'
            middle = (lo+hi)//2
            return f'(if n < {64*middle} then {access(lo,middle)} else {access(middle,hi)})'
        return '\n'.join(chunks) + f'\ndef {name}At (n : Nat) : Nat := {access(0,len(chunks))}\n\n'
    lines = [', '.join(map(str, values[i:i+24])) for i in range(0, len(values), 24)]
    return f'def {name} : Array Nat := #[\n  ' + ',\n  '.join(lines) + '\n]\n\n'

search_declarations = []

def search_function(items):
    if not items:
        return None
    middle = len(items) // 2
    code, index = items[middle]
    left = search_function(items[:middle])
    right = search_function(items[middle+1:])
    name = f'searchNode{index:04}'
    if not left and not right:
        body = f'if n = {code} then {index} else 0'
    else:
        body = f'if n = {code} then {index} else if n < {code} then '
        body += f'{left} n' if left else '0'
        body += ' else ' + (f'{right} n' if right else '0')
    search_declarations.append(f'def {name} (n : Nat) : Nat := {body}\n')
    return name

text = '''import KleinFour.Tables

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

inductive Search
  | empty
  | node : Nat → Nat → Search → Search → Search

def Search.find : Search → Nat → Nat
  | .empty, _ => 0
  | .node key index left right, n =>
    if n = key then index else if n < key then left.find n else right.find n

'''
text += array('codes', codes) + array('parents', parents) + array('lastGenerator', last)
text += array('generatorCodes', [pack(g) for g in generators])
text += array('neighborhoods', [S for S, p in parameters])
text += array('patterns', [p for S, p in parameters])
root = search_function(sorted((code, i) for i, code in enumerate(codes)))
text += '\n'.join(search_declarations) + f'\ndef searchFind (n : Nat) : Nat := {root} n\n\n'
text += 'end KleinFour.LazyCertificate\n'
if '--check' in sys.argv:
    assert Path('KleinFour/LazyData.lean').read_text() == text, 'Generated data differs'
else:
    Path('KleinFour/LazyData.lean').write_text(text)
print(f'Candidate certificate: {len(members)} members, {len(generators)} generators; {len(text)} bytes')
