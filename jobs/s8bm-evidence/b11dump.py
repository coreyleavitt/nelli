import sys
p = sys.argv[1] + '/src/nelli/smt/runtime.nim'
s = open(p).read()
a = '''  let s1 = querySolver(ctx, roots, rlHalf)
  for c in caps: s1.add c
'''
assert s.count(a) == 1
s = s.replace(a, a + '''  when defined(symexQueryStats):
    echo "ZZBEGIN"
    for x in roots: echo "ZZQ ", $x
    for x in caps: echo "ZZC ", $x
''')
open(p, 'w').write(s)
