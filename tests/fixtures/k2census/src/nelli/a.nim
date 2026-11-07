proc walk(n: Node) =
  case n.kind
  of nkA: discard
  else: discard
  case n.kind  # second dispatch
  of nkB: discard
  else: discard
  # case n.kind in a comment is not counted
  discard allocDegrade(x)   # not a literal
  let d = Degrade(kind: k)
  let s = Survivors(a, b)
  let t = Survivors(c) ; let u = Degrade(e)
  # Survivors( in a comment is not counted
