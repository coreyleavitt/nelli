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
  case node.kind
  of nkA: discard
  case sym.typ.kind:
  of tyInt: discard
  case kind(x)
  of nkA: discard
  case node.kinds
  of nkA: discard
