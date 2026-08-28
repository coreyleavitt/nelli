## Z3-free probe: `import nelli` must compile with no z3 on the path.
import nelli

when isMainModule:
  echo "z3-free probe OK"
