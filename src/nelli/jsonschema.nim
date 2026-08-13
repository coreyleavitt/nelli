## JSON Schema → `Strategy[JsonNode]`.
##
## Derive a generator from a runtime JSON Schema document. The schema
## is parsed (already as a `JsonNode`) and traversed; primitive
## constraints map to existing strategy combinators; composite
## constraints (`properties`/`required`, `items`, `oneOf`) map to
## `tuples`-style composition.
##
## **Scope.** Sub-task A of #97. Covers the everyday 80% of JSON Schema
## — type / enum / const / numeric bounds / length bounds / object
## properties+required / array items / oneOf. Not in this MVP:
## `pattern` (regex → strategy), `anyOf` / `allOf` (intersection /
## relaxed-union semantics), conditional (`if`/`then`/`else`), `$ref`
## (recursive schemas). Each of those is genuine extra work and
## fits a follow-up sub-task.

import std/[json, options, strutils]
import ./strategy, ./datasource, ./int128, ./choice

proc strategyFromJsonSchema*(schema: JsonNode): Strategy[JsonNode] =
  ## Main entry. Dispatches on the schema's `type` (or `enum`/`const`/
  ## `oneOf` if present at the top level) and emits a corresponding
  ## `Strategy[JsonNode]`.

  # `enum`: pick from the explicit list. Takes precedence over `type`
  # — if both are present, the enum constrains the type implicitly.
  if schema.hasKey("enum"):
    var values: seq[JsonNode]
    for v in schema["enum"]:
      values.add v
    return sampledFrom(values)

  # `const`: a single allowed value.
  if schema.hasKey("const"):
    return just(schema["const"])

  # `oneOf`: union of alternatives. Each alternative is itself a schema.
  if schema.hasKey("oneOf"):
    var alts: seq[Strategy[JsonNode]]
    for sub in schema["oneOf"]:
      alts.add strategyFromJsonSchema(sub)
    return oneOf(alts)

  if not schema.hasKey("type"):
    # No type, no enum, no const, no oneOf — empty schema matches anything.
    # For generation we default to integer 0; users with this case
    # almost always meant to write something more specific.
    return just(newJInt(0))

  case schema["type"].getStr
  of "integer":
    let lo = if schema.hasKey("minimum"): schema["minimum"].getInt
             else: low(int32).int
    let hi = if schema.hasKey("maximum"): schema["maximum"].getInt
             else: high(int32).int
    let intStrat = integers(lo, hi)
    return map(intStrat, proc(n: int): JsonNode = newJInt(n.BiggestInt))
  of "string":
    let mn = if schema.hasKey("minLength"): schema["minLength"].getInt else: 0
    let mx = if schema.hasKey("maxLength"): schema["maxLength"].getInt else: 32
    let strStrat = strings(minLen = mn, maxLen = mx)
    return map(strStrat, proc(s: string): JsonNode = newJString(s))
  of "boolean":
    return map(booleans(), proc(b: bool): JsonNode = newJBool(b))
  of "null":
    return just(newJNull())
  of "object":
    # `properties` defines per-key sub-schemas; `required` lists the
    # keys that must appear. For the MVP, optional properties (in
    # `properties` but not `required`) are emitted with 50% probability;
    # additional unspecified keys are not generated.
    let propsNode = if schema.hasKey("properties"): schema["properties"]
                    else: newJObject()
    var requiredKeys: seq[string]
    if schema.hasKey("required"):
      for r in schema["required"]:
        requiredKeys.add r.getStr
    # Snapshot the (key, sub-strategy) pairs into a value captured by
    # the closure — JsonNode is ref-shaped, so we don't want to keep
    # the schema reachable across draws.
    var keys: seq[string]
    var subStrats: seq[Strategy[JsonNode]]
    var isRequired: seq[bool]
    for k, sub in propsNode:
      keys.add k
      subStrats.add strategyFromJsonSchema(sub)
      isRequired.add k in requiredKeys
    return newStrategy(proc(src: var DataSource): JsonNode =
      result = newJObject()
      for i in 0 ..< keys.len:
        if isRequired[i] or src.drawBoolean(0.5):
          result[keys[i]] = subStrats[i].run(src))
  of "array":
    let mn = if schema.hasKey("minItems"): schema["minItems"].getInt else: 0
    let mx = if schema.hasKey("maxItems"): schema["maxItems"].getInt else: 10
    let itemStrat =
      if schema.hasKey("items"): strategyFromJsonSchema(schema["items"])
      else: just(newJNull())
    let listStrat = lists(itemStrat, minLen = mn, maxLen = mx)
    return map(listStrat, proc(xs: seq[JsonNode]): JsonNode =
      result = newJArray()
      for x in xs: result.add x)
  else:
    return just(newJNull())
