import std/[unittest, json]
import nelli
import nelli/[datasource, rng]

# JSON Schema → Strategy[JsonNode]: derive a generator from a runtime
# schema document. Covers the everyday 80%: type/enum/const, numeric
# and length bounds, properties+required for objects, items for arrays,
# oneOf for unions.

proc draw(s: Strategy[JsonNode], seed: uint64 = 1): JsonNode =
  var ds = newDataSource(initSplitMix64(seed))
  s.generate(ds)

suite "strategyFromJsonSchema: integer":
  test "integer with minimum and maximum stays in range":
    let schema = parseJson("""{"type": "integer", "minimum": 0, "maximum": 9}""")
    let s = strategyFromJsonSchema(schema)
    for i in 0 ..< 50:
      let v = draw(s, uint64(i + 1))
      check v.kind == JInt
      check v.getInt >= 0
      check v.getInt <= 9

suite "strategyFromJsonSchema: string":
  test "string with minLength and maxLength stays in range":
    let schema = parseJson(
      """{"type": "string", "minLength": 1, "maxLength": 5}""")
    let s = strategyFromJsonSchema(schema)
    for i in 0 ..< 50:
      let v = draw(s, uint64(i + 1))
      check v.kind == JString
      check v.getStr.len >= 1
      check v.getStr.len <= 5

suite "strategyFromJsonSchema: object":
  test "object with required properties produces all required keys with right types":
    let schema = parseJson("""
      {"type": "object",
       "properties": {
         "name": {"type": "string", "minLength": 1, "maxLength": 5},
         "age":  {"type": "integer", "minimum": 0, "maximum": 120}
       },
       "required": ["name", "age"]}""")
    let s = strategyFromJsonSchema(schema)
    for i in 0 ..< 20:
      let v = draw(s, uint64(i + 1))
      check v.kind == JObject
      check v.hasKey("name")
      check v["name"].kind == JString
      check v["name"].getStr.len >= 1
      check v.hasKey("age")
      check v["age"].kind == JInt
      check v["age"].getInt >= 0
      check v["age"].getInt <= 120

suite "strategyFromJsonSchema: enum + oneOf":
  test "enum schema picks from the allowed values":
    let schema = parseJson("""{"enum": ["red", "green", "blue"]}""")
    let s = strategyFromJsonSchema(schema)
    var seen: array[3, bool]
    for i in 0 ..< 100:
      let v = draw(s, uint64(i + 1))
      check v.kind == JString
      case v.getStr
      of "red":   seen[0] = true
      of "green": seen[1] = true
      of "blue":  seen[2] = true
      else: check false  # not in the allowed set
    check seen[0] and seen[1] and seen[2]   # all three were reached

  test "oneOf schema picks from union of alternatives":
    let schema = parseJson("""
      {"oneOf": [
        {"type": "integer", "minimum": 0, "maximum": 9},
        {"type": "string", "minLength": 1, "maxLength": 3}
      ]}""")
    let s = strategyFromJsonSchema(schema)
    var sawInt, sawStr = false
    for i in 0 ..< 50:
      let v = draw(s, uint64(i + 1))
      if v.kind == JInt: sawInt = true
      elif v.kind == JString: sawStr = true
      else: check false  # only int or string allowed
    check sawInt and sawStr
