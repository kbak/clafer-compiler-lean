module

public import ClaferCompiler.IR.ExprObservation

@[expose] public section
namespace ClaferCompiler.Tests.Expressions
open IR.Expr

def s : Support 3 3 := {
  classes := #v[100, 200, 300]
  maps := #v[⟨200, .head, 0, 1, "head"⟩, ⟨200, .dereference, 1, 2, "value"⟩,
    ⟨200, .dereference, 1, 2, "repeated"⟩]
  context := 0
  integer := #v[false, false, true] }

def bounds : Bounds 3 := ⟨5, #v[1, 2, 1], #v[⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 7⟩]⟩
def heads : Term 3 3 := .image 0 1 .this (.map 0)
def values : Term 3 3 := .image 1 2 heads (.map 1)
def outer : Local 3 := ⟨1, "x", 1⟩
def inner : Local 3 := ⟨2, "x", 1⟩
def shadow : Term 3 3 := .all outer heads
  (.all inner (.var 0) (.equal (.collection (.objects 1)) (.var 0) (.var 1)))
def observed : Observation 3 3 := {
  objects := #v[[.object 0], [.object 1, .object 2], [.integer 3]]
  links := #v[[⟨0, .object 0, .object 1⟩, ⟨1, .object 0, .object 2⟩],
    [⟨2, .object 1, .integer 3⟩, ⟨3, .object 2, .integer 3⟩],
    [⟨2, .object 1, .integer 3⟩, ⟨3, .object 2, .integer 3⟩]] }

def outcome (t : Ty 3) (e : Term 3 3) (b : Bounds 3 := bounds) : String :=
  match validateBounds s b [] t e with
  | .ok _ => "ok" | .error d => d.code

/-- Exhaust the actual values in small extraction intervals. The oracle checks
each mathematical result, independently of the analyzer's endpoint transfers. -/
def extractionIntervalCases : IO Unit := do
  let support : Support 2 0 := ⟨#v[1, 2], #v[], 0, #v[true, true]⟩
  let locals : List (Local 2) := [⟨1, "a", 0⟩, ⟨2, "b", 1⟩]
  let intervals : List Interval := [⟨-3, -2⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 3⟩]
  let members := fun r : Interval => (List.range (r.upper - r.lower + 1).toNat).map
    (fun (k : Nat) => r.lower + (k : Int))
  for width in [1, 2, 3, 4, 5] do
    let limit := (2 ^ (width - 1) : Int)
    let fits := fun v => -limit ≤ v && v < limit
    for left in intervals do
      for right in intervals do
        for op in [Arithmetic.add, .subtract] do
          let e : Term 2 0 := .arithmetic op (.integerOf 0 (.var 0)) (.integerOf 1 (.var 1))
          let result := validateBounds support ⟨width, #v[1, 1], #v[left, right]⟩ locals .integer e
          let expected := (members left).all fun x => (members right).all fun y =>
            fits x && fits y && fits (match op with | .add => x + y | .subtract => x - y)
          unless result.isOk == expected do
            throw <| IO.userError s!"extraction interval range: width {width}, {repr left}, {repr right}, {repr op}"

/-!
[utest->req~compiler-expressions~1]
[utest->req~compiler-arithmetic~1]
-/
def cases : List (String × Ty 3 × Term 3 3 × String) := [
  ("Boolean", .boolean, .boolean true, "ok"),
  ("mathematical integer", .integer, .integer (-16), "ok"),
  ("this", .collection (.objects 0), .this, "ok"),
  ("global heads", .collection (.objects 1), .extent 1, "ok"),
  ("map", .collection (.relation 1 2), .map 1, "ok"),
  ("strict conjunction", .boolean, .and (.boolean false) (.boolean true), "ok"),
  ("negation", .boolean, .not (.boolean false), "ok"),
  ("collection equality", .boolean, .equal (.collection (.objects 1)) heads heads, "ok"),
  ("relation equality", .boolean, .equal (.collection (.relation 1 2)) (.map 1) (.map 2), "ok"),
  ("less", .boolean, .less (.integer 3) (.integer 2), "ok"),
  ("addition", .integer, .arithmetic .add (.integer 2) (.integer 3), "ok"),
  ("operand order", .integer, .arithmetic .subtract (.integer 2) (.integer 3), "ok"),
  ("singleton extraction", .integer, .integerOf 2 values, "ok"),
  ("head count", .integer, .cardinality (.objects 1) heads, "ok"),
  ("binary count", .integer, .cardinality (.relation 1 2) (.map 1), "ok"),
  ("union", .collection (.objects 1), .setOp .union (.objects 1) heads heads, "ok"),
  ("difference", .collection (.objects 1), .setOp .difference (.objects 1) heads heads, "ok"),
  ("intersection", .collection (.relation 1 2), .setOp .intersection (.relation 1 2) (.map 1) (.map 2), "ok"),
  ("subset", .boolean, .subset (.objects 1) heads heads, "ok"),
  ("image", .collection (.objects 2), values, "ok"),
  ("join", .collection (.relation 0 2), .join 0 1 2 (.map 0) (.map 1), "ok"),
  ("widen objects", .collection (.objects 1), .widenObjects 1 1 .same heads, "ok"),
  ("widen relation", .collection (.relation 1 2), .widenRelation 1 2 1 2 .same .same (.map 1), "ok"),
  ("shadowed names", .boolean, shadow, "ok"),
  ("UTF-8 byte span", .integer, .located ⟨"μ.cfr", 2, 6⟩ (.integer 3), "ok"),
  ("sort mismatch", .integer, .boolean true, "expr.type-scope-or-span"),
  ("unbound position", .collection (.objects 1), .var 0, "expr.type-scope-or-span"),
  ("binder not in own domain", .boolean, .all outer (.var 0) (.boolean true), "expr.type-scope-or-span"),
  ("duplicate binder ID", .boolean, .all outer heads (.all outer heads (.boolean true)), "expr.type-scope-or-span"),
  ("reversed join", .collection (.relation 0 2), .join 0 1 2 (.map 1) (.map 0), "expr.type-scope-or-span"),
  ("false widening", .collection (.objects 2), .widenObjects 1 2 .same heads, "expr.type-scope-or-span"),
  ("wrong inclusion role", .collection (.objects 1), .widenObjects 0 1 (.inclusion 0) .this, "expr.type-scope-or-span"),
  ("nonprimitive extraction", .integer, .integerOf 1 heads, "expr.type-scope-or-span"),
  ("reversed span", .integer, .located ⟨"a", 6, 2⟩ (.integer 3), "expr.type-scope-or-span"),
  ("whole Int extent", .collection (.objects 2), .extent 2, "expr.infinite-primitive-extent"),
  ("whole Int equality", .boolean, .equal (.collection (.objects 2)) (.extent 2) (.extent 2), "expr.infinite-primitive-extent"),
  ("whole Int binder", .boolean, .all ⟨4, "i", 2⟩ (.extent 2) (.boolean true), "expr.infinite-primitive-extent"),
  ("literal overflow", .integer, .integer 16, "expr.unsafe-bounds"),
  ("intermediate overflow", .integer, .arithmetic .subtract (.arithmetic .add (.integer 15) (.integer 1)) (.integer 1), "expr.unsafe-bounds"),
  ("hidden false branch", .boolean, .and (.boolean false) (.less (.integer 16) (.integer 0)), "expr.unsafe-bounds"),
  ("empty binder body range", .boolean, .all outer (.setOp .difference (.objects 1) heads heads)
    (.less (.integer 16) (.integer 0)), "expr.unsafe-bounds")
]

def run : IO Unit := do
  extractionIntervalCases
  for (label, ty, e, expected) in cases do
    unless outcome ty e == expected do throw <| IO.userError s!"{label}: {outcome ty e}, expected {expected}"
  let nested := (List.range 100).foldl (fun e _ => Term.not e) (.boolean true : Term 3 3)
  unless outcome .boolean nested == "ok" do throw <| IO.userError "nested traversal"
  unless outcome .integer (.integer (10 ^ 100)) == "expr.unsafe-bounds" do
    throw <| IO.userError "literal magnitude must not size traversal"
  unless outcome .integer (.located ⟨"a", 10 ^ 100, 10 ^ 100 + 1⟩ (.integer 0)) == "ok" do
    throw <| IO.userError "source metadata must not size traversal"
  for width in [0, 17] do
    unless outcome .boolean (.boolean true) { bounds with width } == "expr.unsafe-bounds" do
      throw <| IO.userError "bitwidth profile"
  let wide : Bounds 3 := { bounds with width := 4, extents := #v[1, 8, 8] }
  unless outcome .integer (.cardinality (.objects 1) (.extent 1)) wide == "expr.unsafe-bounds" do
    throw <| IO.userError "unary count overflow"
  unless outcome .integer (.cardinality (.relation 1 2) (.map 1)) wide == "expr.unsafe-bounds" do
    throw <| IO.userError "binary endpoint product overflow"
  let numeric : Bounds 3 := { bounds with width := 4, integers := #v[⟨0,0⟩, ⟨0,0⟩, ⟨0,7⟩] }
  unless outcome .integer (.arithmetic .add (.integerOf 2 values) (.integerOf 2 values)) numeric == "expr.unsafe-bounds" do
    throw <| IO.userError "extraction interval intermediate"
  let inherited : Support 3 3 := { s with maps := s.maps.set 0 ⟨200, .inclusion, 1, 0, "super"⟩ }
  let widened : Term 3 3 := .widenObjects 1 0 (.trans 1 .same (.inclusion 0)) (.extent 1)
  unless (check inherited [] (.collection (.objects 0)) widened).isOk do
    throw <| IO.userError "explicit inclusion path"
  let repeatedIds := { s with classes := #v[100, 200, 200], integer := #v[false, false, false] }
  unless (check repeatedIds [] (.collection (.objects 2)) (.widenObjects 1 2 .same heads)).isOk do
    throw <| IO.userError "equal IDs at distinct support occurrences"
  for x in List.range 21 do
    for y in List.range 21 do
      let a := (x : Int) - 10
      let b := (y : Int) - 10
      for op in [Arithmetic.add, .subtract] do
        let result := match op with | .add => a + b | .subtract => a - b
        let expected := if -8 ≤ a && a ≤ 7 && -8 ≤ b && b ≤ 7 && -8 ≤ result && result ≤ 7 then "ok" else "expr.unsafe-bounds"
        unless outcome .integer (.arithmetic op (.integer a) (.integer b)) { bounds with width := 4 } == expected do
          throw <| IO.userError "exhaustive width-4 arithmetic boundary"
  for (xs, expected) in [([], none), ([Atom.integer 3], some 3),
      ([.integer 3, .integer 3], some 3), ([.integer 3, .integer 4], none),
      ([.object 3], none), ([.integer 3, .object 3], none)] do
    unless extract xs == expected do throw <| IO.userError "singleton extraction"
  unless observed.withinBounds s bounds do throw <| IO.userError "observation bounds"
  unless !(observed.withinBounds s { bounds with integers := #v[⟨0,0⟩, ⟨0,0⟩, ⟨4,7⟩] }) do
    throw <| IO.userError "observed value outside interval"
  unless Environment.valid s observed [inner, outer] ⟨.object 0, [.object 1, .object 2]⟩ do
    throw <| IO.userError "lexical environment"
  unless !(Environment.valid s observed [outer] ⟨.object 0, []⟩) do
    throw <| IO.userError "missing lexical object"
  unless Environment.bounded s bounds observed [⟨3, "i", 2⟩] ⟨.object 0, [.integer 3]⟩ do
    throw <| IO.userError "bounded integer environment"
  unless !(Environment.bounded s bounds observed [⟨3, "i", 2⟩] ⟨.object 0, [.integer 100]⟩) do
    throw <| IO.userError "unrecorded integer environment"
  let primitiveTwice : Support 2 0 := ⟨#v[300, 300], #v[], 0, #v[true, true]⟩
  let primitiveBounds : Bounds 2 := ⟨5, #v[1, 1], #v[⟨7,7⟩, ⟨0,0⟩]⟩
  let inconsistent : Observation 2 0 := ⟨#v[[.integer 7], [.integer 0]], #v[]⟩
  unless !(inconsistent.withinBounds primitiveTwice primitiveBounds) do
    throw <| IO.userError "same-ID primitive observations must agree before widening"
  let consistent : Observation 2 0 := ⟨#v[[.integer 7], [.integer 7, .integer 7]], #v[]⟩
  unless consistent.withinBounds primitiveTwice { primitiveBounds with integers := #v[⟨7,7⟩, ⟨7,7⟩] } do
    throw <| IO.userError "same-ID primitive observations compare sets"
  let omitted := { observed with objects := observed.objects.set 2 [] }
  unless !(omitted.withinBounds s bounds) do throw <| IO.userError "missing observed link endpoint"
  IO.println s!"{cases.length} expression cases; 882 arithmetic boundaries; 360 extraction interval boundaries; extraction and observations passed"

end ClaferCompiler.Tests.Expressions
