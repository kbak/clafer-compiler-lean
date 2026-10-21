module

public import ClaferCompiler.Backend.Alloy.ExpressionAttachments
public import ClaferCompiler.Backend.Alloy.Print
public import tests.InheritedNative

@[expose] public section
namespace ClaferCompiler.Tests.ExpressionEncodingNative
open Backend.Alloy Backend.Alloy.Expressions IR.Expr

/-! [utest->req~compiler-expression-encoding~1]
[utest->req~compiler-alloy-text~1] -/

def support : Support 3 4 := {
  classes := #v[10, 20, 30]
  maps := #v[⟨20, .head, 0, 1, "head"⟩, ⟨20, .dereference, 1, 2, "value"⟩,
    ⟨20, .parent, 1, 0, "parent"⟩, ⟨20, .inclusion, 1, 1, "identity"⟩]
  context := 0
  integer := #v[false, false, true] }

def layout : Layout 3 4 := ⟨#v[.sig 0, .sig 1, .sig 2],
  #v[.field 0, .field 1, .transpose (.field 0), .diagonal (.sig 1)], #v[0, 1, 2]⟩

def bounds : IR.Expr.Bounds 3 := ⟨5, #v[1, 2, 2], #v[⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 3⟩]⟩
def heads : Term 3 4 := .image 0 1 .this (.map 0)
def values : Term 3 4 := .image 1 2 heads (.map 1)
def emptyValues : Term 3 4 := .setOp .difference (.objects 2) values values
def number : Term 3 4 := .integerOf 2 values
def undefinedNumber : Term 3 4 := .integerOf 2 emptyValues
def eqn (a : Term 3 4) (n : Int) : Term 3 4 := .equal .integer a (.integer n)
def count (k : Collection 3) (a : Term 3 4) (n : Int) := eqn (.cardinality k a) n
def outer : Local 3 := ⟨1, "x", 1⟩
def inner : Local 3 := ⟨2, "x", 1⟩

/-- Expected results are fixed mathematical examples, never encoder outputs. The
last number is the observed integer-domain size, with zero/one/two-value cases. -/
def cases : List (String × Term 3 4 × Bool × Nat) := [
  ("true", .boolean true, true, 1),
  ("false", .boolean false, false, 1),
  ("owner", .equal (.collection (.objects 0)) .this (.extent 0), true, 1),
  ("head count", count (.objects 1) heads 2, true, 1),
  ("binary count", count (.relation 1 2) (.map 1) 2, true, 1),
  ("strict conjunction", .and (.boolean false) (.boolean true), false, 1),
  ("not", .not (.boolean false), true, 1),
  ("boolean equality", .equal .boolean (.less (.integer 1) (.integer 2)) (.boolean true), true, 1),
  ("singleton extraction", eqn number 3, true, 1),
  ("ordered less", .less (.integer 2) number, true, 1),
  ("addition", eqn (.arithmetic .add number (.integer 2)) 5, true, 1),
  ("subtraction", eqn (.arithmetic .subtract (.integer 2) number) (-1), true, 1),
  ("empty extraction", eqn undefinedNumber 0, false, 1),
  ("undefined negation", .not (eqn undefinedNumber 0), false, 1),
  ("multiple extraction", eqn number 3, false, 2),
  ("unary union", count (.objects 1) (.setOp .union (.objects 1) heads (.extent 1)) 2, true, 1),
  ("unary difference", count (.objects 1) (.setOp .difference (.objects 1) heads (.extent 1)) 0, true, 1),
  ("unary intersection", count (.objects 1) (.setOp .intersection (.objects 1) heads (.extent 1)) 2, true, 1),
  ("binary union", count (.relation 1 2) (.setOp .union (.relation 1 2) (.map 1) (.map 1)) 2, true, 1),
  ("binary difference", count (.relation 1 2) (.setOp .difference (.relation 1 2) (.map 1) (.map 1)) 0, true, 1),
  ("binary intersection", count (.relation 1 2) (.setOp .intersection (.relation 1 2) (.map 1) (.map 1)) 2, true, 1),
  ("subset", .subset (.objects 1) heads (.extent 1), true, 1),
  ("join", count (.relation 0 2) (.join 0 1 2 (.map 0) (.map 1)) 1, true, 1),
  ("object widening", count (.objects 1) (.widenObjects 1 1 .same heads) 2, true, 1),
  ("relation widening", count (.relation 1 2) (.widenRelation 1 2 1 2 .same .same (.map 1)) 2, true, 1),
  ("lexical binding", .all outer heads (.all inner heads
    (.equal (.collection (.objects 1)) (.var 0) (.var 1))), false, 1),
  ("owner under binder", .all outer heads (.equal (.collection (.objects 0)) .this (.extent 0)), true, 1),
  ("primitive binder", .all ⟨3, "i", 2⟩ values (eqn (.integerOf 2 (.var 0)) 3), true, 1),
  ("parent navigation", count (.objects 0) (.image 1 0 heads (.map 2)) 1, true, 2),
  ("identity relation", count (.relation 1 1) (.map 3) 2, true, 1),
  ("empty domain", .all ⟨4, "i", 2⟩ emptyValues (.not (eqn undefinedNumber 0)), true, 1),
  ("nonempty undefined body", .all outer heads (.not (eqn undefinedNumber 0)), false, 1),
  ("strict implication sugar", .not (.and (.boolean false) (.not (eqn undefinedNumber 0))), false, 1),
  ("zero primitive observation", .not (eqn number 0), false, 0),
  ("source span", .located ⟨"μ.cfr", 2, 8⟩ (eqn number 3), true, 1)
]

def schema : Schema := ⟨[{}, {}, { scalar := true }], [⟨0, 1, .set⟩, ⟨1, 2, .set⟩]⟩
def candidate (size : Nat) : Instance := {
  signatures := [[0], [1, 2], List.range' 10 size]
  fields := [[[0, 1], [0, 2]], [1, 2].flatMap fun x => (List.range' 10 size).map fun y => [x, y]]
  values := [[], [], if size == 1 then [(10, 3)] else if size == 2 then [(10, 2), (11, 3)] else []] }

def inheritedSupport (owner : Fin 28) : Support 28 7 := {
  classes := Vector.ofFn Fin.val
  maps := #v[⟨owner.val, .inclusion, owner, 14, "same"⟩,
    ⟨14, .inclusion, 14, 10, "same"⟩, ⟨10, .inclusion, 10, 8, "same"⟩,
    ⟨9, .head, 8, 9, "same"⟩, ⟨9, .dereference, 9, 27, "same"⟩,
    ⟨9, .parent, 9, 8, "same"⟩, ⟨9, .target, 8, 27, "same"⟩]
  context := owner
  integer := Vector.ofFn (fun x => x.val == 27) }

def inheritedValue (owner : Fin 28) : Term 28 7 :=
  .integerOf 27 (.image 9 27 (.image 8 9
    (.widenObjects owner 8 (.trans 14 (.inclusion 0) (.trans 10 (.inclusion 1) (.inclusion 2))) .this)
    (.map 3)) (.map 4))

def attachmentCases : IO Unit := do
  let validated : Except IR.Structural.Diagnostic (IR.Inherited.Validated 28) :=
    IR.Inherited.validateRaw InheritedNative.raw
  let .ok v := validated
    | throw (IO.userError "inherited fixture admission")
  let a : Body 28 := {
    id := 11, owner := 16, source := some ⟨"same.cfr", 4, 12⟩,
    mapCount := 7, support := inheritedSupport 16,
    term := .equal .integer (inheritedValue 16) (.integer 3) }
  let b : Body 28 := {
    id := 12, owner := 17, source := some ⟨"same.cfr", 20, 30⟩,
    mapCount := 7, support := inheritedSupport 17,
    term := .equal .integer (inheritedValue 17) (.integer 3) }
  let intervals := Vector.ofFn (fun x : Fin 28 => if x == 27 then (⟨0, 7⟩ : Interval) else ⟨0, 0⟩)
  let numericOwner := Structural.signatureId v.layout 27
  let base := Backend.Alloy.Inherited.encode v InheritedNative.observation
  let instanceValue : Instance := { base with values := base.signatures.zipIdx.map fun (_, j) =>
    if j == numericOwner then [(999, 3)] else [] }
  for (bs, expected) in [([a, a, b], true),
      ([a, a, { b with term := .equal .integer (inheritedValue 17) (.integer 4) }], false)] do
    let .ok compiled := compile v InheritedNative.limits intervals bs
      | throw (IO.userError "inherited attachment compilation")
    unless compiled.bodies.map (·.original.id) == [11, 11, 12] &&
        compiled.bodies.map (·.original.owner.val) == [16, 16, 17] &&
        compiled.bodies.map (·.original.source) == [a.source, a.source, b.source] do
      throw (IO.userError "attachment occurrence metadata lost")
    let .ok truth := evaluate compiled.module instanceValue
      | throw (IO.userError "inherited attachment evaluation")
    unless truth == expected do throw (IO.userError "inherited context leakage")
    let .ok _ := Text.render compiled.module (Text.anonymousNames compiled.module.raw)
      | throw (IO.userError "inherited constraint reconstruction")
  let .ok bound := bindSupport v a.support a.owner | throw (IO.userError "bind roles")
  let contains := Structural.contains v.layout.core 9
  let dereference := Structural.deref v.layout.core 9
  unless bound.maps[3] == contains && bound.maps[4] == dereference &&
      bound.maps[5] == contains.transpose && bound.maps[6] == contains.join dereference do
    throw (IO.userError "resolved role was selected by name")
  for bad in [{ a with owner := 17 },
      { a with support := { a.support with classes := a.support.classes.set 9 999 } },
      { a with support := { a.support with integer := a.support.integer.set 27 false } },
      { a with support := { a.support with maps := a.support.maps.set 4 ⟨9, .parent, 9, 27, "same"⟩ } }] do
    unless !(encodeBody v (sourceBounds v InheritedNative.limits intervals) bad).isOk do
      throw (IO.userError "mismatched owner/identity/role admitted")

def run (directory : String) : IO Unit := do
  attachmentCases
  let root := System.FilePath.mk directory
  IO.FS.createDirAll root
  for ((label, term, expected, size), index) in cases.zipIdx do
    let .ok admitted := validateBounds support bounds [] .boolean term
      | throw (IO.userError s!"source admission: {label}")
    let code := encode layout admitted
    let fixed := [Formula.equal (.field 0) (.product (.sig 0) (.sig 1)),
      .equal (.field 1) (.product (.sig 1) (.sig 2))] ++ scalarFacts 2 5 ⟨2, 3⟩ ++
      (if size == 1 then [.all (.sig 2) (.compare .eq (scalarAt 2 5 0) (.literal 3))] else [])
    let model : Module := ⟨schema, fixed,
      ⟨.run, attach (.sig 0) code, [⟨1, true⟩, ⟨2, true⟩, ⟨size, true⟩], 5⟩⟩
    let .ok checked := Backend.Alloy.check model
      | throw (IO.userError s!"target admission: {label}")
    let .ok value := evaluate checked (candidate size)
      | throw (IO.userError s!"target evaluation: {label}")
    unless value == expected do throw (IO.userError s!"wrong meaning: {label}")
    let .ok rendered := Text.render checked (Text.anonymousNames model)
      | throw (IO.userError s!"round trip: {label}: {Text.serialize model}")
    IO.FS.writeFile (root / s!"case_{index}.als") rendered.text
    IO.FS.writeFile (root / s!"case_{index}.truth") (if expected then "true" else "false")
  let rawScalar := fun size value =>
    (⟨⟨[{ scalar := true }], []⟩, [],
      ⟨.run, .compare .eq (.scalar 0 (-3) 3 (.sig 0)) (.literal value), [⟨size, true⟩], 4⟩⟩ : Module)
  let direct : List (Module × Instance) := [
    (rawScalar 1 2, ⟨[[0]], [], [[(0, 2)]]⟩),
    (rawScalar 2 (-3), ⟨[[0, 1]], [], [[(0, 2), (1, 3)]]⟩),
    (⟨⟨[{}], []⟩, [], ⟨.run, .compare .eq (.count (.diagonal (.sig 0))) (.literal 2),
      [⟨2, true⟩], 4⟩⟩, ⟨[[0, 1]], [], []⟩)]
  for ((raw, candidateValue), offset) in direct.zipIdx do
    let index := cases.length + offset
    let .ok checked := Backend.Alloy.check raw | throw (IO.userError "direct target admission")
    let .ok true := evaluate checked candidateValue | throw (IO.userError "direct target meaning")
    let .ok rendered := Text.render checked (Text.anonymousNames raw)
      | throw (IO.userError "direct target reconstruction")
    IO.FS.writeFile (root / s!"case_{index}.als") rendered.text
    IO.FS.writeFile (root / s!"case_{index}.truth") "true"
  -- Admission rejects all branches before solving, including vacuous bodies.
  for e in [eqn (.integer 16) 0,
      .not (.and (.boolean false) (eqn (.integer 16) 0)),
      .all outer (.setOp .difference (.objects 1) heads heads) (eqn (.integer 16) 0),
      eqn (.arithmetic .subtract (.arithmetic .add (.integer 15) (.integer 1)) (.integer 1)) 15] do
    unless !(validateBounds support bounds [] .boolean e).isOk do
      throw (IO.userError "hidden overflow admitted")
  -- Scalar declarations independently enforce total, typed, functional values.
  for rows in [[], [(10, 3), (10, 2)], [(11, 3)], [(10, 16)]] do
    unless !({ candidate 1 with values := [[], [], rows] }.scalarFields 5 schema) do
      throw (IO.userError "malformed scalar payload accepted")
  let enforced : Module := ⟨schema, scalarFacts 2 5 ⟨2, 3⟩,
    ⟨.run, .truth, [⟨1, true⟩, ⟨2, true⟩, ⟨2, true⟩], 5⟩⟩
  let .ok enforced := Backend.Alloy.check enforced | throw (IO.userError "scalar fact admission")
  for (rows, expected) in [([(10, 2), (11, 3)], true),
      ([(10, 3), (11, 3)], false), ([(10, 1), (11, 3)], false)] do
    let .ok actual := evaluate enforced { candidate 2 with values := [[], [], rows] }
      | throw (IO.userError "scalar fact evaluation")
    unless actual == expected do throw (IO.userError "numeric range/identity enforcement")
  let scalarText := Text.serialize (rawScalar 1 2)
  for malformed in [scalarText.replace "cc3 : one Int" "cc7 : one Int",
      scalarText.replace "else ( -3 )" "else ( -2 )",
      scalarText.replace "( one ( ( cc0 ) . ( cc3 ) ) )" "( one ( ( cc4 ) . ( cc3 ) ) )"] do
    unless (Text.parse malformed).isNone do throw (IO.userError "malformed scalar conditional reconstructed")
  IO.println s!"{cases.length} source-constraint cases; 3 independent target cases; inherited attachments; overflow and scalar-payload mutations"

end ClaferCompiler.Tests.ExpressionEncodingNative
