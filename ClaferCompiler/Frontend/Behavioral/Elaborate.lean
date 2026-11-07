module

public import ClaferCompiler.Frontend.Behavioral.Parser
public import ClaferCompiler.Frontend.Behavioral.Expressions
public import ClaferCompiler.Frontend.Behavioral.Modifiers
public import ClaferCompiler.Frontend.Behavioral.Headers
public import ClaferCompiler.IR.Behavioral.Properties

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral
open IR.Behavioral

/-- The vectors are indexed by the full source inventories, so successful
elaboration cannot omit a property or conflate assertions with constraints. -/
structure Elaborated (source : Document) where
  declarations : BoundDeclarations source
  modifiers : BoundModifiers declarations
  bodies : Vector (Expression.Formula declarations.resolved.count 0) (properties declarations).length
  headers : List (BoundHeaderProperty declarations.resolved.candidate.core)
  headerBodies : Vector (Expression.Formula declarations.resolved.count 0) headers.length

-- [impl->req~compiler-behavioral-elaboration~1]
def Elaborated.authored {source : Document} (e : Elaborated source) (kind : PropertyKind) :
    List (Properties.Constraint e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count)) :=
  (List.finRange (properties e.declarations).length).filterMap fun i =>
    let p := (properties e.declarations)[i]
    if p.kind = kind then some ⟨p.owner, e.bodies[i], p.span⟩ else none

def Elaborated.generated {source : Document} (e : Elaborated source) :
    List (Properties.Constraint e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count)) :=
  (List.finRange e.headers.length).map fun i =>
    ⟨e.headers[i].owner, e.headerBodies[i], e.headers[i].span⟩

def Elaborated.model {source : Document} (e : Elaborated source) :
    Properties.Model e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count) :=
  ⟨e.declarations.resolved.admitted, e.modifiers.declared,
    e.authored .constraint ++ e.generated, e.authored .assertion⟩

/-- Generated heads retain the declaration of origin; source name lookup is
used only for the initializer's authored right-hand side. -/
def initializerHeads {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) : SetExpr d.resolved.count 0 :=
  if (d.resolved.candidate.core.get p.declaration).parent.isSome then
    .thisStep (.child p.declaration) else .extent p.declaration

inductive HeaderElaborates {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) : Expression.Formula d.resolved.count 0 → Prop where
  | transition (kind : p.kind = .transition)
      (body : Expressions.FormulaElaborates d.resolved.admitted p.owner p.expression formula) : HeaderElaborates d p formula
  | initializer {header : Header} (kind : p.kind ≠ .transition)
      (origin : d.resolved.candidate.paths[p.declaration].bind (headerAt d.expanded) = some header)
      (authored : header.initializer = some (op, rhs))
      (right : Expressions.Elaborates d.resolved.admitted p.owner #v[] none rhs value)
      (equation : ValueRules.Binary d.resolved.admitted "="
        (.collection (.objects p.declaration) (.set (initializerHeads d p))) value eqn)
      (boolean : ValueRules.Boolean eqn formula) :
      HeaderElaborates d p (.implies (Values.present (.set (initializerHeads d p))) formula)

-- [impl->req~compiler-behavioral-elaboration~1]
-- [proof->req~compiler-behavioral-elaboration~1]
def elaborateHeaderCertified {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) :
    Except Diagnostic {formula // HeaderElaborates d p formula} := do
  let budget := source.source.utf8ByteSize + 1
  if hk : p.kind = .transition then
    let body ← Expressions.elaborateCertified source d.resolved.admitted p.owner budget p.expression
    return ⟨body.val, .transition hk body.property⟩
  else
    match hh : d.resolved.candidate.paths[p.declaration].bind (headerAt d.expanded) with
    | none => throw (Expressions.failure source p.expression "behavioral.initializer-origin")
    | some header => match hi : header.initializer with
      | none => throw (Expressions.failure source p.expression "behavioral.initializer-origin")
      | some (_, rhs) =>
        let right ← Expressions.certifiedAt source d.resolved.admitted p.owner budget #v[] none rhs
        let left := Values.Value.collection (.objects p.declaration) (.set (initializerHeads d p))
        let equation ← (MonadAttach.attach (Values.binary d.resolved.admitted "=" left right.val)).mapError
          (Expressions.failure source p.expression)
        let boolean ← (Expressions.booleanCertified equation.val).mapError (Expressions.failure source p.expression)
        return ⟨.implies (Values.present (.set (initializerHeads d p))) boolean.val,
          .initializer hk hh hi right.property (ValueRules.binary_sound equation.property) boolean.property⟩

def elaborateHeader {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) : Except Diagnostic (Expression.Formula d.resolved.count 0) :=
  (elaborateHeaderCertified d p).map Subtype.val

-- [proof->req~compiler-behavioral-elaboration~1]
theorem elaborateHeader_sound (h : elaborateHeader d p = .ok formula) : HeaderElaborates d p formula := by
  obtain ⟨result, _, rfl⟩ := Traversal.map_success h
  exact result.property

-- [impl->req~compiler-behavioral-elaboration~1]
def elaborate (profile : String) (source : Document) : Except Diagnostic (Elaborated source) := do
  let d ← bindDeclarations profile source
  let modifiers ← bindModifiers d
  let bodies ← Vector.ofFnM fun i : Fin (properties d).length =>
    let p := (properties d)[i]
    Expressions.elaborate source d.resolved.admitted p.owner (source.source.utf8ByteSize + 1) p.expression
  let headers ← headerProperties d
  let headerBodies ← Vector.ofFnM fun i : Fin headers.length =>
    elaborateHeader d headers[i]
  return ⟨d, modifiers, bodies, headers, headerBodies⟩

structure ParsedModel where
  source : Document
  elaborated : Elaborated source

-- [impl->req~compiler-behavioral-frontend~1]
def parseAndElaborate (profile file source : String) : Except Diagnostic ParsedModel := do
  let doc ← parseBehavioral profile file source
  return ⟨doc, ← elaborate profile doc⟩

/-- An assertion index selects its full authored property. The request never
source-negates its body; counterexamples negate complete property satisfaction. -/
def Elaborated.check {source : Document} (e : Elaborated source) (index : Nat) :
    Except Diagnostic (Properties.Request e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count)) :=
  if h : index < e.model.assertions.length then .ok ⟨e.model, .check ⟨index, h⟩⟩
  else .error (Resolution.errorAt ⟨"", ⟨source.file, 0, 0⟩, 1, 1, 1⟩
    "behavioral.assertion-index" "No assertion at this index.")

/-- Caller-selected scenario attachment is a bounded declaration ID from the
model. Its source contains ordinary bracketed constraints and explicit anchors.
No implicit anchor or declaration copying changes the scenario's meaning. -/
structure ScenarioSource (k : Nat) where
  owner : Fin k
  document : Document

-- [impl->req~compiler-behavioral-elaboration~1]
def Elaborated.run {source : Document} (e : Elaborated source)
    (scenarios : List (ScenarioSource e.declarations.resolved.count)) :
    Except Diagnostic (Properties.Request e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count)) := do
  let lists ← scenarios.mapM fun scenario => do
    let lists ← scenario.document.elements.mapM fun element => do
      match element with
      | .property .constraint bodies span => bodies.mapM fun body => do
          let formula ← Expressions.elaborate scenario.document e.declarations.resolved.admitted
            scenario.owner (scenario.document.source.utf8ByteSize + 1) body
          return (⟨scenario.owner, formula, span⟩ : Properties.Constraint _ (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count))
      | .property .assertion _ span => throw (Constraints.errorAt
          ⟨scenario.document.file, scenario.document.source, []⟩ span "behavioral.scenario-assertion"
          "A scenario contains additional constraints; assertions require a check request.")
      | element => throw (Constraints.errorAt ⟨scenario.document.file, scenario.document.source, []⟩
          element.span "behavioral.scenario-declaration" "Declare scenario objects in the model." .unsupported)
    return lists.flatten
  return ⟨e.model, .run lists.flatten⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem authored_owner {source : Document} (e : Elaborated source) (kind : PropertyKind)
    (p : Properties.Constraint e.declarations.resolved.count (Expression.Atom e.declarations.resolved.count) (Expression.Collection e.declarations.resolved.count))
    (hp : p ∈ e.authored kind) :
    ∃ i : Fin (properties e.declarations).length,
      (properties e.declarations)[i].kind = kind ∧ p.owner = (properties e.declarations)[i].owner ∧
      p.body = e.bodies[i] ∧ p.source = (properties e.declarations)[i].span := by
  simp only [Elaborated.authored, List.mem_filterMap] at hp
  obtain ⟨i, _, hi⟩ := hp
  split at hi
  · rename_i h
    cases Option.some.inj hi
    exact ⟨i, h, rfl, rfl, rfl⟩
  · contradiction

end ClaferCompiler.Frontend.Behavioral
