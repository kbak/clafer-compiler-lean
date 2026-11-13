module

public import ClaferCompiler.Frontend.Behavioral.Parser
public import ClaferCompiler.Frontend.Behavioral.Expressions
public import ClaferCompiler.Frontend.Behavioral.Warnings
public import ClaferCompiler.Frontend.Behavioral.Modifiers
public import ClaferCompiler.Frontend.Behavioral.Headers
public import ClaferCompiler.Frontend.Behavioral.InitializerBounds
public import ClaferCompiler.Frontend.Behavioral.TemporalSelection
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
    (p : BoundHeaderProperty d.resolved.candidate.core) : SetExpr d.resolved.count n :=
  if (d.resolved.candidate.core.get p.declaration).parent.isSome then
    .thisStep (.child p.declaration) else .extent p.declaration

/-- Classify authored `:=` independently of temporal selection. `=` retains
its aggregate every-live rule. Unsupported admission never changes a clock. -/
def InitializerClassification {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) (header : Header) (op : Token)
    (rhs : Expression.Collection d.resolved.count 0) (clock : Option Initializers.Clock) : Prop :=
  (op.text = "=" ∧ clock = none) ∨ (op.text = ":=" ∧ ∃ c,
    Initializers.classify (Initializers.metadata d p.declaration header)
      (Initializers.scalarAt d.resolved.candidate.core (source.source.utf8ByteSize + 1) rhs) = .ok c ∧ clock = some c)

def initializerSingle (clock : Option Initializers.Clock) (temporal : Bool) : Bool :=
  temporal && clock == some .instanceBirth

/-- Resolved runtime expansion. The closed RHS type prevents generated capture
slots from becoming authored lexical bindings. -/
-- [impl->req~compiler-behavioral-elaboration~1]
def initializerFormula (declaration : Fin k) (parented referenced temporal : Bool)
    (clock : Option Initializers.Clock) (rhs : Expression.Collection k 0) : Expression.Formula k 0 :=
  let heads : SetExpr k 0 := if parented then .thisStep (.child declaration) else .extent declaration
  let heads' : SetExpr k 1 := if parented then .thisStep (.child declaration) else .extent declaration
  let left := if initializerSingle clock temporal then .var 0 else heads'
  let targets := if referenced then SetExpr.step (.deref declaration) left else left
  let equation := FormulaF.atom (Expression.Atom.equalClosed targets rhs)
  if initializerSingle clock temporal then
    let original : SetExpr k 1 := if parented then .thisStep .parent else .root
    .atom (.inContext heads
      (.initially (.quant .all (.set .this) (.atom (.inContext original equation)))))
  else
    let guarded := FormulaF.quant .all (.set heads) equation
    if temporal && clock.isSome then .initially guarded else guarded

-- [impl->req~compiler-behavioral-elaboration~1]
def initializerBody {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) (clock : Option Initializers.Clock)
    (rhs : Expression.Collection d.resolved.count 0) : Expression.Formula d.resolved.count 0 :=
  initializerFormula p.declaration (d.resolved.candidate.core.get p.declaration).parent.isSome
    (IR.BehavioralSupport.referenceView d.resolved.admitted p.declaration).isSome source.temporal clock rhs

inductive HeaderElaborates {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) : Expression.Formula d.resolved.count 0 → Prop where
  | transition (kind : p.kind = .transition)
      (body : Expressions.FormulaElaborates d.resolved.admitted p.owner p.expression formula) : HeaderElaborates d p formula
  | initializer {header : Header} (kind : p.kind ≠ .transition)
      (origin : d.resolved.candidate.paths[p.declaration].bind (headerAt d.expanded) = some header)
      (authored : header.initializer = some (op, rhs))
      (provenance : Initializers.Provenance d p.declaration header)
      (right : Expressions.Elaborates d.resolved.admitted p.owner #v[] none rhs value)
      (target : ValueRules.Target d.resolved.admitted value converted)
      (heads : ValueRules.Heads converted type collection)
      (classification : InitializerClassification d p header op collection clock)
      (equation : ValueRules.Binary d.resolved.admitted "="
        (.collection (.objects p.declaration) (.set (initializerHeads d p))) value eqn)
      (boolean : ValueRules.Boolean eqn formula) :
      HeaderElaborates d p (initializerBody d p clock collection)

def classifyInitializer {source : Document} (d : BoundDeclarations source)
    (p : BoundHeaderProperty d.resolved.candidate.core) (header : Header) (op : Token)
    (rhs : Expression.Collection d.resolved.count 0) :
    Except Diagnostic {clock // InitializerClassification d p header op rhs clock} := do
  if constant : op.text = "=" then
    return ⟨none, Or.inl ⟨constant, rfl⟩⟩
  else if initial : op.text = ":=" then
    match classified : Initializers.classify (Initializers.metadata d p.declaration header)
        (Initializers.scalarAt d.resolved.candidate.core (source.source.utf8ByteSize + 1) rhs) with
    | .ok clock => return ⟨some clock, Or.inr ⟨initial, clock, classified, rfl⟩⟩
    | .error error =>
      let (code, message, category) := match error with
        | .invalidMultiplicity => ("behavioral.initializer-multiplicity", "Invalid initializer multiplicity.", IR.Structural.Category.malformed)
        | .parentlessMultiplicity => ("behavioral.initializer-parentless-multiplicity", "Parentless abstract initializers support omitted or explicitly unrestricted multiplicity only.", IR.Structural.Category.unsupported)
        | .scalarNotEstablished => ("behavioral.initializer-scalar", "The supported rules cannot establish an at-most-one RHS bound for this abstract initializer.", IR.Structural.Category.unsupported)
      throw (Resolution.errorAt op code message category)
  else throw (Resolution.errorAt op "behavioral.initializer-token" "Invalid initializer token.")

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
      | some (op, rhs) =>
        if provenance : Initializers.Provenance d p.declaration header then
          let right ← Expressions.certifiedAt source d.resolved.admitted p.owner budget #v[] none rhs
          let converted ← (MonadAttach.attach (Values.target d.resolved.admitted right.val)).mapError
            (Expressions.failure source rhs)
          let collection ← (MonadAttach.attach (Values.heads converted.val)).mapError
            (Expressions.failure source rhs)
          let clock ← classifyInitializer d p header op collection.val.2
          let left := Values.Value.collection (.objects p.declaration) (.set (initializerHeads d p))
          let equation ← (MonadAttach.attach (Values.binary d.resolved.admitted "=" left right.val)).mapError
            (Expressions.failure source p.expression)
          let boolean ← (Expressions.booleanCertified equation.val).mapError (Expressions.failure source p.expression)
          return ⟨initializerBody d p clock.val collection.val.2,
            .initializer hk hh hi provenance right.property (ValueRules.target_sound _ converted.property)
              (ValueRules.heads_sound collection.property) clock.property
              (ValueRules.binary_sound equation.property) boolean.property⟩
        else throw (Expressions.failure source rhs "behavioral.initializer-provenance")

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

/-- Reporting is additive: the existing parsed-model API and error type stay
unchanged. Warnings are available only after the entire model elaborates. -/
structure Report where
  model : ParsedModel
  warnings : List Warning

-- [impl->req~compiler-diagnostics~1]
def parseAndElaborateReport (profile file source : String) : Except Diagnostic Report := do
  let model ← parseAndElaborate profile file source
  return ⟨model, Warnings.document model.source⟩

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
