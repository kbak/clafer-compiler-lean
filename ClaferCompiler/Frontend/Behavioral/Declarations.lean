module

public import ClaferCompiler.Frontend.Behavioral.Surface
public import ClaferCompiler.Frontend.BehavioralDeclarations
public import ClaferCompiler.IR.Behavioral.Surface

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral
open Resolution (Path errorAt)

/-- Adapt the accepted enum declaration constructors and retain finality in the
behavioral header. This adapter is used only for their declaration-only output. -/
def enumElement (final : Bool) : Frontend.Element → Element
  | .declaration h _ s => .declaration
      { structural := h, modifiers := if final then [{ h.name with text := "final" }] else [] } [] s
  | .constraint _ s => .property .constraint [] s

def enumElements (name : Name) (literals : List Name) (span : SourceSpan) : List Element :=
  enumElement false (BehavioralDeclarations.enumFamily name span) ::
    literals.map (fun literal => enumElement true (BehavioralDeclarations.enumLiteral name literal))

mutual
  /-- Source expansion rules retain all authored property bodies and headers.
  Only enum declarations expand; their literals acquire dynamic finality. -/
  inductive Expands : Bool → Element → List Element → Prop where
    | declaration (children : ExpandsList false xs ys) :
        Expands top (.declaration h xs span) [.declaration h ys span]
    | property : Expands top (.property kind bodies span) [.property kind bodies span]
    | enumeration (allowed : top = true) (nonempty : literals ≠ []) :
        Expands top (.enumeration name literals span) (enumElements name literals span)
  inductive ExpandsList : Bool → List Element → List Element → Prop where
    | nil : ExpandsList top [] []
    | cons (head : Expands top x ys) (tail : ExpandsList top xs zs) : ExpandsList top (x :: xs) (ys ++ zs)
end

-- [impl->req~compiler-behavioral-elaboration~1]
/-- Budget exhaustion is a diagnostic, never a truncated accepted tree. Parsed
documents have more source bytes than elements along any traversal branch. -/
def expandAt : Nat → (top : Bool) → (xs : List Element) → Except Diagnostic {ys // ExpandsList top xs ys} :=
  Nat.rec (fun _ xs => match xs with
      | [] => .ok ⟨[], .nil⟩
      | e :: _ => .error (errorAt ⟨"", e.span, 1, 1, 1⟩
          "behavioral.expansion-budget" "source expansion traversal exhausted"))
    (fun _ next top xs => do
      match hx : xs with
      | [] => return ⟨[], by simpa only [hx] using (ExpandsList.nil (top := top))⟩
      | x :: rest =>
        let head : {ys // Expands top x ys} ← match he : x with
          | .declaration h children span => do
            let children ← next false children
            pure ⟨[.declaration h children.val span], by simpa only [he] using (Expands.declaration (h := h) (span := span) children.property)⟩
          | .property kind bodies span => pure ⟨[.property kind bodies span], by simpa only [he] using (Expands.property (kind := kind) (bodies := bodies) (span := span))⟩
          | .enumeration name literals span => do
            if ht : top = true then
              if hn : literals = [] then
                throw (errorAt name "behavioral.enum-empty" "an enum requires a literal")
              else pure ⟨enumElements name literals span, by simpa only [he] using (Expands.enumeration (name := name) (span := span) ht hn)⟩
            else throw (errorAt name "behavioral.nested-enum" "enums must be top-level")
        let tail ← next top rest
        return ⟨head.val ++ tail.val, by simpa only [hx] using ExpandsList.cons head.property tail.property⟩)

/-- An empty constraint marker makes the structural resolver supply its integer
universe for initializer/transition expressions. It is appended, so authored
child indices remain unchanged. Its body is never interpreted as a property. -/
def expressionMarker (h : Header) (span : SourceSpan) : List Frontend.Element :=
  if h.initializer.isSome || h.transition.isSome then [.constraint [] span] else []

mutual
  inductive Projects : Element → Frontend.Element → Prop where
    | declaration (children : ProjectsList xs ys) : Projects (.declaration h xs span)
        (.declaration h.structural (ys ++ expressionMarker h span) span)
    | property : Projects (.property kind bodies span) (.constraint [] span)
  inductive ProjectsList : List Element → List Frontend.Element → Prop where
    | nil : ProjectsList [] []
    | cons (head : Projects x y) (tail : ProjectsList xs ys) : ProjectsList (x :: xs) (y :: ys)
end

-- [impl->req~compiler-behavioral-elaboration~1]
def projectAt : Nat → (xs : List Element) → Except Diagnostic {ys // ProjectsList xs ys} :=
  Nat.rec (fun xs => match xs with
      | [] => .ok ⟨[], .nil⟩
      | e :: _ => .error (errorAt ⟨"", e.span, 1, 1, 1⟩
          "behavioral.projection-budget" "declaration projection traversal exhausted"))
    (fun _ next xs => do
      match hx : xs with
      | [] => return ⟨[], by simpa only [hx] using ProjectsList.nil⟩
      | x :: rest =>
        let head : {y // Projects x y} ← match he : x with
          | .declaration h children span => do
            let children ← next children
            pure ⟨.declaration h.structural (children.val ++ expressionMarker h span) span,
              by simpa only [he] using (Projects.declaration (h := h) (span := span) children.property)⟩
          | .property kind bodies span => pure ⟨.constraint [] span, by simpa only [he] using (Projects.property (kind := kind) (bodies := bodies) (span := span))⟩
          | .enumeration name _ _ => throw (errorAt name
              "behavioral.unexpanded-enum" "enum expansion must precede structural binding")
        let tail ← next rest
        return ⟨head.val :: tail.val, by simpa only [hx] using ProjectsList.cons head.property tail.property⟩)

def children : Element → List Element
  | .declaration _ es _ => es
  | _ => []

def childrenAt (doc : Document) (path : Path) : Option (List Element) :=
  path.foldl (fun es k => do pure (children (← (← es)[k]?))) (some doc.elements)

def nodeAt (doc : Document) (path : Path) : Option Element := do
  let k ← path.getLast?
  (← childrenAt doc path.dropLast)[k]?

def headerAt (doc : Document) (path : Path) : Option Header := do
  match ← nodeAt doc path with
  | .declaration h _ _ => some h
  | _ => none

/-- Reserve the built-in integer domain before separately supplied scenarios are
elaborated. The empty marker uses the existing structural resolver rule and is
appended after authored elements, so it changes no authored declaration path.
Only the retained expanded document supplies behavioral properties. -/
def declarationDocument (source : Document) (elements : List Frontend.Element) : Frontend.Document :=
  ⟨source.file, source.source,
    elements ++ [.constraint [] ⟨source.file, source.source.utf8ByteSize, source.source.utf8ByteSize⟩]⟩

/-- The retained expanded document owns properties, initializers and transitions.
The projection and domain marker are inputs to structural binding only. -/
structure BoundDeclarations (source : Document) where
  expandedElements : List Element
  expansion : ExpandsList true source.elements expandedElements
  projectedElements : List Frontend.Element
  projection : ProjectsList expandedElements projectedElements
  resolved : BehavioralResolution.Elaborated (declarationDocument source projectedElements)

def BoundDeclarations.expanded {source : Document} (b : BoundDeclarations source) : Document :=
  ⟨source.file, source.source, b.expandedElements⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem BoundDeclarations.integerDomain {source : Document} (b : BoundDeclarations source) :
    ∃ d, (b.resolved.candidate.core.get d).origin = .integer := by
  have root := b.resolved.correspondence.2.2.2.1 b.resolved.candidate.core.root
  simp only at root
  apply root.2.2.2.2.2
  simp [Resolution.hasConstraints, declarationDocument, Resolution.constraintHere,
    Resolution.isDeclaration]

/-- One authored expression occurrence; superclass properties remain attached
to their authored declaration rather than copied onto each refinement. -/
structure PropertyOccurrence (k : Nat) where
  owner : Fin k
  kind : PropertyKind
  elementIndex : Nat
  bodyIndex : Nat
  expression : Expr
  span : SourceSpan

-- [impl->req~compiler-behavioral-elaboration~1]
def properties {source : Document} (b : BoundDeclarations source) :
    List (PropertyOccurrence b.resolved.count) :=
  (List.finRange b.resolved.count).flatMap fun owner =>
    let elements := if owner == b.resolved.candidate.core.root then b.expandedElements
      else ((b.resolved.candidate.paths[owner].bind (childrenAt b.expanded))).getD []
    elements.zipIdx.flatMap fun (element, elementIndex) =>
      match element with
      | .property kind bodies span => bodies.zipIdx.map fun (expression, bodyIndex) =>
          ⟨owner, kind, elementIndex, bodyIndex, expression, span⟩
      | _ => []

-- [impl->req~compiler-behavioral-elaboration~1]
def bindDeclarations (profile : String) (source : Document) :
    Except Diagnostic (BoundDeclarations source) := do
  if profile != IR.BehavioralStructural.profile then
    throw (errorAt ⟨"", ⟨source.file, 0, 0⟩, 1, 1, 1⟩ "behavioral.profile"
      "unsupported behavioral profile" .unsupported)
  let expanded ← expandAt (source.source.utf8ByteSize + 1) true source.elements
  let projected ← projectAt (source.source.utf8ByteSize + 1) expanded.val
  let resolved ← BehavioralResolution.elaborate profile (declarationDocument source projected.val)
  return ⟨expanded.val, expanded.property, projected.val, projected.property, resolved⟩

end ClaferCompiler.Frontend.Behavioral
