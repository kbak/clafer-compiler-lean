module

public import ClaferCompiler.Frontend.Resolve
public import ClaferCompiler.IR.BehavioralStructural

@[expose] public section
namespace ClaferCompiler.Frontend.BehavioralResolution
open Resolution IR.Structural

-- [impl->req~compiler-behavioral-structural-bridge~1]
/-- The selected behavioral type policy keeps unique lexical/global lookup,
including forward references, and permits ordinary and nested superclasses. -/
def SuperRule (doc : Document) (c : Candidate n) (path : Path)
    (name : Option Name) (target : Option (Fin n)) : Prop :=
  match name, target with
  | none, none => True
  | some name, some j => integerName name.text = false ∧
      Resolves doc c path.dropLast false name.text j ∧ (c.core.get j).origin = .user
  | _, _ => False

instance (doc : Document) (c : Candidate n) (p : Path) (name : Option Name) (j : Option (Fin n)) :
    Decidable (SuperRule doc c p name j) := by unfold SuperRule; split <;> infer_instance

/-- Independent source/table correspondence. Only the nested-abstract and
supertype domains differ from the selected static source rule. -/
def SourceRow (doc : Document) (c : Candidate n) (i : Fin n) : Prop :=
  match c.paths[i], c.header doc i with
  | some path, some h =>
    let d := c.core.get i
    let parent := d.parent.map c.core.get
    let super := d.super.map (fun j => c.groups[j])
    d.origin = .user ∧ path ≠ [] ∧ reserved h.name.text = false ∧
    d.name = h.name.text ∧ d.source = (nodeAt doc path).map Element.span ∧
    d.authored = some ⟨h.abstractToken.isSome, h.cardinality.map cardBounds,
      h.group.map (fun g => (authoredGroup g).range)⟩ ∧
    (if path.length = 1 then
      d.parent = (if h.abstractToken.isSome then none else some c.core.root)
     else ∃ p : Fin n, d.parent = some p ∧ c.paths[p] = some path.dropLast) ∧
    SuperRule doc c path (h.super.orElse (fun _ => if h.useToken.isSome then some h.name else none)) d.super ∧
    ReferenceRule doc c path h.reference d.reference ∧
    c.groups[i] = (h.group.map authoredGroup).getD (super.getD (.bounds {})) ∧
    d.groupBounds = c.groups[i].range ∧
    d.localBounds = (h.cardinality.map cardBounds).getD
      ((d.parent.map (fun p => c.groups[p].childDefault)).getD ⟨1, .finite 1⟩) ∧
    d.isAbstract = (h.abstractToken.isSome || (parent.map (·.isAbstract)).getD false) ∧
    CoversChildren doc c path
  | _, _ => False

instance (doc : Document) (c : Candidate n) (i : Fin n) : Decidable (SourceRow doc c i) := by
  unfold SourceRow; split <;> infer_instance

def Elaboration (doc : Document) (c : Candidate n) : Prop :=
  c.core.root.val = 0 ∧
  (∀ i : Fin n, (c.core.get i).id = i.val) ∧
  CoversChildren doc c [] ∧
  (∀ i : Fin n, if i = c.core.root then
    c.paths[i] = none ∧ (c.core.get i).name = "Sing" ∧
      c.groups[i] = .bounds {} ∧ (c.core.get i).groupBounds = {} ∧
      (c.core.get i).localBounds = ⟨1, .finite 1⟩ ∧
      (hasConstraints doc c = true → ∃ d, (c.core.get d).origin = .integer)
   else if (c.core.get i).origin = .integer then
    c.paths[i] = none ∧ (c.core.get i).name = "int" ∧
      (c.core.get i).parent = some c.core.root ∧ (c.core.get i).super = none ∧
      (c.core.get i).reference = .basic ∧ (c.core.get i).isAbstract = false ∧
      c.groups[i] = .bounds {} ∧ (c.core.get i).groupBounds = {} ∧
      (c.core.get i).localBounds = {} ∧ i.val + 1 = n ∧
      ((∃ j : Fin n, (c.core.get j).reference.target = some i) ∨ hasConstraints doc c = true)
   else SourceRow doc c i) ∧
  (∀ i j : Fin n, PathOrder c i j)

set_option synthInstance.maxSize 1024 in
instance (doc : Document) (c : Candidate n) : Decidable (Elaboration doc c) := by
  unfold Elaboration; infer_instance

def core (doc : Document) (c : Candidate n) : IR.BehavioralStructural.Core n :=
  ⟨c.core, Vector.ofFn (explicitAbstract doc c), c.groups⟩

structure Elaborated (doc : Document) where
  count : Nat
  candidate : Candidate count
  correspondence : Elaboration doc candidate
  admitted : IR.BehavioralStructural.Validated count
  sameCore : admitted.core = core doc candidate

/-- Explicit profile selection precedes all work. Parsing full behavioral syntax
belongs to the behavioral frontend; this API accepts the authored declaration tree. -/
def elaborate (selectedProfile : String) (doc : Document) : Except Diagnostic (Elaborated doc) := do
  if selectedProfile != IR.BehavioralStructural.profile then
    throw (errorAt (startToken doc) "behavioral.profile" "unsupported behavioral profile" .unsupported)
  let (raw, paths, groups, realized) ← prepareWith true doc
  let c ← (bindCandidate raw paths groups realized).mapError
    (fun e => errorAt (startToken doc) e.code "invalid resolved table" e.category)
  if h : Elaboration doc c then
    let m := core doc c
    if hs : IR.BehavioralStructural.supported m then
      let a := IR.BehavioralStructural.analyze m
      if hc : IR.BehavioralStructural.checks m c.certificate a then
        return ⟨_, c, h, ⟨m, c.certificate, a, hc, hs⟩, rfl⟩
      else throw (errorAt (startToken doc) "behavioral.structural-admission" "invalid behavioral declaration relationships")
    else throw (errorAt (startToken doc) "behavioral.primitive-domain" "unsupported primitive domain" .unsupported)
  else throw (errorAt (startToken doc) "behavioral.correspondence" "declarative elaboration validation failed")

end ClaferCompiler.Frontend.BehavioralResolution
