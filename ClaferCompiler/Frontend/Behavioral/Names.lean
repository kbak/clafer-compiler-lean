module

public import ClaferCompiler.Frontend.Behavioral.NameRules

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Names
open IR.Behavioral Values

structure Navigation (v : IR.BehavioralStructural.Validated k) (d : Fin k)
    (a : Expression.Collection k n) (name : String) where
  type : Ty k
  term : Expression.Collection k n
  derivation : Navigate v d a name type term

-- [proof->req~compiler-behavioral-elaboration~1]
def navigation (v : IR.BehavioralStructural.Validated k) : Nat →
    (d : Fin k) → (a : Expression.Collection k n) → (name : String) → Except String (Navigation v d a name) :=
  Nat.rec (fun _ _ _ => .error "behavioral.navigation-cycle") (fun _ next d a name => do
    let c := v.core.structural
    if hn : name = "parent" then
      return ⟨parentType v d, navigateCollection .parent a, by subst name; exact .parent⟩
    if hn : name = "dref" then
      match hr : IR.BehavioralSupport.referenceView v d with
      | some r => return ⟨classType v r.target, navigateCollection (.deref d) a,
          by subst name; exact .dereference hr⟩
      | none => throw "behavioral.not-reference"
    if Resolution.integerName name then throw "behavioral.infinite-primitive-extent"
    if ho : name ≠ "parent" ∧ name ≠ "dref" then
      for depth in List.range (k + 1) do
        for p in List.finRange k do
          for y in List.finRange k do
            if hf : Constraints.Field c d name depth p y then
              return ⟨classType v y, navigateCollection (.child y) a, .field ho hf⟩
      if hf : Constraints.HasField c d name then throw "behavioral.ambiguous-navigation"
      else
        match hr : IR.BehavioralSupport.referenceView v d with
        | some r =>
          let b ← next r.target (navigateCollection (.deref d) a) name
          return ⟨b.type, b.term, .reference ho hf hr b.derivation⟩
        | none => throw "behavioral.missing-navigation"
    throw "behavioral.missing-navigation")

def mixedAt (v : IR.BehavioralStructural.Validated k) (a : Expression.Collection k n) (name : String) :
    (fuel : Nat) → (ds : List (Fin k)) → ds.length < fuel →
      Except String {out // Pieces v a name ds out} :=
  Nat.rec (fun _ h => False.elim (Nat.not_lt_zero _ h)) (fun _ next ds h =>
    match ds with
    | [] => .ok ⟨[], .nil⟩
    | d :: ds => do
      if hp : Applicable v d name then
        let head ← navigation v (k + 1) d (.ofType d a) name
        let tail ← next ds (by simp only [List.length_cons] at h; omega)
        return ⟨(head.type, head.term) :: tail.val, .cons hp head.derivation tail.property⟩
      else
        let tail ← next ds (by simp only [List.length_cons] at h; omega)
        return ⟨tail.val, .skip hp tail.property⟩)

structure ScopeEntry (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (n : Nat) where
  depth : Nat
  declaration : Fin k
  term : SetExpr k n
  derivation : ScopePath v owner depth declaration term

def scopes (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (n : Nat) : List (ScopeEntry v owner n) :=
  (List.range k).foldl (fun (acc : List (ScopeEntry v owner n)) _ =>
    match acc.getLast? with
    | none => acc
    | some p => match hp : (v.core.structural.get p.declaration).parent with
      | none => acc
      | some d => acc ++ [⟨p.depth + 1, d, navigateSet .parent p.term, .parent p.derivation hp⟩])
    [⟨0, owner, .this, .here⟩]

structure BoundName (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (Γ : Context k n)
    (cursor : Option (Value k n)) (name : String) where
  value : Value k n
  derivation : Name v owner Γ cursor name value

-- [impl->req~compiler-behavioral-elaboration~1]
def absolute (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (Γ : Context k n)
    (name : String) : Except String (BoundName v owner Γ none name) := do
  let c := v.core.structural
  if hn : name = "this" then
    return ⟨.collection (.objects owner) (.set .this), by subst name; exact .this⟩
  if hn : name = "root" then
    return ⟨.collection (.objects c.root) (.set .root), by subst name; exact .root⟩
  if hn : name = "parent" ∨ name = "dref" then
    let b ← navigation v (k + 1) owner (.set .this) name
    return ⟨.collection b.type b.term, .special hn b.derivation⟩
  if let some found := Binders.lookup Γ name then
    return ⟨.collection found.type (.set (.var found.index)), .local found⟩
  if hl : NoLocal Γ name then
    if hn : name ≠ "this" ∧ name ≠ "root" ∧ name ≠ "parent" ∧ name ≠ "dref" then
      for p in scopes v owner n do
        if hp : p.declaration ≠ c.root then
          if hc : Constraints.NoContext c owner name p.depth then
            if hf : Constraints.HasField c p.declaration name then
              let b ← navigation v (k + 1) p.declaration (.set p.term) name
              return ⟨.collection b.type b.term, .contextual hl hn p.derivation hp hc hf b.derivation⟩
      if hc : Constraints.NoContext c owner name (k + 1) then
        if ht : HasTarget v owner name then
          match hr : IR.BehavioralSupport.referenceView v owner with
          | some r =>
            have reachable : Reachable v r.target name := by simpa only [HasTarget, hr] using ht
            let b ← navigation v (k + 1) r.target (.set (navigateSet (.deref owner) .this)) name
            return ⟨.collection b.type b.term, .target hl hn hc hr reachable b.derivation⟩
          | none => throw "behavioral.missing-navigation"
        else
          for d in List.finRange k do
            if hg : Constraints.Global c name d then
              return ⟨.collection (classType v d) (.set (.extent d)), .global hl hn hc ht hg⟩
  if c.declarations.any (fun d => d.name == name) then throw "behavioral.ambiguous-name"
  throw "behavioral.unknown-name"

-- [impl->req~compiler-behavioral-elaboration~1]
def name (v : IR.BehavioralStructural.Validated k) (owner : Fin k) (Γ : Context k n)
    (cursor : Option (Value k n)) (text : String) : Except String (BoundName v owner Γ cursor text) := do
  if hn : text = "noclafer" then
    match hc : cursor with
    | none => return ⟨.collection .empty (.set .empty), by simpa only [hc, hn] using (Name.empty (v := v) (owner := owner) (Γ := Γ))⟩
    | some (.collection type a) => return ⟨.collection .empty (.inter a (.set .empty)),
        by simpa only [hc, hn] using (Name.emptyRelative (v := v) (owner := owner) (Γ := Γ) (type := type) (a := a))⟩
    | some _ => throw "behavioral.navigation-type"
  if Resolution.integerName text then throw "behavioral.infinite-primitive-extent"
  match hcursor : cursor with
  | some (.collection (.objects d) a) =>
    let b ← navigation v (k + 1) d a text
    return ⟨.collection b.type b.term, by simpa only [hcursor] using (Name.relative (owner := owner) (Γ := Γ) b.derivation)⟩
  | some (.collection (.mixed ds) a) =>
    let pieces ← mixedAt v a text (ds.length + 1) ds (by omega)
    if he : pieces.val ≠ [] then
      return ⟨.collection (classUnion v (pieces.val.flatMap (classes v ·.1)))
        (pieces.val.foldl (fun acc p => .union acc p.2) (.set .empty)), by simpa only [hcursor] using (Name.mixed (owner := owner) (Γ := Γ) pieces.property he)⟩
    throw "behavioral.missing-navigation"
  | some (.collection .empty a) =>
    if hn : text = "parent" then
      return ⟨.collection .empty (navigateCollection .parent a), by subst text; simpa only [hcursor] using (Name.emptyParent (v := v) (owner := owner) (Γ := Γ) (a := a))⟩
    if hn : text = "dref" then
      return ⟨.collection .empty a, by subst text; simpa only [hcursor] using (Name.emptyDereference (v := v) (owner := owner) (Γ := Γ) (a := a))⟩
    for d in List.finRange k do
      if hd : (v.core.structural.get d).name = text ∧ (v.core.structural.get d).origin = .user then
        return ⟨.collection .empty (navigateCollection (.child d) a), by simpa only [hcursor] using (Name.emptyField (owner := owner) (Γ := Γ) (a := a) hd.1 hd.2)⟩
    throw "behavioral.unknown-name"
  | some _ => throw "behavioral.navigation-type"
  | none =>
    let b ← absolute v owner Γ text
    return ⟨b.value, by simpa only [hcursor] using b.derivation⟩

end ClaferCompiler.Frontend.Behavioral.Names
