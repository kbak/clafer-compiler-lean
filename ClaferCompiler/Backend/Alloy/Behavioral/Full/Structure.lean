module

public import ClaferCompiler.IR.BehavioralStructural
public import ClaferCompiler.IR.Behavioral.Trace
public import ClaferCompiler.Backend.Alloy.Temporal.Syntax

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full
open IR.BehavioralStructural

-- [impl->req~compiler-trace-assurance~1]
/-- Each signature denotes one exact direct type. Ancestor views are unions,
so concrete supers do not inherit Alloy's abstract-signature restrictions. -/
def signatureId (d : Fin k) : Nat := 1 + d.val

def directPool (d : Fin k) : Temporal.Rel := .sig (signatureId d)

def union (rs : List Temporal.Rel) : Temporal.Rel :=
  rs.foldl Temporal.Rel.union (.empty .unary)

def integerDeclaration (v : Validated k) (d : Fin k) : Bool :=
  (v.core.structural.get d).origin == .integer

/-- Completion of a finite primitive observation uses the frontend's primitive
shape. General structural admission alone does not imply these restrictions. -/
def PrimitiveShape (v : Validated k) : Prop :=
  ∀ p, (v.core.structural.get p).origin = .integer →
    v.core.authoredAbstract[p] = false ∧
    (v.core.structural.get p).localBounds = {} ∧
    (v.core.structural.get p).groupBounds = {} ∧
    (v.core.structural.get v.core.structural.root).groupBounds = {} ∧
    (∀ d, (v.core.structural.get d).super ≠ some p) ∧
    (∀ d, (v.core.structural.get d).parent ≠ some p)

instance (v : Validated k) : Decidable (PrimitiveShape v) := by
  unfold PrimitiveShape; infer_instance

def pool (v : Validated k) (d : Fin k) : Temporal.Rel :=
  if integerDeclaration v d then .ints else
    union (((List.finRange k).filter fun c => d ∈ v.analysis.ancestors[c]).map directPool)

def root (v : Validated k) : Temporal.Rel := directPool v.core.structural.root
def parent : Temporal.Rel := .field 0
def live (v : Validated k) : Temporal.Rel := .join (root v) (.field 1)
/-- Primitive integers are always present when an expression captures one. -/
def observedLive (v : Validated k) : Temporal.Rel := .union (live v) .ints
def head (v : Validated k) (d : Fin k) : Temporal.Rel :=
  if integerDeclaration v d then .ints else .inter (pool v d) (live v)
def rawDeref (d : Fin k) : Temporal.Rel := .field (2 + d.val)

def declaredDeref (v : Validated k) (d : Fin k) : Temporal.Rel :=
  match (v.core.structural.get d).reference.target with
  | some target => if integerDeclaration v target then
      .inter (.values 0) (.product (head v d) .ints) else rawDeref d
  | none => rawDeref d

/-- An inherited view follows its nearest declared reference owner and retains
the original occurrence as the first column. -/
def deref (v : Validated k) (d : Fin k) : Temporal.Rel :=
  match v.analysis.referenceOwners[d] with
  | none => .empty .binary
  | some owner => .inter (declaredDeref v owner)
      (.product (head v d) (.union (.sig 0) .ints))

def contains (v : Validated k) (d : Fin k) : Temporal.Rel :=
  match (v.core.structural.get d).parent with
  | none => .empty .binary
  | some _ => if integerDeclaration v d then .product (root v) .ints else
      .inter (.transpose parent) (.product (live v) (head v d))

def step (v : Validated k) : IR.Behavioral.Step k → Temporal.Rel
  | .parent => .union (.inter parent (.product (.sig 0) (live v)))
      (.product .ints (root v))
  | .child d => contains v d
  | .deref d => deref v d

-- [impl->req~compiler-trace-assurance~1]
/-- All direct-type signatures are disjoint children of the common inventory.
Authored abstractness is enforced separately; effective abstractness does not
erase ordinary inherited field occurrences. -/
def schema (_v : Validated k) : Temporal.Schema where
  declarations := {
    signatures := { isAbstract := true, scalar := true } ::
      (List.finRange k).map (fun _ => { parent := some 0 })
    fields := [{ owner := 0, target := 0 }, { owner := 0, target := 0 }] ++
      (List.finRange k).map (fun _ => { owner := 0, target := 0 }) }
  mutableSignatures := List.replicate (k + 1) false
  mutableFields := [false, true] ++ List.replicate k true

def interval (b : IR.Structural.Bounds) (r : Temporal.Rel) : Temporal.Formula :=
  let lower := if b.lower == 0 then Temporal.Formula.truth
    else .compare .le (.literal (Int.ofNat b.lower)) (.count r)
  let upper := match b.upper with
    | .unbounded => Temporal.Formula.truth
    | .finite n => .compare .le (.count r) (.literal (Int.ofNat n))
  .binary .conj lower upper

/-- Effective groups count the union of head fibers, including ordinary inherited
fields. Overlapping subtype views and equal reference targets never add counts. -/
def childHeads (v : Validated k) (d : Fin k) : Temporal.Rel :=
  union ((childDeclarations v d).map fun c => .join (.var 0) (contains v c))

def setKey (v : Validated k) (d p : Fin k) : Temporal.Formula :=
  .all (head v p)
    (.all (.join (.var 0) (contains v d))
      (.all (.join (.var 1) (contains v d))
        (.binary .implies
          (.equal (.join (.var 1) (deref v d)) (.join (.var 0) (deref v d)))
          (.equal (.var 1) (.var 0)))))

-- [impl->req~compiler-trace-assurance~1]
def identityFacts (v : Validated k) : List Temporal.Formula :=
  [.mult .one (root v),
   .equal (.join (root v) parent) (.empty .unary),
   .all (.diff (.sig 0) (root v)) (.mult .one (.join (.var 0) parent))] ++
  (List.finRange k).flatMap fun d =>
    if v.core.authoredAbstract[d] || integerDeclaration v d then
      [.equal (directPool d) (.empty .unary)]
    else match (v.core.structural.get d).parent with
    | none => []
    | some p => [.all (directPool d) (.subset (.join (.var 0) parent) (pool v p))]

/-- Raw reference rows are checked before inherited views restrict their domain.
Thus a dangling or mistyped raw row cannot disappear during projection. -/
def referenceFacts (v : Validated k) (d : Fin k) : List Temporal.Formula :=
  match (v.core.structural.get d).reference.target with
  | none => [.equal (rawDeref d) (.empty .binary)]
  | some target =>
    (if integerDeclaration v target then [.equal (rawDeref d) (.empty .binary)] else []) ++
    [.subset (declaredDeref v d) (.product (head v d) (head v target)),
     .all (head v d) (.mult .one (.join (.var 0) (declaredDeref v d)))]

def declarationFacts (v : Validated k) (d : Fin k) : List Temporal.Formula :=
  let row := v.core.structural.get d
  let group := if v.core.authoredAbstract[d] then [] else
    [.all (head v d) (interval row.groupBounds (childHeads v d))]
  let containment := match row.parent with
    | none => []
    | some p =>
      [.subset (contains v d) (.product (head v p) (head v d)),
       .all (head v d) (.mult .one (.join (.var 0) (.transpose (contains v d)))),
       .all (head v p) (interval row.localBounds (.join (.var 0) (contains v d)))] ++
      match v.analysis.referenceOwners[d] with
      | some owner => match (v.core.structural.get owner).reference with
        | .set _ => [setKey v d p]
        | _ => []
      | none => []
  referenceFacts v d ++ group ++ containment

/-- Refined annotations share one assignment per occurrence, even when their
nearest owners differ. This is stronger than per-field functionality. -/
def coherentFacts (v : Validated k) : List Temporal.Formula :=
  [(Temporal.Formula.all (.sig 0)
    (.mult .lone (.join (.var 0)
      (((List.finRange k).map (declaredDeref v)).foldl Temporal.Rel.union (.empty .binary)))))]

def stateFacts (v : Validated k) : List Temporal.Formula :=
  [.subset (.field 1) (.product (root v) (.sig 0)),
   .equal (head v v.core.structural.root) (root v),
   .subset (root v) (live v), .subset (.join (live v) parent) (live v)] ++
    coherentFacts v ++ (List.finRange k).flatMap (declarationFacts v)

/-- Bounded reachability uses the global identity capacity, not a time bound.
The enclosing compiler supplies its actual object scope. Parent presence makes
every intermediate object live whenever the reached child is live. -/
def reachabilityFact (v : Validated k) (capacity : Nat) : Temporal.Formula :=
  .subset (live v)
    (union ((List.range (capacity + 1)).map fun depth =>
      Nat.repeat (fun r => Temporal.Rel.join r (.transpose parent)) depth (root v)))

end ClaferCompiler.Backend.Alloy.Behavioral.Full
