module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Structure
public import ClaferCompiler.Backend.Alloy.Behavioral.Partial
public import ClaferCompiler.IR.Behavioral.Ranges

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full

/-- Finite guarded choices are the first-slice capture construction in data form.
This allows the checked expression traversal to visit every branch before use.
The target postfix AST, upstream partial primitives and frontend range derivations
supply no branch-preserving value constructor. Standard List folds are reused;
there is no new dependency. Branch expansion may be exponential in finite bounds. -/
structure Value (α : Type) where
  cases : List (Temporal.Formula × α)

namespace Value
-- [impl->req~compiler-behavioral-partial-lowering~1]
def pure (a : α) : Value α := ⟨[(.truth, a)]⟩
def missing : Value α := ⟨[]⟩
def map (f : α → β) (a : Value α) : Value β :=
  ⟨a.cases.map fun (g, x) => (g, f x)⟩
def bind (a : Value α) (f : α → Value β) : Value β :=
  ⟨a.cases.flatMap fun (g, x) => (f x).cases.map fun (h, y) => (.binary .conj g h, y)⟩
def pair (a : Value α) (b : Value β) : Value (α × β) :=
  a.bind fun x => b.map fun y => (x, y)
def guard (p : Temporal.Formula) (a : Value α) : Value α :=
  ⟨a.cases.map fun (g, x) => (.binary .conj p g, x)⟩
def use (a : Value α) (f : α → Temporal.Formula) : Temporal.Formula :=
  a.cases.foldr (fun (g, x) rest => .binary .disj (.binary .conj g (f x)) rest) .falsity
def defined (a : Value α) : Temporal.Formula := a.use fun _ => .truth

/-- Both branches contribute their original domain. Only raw condition truth
selects the value; signed normalization cannot rewrite a value condition. -/
def conditional (c : Partial.Translation) (a b : Value α) : Value α :=
  (a.pair b).bind fun (x, y) =>
    ⟨[(.binary .conj c.defined c.truth.raw, x),
      (.binary .conj c.defined (.unary .neg c.truth.raw), y)]⟩

def predicate (a : Value α) (p : α → Temporal.Formula) : Partial.Translation :=
  Partial.atom a.defined (a.use p)

/-- Membership cases freeze each identity once. The `seen` union prevents
padded duplicate aliases from adding occurrences; syntactically repeated source
domains are handled by separate calls and remain separate occurrences. -/
def selections (aliases : List Temporal.Rel) (domain : Temporal.Rel) (budget : Nat) :
    Value (List Temporal.Rel) :=
  let initial : Value (List Temporal.Rel × Temporal.Rel) :=
    .pure ([], .empty .unary)
  let choices := aliases.foldl (fun values alias => values.bind fun (chosen, seen) =>
    let member := Temporal.Formula.binary .conj (.mult .one alias)
      (.binary .conj (.subset alias domain) (.unary .neg (.subset alias seen)))
    let absent := (Temporal.Formula.unary .neg member, (chosen, seen))
    let present := (member, (alias :: chosen, .union seen alias))
    ⟨if chosen.length < budget then [present, absent] else [absent]⟩) initial
  choices.map fun (chosen, _) => chosen.reverse

/-- Freeze a complete current collection, requiring that all its members occur
in the finite alias cover. The budget is validated from structural scopes. -/
def capture (aliases : List Temporal.Rel) (domain : Temporal.Rel) (budget : Nat) :
    Value Temporal.Rel :=
  (selections aliases domain budget).bind fun selected =>
    let captured := Full.union selected
    ⟨[(.equal domain captured, captured)]⟩
end Value

-- [impl->req~compiler-behavioral-partial-lowering~1]
def collectionUnion (a b : Value Temporal.Rel) : Value Temporal.Rel :=
  (a.pair b).map fun (x, y) => .union x y
def collectionInter (a b : Value Temporal.Rel) : Value Temporal.Rel :=
  (a.pair b).map fun (x, y) => .inter x y
def collectionDiff (a b : Value Temporal.Rel) : Value Temporal.Rel :=
  (a.pair b).map fun (x, y) => .diff x y

def integerCandidates (r : IR.Expr.Interval) : List Int :=
  (List.range ((r.upper - r.lower + 1).toNat)).map fun n => r.lower + Int.ofNat n

/-- Empty extrema remain a defined empty collection. Wrong-domain values are
undefined; minimum/maximum are selected over the entire integer collection. -/
def collectionExtreme (op : IR.Behavioral.Primitive.Extreme) (r : IR.Expr.Interval)
    (a : Value Temporal.Rel) : Value Temporal.Rel :=
  a.bind fun value =>
    let empty : Temporal.Formula × Temporal.Rel :=
      (.equal value (.empty .unary), .empty .unary)
    let candidates := (integerCandidates r).map fun i =>
      let better := (integerCandidates r).filter fun j =>
        match op with | .minimum => j < i | .maximum => i < j
      let forbidden := Full.union (better.map Temporal.Rel.integer)
      let guard := Temporal.Formula.binary .conj (.subset value .ints)
        (.binary .conj (.subset (.integer i) value)
          (.equal (.inter value forbidden) (.empty .unary)))
      (guard, Temporal.Rel.integer i)
    ⟨empty :: candidates⟩

end ClaferCompiler.Backend.Alloy.Behavioral.Full
