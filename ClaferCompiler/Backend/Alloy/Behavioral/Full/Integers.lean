module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Collections
public import ClaferCompiler.Backend.Alloy.Behavioral.Arithmetic

@[expose] public section
namespace ClaferCompiler.Backend.Alloy.Behavioral.Full

-- [impl->req~compiler-behavioral-partial-lowering~1]
def integerBinary (op : IR.BehavioralArithmetic.Binary)
    (a b : Value Temporal.Integer) : Value Temporal.Integer :=
  (a.pair b).map fun (x, y) => Arithmetic.binary op x y

def integerNegate (a : Value Temporal.Integer) : Value Temporal.Integer :=
  a.map fun x => .subtract (.literal 0) x

/-- Extraction has an explicit original source domain. The target scalar term
is total even when that domain is false, allowing assertion counterexamples
caused by undefined source observations. -/
def integerExtract (r : IR.Expr.Interval) (a : Value Temporal.Rel) : Value Temporal.Integer :=
  a.bind fun value =>
    ⟨[(.binary .conj (.mult .one value) (.subset value .ints),
      .scalar r.lower r.upper value)]⟩

/-- Integer values become integer atoms, never ordinary identity aliases.
Only the admitted interval is enumerated; arithmetic stays in target terms. -/
def integerCollection (r : IR.Expr.Interval) (a : Value Temporal.Integer) : Value Temporal.Rel :=
  a.bind fun value =>
    ⟨(integerCandidates r).map fun i =>
      (.compare .eq value (.literal i), .integer i)⟩

/-- Count a deduplicated finite observation. Generating literals from bounded
membership cases keeps the target admission bound equal to the structural
observation budget, rather than the whole target universe. -/
def integerCardinality (aliases : List Temporal.Rel) (budget : Nat)
    (a : Value Temporal.Rel) : Value Temporal.Integer :=
  a.bind fun value =>
    (Value.selections aliases value budget).bind fun chosen =>
      ⟨[(.equal value (Full.union chosen), .literal (Int.ofNat chosen.length))]⟩

/-- A source operand occurrence list is retained. Each chosen head contributes
its body value, even if another occurrence has the same target integer. -/
def integerFold (op : IR.BehavioralArithmetic.Fold)
    (values : List (Value Temporal.Integer)) : Value Temporal.Integer :=
  let initial := Value.pure (Temporal.Integer.literal (if op == .sum then 0 else 1))
  values.foldl (fun result value => integerBinary
    (if op == .sum then .add else .multiply) result value) initial

end ClaferCompiler.Backend.Alloy.Behavioral.Full
