module

public import tests.BehavioralFullNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullPatterns
open Backend.Alloy
open Behavioral.Full

abbrev Frame := Bool × Bool × Bool × Bool

def atTime (t : Nat) (a : Temporal.Formula) : Temporal.Formula :=
  t.repeat (Temporal.Formula.unary .after) a

def presence (r : Temporal.Rel) (present : Bool) : Temporal.Formula :=
  if present then .mult .some r else .unary .neg (.mult .some r)

def bounds (frames : List Frame) : Bounds :=
  let used := [frames.any (·.1), frames.any (·.2.1), frames.any (·.2.2.1), frames.any (·.2.2.2)]
  { declarations := used.zipIdx.map fun (present, i) => (i + 1, ⟨if present then 1 else 0, true⟩)
    objects := 1 + (used.filter id).length, bitwidth := 4,
    minSteps := frames.length, maxSteps := frames.length, values := some ⟨0, 0⟩ }

/-- The expected traces are fixed independently of the pattern expansion.
The final frame repeats forever, so the solver cannot satisfy an obligation by
choosing a different loop or inventing a later event. -/
def pinned (property : String) (frames : List Frame) : Except String Temporal.Module := do
  let p ← BehavioralFull.parsed ("P ?\nS ?\nQ ?\nR ?\n[" ++ property ++ "]\n")
  let v := p.elaborated.model.structural
  let names ← ["P", "S", "Q", "R"].mapM fun name => do
    let some d := (List.finRange p.elaborated.declarations.resolved.count).find?
      (fun d => (v.core.structural.get d).name == name) | throw ("missing " ++ name)
    return head v d
  let [pRel, sRel, qRel, rRel] := names | throw "pattern declarations"
  let frame (values : Frame) : Temporal.Formula :=
    Expressions.all [presence pRel values.1, presence sRel values.2.1,
      presence qRel values.2.2.1, presence rRel values.2.2.2]
  let out ← (compile ⟨p.elaborated.model, .run []⟩ (bounds frames) 512).mapError (·.code)
  let some last := frames.getLast? | throw "empty trace"
  let facts := frames.zipIdx.map (fun (values, t) => atTime t (frame values))
  return { out.module.raw with facts := out.module.raw.facts ++ facts ++
    [atTime (frames.length - 1) (.unary .always (frame last))] }

def witness (row : Nat) (good : Bool) : List Frame :=
  (List.range 4).map fun t =>
    let p := if row == 0 then !good && t == 1
      else if row == 1 then good && t == 1
      else if row == 2 then if good then t == 1 else t == 0 || t == 2
      else if row == 3 then good else t == 1
    let s := good && ((row == 4 && t == 0) || (row == 5 && t == 2))
    (p, s, t == 0, t == 3)

-- [utest->req~compiler-full-behavioral-correctness~1]
def cases : Except String (List (String × Bool × Temporal.Module)) := do
  let mut result := []
  for (pattern, row) in ["never P", "sometime P", "lonce P", "always P",
      "S must precede P", "S must follow P"].zipIdx do
    for (scope, column) in ["", " before R", " after Q", " between Q and R", " after Q until R"].zipIdx do
      for good in [true, false] do
        for positive in [true, false] do
          let body := "(" ++ pattern ++ scope ++ ")"
          let property := "initially " ++ (if positive then body else "!(" ++ body ++ ")")
          let m ← pinned property (witness row good)
          result := result ++ [(s!"full-pattern-{row}-{column}-{good}-{positive}", good == positive, m)]
  let lateTrigger := [(false, false, true, false), (false, false, false, false),
    (true, false, false, false), (false, false, false, true)]
  result := result ++ [("full-response-between-late-trigger", false,
    ← pinned "initially (S must follow P between Q and R)" lateTrigger)]
  let laterOpener := [(false, false, true, false), (true, false, false, false),
    (false, false, true, false), (false, true, false, true)]
  result := result ++ [("full-precedence-after-first-opener", false,
    ← pinned "initially (S must precede P after Q)" laterOpener)]
  let once := witness 1 true
  result := result ++ [("full-eventual-initially", true, ← pinned "initially (sometime P)" once),
    ("full-eventual-recurrent", false, ← pinned "sometime P" once)]
  return result

end ClaferCompiler.Tests.BehavioralFullPatterns
