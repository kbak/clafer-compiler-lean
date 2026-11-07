module

public import tests.BehavioralFullNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullModifiers
open Backend.Alloy
open Behavioral.Full

inductive Change where
  | swap | replaceHead | addOccurrence | gap

/-- Bind two fixed head identities once, independently of their changing live
membership and scalar values. Integer targets avoid conflating head identities
with the shared target image. -/
def pinned (modifiers : String) (change : Change) (inherited : Bool := false) : Except String Temporal.Module := do
  let card := match change with | .swap => "2..2" | .replaceHead => "1..1" | .addOccurrence => "1..2" | .gap => "*"
  let source := if inherited then "abstract " ++ modifiers ++ " R ->> int\nr : R " ++ card ++ "\n"
    else modifiers ++ " r ->> int " ++ card ++ "\n"
  let parsed ← BehavioralFull.parsed source
  let model := parsed.elaborated.model
  let v := model.structural
  let some d := (List.finRange parsed.elaborated.declarations.resolved.count).find?
    (fun d => (v.core.structural.get d).name == "r") | throw "missing reference"
  let bounds : Bounds := {
    declarations := [((v.core.structural.get d).id, ⟨2, true⟩)], objects := 3,
    bitwidth := 3, minSteps := 3, maxSteps := 3, values := some ⟨0, 1⟩ }
  let out ← (compile ⟨model, .run []⟩ bounds 512).mapError (·.code)
  let x := Temporal.Rel.var 1
  let y := Temporal.Rel.var 0
  let both := Temporal.Rel.union x y
  let heads := fun r => Temporal.Formula.equal (head v d) r
  let value := fun r i => Temporal.Formula.subset (.product r (.integer i)) (.values 0)
  let later := fun p => Temporal.Formula.unary .after (.unary .always p)
  let assignments := match change with
    | .swap => Expressions.all [heads both, value x 0, value y 1,
        later (Expressions.all [heads both, value x 1, value y 0])]
    | .replaceHead => Expressions.all [heads x, value x 0,
        later (Expressions.all [heads y, value y 0])]
    | .addOccurrence => Expressions.all [heads x, value x 0,
        later (Expressions.all [heads both, value both 0])]
    | .gap => Expressions.all [heads x, value x 0,
        .unary .after (heads (.empty .unary)),
        .unary .after (.unary .after (.unary .always (Expressions.all [heads x, value x 1])))]
  let pins := Temporal.Formula.exists_ (directPool d)
    (.exists_ (.diff (directPool d) (.var 0)) assignments)
  return { out.module.raw with facts := out.module.raw.facts ++ [pins] }

-- [utest->req~compiler-full-behavioral-correctness~1]
def cases : Except String (List (String × Bool × Temporal.Module)) := do
  let mut result := []
  for inherited in [false, true] do
    for (name, modifier, change, expected) in [
        ("target-swap", "finaltarget", Change.swap, true),
        ("reference-swap", "finalref", Change.swap, false),
        ("final-swap", "final", Change.swap, false),
        ("replace-head-both", "finalref finaltarget", Change.replaceHead, true),
        ("replace-head-reverse", "finaltarget finalref", Change.replaceHead, true),
        ("replace-head-final", "final", Change.replaceHead, false),
        ("target-multiplicity", "finaltarget", Change.addOccurrence, true),
        ("reference-multiplicity", "finalref", Change.addOccurrence, true),
        ("final-multiplicity", "final", Change.addOccurrence, false),
        ("reference-gap", "finalref", Change.gap, true),
        ("target-gap", "finaltarget", Change.gap, false)] do
      result := result ++ [(s!"full-modifier-{name}-{inherited}", expected, ← pinned modifier change inherited)]
  return result

end ClaferCompiler.Tests.BehavioralFullModifiers
