module

public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile
public import ClaferCompiler.Frontend.Behavioral.Elaborate

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFull
open Backend.Alloy.Behavioral.Full
open IR.Behavioral

def bounds : Bounds := {
  declarations := [], objects := 3, bitwidth := 4, minSteps := 1, maxSteps := 3
  values := some ⟨0, 1⟩ }

def parsed (source : String) : Except String Frontend.Behavioral.ParsedModel :=
  (Frontend.Behavioral.parseAndElaborate IR.BehavioralStructural.profile "full.cfr" source).mapError
    (fun e => e.code ++ ": " ++ e.message)

def runModel (source : String) : Except String Backend.Alloy.Temporal.Module := do
  let p ← parsed source
  let r : Request p.elaborated.declarations.resolved.count := ⟨p.elaborated.model, .run []⟩
  let out ← (compile r bounds 512).mapError (fun e => e.code)
  return out.module.raw

def runScenario (source scenario : String) : Except String Backend.Alloy.Temporal.Module := do
  let p ← parsed source
  let s ← (Frontend.Behavioral.parseBehavioral IR.BehavioralStructural.profile "scenario.cfr" scenario).mapError (·.code)
  let request ← (p.elaborated.run [⟨p.elaborated.model.structural.core.structural.root, s⟩]).mapError (·.code)
  let out ← (compile request bounds 512).mapError (·.code)
  return out.module.raw

-- [utest->req~compiler-full-behavioral-correctness~1]
-- [utest->req~compiler-behavioral-property-commands~1]
def undefinedAssertion : Except String Backend.Alloy.Temporal.Module := do
  let p ← parsed "A ?\n"
  let model := p.elaborated.model
  let assertion : Constraint p.elaborated.declarations.resolved.count :=
    ⟨model.structural.core.structural.root,
      .atom (.primitive (.integerEqual (.extract (.set .empty)) (.literal 0))), ⟨"full.cfr", 0, 0⟩⟩
  let model := { model with assertions := [assertion] }
  let out ← (compile ⟨model, .check ⟨0, by change 0 < 1; omega⟩⟩ bounds 512).mapError (fun e => e.code)
  return out.module.raw

-- [utest->req~compiler-full-behavioral-correctness~1]
def finiteObservationRejections : Except String Unit := do
  let p ← parsed ""
  let model := p.elaborated.model
  let some int := (List.finRange p.elaborated.declarations.resolved.count).find?
    (integerDeclaration model.structural) | throw "missing primitive domain"
  let source : IR.Structural.SourceSpan := ⟨"full.cfr", 0, 0⟩
  let wholeDomain : Constraint p.elaborated.declarations.resolved.count := ⟨int, .truth, source⟩
  let result := compile ⟨model, .run [wholeDomain]⟩ bounds 512
  match result with
  | .error e => unless e.code == "behavioral.infinite-attachment" do throw e.code
  | .ok _ => throw "whole primitive attachment accepted"
  let primitiveModifier := { model with modifiers := model.modifiers.set int [.finalref] }
  match compile ⟨primitiveModifier, .run []⟩ bounds 512 with
  | .error e => unless e.code == "behavioral.infinite-attachment" do throw e.code
  | .ok _ => throw "whole primitive modifier attachment accepted"
  let vacuous : Expression.Formula p.elaborated.declarations.resolved.count 0 :=
    .quant .all (.set .empty) (.atom (.primitive (.inhabited (.set (.extent int)))))
  let scenario : Constraint p.elaborated.declarations.resolved.count :=
    ⟨model.structural.core.structural.root, vacuous, source⟩
  match compile ⟨model, .run [scenario]⟩ bounds 512 with
  | .error e => unless e.code == "behavioral.infinite-observation" do throw e.code
  | .ok _ => throw "infinite observation in vacuous body accepted"

def cases : Except String (List (String × Bool × Backend.Alloy.Temporal.Module)) := do
  finiteObservationRejections
  return [
    ("full-empty-model", true, ← runModel "A ?\n"),
    ("full-constraint", false, ← runModel "A\n[no A]\n"),
    ("full-partial-assertion", true, ← undefinedAssertion),
    ("full-empty-numeric-scenario", true, ← runScenario "" "[0 = 0]"),
    ("full-empty-numeric-scenario-false", false, ← runScenario "" "[0 = 1]"),
    ("full-empty-numeric-scenario-quantifier", true, ← runScenario "" "[all x : 0 | some x]"),
    ("full-model-and-scenario", false, ← runScenario "A\n" "[no A]")]

end ClaferCompiler.Tests.BehavioralFull
