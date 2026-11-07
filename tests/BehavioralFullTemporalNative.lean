module

public import tests.BehavioralFullPatternsNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullTemporal
open Backend.Alloy
open Behavioral.Full

/-- Fix the lifetime of each named identity independently of the source property.
The last frame repeats forever, including after a gap or a transition failure. -/
def pinned (source : String) (names : List String) (frames : List (List Bool)) :
    Except String Temporal.Module := do
  let parsed ← BehavioralFull.parsed source
  let model := parsed.elaborated.model
  let v := model.structural
  let declarations ← names.mapM fun name => do
    let some d := (List.finRange parsed.elaborated.declarations.resolved.count).find?
      (fun d => (v.core.structural.get d).name == name) | throw ("missing " ++ name)
    return d
  let used := names.zipIdx.map fun (_, i) => frames.any (fun frame => frame[i]?.getD false)
  let bounds : Bounds := {
    declarations := declarations.zip used |>.map fun (d, present) =>
      ((v.core.structural.get d).id, ⟨if present then 1 else 0, true⟩)
    objects := 1 + (used.filter id).length, bitwidth := 4,
    minSteps := frames.length, maxSteps := frames.length, values := some ⟨0, 0⟩ }
  let out ← (compile ⟨model, .run []⟩ bounds 512).mapError (·.code)
  let frame (values : List Bool) := Expressions.all
    ((declarations.zip values).map fun (d, present) => BehavioralFullPatterns.presence (head v d) present)
  let some last := frames.getLast? | throw "empty trace"
  let facts := frames.zipIdx.map fun (values, t) => BehavioralFullPatterns.atTime t (frame values)
  return { out.module.raw with facts := out.module.raw.facts ++ facts ++
    [BehavioralFullPatterns.atTime (frames.length - 1) (.unary .always (frame last))] }

-- [utest->req~compiler-full-behavioral-correctness~1]
def cases : Except String (List (String × Bool × Temporal.Module)) := do
  let chain := "initially (P -[Q]->> S -[R]-> Q)"
  let good := [(true, false, true, false), (true, false, false, false),
    (false, true, false, true), (false, false, true, false)]
  let missingMiddle := [(true, false, true, false), (true, false, false, false),
    (false, false, false, true), (false, false, true, false)]
  let missingGuard := [(true, false, true, false), (true, false, false, false),
    (false, true, false, false), (false, false, true, false)]
  let missingTarget := [(true, false, true, false), (true, false, false, false),
    (false, true, false, true), (false, false, false, false)]
  let sourceLost := [(true, false, true, false), (false, false, false, false),
    (false, true, false, true), (false, false, true, false)]
  let mut result := []
  for (name, frames, expected) in [
      ("guard-lapses", good, true), ("missing-middle", missingMiddle, false),
      ("missing-later-guard", missingGuard, false), ("missing-target", missingTarget, false),
      ("source-lost", sourceLost, false)] do
    result := result ++ [("full-chain-" ++ name, expected, ← BehavioralFullPatterns.pinned chain frames)]
  let declaration := "P ?\n  A ? --> B\n  B ?\n"
  for (name, frames, expected) in [
      ("target", [[true, true, false], [true, false, true]], true),
      ("context-dies", [[true, true, false], [true, false, false]], false),
      ("parent-dies", [[true, true, false], [false, false, false]], true),
      ("reappears", [[true, true, false], [false, false, false],
        [true, true, false], [true, false, false]], false)] do
    result := result ++ [("full-declaration-transition-" ++ name, expected,
      ← pinned declaration ["P", "A", "B"] frames)]
  for (name, property, frames, expected) in [
      ("birth-true", "initially some B", [[true, true, true], [true, true, false]], true),
      ("birth-false", "initially some B", [[true, true, false], [true, true, true]], false),
      ("rebirth-false", "initially some B", [[true, true, true], [true, false, false],
        [true, true, false]], false),
      ("end-true", "finally some B", [[true, true, false], [true, true, true], [true, false, false]], true),
      ("end-false", "finally some B", [[true, true, true], [true, true, false], [true, false, false]], false)] do
    let source := "P ?\n  A ?\n    [" ++ property ++ "]\n  B ?\n"
    result := result ++ [("full-anchor-" ++ name, expected, ← pinned source ["P", "A", "B"] frames)]
  for (name, property, frames, expected) in [
      ("no-opener", "S must follow P after Q", [(true, false, false, false)], true),
      ("no-closer-before", "sometime P before R", [(false, false, false, false)], true),
      ("no-closer-between", "sometime P between Q and R", [(false, false, true, false)], true),
      ("no-closer-until", "sometime P after Q until R", [(false, false, true, false)], false),
      ("simultaneous-boundaries", "sometime P between Q and R", [(false, false, true, true)], true),
      ("event-at-closing-boundary", "sometime P before R", [(true, false, false, true)], false),
      ("event-at-opening-boundary", "sometime P after Q", [(true, false, true, false)], true)] do
    result := result ++ [("full-pattern-boundary-" ++ name, expected,
      ← BehavioralFullPatterns.pinned ("initially (" ++ property ++ ")") frames)]
  let scopedSource := "Parent ?\n  A ?\n    [S must follow this after Q until R]\n  S ?\n  Q ?\n  R ?\n"
  let entered := [true, true, false, true, false]
  let absent := [false, false, false, false, false]
  result := result ++ [
    ("full-pattern-parent-death", true, ← pinned scopedSource ["Parent", "A", "S", "Q", "R"] [entered, absent]),
    ("full-pattern-parent-reappearance", false,
      ← pinned scopedSource ["Parent", "A", "S", "Q", "R"] [entered, absent, entered])]
  return result

end ClaferCompiler.Tests.BehavioralFullTemporal
