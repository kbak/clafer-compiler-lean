module

public import tests.BehavioralFullNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullStructureNative
open Backend.Alloy
open Behavioral.Full

inductive Violation where
  | none | wrongParent | missingReference | wrongTarget

/-- These target mutations constrain the generated structure directly. They do
not rely on expression lowering to expose a missing containment/reference fact. -/
def model (source : String) (violation : Violation := .none) : Except String Temporal.Module := do
  let parsed ← BehavioralFull.parsed source
  let m := parsed.elaborated.model
  let v := m.structural
  let b : Bounds := {
    declarations := [], objects := 6, bitwidth := 8,
    minSteps := 1, maxSteps := 2, values := some ⟨0, 0⟩ }
  let out ← (compile ⟨m, .run []⟩ b 512).mapError (fun e => e.code ++ "\n" ++ source)
  match violation with
  | .none => return out.module.raw
  | _ =>
    let some port := (List.finRange parsed.elaborated.declarations.resolved.count).find?
      (fun d => (v.core.structural.get d).name == "port") | throw "missing port"
    let bad : Temporal.Formula := match violation with
      | .wrongParent => .subset (.product (head v port) (root v)) parent
      | .missingReference => .equal (deref v port) (.empty .binary)
      | .wrongTarget => .subset (.product (head v port) (root v)) (deref v port)
      | .none => .truth
    return { out.module.raw with facts := out.module.raw.facts ++ [bad] }

-- [utest->req~compiler-full-behavioral-correctness~1]
def cases : Except String (List (String × Bool × Temporal.Module)) := do
  let rich := "Target ?\nSystem ?\n  abstract Port ->> Target\n    entry ->> Target\nSubSystem : System\n  port : Port\n"
  let grouped := "abstract xor Choice\n  a ?\nchosen : Choice\n  b ?\n"
  return [
    ("full-structure-refined-parent", true, ← model rich),
    ("full-structure-wrong-parent", false, ← model rich .wrongParent),
    ("full-structure-missing-inherited-reference", false, ← model rich .missingReference),
    ("full-structure-wrong-reference-target", false, ← model rich .wrongTarget),
    ("full-structure-inherited-child", false, ← model (rich ++ "[no SubSystem.port.entry]\n")),
    ("full-structure-concrete-super", true, ← model "Base *\nChild : Base\n[some Base]\n"),
    ("full-structure-missing-super-view", false, ← model "Base *\nChild : Base\n[no Base]\n"),
    ("full-structure-group-one", true, ← model (grouped ++ "[some chosen.a && no chosen.b]\n")),
    ("full-structure-group-both", false, ← model (grouped ++ "[some chosen.a && some chosen.b]\n")),
    ("full-structure-group-neither", false, ← model (grouped ++ "[no chosen.a && no chosen.b]\n")),
    ("full-structure-bag-duplicates", true, ← model "Target\nabstract Ref ->> Target\nport : Ref 2..2\n"),
    ("full-structure-inherited-set-key", false, ← model "Target\nabstract Ref -> Target\nport : Ref 2..2\n")]

end ClaferCompiler.Tests.BehavioralFullStructureNative
