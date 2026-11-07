module

public import tests.BehavioralFullTemporalNative

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralFullFrontend
open Backend.Alloy
open Behavioral.Full

def declaration (p : Frontend.Behavioral.ParsedModel) (name : String) :
    Except String (Fin p.elaborated.declarations.resolved.count) := do
  let some d := (List.finRange p.elaborated.declarations.resolved.count).find?
    (fun d => (p.elaborated.model.structural.core.structural.get d).name == name)
    | throw ("missing " ++ name)
  return d

/-- Both traces keep one live literal at every instant. Only replacement of its
fixed identity distinguishes the dynamic enum's generated `final` modifier. -/
def enumLiteral (replace : Bool) : Except String Temporal.Module := do
  let parsed ← BehavioralFull.parsed "enum Colour = Red | Blue\n"
  let model := parsed.elaborated.model
  let v := model.structural
  let red ← declaration parsed "Red"
  let blue ← declaration parsed "Blue"
  let bounds : Bounds := {
    declarations := [((v.core.structural.get red).id, ⟨2, true⟩),
      ((v.core.structural.get blue).id, ⟨1, true⟩)],
    objects := 4, bitwidth := 4, minSteps := 2, maxSteps := 2, values := some ⟨0, 0⟩ }
  let out ← (compile ⟨model, .run []⟩ bounds 512).mapError (·.code)
  let first := Temporal.Rel.var 1
  let second := Temporal.Rel.var 0
  let pins := Temporal.Formula.exists_ (directPool red)
    (.exists_ (.diff (directPool red) (.var 0))
      (Expressions.all [.equal (head v red) first,
        .unary .after (.unary .always (.equal (head v red) (if replace then second else first)))]))
  return { out.module.raw with facts := out.module.raw.facts ++ [pins] }

/-- Two live owners each have at most one child. With one child, exactly one
owner violates the authored nested assertion; with two, every owner satisfies it.
The frontend check API selects the assertion without negating its source body. -/
def nestedAssertion (allOwners : Bool) : Except String Temporal.Module := do
  let parsed ← BehavioralFull.parsed "P 2..2\n  A ?\n  assert [some A]\n"
  let v := parsed.elaborated.model.structural
  let parentDecl ← declaration parsed "P"
  let child ← declaration parsed "A"
  let children := if allOwners then 2 else 1
  let bounds : Bounds := {
    declarations := [((v.core.structural.get parentDecl).id, ⟨2, true⟩),
      ((v.core.structural.get child).id, ⟨children, true⟩)],
    objects := 3 + children, bitwidth := 4, minSteps := 1, maxSteps := 1, values := some ⟨0, 0⟩ }
  let request ← (parsed.elaborated.check 0).mapError (·.code)
  let out ← (compile request bounds 512).mapError (·.code)
  let pins := Temporal.Formula.unary .always (.equal (head v child) (pool v child))
  return { out.module.raw with facts := out.module.raw.facts ++ [pins] }

/-- The mandatory value is continuously live, starts at the declared value, and
is independently pinned thereafter. A later change violates the equation even
though the birth value satisfied it. -/
def equation (change : Bool) : Except String Temporal.Module := do
  let parsed ← BehavioralFull.parsed "P\n  value -> int = 0\n"
  let model := parsed.elaborated.model
  let v := model.structural
  let parentDecl ← declaration parsed "P"
  let value ← declaration parsed "value"
  let bounds : Bounds := {
    declarations := [((v.core.structural.get parentDecl).id, ⟨1, true⟩),
      ((v.core.structural.get value).id, ⟨1, true⟩)],
    objects := 3, bitwidth := 4, minSteps := 2, maxSteps := 2, values := some ⟨0, 1⟩ }
  let out ← (compile ⟨model, .run []⟩ bounds 512).mapError (·.code)
  let scalar := fun z => Temporal.Formula.subset (.product (head v value) (.integer z)) (.values 0)
  let pins := Expressions.all [scalar 0,
    .unary .after (.unary .always (scalar (if change then 1 else 0)))]
  return { out.module.raw with facts := out.module.raw.facts ++ [pins] }

-- [utest->req~compiler-full-behavioral-correctness~1]
-- [utest->req~compiler-behavioral-property-commands~1]
-- [utest->req~compiler-behavioral-elaboration~1]
def cases : Except String (List (String × Bool × Temporal.Module)) := do
  let inheritedInitial := "abstract Parent\n  initial flag ?\np : Parent ?\n"
  let inheritedFinal := "abstract Parent\n  final flag ?\np : Parent ?\n"
  let present := [true, true]
  let absent := [false, false]
  let missing := [true, false]
  return [
    ("full-frontend-inherited-initial-rebirth", true,
      ← BehavioralFullTemporal.pinned inheritedInitial ["p", "flag"] [present, absent, present]),
    ("full-frontend-inherited-initial-missing-rebirth", false,
      ← BehavioralFullTemporal.pinned inheritedInitial ["p", "flag"] [present, absent, missing]),
    ("full-frontend-final-parent-gap", true,
      ← BehavioralFullTemporal.pinned inheritedFinal ["p", "flag"] [present, absent, missing]),
    ("full-frontend-final-parent-continuous", false,
      ← BehavioralFullTemporal.pinned inheritedFinal ["p", "flag"] [present, missing]),
    ("full-frontend-enum-fixed-literal", true, ← enumLiteral false),
    ("full-frontend-enum-replaced-literal", false, ← enumLiteral true),
    ("full-frontend-nested-assertion-all-owners", false, ← nestedAssertion true),
    ("full-frontend-nested-assertion-one-owner-fails", true, ← nestedAssertion false),
    ("full-frontend-equation-always", true, ← equation false),
    ("full-frontend-equation-later-change", false, ← equation true)]

end ClaferCompiler.Tests.BehavioralFullFrontend
