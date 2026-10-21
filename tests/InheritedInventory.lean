module

public import tests.InheritedNative
public import ClaferCompiler.SemanticsBridge.Inherited
public import Clafer.Examples.Telematics.Input
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace ClaferCompiler.Tests.InheritedInventory

/-! Compare every semantic declaration slot against the complete pinned source
inventory, including the unrestricted integer declaration. Constraints are outside
this structural projection. Source IDs are distinct from upstream preorder indices.
[utest->req~compiler-inherited-realization~1] -/
theorem appendix6_inventory (d : Fin 28) :
    let row := InheritedNative.raw.structural.declarations[d.val]
    let source := Clafer.Examples.Telematics.decl d.val
    row.id = source.id.value ∧ row.name = source.name ∧
    SemanticsBridge.Structural.origin row.origin = source.origin ∧
    row.isAbstract = source.isAbstract ∧
    InheritedNative.raw.explicitAbstract[d.val] = source.authoredAbstract ∧
    row.super = source.super.map (·.value) ∧
    row.reference.target = source.reference.target.map (·.value) ∧
    (SemanticsBridge.Structural.reference row.reference).kind = source.reference.kind ∧
    SemanticsBridge.Structural.bounds row.localBounds = source.multiplicity.effective ∧
    SemanticsBridge.Structural.bounds row.groupBounds = source.group.effective.range := by
  fin_cases d <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendix6_parents (d : Fin 28) :
    InheritedNative.raw.structural.declarations[d.val].parent =
      ((Clafer.Examples.Telematics.ast.entries.find? fun entry => entry.declaration.id.value == d.val).bind
        (·.parent)).map (·.value) := by
  fin_cases d <;> rfl

end ClaferCompiler.Tests.InheritedInventory
