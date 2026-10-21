module

public import ClaferCompiler.SemanticsBridge.Structural
public import tests.StructuralNative

public section
namespace ClaferCompiler.Tests.Structural
open IR.Structural SemanticsBridge.Structural

/-- Kernel witnesses exercise the typed table guards; raw resolution runs natively. -/
def rootCore : Core 1 := ⟨#v[{ id := 100, name := "root", origin := .syntheticRoot }], 0⟩
def rootCert : Certificate 1 := ⟨#v[0], #v[0], #v[false]⟩
theorem root_checked : coreChecks rootCore rootCert ∧ supportChecks rootCore rootCert := by
  decide

def cycleCore : Core 3 := ⟨#v[
  { id := 100, name := "root", origin := .syntheticRoot },
  { id := 200, name := "same", parent := some 0, reference := .set 2 },
  { id := 300, name := "same", parent := some 0, reference := .bag 1 }], 0⟩
def cycleCert : Certificate 3 := ⟨#v[0, 1, 1], #v[0, 0, 0], #v[false, false, false]⟩
theorem reference_cycle_checked : coreChecks cycleCore cycleCert ∧ supportChecks cycleCore cycleCert := by
  decide

theorem cycle_upstream_domain : (interpret cycleCore).WellFormed ∧ (interpret cycleCore).Supported := by
  obtain ⟨v, hv⟩ := (validate_success_iff cycleCore cycleCert).mpr reference_cycle_checked
  exact (admission_iff cycleCore).mp ⟨cycleCert, v, hv⟩

theorem duplicate_id_rejected :
    outcome (raw #[root, child 100] #[0, 1] #[0, 0] #[false, false]) =
      "ir.duplicate-id" := by decide

/-- Metadata cannot affect the guard or reconstruct authored defaults. -/
theorem name_irrelevance (m : Core n) (k : Certificate n) (names : Fin n → String) :
    let renamed : Core n := ⟨Vector.ofFn (fun d => { m.get d with name := names d }), m.root⟩
    coreChecks renamed k ↔ coreChecks m k := by
  simp [coreChecks, Core.get]

end ClaferCompiler.Tests.Structural

#check ClaferCompiler.SemanticsBridge.Structural.admission_iff
#check ClaferCompiler.SemanticsBridge.Structural.validate_preserves
#check ClaferCompiler.SemanticsBridge.Structural.lookup_complete
#check ClaferCompiler.SemanticsBridge.Structural.interpret_fields
