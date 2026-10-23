module

public import Mathlib.Data.List.Sort
public import tests.StructuralAlloyNative
public import ClaferCompiler.Correctness.StructuralGeneration

@[expose] public section
namespace ClaferCompiler.Tests.StructuralAlloy
open Backend.Alloy Backend.Alloy.Structural

/-! Small kernel witnesses supplement, rather than replace, the native corpus.
[utest->req~compiler-structural-encoding~1]
[proof->req~compiler-structural-encoding~1] -/

theorem unrestricted_interval (width : Nat) (i : Instance) (env : List Nat) (r : Rel) :
    (interval {} r).eval width i env = some true := rfl

theorem empty_group_lower_bound :
    (interval ⟨1, .finite 1⟩ (.empty .unary)).eval 4 ⟨[], [], []⟩ [] = some false := by decide

def bagCore : IR.Structural.Core 3 := ⟨#v[
  { id := 100, name := "root", origin := .syntheticRoot },
  { id := 200, name := "same", parent := some 0 },
  { id := 300, name := "same", parent := some 0, reference := .bag 1 }], 0⟩
def bagCertificate : IR.Structural.Certificate 3 := ⟨#v[0, 1, 1], #v[0, 0, 0], #v[false, false, false]⟩
def bagValidated : IR.Structural.Validated 3 := ⟨bagCore, bagCertificate, by decide, by decide⟩

theorem bag_order : order bagValidated.toLayout = [0, 1, 2] := by
  have hc : ∀ a b : Fin 3,
      (bagValidated.toLayout.certificate.superRank[a] < bagValidated.toLayout.certificate.superRank[b] ||
        (bagValidated.toLayout.certificate.superRank[a] == bagValidated.toLayout.certificate.superRank[b] && a.val ≤ b.val)) =
      decide (a ≤ b) := by decide
  unfold order
  rw [funext (fun a => funext (hc a))]
  exact List.mergeSort_eq_self (r := (· ≤ ·)) (by decide)

set_option maxRecDepth 10000 in
theorem bag_heads_preserved :
    (Integer.count (childHeads bagCore 0)).eval 5 bagInstance [0] = some 3 := by decide

set_option maxRecDepth 10000 in
theorem set_key_enforced : (setKey bagValidated.toLayout 2 0).eval 5 bagInstance [] = some false := by
  simp only [setKey, allocation_head_apply, allocation_contains_apply,
    allocation_deref_apply, head, signatureId, bag_order]
  decide

set_option maxRecDepth 10000 in
theorem generated_bag_facts :
    (target bagValidated.toLayout (List.replicate 4 ⟨4, false⟩) 5).eval bagInstance = some true := by
  simp only [target, Module.eval, Instance.scalarFields, schema, facts, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, List.map_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    declarationFacts, ownership, setKey, allocation_head_apply, allocation_contains_apply,
    allocation_deref_apply, allocation_head, allocation_fields, allocation_signatures,
    head, signatureId, bag_order]
  decide

end ClaferCompiler.Tests.StructuralAlloy
