module

public import ClaferCompiler.Correctness.Behavioral.CompletionDeclarations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral

/-- Source identities contributing to each static scope, in compiler allocation
order. An inherited head counts each identity once, including absent objects. -/
def identityPool (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o) :
    Nat → List (Fin o)
  | 0 => List.finRange o
  | j + 1 => ((Backend.Alloy.Structural.order v)[j]?.map fun d =>
      (List.finRange o).filter (fun x => IR.Behavioral.ancestor v.core ids.directType[x] d)).getD []

-- [proof->req~compiler-behavioral-correctness~1]
/-- Finite source counts meet the requested exact or upper identity capacities.
This predicate contains no target satisfaction or formula evaluation. -/
def SourceScopeFits (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (scopes : List Scope) : Prop :=
  ∀ (j : Nat) (scope : Scope), scopes[j]? = some scope →
    if scope.exact then (identityPool v ids j).length = scope.size
    else (identityPool v ids j).length ≤ scope.size

theorem identityPool_nodup (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (j : Nat) : (identityPool v ids j).Nodup := by
  cases j with
  | zero => exact List.nodup_finRange o
  | succ j =>
    cases h : (Backend.Alloy.Structural.order v)[j]? with
    | none => simp [identityPool, h]
    | some d =>
      simpa [identityPool, h] using (List.nodup_finRange o).filter
        (fun x => IR.Behavioral.ancestor v.core ids.directType[x] d)

theorem encode_identityPool (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (j : Nat) :
    (encodeState v ids frame).signatures[j]?.getD [] =
      (identityPool v ids j).map (fun x => ids.ids[x]) := by
  cases j with
  | zero =>
    simp only [encodeState, identityPool, List.getElem?_cons_zero, Option.getD_some]
    apply List.ext_getElem
    · simp
    · intro j hj hk
      simp
  | succ j =>
    cases h : (Backend.Alloy.Structural.order v)[j]? <;>
      simp [encodeState, identityPool, h]

-- [proof->req~compiler-behavioral-correctness~1]
theorem encode_inScope (v : IR.Structural.Layout k)
    (source : IR.Behavioral.Lasso k o steps) (scopes : List Scope)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (fits : SourceScopeFits v source.identities scopes) :
    (encode v source).unfold.InScope scopes := by
  intro j scope hj
  refine ⟨(identityPool v source.identities j).map (fun x => source.identities.ids[x]),
    (identityPool_nodup v source.identities j).map unique, ?_, ?_⟩
  · intro x
    simp only [encode_unfold, encode_identityPool]
    exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
  · simpa only [List.length_map] using fits j scope hj

end ClaferCompiler.Correctness.Behavioral
