module

public import ClaferCompiler.Correctness.Behavioral.CompletionFacts
public import ClaferCompiler.Correctness.Behavioral.RepresentationTables
public import ClaferCompiler.Correctness.StructuralCompletionDeclarations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

/-- Static identity heads include currently absent objects. Only inheritance
observations are used here; snapshot multiplicities are checked separately. -/
def identityConfiguration (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o) :
    Clafer.Semantics.Configuration (Fin k) (Fin o) where
  root := ids.root
  head := fun d => {x | (SemanticsBridge.Structural.interpret v.core).Ancestor ids.directType[x] d}
  contains := fun _ _ _ => False
  deref := fun _ _ _ => False

theorem identity_inherits (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o) :
    (identityConfiguration v ids).Inherits (SemanticsBridge.Structural.interpret v.core) := by
  intro d c h x hx
  exact hx.tail h

theorem identity_disjoint (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o) :
    (identityConfiguration v ids).DeclarationDisjoint (SemanticsBridge.Structural.interpret v.core) := by
  intro d e x hd he
  exact Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)) hd he

def identityObjects (ids : IR.Behavioral.Identities k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y) :
    Fin o ≃ {x : Nat // x ∈ ids.ids.toList} :=
  Equiv.ofBijective (fun x => ⟨ids.ids[x], by
    simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
    exact ⟨x.val, x.isLt, rfl⟩⟩) (by
      constructor
      · intro x y h
        exact unique x y (congrArg Subtype.val h)
      · rintro ⟨a, ha⟩
        obtain ⟨j, hj, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp ha)
        exact ⟨⟨j, hj⟩, Subtype.ext he⟩)

theorem encodeState_extent_live (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o) (j a : Nat)
    (h : a ∈ (encodeState v ids frame).signatures[j]?.getD []) : a ∈ ids.ids.toList := by
  cases j with
  | zero => exact h
  | succ j =>
    simp only [encodeState, List.getElem?_cons_succ, List.getElem?_map] at h
    cases he : (Backend.Alloy.Structural.order v)[j]? with
    | none => simp [he] at h
    | some d =>
      simp only [he, Option.map_some, Option.getD_some, List.mem_map, List.mem_filter] at h
      obtain ⟨x, _, rfl⟩ := h
      simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
      exact ⟨x.val, x.isLt, rfl⟩

-- [proof->req~compiler-behavioral-correctness~1]
theorem encodeState_declarations (v : IR.Structural.Layout k) (ids : IR.Behavioral.Identities k o)
    (frame : IR.Behavioral.Frame k o)
    (unique : ∀ x y : Fin o, ids.ids[x] = ids.ids[y] → x = y)
    (rootType : ids.directType[ids.root] = v.core.root)
    (concrete : ∀ x : Fin o, (v.core.get ids.directType[x]).isAbstract = false) :
    (encodeState v ids frame).declarations (schema v).declarations = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Structural.signature_declarations_of_observations v (identityConfiguration v ids)
      (encodeState v ids frame) (identityObjects ids unique)
    · intro d x
      simp only [encode_pool, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
      change (SemanticsBridge.Structural.interpret v.core).Ancestor ids.directType[x] d ↔
        ∃ y, IR.Behavioral.ancestor v.core ids.directType[y] d = true ∧ ids.ids[y] = ids.ids[x]
      constructor
      · intro h; exact ⟨x, (ancestor_agrees _ _ _).mpr h, rfl⟩
      · rintro ⟨y, h, he⟩; exact unique y x he ▸ (ancestor_agrees _ _ _).mp h
    · exact encodeState_extent_live v ids frame
    · intro x; exact ⟨ids.directType[x], .refl⟩
    · exact identity_inherits v ids
    · intro d ha x hx
      rcases hx.cases_tail with he | ⟨c, hc, hedge⟩
      · have impossible : true = false := ha.symm.trans (he ▸ concrete x)
        cases impossible
      · exact ⟨c, hedge, hc⟩
    · exact identity_disjoint v ids
  · apply List.all_eq_true.mpr
    rintro ⟨field, j⟩ hj
    have hj := List.mk_mem_zipIdx_iff_getElem?.mp hj
    have label_mem (x : Fin o) : ids.ids[x] ∈ ids.ids.toList := by
      simp only [Vector.mem_toList_iff, Vector.mem_iff_getElem]
      exact ⟨x.val, x.isLt, rfl⟩
    have root_mem : ids.ids[ids.root] ∈ (encodeState v ids frame).signatures[
        Backend.Alloy.Structural.signatureId v v.core.root]?.getD [] := by
      rw [encode_pool]
      apply List.mem_map.mpr
      refine ⟨ids.root, List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, rfl⟩
      apply (ancestor_agrees _ _ _).mpr
      change (SemanticsBridge.Structural.interpret v.core).Ancestor ids.directType[ids.root] v.core.root
      rw [rootType]
      exact .refl
    cases j with
    | zero =>
      have hf : field = { owner := 0, target := 0 } := by simpa [schema] using hj.symm
      subst field
      simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
      refine ⟨?_, fun _ _ => True.intro⟩
      intro row hr
      simp only [encodeState, List.cons_append, List.getElem?_cons_zero, Option.getD_some,
        List.mem_flatMap, List.mem_map, Option.mem_toList] at hr
      obtain ⟨x, _, p, _, rfl⟩ := hr
      simp [encodeState]
    | succ j => cases j with
      | zero =>
        have hf : field = { owner := Backend.Alloy.Structural.signatureId v v.core.root, target := 0 } := by
          simpa [schema] using hj.symm
        subst field
        simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
        refine ⟨?_, fun _ _ => True.intro⟩
        intro row hr
        simp only [encodeState, List.cons_append, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, List.mem_map] at hr
        obtain ⟨x, _, rfl⟩ := hr
        simp only [Bool.and_eq_true, List.contains_iff_mem]
        exact ⟨root_mem, label_mem x⟩
      | succ j =>
        have hj' : j < k := by
          have := List.getElem?_eq_some_iff.mp hj |>.1
          simpa [schema] using this
        have hf : field = { owner := 0, target := 0 } := by
          simpa [schema, List.getElem?_append_right, hj'] using hj.symm
        subst field
        simp only [Multiplicity.holds, List.all_eq_true, Bool.and_eq_true]
        refine ⟨?_, fun _ _ => True.intro⟩
        intro row hr
        rw [show j + 1 + 1 = 2 + (⟨j, hj'⟩ : Fin k).val by change j + 1 + 1 = 2 + j; omega, encode_references] at hr
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr
        simp [encodeState]

-- [proof->req~compiler-behavioral-correctness~1]
/-- Encoding establishes the target declaration model, including immutable
identity pools and parents and disjoint types across different frames. -/
theorem encode_declarations (v : IR.Structural.Layout k)
    (source : IR.Behavioral.Lasso k o steps)
    (unique : ∀ x y : Fin o, source.identities.ids[x] = source.identities.ids[y] → x = y)
    (refs : ∀ t, (source.at t).references.Nodup)
    (valid : (trace source).identities.Valid (SemanticsBridge.Structural.interpret v.core)) :
    (encode v source).unfold.Declarations (schema v) := by
  have decl t := encodeState_declarations v source.identities (source.at t)
    unique valid.root_type valid.concrete
  refine ⟨labels_nodup source.identities.ids unique, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [encode_unfold]
    refine ⟨encodeState_wellFormed v source.identities (source.at t) unique (refs t), decl t, ?_⟩
    intro xs hxs a ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hxs
    exact encodeState_extent_live v source.identities (source.at t) j a (by simp [hj, ha])
  · intro j _ t a
    simp only [encode_unfold, encodeState]
  · intro j hj t row
    have hz : j = 0 := by
      cases j with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => simp [schema] at hj
        | succ j => simp [schema, List.getElem?_replicate] at hj
    subst j
    simp [encodeState]
  · intro i j a b hi hj hij hp t u x hx hy
    apply hij
    apply Structural.declaration_siblings (schema v).declarations
      (encodeState v source.identities (source.at 0)) (decl 0) i j a b hi hj hp x
    · simpa only [encode_unfold, encodeState] using hx
    · simpa only [encode_unfold, encodeState] using hy

end ClaferCompiler.Correctness.Behavioral
