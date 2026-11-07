module

public import ClaferCompiler.Correctness.Behavioral.RepresentationInvariants
public import ClaferCompiler.Correctness.StructuralHierarchy
public import Mathlib.Data.Finset.Max

public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

/-- Inclusion is supplied by the target's declarations, including each inherited
pool on a source super path. -/
theorem target_ancestor_included (v : IR.Structural.Layout k) (i : Instance)
    (hd : i.declarations (schema v).declarations = true) {d e : Fin k}
    (path : (SemanticsBridge.Structural.interpret v.core).Ancestor d e)
    (x : Nat) (hx : x ∈ i.signatures[Backend.Alloy.Structural.signatureId v d]?.getD []) :
    x ∈ i.signatures[Backend.Alloy.Structural.signatureId v e]?.getD [] := by
  induction path with
  | refl => exact hx
  | @tail e f path edge ih =>
    change (v.core.get e).super = some f at edge
    exact Structural.declaration_included (schema v).declarations i hd _ _ _
      (Structural.schema_signature v e) (by simp [edge]) x ih

/-- The abstract object union has a child (the source root), so Alloy's abstract
leaf exception cannot leave an object outside every source declaration. -/
theorem target_pool_covered (v : IR.Structural.Layout k) (i : Instance)
    (hd : i.declarations (schema v).declarations = true) (x : Nat)
    (hx : x ∈ i.signatures[0]?.getD []) :
    ∃ d : Fin k, x ∈ i.signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] := by
  let s := (schema v).declarations
  let children := (s.signatures.zipIdx.filter fun (child, _) => child.parent == some 0).map Prod.snd
  have hr := Structural.schema_signature v v.core.root
  have rootParent := v.coreChecked.2.2.1.2.2.1
  have rootmem : Backend.Alloy.Structural.signatureId v v.core.root ∈ children := by
    apply List.mem_map.mpr
    refine ⟨_, List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hr, ?_⟩, rfl⟩
    simp [rootParent]
  have nonempty : children.isEmpty = false := by
    cases he : children with
    | nil => simp [he] at rootmem
    | cons a as => rfl
  have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hd).1
    ({ isAbstract := true }, 0) (by simp [schema, Backend.Alloy.Structural.schema])
  simp only [Id.run, pure, Bool.and_eq_true] at hh
  have cover : children.any (fun c => (i.signatures[c]?.getD []).contains x) = true := by
    have cov := hh.1.1.2
    change (!true || children.isEmpty || _) = true at cov
    simp only [Bool.not_true, Bool.false_or, nonempty] at cov
    exact List.all_eq_true.mp cov x hx
  obtain ⟨c, hc, hcx⟩ := List.any_eq_true.mp cover
  obtain ⟨⟨decl, c'⟩, hchild, hce⟩ := List.mem_map.mp hc
  dsimp at hce
  subst c'
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hchild).1
  have hp : decl.parent = some 0 := beq_iff_eq.mp (List.mem_filter.mp hchild).2
  have hn : c ≠ 0 := by
    intro hz
    subst c
    have he : decl = { isAbstract := true } := by
      simpa [s, schema, Backend.Alloy.Structural.schema] using hg.symm
    subst decl
    cases hp
  obtain ⟨d, rfl⟩ := Structural.signature_preimage v c decl hg hn
  exact ⟨d, List.contains_iff_mem.mp hcx⟩

theorem target_occupied_comparable (v : IR.Structural.Layout k) (i : Instance)
    (hw : (schema v).declarations.wellFormed = true)
    (hd : i.declarations (schema v).declarations = true) (x : Nat) (d e : Fin k)
    (hx : x ∈ i.signatures[Backend.Alloy.Structural.signatureId v d]?.getD [])
    (hy : x ∈ i.signatures[Backend.Alloy.Structural.signatureId v e]?.getD []) :
    (SemanticsBridge.Structural.interpret v.core).Ancestor d e ∨
      (SemanticsBridge.Structural.interpret v.core).Ancestor e d := by
  have pd := Structural.occupied_reachable (schema v).declarations i x hw hd
    (Structural.schema_parentless v) _ _ (Structural.schema_signature v d) hx
  have pe := Structural.occupied_reachable (schema v).declarations i x hw hd
    (Structural.schema_parentless v) _ _ (Structural.schema_signature v e) hy
  rcases Relation.ReflTransGen.total_of_right_unique
    (Structural.occupied_right_unique (schema v).declarations i x hd) pd pe with hp | hp
  · obtain ⟨f, hf, ha⟩ := Structural.occupied_source_path v i x d (by
      simpa only [Structural.occupiedEdge_signatures (schema v).declarations
        (Backend.Alloy.Structural.schema v) i x rfl] using hp)
    have hf := Backend.Alloy.Structural.signatureId_injective v hf
    exact Or.inr (hf ▸ ha)
  · obtain ⟨f, hf, ha⟩ := Structural.occupied_source_path v i x e (by
      simpa only [Structural.occupiedEdge_signatures (schema v).declarations
        (Backend.Alloy.Structural.schema v) i x rfl] using hp)
    have hf := Backend.Alloy.Structural.signatureId_injective v hf
    exact Or.inl (hf ▸ ha)

-- [proof->req~compiler-trace-representation~1]
/-- Actual target declarations and emitted abstract coverage determine a concrete
most-specific type and exactly its ancestor pools. No source configuration or
representation hypothesis is supplied. The finite maximum reuses the standard
finite-set construction underlying upstream `concrete_descendant`; target
hierarchy comparability additionally proves uniqueness of every occupied pool. -/
theorem target_identity_type (v : IR.Structural.Layout k) (w : Nat) (τ : Temporal.Trace)
    (hw : (schema v).declarations.wellFormed = true)
    (hd : (τ.state 0).declarations (schema v).declarations = true)
    (facts : ∀ f ∈ identityFacts v, f.Holds (schema v) w τ [] 0)
    (x : Nat) (hx : x ∈ (τ.state 0).signatures[0]?.getD []) :
    ∃ actual : Fin k, (v.core.get actual).isAbstract = false ∧
      ∀ d : Fin k, x ∈ (τ.state 0).signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] ↔
        IR.Behavioral.ancestor v.core actual d = true := by
  classical
  let members := Finset.univ.filter fun d : Fin k =>
    x ∈ (τ.state 0).signatures[Backend.Alloy.Structural.signatureId v d]?.getD []
  obtain ⟨first, hf⟩ := target_pool_covered v (τ.state 0) hd x hx
  obtain ⟨actual, hm, hmax⟩ := members.exists_max_image
    (fun d => v.certificate.superRank[d]) ⟨first, by simp [members, hf]⟩
  have ha : x ∈ (τ.state 0).signatures[Backend.Alloy.Structural.signatureId v actual]?.getD [] :=
    (Finset.mem_filter.mp hm).2
  have deepest : ∀ d, x ∈ (τ.state 0).signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] →
      (SemanticsBridge.Structural.interpret v.core).Ancestor actual d := by
    intro d hd'
    rcases target_occupied_comparable v (τ.state 0) hw hd x actual d ha hd' with path | path
    · exact path
    · rcases path.cases_head with he | ⟨p, hedge, rest⟩
      · exact he ▸ Relation.ReflTransGen.refl
      · have le := hmax d (by simp [members, hd'])
        have lt := v.coreChecked.2.2.2.2.1 d p hedge
        have reverse := Structural.ancestor_rank v rest
        omega
  refine ⟨actual, ?_, ?_⟩
  · cases hab : (v.core.get actual).isAbstract with
    | false => rfl
    | true =>
      have h := facts (.equal (pool v actual)
        (((Backend.Alloy.Structural.subtypes v.core actual).map (pool v)).foldl
          Temporal.Rel.union (.empty .unary))) (by
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨actual, List.mem_finRange _, ?_⟩
        simp only [hab, ↓reduceIte, List.mem_singleton])
      have poolmem : [.object x] ∈ (pool v actual).eval (schema v) w τ [] 0 := by
        change [.object x] ∈ ((τ.state 0).signatures[Backend.Alloy.Structural.signatureId v actual]?.getD []).map
          (fun a => [Temporal.Atom.object a])
        simpa using ha
      have right := (h [.object x]).mp poolmem
      rcases (poolUnion_rows v _ _ (.empty _) w τ [] 0 _).mp right with hempty | ⟨d, hd', hdm⟩
      · exact (List.not_mem_nil hempty).elim
      · have occupied : x ∈ (τ.state 0).signatures[Backend.Alloy.Structural.signatureId v d]?.getD [] := by
          change [.object x] ∈ ((τ.state 0).signatures[Backend.Alloy.Structural.signatureId v d]?.getD []).map
            (fun a => [Temporal.Atom.object a]) at hdm
          simpa using hdm
        exact (no_reverse_super v actual d
          ((Backend.Alloy.Structural.subtype_inventory v.core actual d).mp hd')
          (deepest d occupied)).elim
  · intro d
    constructor
    · exact fun hd' => (ancestor_agrees v.core actual d).mpr (deepest d hd')
    · intro path
      exact target_ancestor_included v (τ.state 0) hd ((ancestor_agrees v.core actual d).mp path) x ha

end ClaferCompiler.Correctness.Behavioral
