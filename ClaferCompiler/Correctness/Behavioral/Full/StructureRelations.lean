module

public import ClaferCompiler.Correctness.Behavioral.Full.Representation
public import ClaferCompiler.Correctness.Behavioral.RepresentationRelations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

theorem union_term (rs : List Rel) (terms : ∀ r ∈ rs, r.Term)
    (initial : Rel) (hi : initial.Term) : (rs.foldl Rel.union initial).Term := by
  induction rs generalizing initial with
  | nil => exact hi
  | cons r rs ih =>
    exact ih (fun a ha => terms a (List.mem_cons_of_mem _ ha)) _
      (.union hi (terms r List.mem_cons_self))

theorem union_rows (rs : List Rel) (terms : ∀ r ∈ rs, r.Term)
    (initial : Rel) (hi : initial.Term) (s : Schema) (w : Nat) (τ : Trace)
    (e : Environment) (t : Nat) (row : List Atom) :
    row ∈ (rs.foldl Rel.union initial).eval s w τ e t ↔
      row ∈ initial.eval s w τ e t ∨ ∃ r ∈ rs, row ∈ r.eval s w τ e t := by
  induction rs generalizing initial with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun a ha => terms a (List.mem_cons_of_mem _ ha)) _
      (.union hi (terms r List.mem_cons_self))]
    rw [Rel.eval_union hi (terms r List.mem_cons_self)]
    simp only [List.mem_eraseDups, List.mem_append, List.mem_cons]
    aesop

theorem pool_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) : (pool v d).Term := by
  unfold pool
  split
  · exact .ints
  · apply union_term _ ?_ _ (.empty _)
    intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    exact .sig _

theorem root_term (v : IR.BehavioralStructural.Validated k) : (root v).Term := .sig _
theorem live_term (v : IR.BehavioralStructural.Validated k) : (live v).Term := .join (.sig _) (.field 1)
theorem head_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) : (head v d).Term := by
  unfold head
  split
  · exact .ints
  · exact .inter (pool_term v d) (live_term v)

theorem contains_term (v : IR.BehavioralStructural.Validated k) (d : Fin k) : (contains v d).Term := by
  unfold contains
  split
  · exact .empty _
  · split
    · exact .product (root_term v) .ints
    · exact .inter (.transpose (.field _)) (.product (live_term v) (head_term v d))

theorem ancestor_iff (v : IR.BehavioralStructural.Validated k) (d c : Fin k) :
    c ∈ v.analysis.ancestors[d] ↔
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor d c :=
  ⟨SemanticsBridge.BehavioralStructural.ancestor_sound v.checked.2.1 v.checked.1.2.2.2.2.1,
    SemanticsBridge.BehavioralStructural.ancestor_complete v.checked.2.1⟩

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem direct_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) :
    Relations.Unary rep.label {x | source.objects.identities.directType[x] = d}
      ((directPool d).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[signatureId d]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.directTypes]
  constructor
  · rintro ⟨label, ⟨x, hx, rfl⟩, he⟩
    exact ⟨x, hx, he.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rep.label x, ⟨x, hx, rfl⟩, rfl⟩

theorem pool_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Relations.Unary rep.label {x | d ∈ v.analysis.ancestors[source.objects.identities.directType[x]]}
      ((pool v d).eval (schema v) w target.unfold e t) := by
  intro row
  unfold pool
  rw [ordinary]
  simp only [Bool.false_eq_true, ↓reduceIte, union]
  rw [union_rows _ (by intro r hr; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr; exact .sig _) _ (.empty _)]
  simp only [Rel.eval, Rel.fold, Rel.empty, List.foldl_cons, List.foldl_nil,
    RelAlgebra.step, relationAlgebra, List.not_mem_nil, false_or,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨c, hc, rfl⟩, hr⟩
    obtain ⟨x, hx, he⟩ := (rep.direct_meaning w e t c row).mp hr
    change source.objects.identities.directType[x] = c at hx
    subst c
    exact ⟨x, hc, he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨directPool source.objects.identities.directType[x],
      ⟨source.objects.identities.directType[x], hx, rfl⟩,
      (rep.direct_meaning w e t _ row).mpr ⟨x, rfl, he⟩⟩

theorem objects_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label Set.univ ((Rel.sig 0).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[0]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.allObjects]
  constructor
  · rintro ⟨label, ⟨x, rfl⟩, he⟩; exact ⟨x, Set.mem_univ _, he.symm⟩
  · rintro ⟨x, _, rfl⟩; exact ⟨rep.label x, ⟨x, rfl⟩, rfl⟩

theorem root_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label {source.objects.identities.root}
      ((root v).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[signatureId v.core.structural.root]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.roots]
  constructor
  · rintro ⟨label, rfl, he⟩; exact ⟨source.objects.identities.root, rfl, he.symm⟩
  · rintro ⟨x, hx, rfl⟩
    subst x
    exact ⟨rep.label source.objects.identities.root, rfl, rfl⟩

theorem parent_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Binary rep.label (fun x p => source.objects.identities.parent[x] = some p)
      (parent.eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[0]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.parents]
  constructor
  · rintro ⟨labels, ⟨x, p, hp, rfl⟩, he⟩; exact ⟨x, p, hp, he.symm⟩
  · rintro ⟨x, p, hp, rfl⟩
    exact ⟨[rep.label x, rep.label p], ⟨x, p, hp, rfl⟩, rfl⟩

theorem membership_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Binary rep.label (fun x y => x = source.objects.identities.root ∧
      (source.objects.at t).live[y] = true)
      ((Rel.field 1).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[1]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.lives]
  constructor
  · rintro ⟨labels, ⟨x, hx, rfl⟩, he⟩
    exact ⟨source.objects.identities.root, x, ⟨rfl, hx⟩, he.symm⟩
  · rintro ⟨_, y, ⟨rfl, hy⟩, rfl⟩
    exact ⟨[rep.label source.objects.identities.root, rep.label y], ⟨y, hy, rfl⟩, rfl⟩

theorem live_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label {x | (source.objects.at t).live[x] = true}
      ((live v).eval (schema v) w target.unfold e t) := by
  have h := Relations.unary_image rep.label_injective (.sig _) (.field 1)
    (rep.root_meaning w e t) (rep.membership_meaning w e t)
  simpa [live, root, directPool] using h

theorem head_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Relations.Unary rep.label {x | (source.objects.at t).live[x] = true ∧
      d ∈ v.analysis.ancestors[source.objects.identities.directType[x]]}
      ((head v d).eval (schema v) w target.unfold e t) := by
  have h := Relations.unary_inter rep.label_injective (pool_term v d) (live_term v)
    (rep.pool_meaning w e t d ordinary) (rep.live_meaning w e t)
  simpa [head, ordinary, Set.inter_def, and_comm] using h

theorem head_source (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Relations.Unary rep.label
      (((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).head d)
      ((head v d).eval (schema v) w target.unfold e t) := by
  intro row
  rw [rep.head_meaning w e t d ordinary row]
  simp only [Set.mem_ofPred_eq, ancestor_iff, Clafer.Behavioral.Trace.raw,
    SemanticsBridge.Behavioral.trace, SemanticsBridge.Behavioral.identities]

theorem contains_source (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) (ordinary : integerDeclaration v d = false) :
    Relations.Binary rep.label
      (((SemanticsBridge.Behavioral.trace source.objects).raw
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore t).contains d)
      ((contains v d).eval (schema v) w target.unfold e t) := by
  cases hp : (v.core.structural.get d).parent with
  | none =>
    intro row
    simp only [contains, hp]
    constructor
    · intro h; exact List.not_mem_nil h |>.elim
    · rintro ⟨x, y, hy, _⟩
      exact (hy.2.2 hp).elim
  | some p =>
    have product := Relations.binary_product (live_term v) (head_term v d)
      (rep.live_meaning w e t) (rep.head_source w e t d ordinary)
    have inverse := Relations.binary_transpose (.field 0) (rep.parent_meaning w e t)
    have both := Relations.binary_inter rep.label_injective (.transpose (.field 0))
      (.product (live_term v) (head_term v d)) inverse product
    apply Relations.binary_congr (by simpa only [contains, hp, ordinary, Bool.false_eq_true,
      ↓reduceIte, parent] using both)
    intro x y
    change (source.objects.identities.parent[y] = some x ∧
      (source.objects.at t).live[x] = true ∧ (source.objects.at t).live[y] = true ∧
      (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
        source.objects.identities.directType[y] d) ↔
      (((source.objects.at t).live[x] = true ∧ (source.objects.at t).live[y] = true ∧
        source.objects.identities.parent[y] = some x) ∧
        (SemanticsBridge.BehavioralStructural.interpret v.core).toEffectiveCore.Ancestor
          source.objects.identities.directType[y] d ∧ (v.core.structural.get d).parent ≠ none)
    rw [hp]
    tauto

theorem rawDeref_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment)
    (t : Nat) (d : Fin k) :
    Relations.Binary rep.label (fun x y => (d, x, y) ∈ (source.objects.at t).references)
      ((rawDeref d).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[2 + d.val]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.references]
  constructor
  · rintro ⟨labels, ⟨x, y, hr, rfl⟩, he⟩; exact ⟨x, y, hr, he.symm⟩
  · rintro ⟨x, y, hr, rfl⟩
    exact ⟨[rep.label x, rep.label y], ⟨x, y, hr, rfl⟩, rfl⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
