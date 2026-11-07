module

public import ClaferCompiler.Correctness.Behavioral.Representation
public import ClaferCompiler.Correctness.Behavioral.ExpressionsObservations

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral
open SemanticsBridge.Behavioral

namespace Relations

variable {U : Type} {f : U → Nat} {A B : Set U} {R S : U → U → Prop}
  {a b : Rel} {s : Schema} {w : Nat} {τ : Trace} {e : Environment} {t : Nat}

theorem binary_congr {r : Relation} (hr : Binary f R r) (he : ∀ x y, R x y ↔ S x y) :
    Binary f S r := by
  intro row
  rw [hr row]
  simp only [he]

theorem binary_product (ha : a.Term) (hb : b.Term)
    (hA : Unary f A (a.eval s w τ e t)) (hB : Unary f B (b.eval s w τ e t)) :
    Binary f (fun x y => x ∈ A ∧ y ∈ B) ((a.product b).eval s w τ e t) := by
  intro row
  rw [Rel.eval_product ha hb]
  simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨left, hl, right, hr, he⟩
    obtain ⟨x, hx, rfl⟩ := (hA left).mp hl
    obtain ⟨y, hy, rfl⟩ := (hB right).mp hr
    exact ⟨x, y, ⟨hx, hy⟩, he.symm⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨[.object (f x)], (hA _).mpr ⟨x, hx, rfl⟩,
      [.object (f y)], (hB _).mpr ⟨y, hy, rfl⟩, rfl⟩

theorem binary_inter (hf : Function.Injective f) (ha : a.Term) (hb : b.Term)
    (hR : Binary f R (a.eval s w τ e t)) (hS : Binary f S (b.eval s w τ e t)) :
    Binary f (fun x y => R x y ∧ S x y) ((a.inter b).eval s w τ e t) := by
  intro row
  rw [Rel.eval_inter ha hb]
  simp only [List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨x, y, hxy, rfl⟩ := (hR _).mp hr
    obtain ⟨z, q, hs, he⟩ := (hS _).mp hs
    have hz : x = z := hf (by simpa using (List.cons.inj he).1)
    have hq : y = q := hf (by simpa using (List.cons.inj (List.cons.inj he).2).1)
    subst z q
    exact ⟨x, y, ⟨hxy, hs⟩, rfl⟩
  · rintro ⟨x, y, ⟨hr, hs⟩, rfl⟩
    exact ⟨(hR _).mpr ⟨x, y, hr, rfl⟩, (hS _).mpr ⟨x, y, hs, rfl⟩⟩

theorem binary_transpose (ha : a.Term)
    (hR : Binary f R (a.eval s w τ e t)) :
    Binary f (fun x y => R y x) (a.transpose.eval s w τ e t) := by
  intro row
  rw [Rel.eval_transpose ha]
  simp only [List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨source, hs, he⟩
    obtain ⟨x, y, hr, rfl⟩ := (hR _).mp hs
    exact ⟨y, x, hr, by simpa using he.symm⟩
  · rintro ⟨x, y, hr, rfl⟩
    exact ⟨[.object (f y), .object (f x)], (hR _).mpr ⟨y, x, hr, rfl⟩, by simp⟩

end Relations

namespace TraceRep

variable {v : IR.Structural.Layout k} {source : IR.Behavioral.Lasso k o steps}
  {target : Lasso}

theorem pool_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat)
    (d : Fin k) :
    Relations.Unary rep.label {x | IR.Behavioral.ancestor v.core source.identities.directType[x] d = true}
      ((pool v d).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[Backend.Alloy.Structural.signatureId v d]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.pools]
  constructor
  · rintro ⟨label, ⟨x, hx, rfl⟩, hr⟩
    exact ⟨x, hx, hr.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rep.label x, ⟨x, hx, rfl⟩, rfl⟩

theorem objects_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label Set.univ ((Rel.sig 0).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[0]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.allObjects]
  constructor
  · rintro ⟨label, ⟨x, rfl⟩, hr⟩
    exact ⟨x, Set.mem_univ _, hr.symm⟩
  · rintro ⟨x, _, rfl⟩
    exact ⟨rep.label x, ⟨x, rfl⟩, rfl⟩

-- [proof->req~compiler-trace-representation~1]
theorem root_meaning (rep : TraceRep v source target)
    (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label {(trace source).identities.root}
      ((root v).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).signatures[Backend.Alloy.Structural.signatureId v v.core.root]?.getD []).map
    fun label => [Atom.object label]) ↔ _
  simp only [List.mem_map, rep.roots]
  constructor
  · rintro ⟨label, rfl, he⟩
    exact ⟨source.identities.root, rfl, he.symm⟩
  · rintro ⟨x, hx, rfl⟩
    subst x
    exact ⟨rep.label source.identities.root, rfl, rfl⟩

theorem parent_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Binary rep.label (fun x p => source.identities.parent[x] = some p)
      (parent.eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[0]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.parents]
  constructor
  · rintro ⟨labels, ⟨x, p, hp, rfl⟩, he⟩
    exact ⟨x, p, hp, he.symm⟩
  · rintro ⟨x, p, hp, rfl⟩
    exact ⟨[rep.label x, rep.label p], ⟨x, p, hp, rfl⟩, rfl⟩

theorem membership_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat) :
    Relations.Binary rep.label (fun x y => x = source.identities.root ∧ (source.at t).live[y] = true)
      ((Rel.field 1).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[1]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.lives]
  constructor
  · rintro ⟨labels, ⟨x, hx, rfl⟩, he⟩
    exact ⟨source.identities.root, x, ⟨rfl, hx⟩, he.symm⟩
  · rintro ⟨_, y, ⟨rfl, hy⟩, rfl⟩
    exact ⟨[rep.label source.identities.root, rep.label y], ⟨y, hy, rfl⟩, rfl⟩

theorem live_meaning (rep : TraceRep v source target)
    (w : Nat) (e : Environment) (t : Nat) :
    Relations.Unary rep.label ((trace source).live t)
      ((live v).eval (schema v) w target.unfold e t) := by
  have h := Relations.unary_image rep.label_injective (.sig _) (.field 1)
    (rep.root_meaning w e t) (rep.membership_meaning w e t)
  simpa [trace, identities, live, root, pool] using h

theorem head_meaning (rep : TraceRep v source target)
    (w : Nat) (e : Environment) (t : Nat) (d : Fin k) :
    Relations.Unary rep.label (((trace source).raw (SemanticsBridge.Structural.interpret v.core) t).head d)
      ((head v d).eval (schema v) w target.unfold e t) := by
  have h := Relations.unary_inter rep.label_injective (.sig _) (.join (.sig _) (.field 1))
    (rep.pool_meaning w e t d) (rep.live_meaning w e t)
  simpa [trace, identities, head, live, root, pool, Clafer.Behavioral.Trace.raw,
    Set.inter_def, ancestor_agrees, and_comm] using h

theorem deref_meaning (rep : TraceRep v source target) (w : Nat) (e : Environment) (t : Nat)
    (d : Fin k) :
    Relations.Binary rep.label ((trace source).deref t d)
      ((deref d).eval (schema v) w target.unfold e t) := by
  intro row
  change row ∈ (((target.unfold.state t).fields[2 + d.val]?.getD []).map (List.map Atom.object)) ↔ _
  simp only [List.mem_map, rep.references]
  constructor
  · rintro ⟨labels, ⟨x, y, hr, rfl⟩, he⟩
    exact ⟨x, y, hr, he.symm⟩
  · rintro ⟨x, y, hr, rfl⟩
    exact ⟨[rep.label x, rep.label y], ⟨x, y, hr, rfl⟩, rfl⟩

-- [proof->req~compiler-behavioral-correctness~1]
theorem step_meaning (rep : TraceRep v source target)
    (w : Nat) (e : Environment) (t : Nat) (st : IR.Behavioral.Step k) :
    Relations.Binary rep.label ((SemanticsBridge.Behavioral.step st).relation
      (SemanticsBridge.Structural.interpret v.core) (trace source) t)
      ((Backend.Alloy.Behavioral.step v st).eval (schema v) w target.unfold e t) := by
  cases st with
  | parent =>
    have h := Relations.binary_inter rep.label_injective (.field 0)
      (.product (.sig 0) (live_term v)) (rep.parent_meaning w e t)
      (Relations.binary_product (.sig 0) (live_term v) (rep.objects_meaning w e t)
        (rep.live_meaning w e t))
    apply Relations.binary_congr h
    intro x y
    simp [SemanticsBridge.Behavioral.step, Clafer.Behavioral.Step.relation, trace, identities]
  | child d =>
    cases hp : (v.core.get d).parent with
    | none =>
      intro row
      simp [Backend.Alloy.Behavioral.step, contains, hp, Rel.eval, Rel.fold,
        Rel.empty, RelAlgebra.step, relationAlgebra,
        SemanticsBridge.Behavioral.step, Clafer.Behavioral.Step.relation,
        Clafer.Behavioral.Trace.raw, SemanticsBridge.Structural.interpret]
    | some p =>
      have h := Relations.binary_inter rep.label_injective (.transpose (.field 0))
        (.product (live_term v) (head_term v d))
        (Relations.binary_transpose (.field 0) (rep.parent_meaning w e t))
        (Relations.binary_product (live_term v) (head_term v d)
          (rep.live_meaning w e t) (rep.head_meaning w e t d))
      simp only [Backend.Alloy.Behavioral.step, contains, hp]
      apply Relations.binary_congr h
      intro x y
      simp [SemanticsBridge.Behavioral.step, Clafer.Behavioral.Step.relation,
        Clafer.Behavioral.Trace.raw, Clafer.Behavioral.Trace.ParentAt,
        SemanticsBridge.Structural.interpret, trace, identities, hp, and_assoc, and_left_comm, and_comm]
  | deref d =>
    have h := Relations.binary_inter rep.label_injective (.field (2 + d.val))
      (.product (live_term v) (live_term v)) (rep.deref_meaning w e t d)
      (Relations.binary_product (live_term v) (live_term v)
        (rep.live_meaning w e t) (rep.live_meaning w e t))
    apply Relations.binary_congr h
    intro x y
    simp [SemanticsBridge.Behavioral.step, Clafer.Behavioral.Step.relation,
      trace, and_left_comm, and_comm]

/-- Discharges primitive agreement using concrete table equations. In particular,
the source formula interpretation is never a premise. -/
theorem primitiveAgreement (rep : TraceRep v source target)
    (w : Nat) :
    PrimitiveAgreement v w (trace source) target.unfold rep.label :=
  ⟨rep.label_injective, rep.root_meaning w, rep.live_meaning w,
    fun d e t => rep.head_meaning w e t d,
    fun st e t => rep.step_meaning w e t st⟩

end TraceRep
end ClaferCompiler.Correctness.Behavioral
