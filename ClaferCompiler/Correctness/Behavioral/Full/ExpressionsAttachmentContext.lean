module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsContexts
public import ClaferCompiler.Correctness.Behavioral.Full.CollectionsExtreme
public import ClaferCompiler.Correctness.Behavioral.RepresentationContext
public import ClaferCompiler.Backend.Alloy.Behavioral.Full.Compile

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral.Full

namespace Expressions

-- [proof->req~compiler-behavioral-partial-lowering~1]
/-- The executable initial context contains a frozen cover of every object and
all representable integer literals, with no hypothesis about expression truth. -/
theorem attachmentContextWith (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (s : Schema) (τ : Trace) (labels : Fin o ↪ Nat) (owner : Fin o)
    (objects : List (Fin o)) (length : objects.length = b.objects) (covers : ∀ x, x ∈ objects)
    (this : Rel) (term : this.Term)
    (thisRows : ∀ t, Mixed.Unary (completionAtom labels) {Sum.inl owner}
      (this.eval s b.bitwidth τ (.object (labels owner) :: objects.map (fun x => .object (labels x))) t)) :
    LexicalRows (estimates v b) s τ labels
      { context b with lexical := { (context b).lexical with this := this } }
      (.closed (Sum.inl owner))
      (.object (labels owner) :: objects.map (fun x => .object (labels x))) := by
  have aliasAt (i : Nat) (hi : i < objects.length) :
      ∀ t, Mixed.Unary (completionAtom labels) {Sum.inl objects[i]}
        ((Rel.var (i + 1)).eval s b.bitwidth τ
          (.object (labels owner) :: objects.map (fun x => .object (labels x))) t) := by
    intro t row
    change row ∈ (((.object (labels owner) :: objects.map (fun x => .object (labels x)))[i + 1]?).toList.map
      fun x => [x]) ↔ ∃ x ∈ ({Sum.inl objects[i]} : Set (Completion o)), row = [completionAtom labels x]
    simp [hi]
  refine ⟨⟨term, thisRows, trivial, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩,
    ⟨?_, (fun i => Fin.elim0 i)⟩, ?_, ?_⟩
  · refine ⟨Set.finite_singleton _, by simp [estimates], ?_⟩
    intro x hx typed
    obtain rfl := Set.mem_singleton_iff.mp hx
    obtain ⟨z, impossible⟩ := (completeIntegers_domain _).mp typed
    cases impossible
  · intro entry member
    change entry ∈ (List.range b.objects).map (fun i => Rel.var (i + 1)) ++
      (integerCandidates ⟨Backend.Alloy.minInt b.bitwidth, Backend.Alloy.maxInt b.bitwidth⟩).map Rel.integer at member
    rcases List.mem_append.mp member with hm | hm
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨.var _, fun _ _ _ => Iff.rfl⟩
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨.integer _, fun _ _ _ => Iff.rfl⟩
  · intro x hx
    cases x with
    | inl x =>
      obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp (covers x)
      refine ⟨.var (i + 1), List.mem_append_left _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr (length ▸ hi), rfl⟩), ?_⟩
      simpa only [equal, estimates] using aliasAt i hi
    | inr z =>
      have fit : Backend.Alloy.fitsInt b.bitwidth z = true := hx
      have range : (⟨Backend.Alloy.minInt b.bitwidth, Backend.Alloy.maxInt b.bitwidth⟩ : IR.Expr.Interval).Contains z := by
        simp only [Backend.Alloy.fitsInt, Bool.and_eq_true, decide_eq_true_eq] at fit
        exact ⟨fit.1.2, fit.2⟩
      refine ⟨.integer z, List.mem_append_right _
        (List.mem_map.mpr ⟨z, (integerCandidates_member _ _).mpr range, rfl⟩), ?_⟩
      intro t
      exact Extreme.integer_rows labels z fit

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem attachmentContext (v : IR.BehavioralStructural.Validated k) (b : Bounds)
    (s : Schema) (τ : Trace) (labels : Fin o ↪ Nat) (owner : Fin o)
    (objects : List (Fin o)) (length : objects.length = b.objects) (covers : ∀ x, x ∈ objects) :
    LexicalRows (estimates v b) s τ labels (context b) (.closed (Sum.inl owner))
      (.object (labels owner) :: objects.map (fun x => .object (labels x))) :=
  attachmentContextWith v b s τ labels owner objects length covers (.var 0) (.var 0)
    (fun _ => Mixed.unary_singleton _)

end Expressions

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-behavioral-partial-lowering~1]
theorem root_attachmentContext (rep : TraceRep v source target) (b : Bounds)
    (objects : List (Fin o)) (length : objects.length = b.objects) (covers : ∀ x, x ∈ objects) :
    Expressions.LexicalRows (estimates v b) (schema v) target.unfold rep.labels
      { context b with lexical := { (context b).lexical with this := root v } }
      (.closed (Sum.inl source.objects.identities.root))
      (.object (rep.label source.objects.identities.root) :: objects.map (fun x => .object (rep.label x))) :=
  Expressions.attachmentContextWith v b (schema v) target.unfold rep.labels
    source.objects.identities.root objects length covers (root v) (root_term v)
    (fun t => rep.root_completed v.core.structural.root b.bitwidth _ t)

-- [proof->req~compiler-full-behavioral-correctness~1]
/-- Reuses the established existential pool-cover argument with the full
schema's concrete object representation. Integers are never enumerated here. -/
theorem exists_many_meaning (rep : TraceRep v source target) (w : Nat)
    (n : Nat) (body : Formula) (hb : body.Built) (e : Environment) (t : Nat) :
    (Nat.repeat (Formula.exists_ (.sig 0)) n body).Holds (schema v) w target.unfold e t ↔
      ∃ objects : List (Fin o), objects.length = n ∧
        body.Holds (schema v) w target.unfold
          (objects.map (fun x => .object (rep.label x)) ++ e) t := by
  induction n generalizing e with
  | zero => simp [Nat.repeat]
  | succ n ih =>
    simp only [Nat.repeat, Formula.Holds,
      Formula.fold_exists _ _ _ (Behavioral.exists_many_built n body hb)]
    change (∃ atom, [atom] ∈ (Rel.sig 0).eval (schema v) w target.unfold e t ∧
      (Nat.repeat (Formula.exists_ (.sig 0)) n body).Holds (schema v) w target.unfold (atom :: e) t) ↔ _
    constructor
    · rintro ⟨atom, ha, hbody⟩
      obtain ⟨x, _, he⟩ := (rep.objects_meaning w e t [atom]).mp ha
      have he : atom = .object (rep.label x) := List.cons.inj he |>.1
      subst atom
      obtain ⟨objects, hn, hp⟩ := (ih _).mp hbody
      exact ⟨objects ++ [x], by simp [hn], by simpa [Formula.Holds, List.map_append, List.append_assoc] using hp⟩
    · rintro ⟨objects, hn, hp⟩
      rcases objects.eq_nil_or_concat' with rfl | ⟨front, x, rfl⟩
      · simp at hn
      · refine ⟨.object (rep.label x), (rep.objects_meaning w e t _).mpr ⟨x, Set.mem_univ _, rfl⟩, ?_⟩
        apply (ih _).mpr
        exact ⟨front, by simpa using hn, by simpa [Formula.Holds, List.map_append, List.append_assoc] using hp⟩

end TraceRep

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem aliases_meaning (s : Schema) (w : Nat) (τ : Trace) (f : U → Nat)
    (objects : List U) (t : Nat) :
    Relations.Unary f {x | x ∈ objects}
      ((((List.range objects.length).map Rel.var).foldl Rel.union (.empty .unary)).eval
        s w τ (objects.map fun x => Atom.object (f x)) t) := by
  intro row
  rw [union_rows _ (by intro r hr; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr; exact .var _) _ (.empty _)]
  have hempty : (Rel.empty .unary).eval s w τ (objects.map fun x => Atom.object (f x)) t = [] := rfl
  rw [hempty]
  simp only [List.not_mem_nil, false_or, List.mem_map, List.mem_range, exists_exists_and_eq_and]
  constructor
  · rintro ⟨i, hi, hr⟩
    have he : (Rel.var i).eval s w τ (objects.map fun x => Atom.object (f x)) t =
        [[.object (f objects[i])]] := by
      change (((objects.map fun x => Atom.object (f x))[i]?).toList.map fun x => [x]) = _
      simp [hi]
    rw [he] at hr
    exact ⟨objects[i], List.getElem_mem hi, List.mem_singleton.mp hr⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i, hi, ?_⟩
    change [Atom.object (f x)] ∈ (((objects.map fun x => Atom.object (f x))[i]?).toList.map fun x => [x])
    simp [hi, he]

namespace TraceRep
variable {v : IR.BehavioralStructural.Validated k}
  {source : ObservedLasso k o steps} {target : Lasso}

-- [proof->req~compiler-full-behavioral-correctness~1]
theorem coverPool_meaning (rep : TraceRep v source target) (w capacity : Nat)
    (body : Formula) (hb : body.Built) :
    (Backend.Alloy.Behavioral.coverPool capacity body).Holds (schema v) w target.unfold [] 0 ↔
      ∃ objects : List (Fin o), objects.length = capacity ∧ (∀ x, x ∈ objects) ∧
        body.Holds (schema v) w target.unfold (objects.map fun x => .object (rep.label x)) 0 := by
  unfold Backend.Alloy.Behavioral.coverPool
  rw [rep.exists_many_meaning w capacity _ (.binary .conj (.equal _ _) hb)]
  constructor
  · rintro ⟨objects, hn, h⟩
    simp only [List.append_nil] at h
    rw [← hn] at h
    change (Formula.binary .conj _ body).Holds _ _ _ _ _ at h
    rw [Encoding.holds_and (.equal _ _) hb] at h
    have he := (Relations.unary_equal rep.label_injective
      (aliases_meaning (schema v) w target.unfold rep.label objects 0)
      (rep.objects_meaning w (objects.map fun x => .object (rep.label x)) 0)).mp h.1
    refine ⟨objects, hn, ?_, h.2⟩
    intro x
    have hx : x ∈ ({y | y ∈ objects} : Set (Fin o)) := he.symm ▸ Set.mem_univ x
    exact hx
  · rintro ⟨objects, hn, hc, hp⟩
    refine ⟨objects, hn, ?_⟩
    simp only [List.append_nil]
    rw [← hn, Encoding.holds_and (.equal _ _) hb]
    refine ⟨?_, hp⟩
    apply (Relations.unary_equal rep.label_injective
      (aliases_meaning (schema v) w target.unfold rep.label objects 0)
      (rep.objects_meaning w (objects.map fun x => .object (rep.label x)) 0)).mpr
    ext x
    simp [hc x]

end TraceRep
end ClaferCompiler.Correctness.Behavioral.Full
