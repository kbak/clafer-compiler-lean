module

public import ClaferCompiler.Backend.Alloy.ExpressionAttachments
public import ClaferCompiler.Correctness.ExpressionPreservation
public import ClaferCompiler.Correctness.InheritedGeneration

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction

/-- Standard `mapM` retains each input/output occurrence. This small relational
lemma specializes the existing traversal; it is not a replacement traversal. -/
theorem mapM_pairs {α β ε : Type} (f : α → Except ε β) (xs : List α) {ys : List β}
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure] at h; cases h; exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases ht : xs.mapM f with
      | error e => simp [hx, ht, bind, Except.bind] at h
      | ok tail =>
        simp only [hx, ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst ys
        exact .cons hx (ih ht)

theorem pairs_map {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (g : β → α) (hg : ∀ x y, R x y → g y = x) : ys.map g = xs := by
  induction h with
  | nil => rfl
  | cons hh _ ih => simp only [List.map_cons, hg _ _ hh, ih]

theorem pairs_forall {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (P : β → Prop) (hp : ∀ x y, R x y → P y) :
    ∀ y ∈ ys, P y := by
  induction h with
  | nil => simp
  | cons hh _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hp _ _ hh
    · exact ih y hy

theorem bindMap_built (v : IR.Inherited.Validated n) (e : MapRef n) (r : Rel)
    (h : bindMap v e = .ok r) : r.Term := by
  cases hf : (List.finRange n).find? (fun d => (v.core.structural.get d).id == e.owner) with
  | none => cases hk : e.kind <;> simp [bindMap, hf] at h
  | some d =>
    cases hk : e.kind <;> simp only [bindMap, hk, hf] at h
    all_goals split at h
    all_goals simp_all [bind, Except.bind, pure, Except.pure]
    all_goals subst r
    · exact .field _
    · exact .transpose (.field _)
    · exact .field _
    · exact .join (.field _) (.field _)
    · exact .diagonal (.sig _)

theorem bindSupport_output (v : IR.Inherited.Validated n) (s : Support n m)
    (owner : Fin n) (l : Layout n m) (h : bindSupport v s owner = .ok l) :
    s.context = owner ∧ LayoutBuilt l ∧ l.extents = Vector.ofFn (Structural.head v.layout) := by
  dsimp only [bindSupport] at h
  split at h
  · simp [bind, Except.bind] at h
  · rename_i hguard
    have hctx : s.context = owner := by
      simp only [Bool.or_eq_true, not_or, bne_iff_ne, not_not] at hguard
      exact hguard.1
    cases hm : (List.finRange m).mapM (fun edge => bindMap v (s.maps.get edge)) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok maps =>
      simp only [hm, bind, Except.bind] at h
      split at h
      · rename_i hlen
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst l
        refine ⟨hctx, ⟨?_, ?_⟩, rfl⟩
        · intro x
          simpa [Vector.get, Vector.ofFn, Structural.head] using (Rel.Term.sig (Structural.signatureId v.layout x))
        · intro edge
          have hall := pairs_forall (mapM_pairs _ _ hm) Rel.Term (fun x r hr => bindMap_built v _ _ hr)
          have hmemb : maps[edge.val]'(by omega) ∈ maps := List.getElem_mem _
          simpa [Vector.get] using hall _ hmemb
      · cases h

theorem validateBounds_term (s : Support n m) (b : IR.Expr.Bounds n) (e : Term n m)
    (a : Admitted s b [] .boolean) (h : validateBounds s b [] .boolean e = .ok a) :
    a.checked.term = e := by
  unfold validateBounds at h
  cases hc : IR.Expr.check s [] .boolean e with
  | error err => simp [hc] at h
  | ok checked =>
    simp only [hc] at h
    split at h
    · split at h
      · cases h
      · cases h
        exact SemanticsBridge.Expr.check_preserves s [] .boolean e checked hc
    · cases h

theorem encodeBody_output (v : IR.Inherited.Validated n) (b : IR.Expr.Bounds n)
    (body : Body n) (out : EncodedBody n) (h : encodeBody v b body = .ok out) :
    ∃ (l : Layout n body.mapCount) (a : Admitted body.support b [] .boolean),
      bindSupport v body.support body.owner = .ok l ∧
      validateBounds body.support b [] .boolean body.term = .ok a ∧
      a.checked.term = body.term ∧
      out = ⟨body, attach (Structural.head v.layout body.owner) (encode l a),
        (encode l a).defined, (encode l a).value⟩ := by
  unfold encodeBody at h
  cases hl : bindSupport v body.support body.owner with
  | error e => simp [hl, bind, Except.bind] at h
  | ok l =>
    cases ha : validateBounds body.support b [] .boolean body.term with
    | error e => simp [hl, ha, bind, Except.bind, Except.mapError] at h
    | ok a =>
      simp only [hl, ha, Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      exact ⟨l, a, rfl, rfl, validateBounds_term _ _ _ _ ha, h.symm⟩

theorem encodeBody_original (v : IR.Inherited.Validated n) (b : IR.Expr.Bounds n)
    (body : Body n) (out : EncodedBody n) (h : encodeBody v b body = .ok out) :
    out.original = body := by
  obtain ⟨l, a, _, _, _, rfl⟩ := encodeBody_output v b body out h
  rfl

theorem check_raw (raw : Module) (checked : CheckedModule) (h : Backend.Alloy.check raw = .ok checked) :
    checked.raw = raw := by
  unfold Backend.Alloy.check at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem compile_output (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v bounds intervals bodies = .ok out) :
    ∃ base, Inherited.compile v bounds = .ok base ∧
      bodies.mapM (encodeBody v (sourceBounds v bounds intervals)) = .ok out.bodies ∧
      numericFacts v bounds intervals = .ok out.numericFacts ∧
      out.module.raw.facts = base.module.raw.facts ++ out.numericFacts ++ out.bodies.map EncodedBody.formula ∧
      out.module.raw.command = base.module.raw.command := by
  unfold compile at h
  cases hb : Inherited.compile v bounds with
  | error e => simp [hb, bind, Except.bind] at h
  | ok base =>
    cases hn : numericFacts v bounds intervals with
    | error e => simp [hb, hn, bind, Except.bind] at h
    | ok nums =>
      cases he : bodies.mapM (encodeBody v (sourceBounds v bounds intervals)) with
      | error e => simp [hb, hn, he, bind, Except.bind] at h
      | ok encoded =>
        simp only [hb, hn, he, bind, Except.bind] at h
        split at h
        · cases h
        · cases h
        · rename_i checked hc
          cases h
          have hr := check_raw _ checked hc
          exact ⟨base, rfl, rfl, rfl, congrArg Module.facts hr, by simpa only using congrArg Module.command hr⟩

theorem occurrences_preserved (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v bounds intervals bodies = .ok out) : out.bodies.map EncodedBody.original = bodies := by
  obtain ⟨base, _, he, _⟩ := compile_output v bounds intervals bodies out h
  exact pairs_map (mapM_pairs _ _ he) EncodedBody.original (encodeBody_original v _)

/-- Independent interpretation of an original body at its recorded owners.
This predicate refers only to source syntax, its type proof, and upstream meaning. -/
def SourceHolds (body : Body n) (o : Observation n body.mapCount)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support body.support) Atom) : Prop :=
  ∃ ht : body.term.Typed body.support [] .boolean,
    ∀ owner ∈ atomSet o.objects[body.owner],
      (interpret body.support body.term.raw ht).denote model
        (Clafer.Constraints.Environment.closed owner) = some ⟨True⟩

/-- Domain/representation conditions for one attachment. No constraint truth,
source extraction success, or target evaluation appears in these conditions. -/
structure Realization (v : IR.Inherited.Validated n) (b : IR.Expr.Bounds n)
    (body : Body n) (i : Instance) where
  layout : Layout n body.mapCount
  bound : bindSupport v body.support body.owner = .ok layout
  observation : Observation n body.mapCount
  valid : ObservationValid body.support observation
  bounded : observation.withinBounds body.support b = true
  atoms : Atom → Nat
  leaves : LayoutRep body.support layout observation i atoms
  model : Clafer.Constraints.IntegerBinding.{0,0} (support body.support) Atom
  fullExtension : ExtendsObservation body.support observation valid model

theorem encoded_body_iff (v : IR.Inherited.Validated n) (b : IR.Expr.Bounds n)
    (body : Body n) (out : EncodedBody n) (h : encodeBody v b body = .ok out)
    (i : Instance) (r : Realization v b body i) :
    out.formula.eval b.width i [] = some true ↔ SourceHolds body r.observation r.model := by
  obtain ⟨l, a, hl, _, he, rfl⟩ := encodeBody_output v b body out h
  have hle : l = r.layout := Except.ok.inj (hl.symm.trans r.bound)
  subst l
  obtain ⟨hctx, hbuilt, hext⟩ := bindSupport_output v body.support body.owner r.layout r.bound
  have howners : Unary r.atoms (atomSet r.observation.objects[body.support.context])
      ((Structural.head v.layout body.owner).eval i []) := by
    have hx := r.leaves.extents body.owner []
    rw [hext] at hx
    simpa [Vector.get, Vector.ofFn, hctx] using hx
  rw [attachment_iff a r.valid r.bounded r.leaves hbuilt r.model r.fullExtension _ howners]
  unfold SourceHolds
  rw [← he]
  simp only [hctx]
  constructor
  · intro hh
    exact ⟨a.checked.typed, hh⟩
  · rintro ⟨ht, hh⟩
    exact hh

/-- The public generated list preserves every attachment and characterizes all
of their source meanings. Structural and numeric facts remain separate conjuncts. -/
theorem all_attachments_iff (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v bounds intervals bodies = .ok out) (i : Instance)
    (r : ∀ entry ∈ out.bodies, Realization v (sourceBounds v bounds intervals) entry.original i) :
    (do let values ← out.bodies.mapM (fun entry => entry.formula.eval bounds.bitwidth i [])
        pure (values.all id)) = some true ↔
      ∀ (entry) (he : entry ∈ out.bodies), SourceHolds entry.original (r entry he).observation (r entry he).model := by
  obtain ⟨base, _, he, _⟩ := compile_output v bounds intervals bodies out h
  have hall := pairs_forall (mapM_pairs _ _ he)
    (fun entry => encodeBody v (sourceBounds v bounds intervals) entry.original = .ok entry)
    (fun body entry hh => by rw [encodeBody_original v _ body entry hh]; exact hh)
  rw [mapM_all_true]
  constructor
  · intro ht entry he
    exact (encoded_body_iff v _ _ entry (hall entry he) i (r entry he)).mp (ht entry he)
  · intro ht entry he
    exact (encoded_body_iff v _ _ entry (hall entry he) i (r entry he)).mpr (ht entry he)

/-- Satisfying the generated module enforces every original attached constraint.
This derives constraint truth from emitted facts, rather than assuming it. -/
theorem satisfied_attachments (v : IR.Inherited.Validated n) (bounds : Structural.Bounds)
    (intervals : Vector Interval n) (bodies : List (Body n)) (out : Compiled n)
    (h : compile v bounds intervals bodies = .ok out) (i : Instance)
    (r : ∀ entry ∈ out.bodies, Realization v (sourceBounds v bounds intervals) entry.original i)
    (hs : Satisfies out.module.raw i) :
    ∀ (entry) (he : entry ∈ out.bodies), SourceHolds entry.original (r entry he).observation (r entry he).model := by
  apply (all_attachments_iff v bounds intervals bodies out h i r).mp
  rw [mapM_all_true]
  intro entry he
  obtain ⟨base, hb, _, _, hfacts, hcommand⟩ := compile_output v bounds intervals bodies out h
  obtain ⟨scopes, _, hbase, _, _⟩ := Correctness.Inherited.compile_output v bounds base hb
  have hwidth : out.module.raw.command.bitwidth = bounds.bitwidth := by rw [hcommand, hbase]; rfl
  rw [← hwidth]
  apply Module.fact_true out.module.raw i hs.2.2.2.2.2
  rw [hfacts]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨entry, he, rfl⟩)

end ClaferCompiler.Correctness.ExpressionMeaning
