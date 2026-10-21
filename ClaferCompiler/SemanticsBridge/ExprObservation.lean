module

public import ClaferCompiler.IR.ExprObservation
public import ClaferCompiler.SemanticsBridge.Expr
public import Clafer.Constraints.CollectionMeaning

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Expr
open IR.Expr
open CategoryTheory DPGraph.Predicates

/-- The ambient universe retains every mathematical integer; the decoder's
nonprimitive value is irrelevant because extraction checks domain membership. -/
def integers : FormalCD.IntegerRealization Atom where
  encode := ⟨Atom.integer, fun _ _ h => Atom.integer.inj h⟩
  decode | .object _ => 0 | .integer i => i
  decode_encode _ := rfl

def atomSet (xs : List Atom) : Set Atom := {x | x ∈ xs}

def observedRelation (xs : List Link) : Set (Atom × Atom) :=
  {p | ∃ l ∈ xs, l.source = p.1 ∧ l.target = p.2}

/-- Full primitive extents coexist with finite nonprimitive object extents. -/
def fullExtent (s : Support n m) (o : Observation n m) (x : Fin n) : Set Atom :=
  if s.integer[x] then integers.domain else atomSet o.objects[x]

/-- Independent model obligations, with no constraint truth assumption. The
finite observation is not required to realize the whole primitive domain. -/
structure ObservationValid (s : Support n m) (o : Observation n m) : Prop where
  same_id : ∀ x y : Fin n, s.classes[x] = s.classes[y] → fullExtent s o x = fullExtent s o y
  endpoints : ∀ (e : Fin m) (l : Link), l ∈ o.links[e] →
    l.source ∈ fullExtent s o s.maps[e].source ∧ l.target ∈ fullExtent s o s.maps[e].target
  link_ids : ∀ e : Fin m, (o.links[e].map Link.id).Nodup
  repeated : ∀ e f : Fin m, s.maps[e].owner = s.maps[f].owner → s.maps[e].kind = s.maps[f].kind →
    ∀ l, l ∈ o.links[e] ↔ l ∈ o.links[f]
  inclusion_one : ∀ e : Fin m, s.maps[e].kind = .inclusion →
    ∀ a ∈ fullExtent s o s.maps[e].source, ∃! l, l ∈ o.links[e] ∧ l.source = a
  inclusion_same : ∀ e : Fin m, s.maps[e].kind = .inclusion →
    ∀ l ∈ o.links[e], l.target = l.source

variable {s : Support n m} {o : Observation n m}

/-- Each original link, including its ID, remains a distinct span element. -/
def observedSpan (s : Support n m) (o : Observation n m) (h : ObservationValid s o) (e : Fin m) :
    DPGraph.Span (fullExtent s o s.maps[e].source) (fullExtent s o s.maps[e].target) where
  Link := {l : Link // l ∈ o.links[e]}
  source l := ⟨l.val.source, (h.endpoints e l.val l.property).1⟩
  target l := ⟨l.val.target, (h.endpoints e l.val l.property).2⟩

def observedModel (s : Support n m) (o : Observation n m) (h : ObservationValid s o) :
    (support s).graph ⥤q semanticGraph.{0,0} Atom where
  obj := fullExtent s o
  map {x y} a := by
    obtain ⟨e, hs, ht⟩ := a
    subst x; subst y
    exact observedSpan s o h e

/-!
[proof->req~compiler-expressions~1]
[proof->req~compiler-arithmetic~1]
-/
def extend (s : Support n m) (o : Observation n m) (h : ObservationValid s o) :
    Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom where
  realization := integers
  model := observedModel s o h
  same_id := fun x y he => h.same_id x y (congrArg Clafer.DeclId.value he)
  inclusion := by
    intro e he
    have hk : s.maps[e].kind = .inclusion := by
      change mapKind s.maps[e].kind = .inclusion at he
      cases hkind : s.maps[e].kind <;> simp_all [mapKind]
    constructor
    · constructor
      · intro a b hab
        apply Subtype.ext
        have heq : a.val.source = b.val.source := congrArg Subtype.val hab
        obtain ⟨l, _, unique⟩ := h.inclusion_one e hk a.val.source (h.endpoints e _ a.property).1
        exact (unique a.val ⟨a.property, rfl⟩).trans (unique b.val ⟨b.property, heq.symm⟩).symm
      · intro a
        obtain ⟨l, hl, _⟩ := h.inclusion_one e hk a.val a.property
        exact ⟨⟨l, hl.1⟩, Subtype.ext hl.2⟩
    · intro l
      exact h.inclusion_same e hk l.val l.property
  integer_domain := by
    intro x hx
    simp [observedModel, fullExtent, support] at hx ⊢
    simp [hx]

@[simp] theorem extend_extent (h : ObservationValid s o) (x) :
    ((extend s o h).model.obj x : Set Atom) = fullExtent s o x := rfl

@[simp] theorem extend_map (h : ObservationValid s o) (e) :
    ambientRelation ((extend s o h).model.map ((support s).arrow e)) =
      observedRelation o.links[e] := by
  ext p
  constructor
  · rintro ⟨l, hs, ht⟩
    exact ⟨l.val, l.property, hs, ht⟩
  · rintro ⟨l, hl, hs, ht⟩
    exact ⟨⟨l, hl⟩, hs, ht⟩

theorem extend_coherent (h : ObservationValid s o) : (extend s o h).Coherent := by
  intro e f ho hk
  have howner : s.maps[e].owner = s.maps[f].owner := congrArg Clafer.DeclId.value ho
  have hkind : s.maps[e].kind = s.maps[f].kind := by
    change mapKind s.maps[e].kind = mapKind s.maps[f].kind at hk
    cases he : s.maps[e].kind <;> cases hf : s.maps[f].kind <;> simp_all [mapKind]
  refine ⟨{
    equiv := {
      toFun := fun l => ⟨l.val, (h.repeated e f howner hkind l.val).mp l.property⟩
      invFun := fun l => ⟨l.val, (h.repeated e f howner hkind l.val).mpr l.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    source := fun _ => rfl
    target := fun _ => rfl }⟩

/-- A full independent binding agrees with the observed nonprimitive extents and
all original links through bijections. Its primitive extent remains complete. -/
structure ExtendsObservation (s : Support n m) (o : Observation n m)
    (h : ObservationValid s o) (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom) : Prop where
  realization : model.realization = integers
  objects : ∀ x : Fin n, s.integer[x] = false → (model.model.obj x : Set Atom) = atomSet o.objects[x]
  links : ∀ e : Fin m, Nonempty (Clafer.Constraints.LinkEquivalence
    (model.model.map ((support s).arrow e)) (observedSpan s o h e))

/-- Constructive existence: every observation satisfying the stated structural
binding obligations has a full-Int extension with the same original links. -/
theorem extend_realizes (h : ObservationValid s o) : ExtendsObservation s o h (extend s o h) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx; simp [fullExtent, hx]
  · intro e
    exact ⟨⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

/-- Denotation is unchanged in every full integer extension of the finite
observation. Primitive/root structural satisfaction is not assumed or concluded:
the support context and its admissibility must be supplied separately. -/
theorem finite_observation_agreement (c : Checked s Γ t) (h : ObservationValid s o)
    (model : Clafer.Constraints.IntegerBinding.{0,0} (support s) Atom)
    (hm : ExtendsObservation s o h model)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s))) :
    denote c model ρ = denote c (extend s o h) ρ := by
  apply Clafer.Constraints.Expr.denote_support_congr
  · exact hm.realization
  · intro x hx
    have hn := checked_nonprimitive c x hx
    simpa [fullExtent, hn] using hm.objects x hn
  · intro e _
    obtain ⟨he⟩ := hm.links e
    exact he.reduction

/-- Interval arithmetic is mathematical; representability never wraps a value. -/
theorem add_contains {a b : Interval} {x y : Int} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  dsimp [Interval.Contains, Interval.add] at *; omega

theorem subtract_contains {a b : Interval} {x y : Int} (hx : a.Contains x) (hy : b.Contains y) :
    (a.subtract b).Contains (x - y) := by
  dsimp [Interval.Contains, Interval.subtract] at *; omega

theorem fits_representable {r : Interval} {width : Nat} {x : Int}
    (h : r.fits width = true) (hx : r.Contains x) : (signedRange width).Contains x := by
  simp only [Interval.fits, decide_eq_true_eq] at h
  dsimp [Interval.Contains] at *
  exact ⟨h.2.2.2.1.trans hx.1, hx.2.trans h.2.2.2.2⟩

/-- Exact singleton membership is the executable extraction contract. -/
theorem extract_iff (xs : List Atom) (i : Int) :
    extract xs = some i ↔ atomSet xs = {Atom.integer i} := by
  cases xs with
  | nil => simp [extract, atomSet, Set.ext_iff]
  | cons a xs =>
    cases a with
    | object id =>
      simp only [extract, reduceCtorEq, false_iff]
      intro he
      have hm : Atom.object id ∈ atomSet (Atom.object id :: xs) := by simp [atomSet]
      rw [he] at hm
      cases hm
    | integer j =>
      simp only [extract]
      constructor
      · split
        · intro he
          cases Option.some.inj he
          rename_i hall
          ext a
          simp only [atomSet, Set.mem_ofPred_eq, List.mem_cons, Set.mem_singleton_iff]
          constructor
          · rintro (rfl | ha)
            · rfl
            · exact beq_iff_eq.mp (List.all_eq_true.mp hall a ha)
          · exact Or.inl
        · intro he; cases he
      · intro he
        have hj : Atom.integer j ∈ atomSet (Atom.integer j :: xs) := by simp [atomSet]
        rw [he] at hj
        have hji : j = i := Atom.integer.inj hj
        subst j
        have hall : xs.all (· == Atom.integer i) = true := by
          apply List.all_eq_true.mpr
          intro a ha
          have hm : a ∈ atomSet (Atom.integer i :: xs) := by simp [atomSet, ha]
          rw [he] at hm
          exact beq_iff_eq.mpr hm
        simp [hall]

/-- Agreement on every finite collection, including undefined cases. -/
theorem extract_agreement (xs : List Atom) : extract xs = integers.extract (atomSet xs) := by
  cases hx : extract xs with
  | some i =>
    symm
    apply (integers.extract_eq_some_iff _ _).mpr
    exact (extract_iff xs i).mp hx
  | none =>
    symm
    cases hi : integers.extract (atomSet xs) with
    | none => rfl
    | some i =>
      have he := (integers.extract_eq_some_iff _ _).mp hi
      have hc := (extract_iff xs i).mpr he
      rw [hx] at hc
      cases hc

@[simp] theorem member_iff (s : Support n m) (o : Observation n m) (x : Fin n) (a : Atom) :
    member s o x a = true ↔ a ∈ fullExtent s o x := by
  cases hi : s.integer[x] <;> cases a <;>
    simp [member, fullExtent, hi, atomSet, FormalCD.IntegerRealization.domain, integers]
  exact ⟨_, rfl⟩

noncomputable def environment (s : Support n m) (Γ : List (Local n)) (ρ : Environment) :
    Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)) where
  this := ρ.this
  lookup v := ρ.locals[v.index]?.getD (.object 0)

/-- Finite lexical membership checks imply upstream environment admissibility.
The fallback in the raw lookup is unreachable for a validated environment. -/
theorem environment_admissible (s : Support n m) (o : Observation n m)
    (h : ObservationValid s o) (Γ : List (Local n)) (ρ : Environment)
    (hv : ρ.valid s o Γ = true) : (environment s Γ ρ).Admissible (extend s o h) := by
  simp only [Environment.valid, Bool.and_eq_true] at hv
  refine ⟨(member_iff s o _ _).mp hv.1, ?_⟩
  have hl := hv.2
  clear hv
  intro x v
  induction Γ generalizing ρ x with
  | nil => exact (Clafer.Constraints.Var.closed.false v).elim
  | cons b Γ ih =>
    cases hs : ρ.locals with
    | nil => simp [localsValid, hs] at hl
    | cons a xs =>
      simp only [hs, localsValid_cons, Bool.and_eq_true] at hl
      cases v with
      | here =>
        change (ρ.locals[0]?.getD (.object 0)) ∈ fullExtent s o b.element
        simpa only [hs, List.getElem?_cons_zero, Option.getD_some] using (member_iff s o _ _).mp hl.1
      | there v =>
        have hh := ih { this := ρ.this, locals := xs } hl.2 x v
        simpa [environment, Clafer.Constraints.Var.index, hs, binder] using hh

end ClaferCompiler.SemanticsBridge.Expr
