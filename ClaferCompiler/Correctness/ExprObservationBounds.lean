module

public import ClaferCompiler.SemanticsBridge.ExprFinite
public import ClaferCompiler.Correctness.StructuralRelations

@[expose] public section
namespace ClaferCompiler.Correctness.Expressions
open IR.Expr SemanticsBridge.Expr
open Clafer.Constraints (ambientRelation relationalImage relationalJoin)

/-! Finite observation obligations derived from the executable candidate check.
No expression value, definedness or truth is assumed.
[proof->req~compiler-arithmetic~1] -/

variable {s : Support n m} {o : Observation n m} {b : Bounds n}

theorem withinBounds_objects (h : o.withinBounds s b = true) (x : Fin n) :
    ((List.finRange n).all (fun y => s.classes[x] != s.classes[y] ||
      (o.objects[x].all (o.objects[y].contains) && o.objects[y].all (o.objects[x].contains)))) = true ∧
    o.objects[x].eraseDups.length ≤ b.extents[x] ∧
    ∀ a ∈ o.objects[x], match a with
      | .object _ => s.integer[x] = false
      | .integer i => s.integer[x] = true ∧ b.integers[x].fits b.width = true ∧
          b.integers[x].Contains i := by
  simp only [Observation.withinBounds, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  have hx := h.1.2 x (List.mem_finRange x)
  refine ⟨?_, hx.1.2, ?_⟩
  · simpa only [List.all_eq_true] using hx.1.1
  · intro a ha
    have hh := hx.2 a ha
    cases a <;> simpa [Bool.and_eq_true, Interval.Contains, and_assoc] using hh

theorem withinBounds_links (h : o.withinBounds s b = true) (e : Fin m)
    (l : Link) (hl : l ∈ o.links[e]) :
    l.source ∈ atomSet o.objects[s.maps[e].source] ∧
      l.target ∈ atomSet o.objects[s.maps[e].target] := by
  simp only [Observation.withinBounds, Bool.and_eq_true, List.all_eq_true] at h
  simpa [atomSet] using h.2 e (List.mem_finRange e) l hl

theorem atomSet_finite (xs : List Atom) : (atomSet xs).Finite := List.finite_toSet xs

theorem atomSet_ncard (xs : List Atom) : (atomSet xs).ncard = xs.eraseDups.length := by
  classical
  have he : atomSet xs = (xs.eraseDups.toFinset : Set Atom) := by ext a; simp [atomSet]
  rw [he, Set.ncard_coe_finset]
  exact List.toFinset_card_of_nodup (Structural.eraseDups_nodup xs)

theorem withinBounds_card (h : o.withinBounds s b = true) (x : Fin n) :
    (atomSet o.objects[x]).ncard ≤ b.extents[x] := by
  rw [atomSet_ncard]
  exact (withinBounds_objects h x).2.1

theorem withinBounds_same (h : o.withinBounds s b = true) {x y : Fin n}
    (he : s.classes[x] = s.classes[y]) : atomSet o.objects[x] = atomSet o.objects[y] := by
  have hh := List.all_eq_true.mp (withinBounds_objects h x).1 y (List.mem_finRange y)
  simp only [he, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at hh
  exact Set.Subset.antisymm (fun _ ha => hh.1 _ ha) (fun _ ha => hh.2 _ ha)

theorem recorded_full (h : o.withinBounds s b = true) {x : Fin n} {a : Atom}
    (ha : a ∈ atomSet o.objects[x]) : a ∈ fullExtent s o x := by
  have hh := (withinBounds_objects h x).2.2 a ha
  cases a with
  | object id => simp [fullExtent, hh, atomSet] at ha ⊢; exact ha
  | integer i =>
    simp [fullExtent, hh.1, integers, FormalCD.IntegerRealization.domain]
    exact ⟨i, rfl⟩

theorem widen_recorded (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    {x y : Fin n} (p : Path n m) (hp : p.Valid s x y) :
    atomSet o.objects[x] ⊆ atomSet o.objects[y] := by
  induction p generalizing x y with
  | same => rw [withinBounds_same hb hp]
  | inclusion e =>
    obtain ⟨hk, rfl, rfl⟩ := hp
    intro a ha
    obtain ⟨l, hl, _⟩ := hv.inclusion_one e hk a (recorded_full hb ha)
    have ht := (withinBounds_links hb e l hl.1).2
    simpa [hv.inclusion_same e hk l hl.1, hl.2] using ht
  | trans z p q ihp ihq => exact (ihp hp.1).trans (ihq hp.2)

/-- Every externally bound object is recorded; binders extend this condition
using the actual domain result, including primitive observations. -/
def RecordedEnvironment (o : Observation n m) {Γ : List (Clafer.Constraints.Local (support s))}
    (ρ : Clafer.Constraints.Environment (support s) Atom Γ) : Prop :=
  ρ.this ∈ atomSet o.objects[s.context] ∧
  ∀ x (v : Clafer.Constraints.Var Γ x), ρ.lookup v ∈ atomSet o.objects[x]

theorem recorded_push {Γ : List (Local n)} {ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s))}
    (h : RecordedEnvironment o ρ) (v : Local n) {a : Atom}
    (ha : a ∈ atomSet o.objects[v.element]) :
    RecordedEnvironment o (ρ.push (binder s v) a) := by
  refine ⟨h.1, ?_⟩
  intro x vlocal
  cases vlocal with
  | here => exact ha
  | there vlocal => exact h.2 _ vlocal

theorem environment_recorded (Γ : List (Local n)) (ρ : Environment)
    (h : ρ.bounded s b o Γ = true) : RecordedEnvironment o (environment s Γ ρ) := by
  simp only [Environment.bounded, Bool.and_eq_true] at h
  refine ⟨by simpa [atomSet, environment] using h.1.2, ?_⟩
  have hl := h.2
  clear h
  intro x v
  induction Γ generalizing ρ x with
  | nil => exact (Clafer.Constraints.Var.closed.false v).elim
  | cons c Γ ih =>
    cases hs : ρ.locals with
    | nil => simp [localsRecorded, hs] at hl
    | cons a xs =>
      have hc : a ∈ o.objects[c.element] ∧ localsRecorded o Γ xs = true := by
        simpa [localsRecorded, hs, Bool.and_eq_true, and_assoc, and_left_comm] using hl
      cases v with
      | here => simpa [environment, hs, Clafer.Constraints.Var.index, atomSet, binder] using hc.1
      | there v =>
        simpa [environment, hs, Clafer.Constraints.Var.index, binder] using
          ih { this := ρ.this, locals := xs } hc.2 x v

def RecordedCollection (o : Observation n m) : (k : Clafer.Constraints.Collection (support s)) →
    Set (k.Carrier Atom) → Prop
  | .objects x, S => S ⊆ atomSet o.objects[x]
  | .relation x y, S => S ⊆ (atomSet o.objects[x]) ×ˢ (atomSet o.objects[y])

theorem recorded_finite {k : Clafer.Constraints.Collection (support s)} {S : Set (k.Carrier Atom)}
    (h : RecordedCollection o k S) : S.Finite := by
  cases k with
  | objects x => exact (atomSet_finite _).subset h
  | relation x y => exact ((atomSet_finite _).prod (atomSet_finite _)).subset h

theorem widen_observation (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    {x y} (p : Clafer.Constraints.Widen (support s) x y) :
    atomSet o.objects[x] ⊆ atomSet o.objects[y] := by
  induction p with
  | same he => rw [withinBounds_same hb (congrArg Clafer.DeclId.value he)]
  | inclusion e hk =>
    apply widen_recorded hv hb (.inclusion e)
    refine ⟨?_, rfl, rfl⟩
    change mapKind s.maps[e].kind = .inclusion at hk
    cases he : s.maps[e].kind <;> simp_all [mapKind]
  | trans p q ihp ihq => exact ihp.trans ihq

def RecordedResult (o : Observation n m) : (t : Clafer.Constraints.Ty (support s)) →
    Option (Clafer.Constraints.Value Atom t) → Prop
  | .collection k, r => ∃ S, r = some S ∧ RecordedCollection o k S
  | _, _ => True

/-- Stronger than membership in the full primitive class: collection results
stay inside the finite observations throughout widening and navigation. -/
theorem recorded_result (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    {Γ t} (e : Clafer.Constraints.Expr (support s) Γ t)
    (hx : ∀ x ∈ e.extents, s.integer[x] = false)
    (ρ : Clafer.Constraints.Environment (support s) Atom Γ)
    (hρ : RecordedEnvironment o ρ) : RecordedResult o t (e.denote (extend s o hv) ρ) := by
  induction e with
  | this => exact ⟨_, rfl, by simpa [RecordedCollection] using hρ.1⟩
  | var v => exact ⟨_, rfl, by simpa [RecordedCollection] using hρ.2 _ v⟩
  | extent x =>
    refine ⟨_, rfl, ?_⟩
    have hn := hx x (Set.mem_singleton x)
    simp [RecordedCollection, fullExtent, hn]
  | map e =>
    refine ⟨_, rfl, ?_⟩
    rw [extend_map]
    rintro p ⟨l, hl, hs, ht⟩
    have hh := withinBounds_links hb e l hl
    exact ⟨hs ▸ hh.1, ht ▸ hh.2⟩
  | @setOp Γ k op a c iha ihc =>
    simp only [Clafer.Constraints.Expr.extents, Set.forall_mem_union] at hx
    obtain ⟨A, ha, hA⟩ := iha hx.1 ρ hρ
    obtain ⟨C, hc, hC⟩ := ihc hx.2 ρ hρ
    refine ⟨Clafer.Constraints.collectionOp op A C,
      by simp [Clafer.Constraints.Expr.denote, Clafer.Constraints.lift₂, ha, hc], ?_⟩
    cases k <;> cases op
    all_goals simp only [RecordedCollection, Clafer.Constraints.collectionOp] at *
    all_goals first | exact Set.union_subset hA hC
                    | exact Set.Subset.trans Set.sdiff_subset hA
                    | exact Set.Subset.trans Set.inter_subset_left hA
  | image a c iha ihc =>
    simp only [Clafer.Constraints.Expr.extents, Set.forall_mem_union] at hx
    obtain ⟨A, ha, _⟩ := iha hx.1 ρ hρ
    obtain ⟨C, hc, hC⟩ := ihc hx.2 ρ hρ
    refine ⟨relationalImage A C,
      by simp [Clafer.Constraints.Expr.denote, Clafer.Constraints.lift₂, ha, hc], ?_⟩
    rintro y ⟨x, _, hxy⟩
    exact (hC hxy).2
  | join a c iha ihc =>
    simp only [Clafer.Constraints.Expr.extents, Set.forall_mem_union] at hx
    obtain ⟨A, ha, hA⟩ := iha hx.1 ρ hρ
    obtain ⟨C, hc, hC⟩ := ihc hx.2 ρ hρ
    refine ⟨relationalJoin A C,
      by simp [Clafer.Constraints.Expr.denote, Clafer.Constraints.lift₂, ha, hc], ?_⟩
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact ⟨(hA hxy).1, (hC hyz).2⟩
  | widenObjects p a ih =>
    obtain ⟨A, ha, hA⟩ := ih hx ρ hρ
    exact ⟨A, ha, hA.trans (widen_observation hv hb p)⟩
  | widenRelation p q a ih =>
    obtain ⟨A, ha, hA⟩ := ih hx ρ hρ
    refine ⟨A, ha, ?_⟩
    intro z hz
    exact ⟨widen_observation hv hb p (hA hz).1, widen_observation hv hb q (hA hz).2⟩
  | _ => trivial

theorem checked_recorded (c : Checked s Γ (.collection k))
    (hv : ObservationValid s o) (hb : o.withinBounds s b = true)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (hρ : RecordedEnvironment o ρ) :
    ∃ S, denote c (extend s o hv) ρ = some S ∧ RecordedCollection o (collection s k) S :=
  recorded_result hv hb (interpret s c.term.raw c.typed) (checked_nonprimitive c) ρ hρ

theorem image_card {A : Set Atom} {R : Set (Atom × Atom)} (hR : R.Finite) :
    (relationalImage A R).ncard ≤ R.ncard := by
  have hsub : relationalImage A R ⊆ Prod.snd '' R := by
    rintro y ⟨x, _, hxy⟩; exact ⟨(x, y), hxy, rfl⟩
  exact (Set.ncard_le_ncard hsub (hR.image _)).trans (Set.ncard_image_le hR)

theorem join_card {A B : Set (Atom × Atom)} (hA : A.Finite) (hB : B.Finite) :
    (relationalJoin A B).ncard ≤ A.ncard * B.ncard := by
  have hsub : relationalJoin A B ⊆ (fun p : (Atom × Atom) × (Atom × Atom) =>
      (p.1.1, p.2.2)) '' (A ×ˢ B) := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact ⟨((x, y), (y, z)), ⟨hxy, hyz⟩, rfl⟩
  exact (Set.ncard_le_ncard hsub ((hA.prod hB).image _)).trans
    (by simpa only [Set.ncard_prod] using Set.ncard_image_le (hA.prod hB))

end ClaferCompiler.Correctness.Expressions
