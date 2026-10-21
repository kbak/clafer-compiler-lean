module

public import ClaferCompiler.IR.Expr
public import Clafer.Constraints.DenotationSupport

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Expr
open IR.Expr

def mapKind : MapKind → Clafer.Constraints.MapKind
  | .head => .head | .parent => .parent | .dereference => .dereference
  | .target => .target | .inclusion => .inclusion

abbrev support (s : Support n m) : Clafer.Constraints.Support where
  classCount := n
  mapCount := m
  classId := fun x => ⟨s.classes[x]⟩
  mapRef := fun e => ⟨⟨s.maps[e].owner⟩, mapKind s.maps[e].kind,
    s.maps[e].source, s.maps[e].target, s.maps[e].name⟩
  context := s.context
  integer := fun x => s.integer[x]

abbrev collection (s : Support n m) : Collection n → Clafer.Constraints.Collection (support s)
  | .objects x => .objects x | .relation x y => .relation x y

abbrev type (s : Support n m) : Ty n → Clafer.Constraints.Ty (support s)
  | .boolean => .boolean | .integer => .integer | .collection k => .collection (collection s k)

def binder (s : Support n m) (b : Local n) : Clafer.Constraints.Local (support s) :=
  ⟨⟨b.id⟩, b.name, b.element⟩

def setOp : SetOp → Clafer.Constraints.SetOp
  | .union => .union | .difference => .difference | .intersection => .intersection

def arithmetic : Arithmetic → Clafer.Constraints.Arithmetic
  | .add => .add | .subtract => .subtract

noncomputable def widen (s : Support n m) {x y : Fin n} (p : Path n m)
    (h : p.Valid s x y) : Clafer.Constraints.Widen (support s) x y := by
  cases p with
  | same => exact .same (congrArg Clafer.DeclId.mk h)
  | inclusion e =>
    obtain ⟨hk, hx, hy⟩ := h
    subst x; subst y
    exact @Clafer.Constraints.Widen.inclusion (support s) e (by change mapKind s.maps[e].kind = _; rw [hk]; rfl)
  | trans z p q => exact .trans (widen s p h.1) (widen s q h.2)

/-- A checked position, not a name lookup. -/
noncomputable def lexical (s : Support n m) : (Γ : List (Local n)) → (i : Nat) →
    (b : Local n) → Γ[i]? = some b → Clafer.Constraints.Var (Γ.map (binder s)) b.element
  | [], _, _, h => by simp at h
  | a :: Γ, 0, b, h => by
      have he : a = b := Option.some.inj h
      subst b
      exact .here
  | _ :: Γ, i + 1, b, h => .there (lexical s Γ i b h)

/-!
[impl->req~compiler-expressions~1]
-/
/-- Total interpretation on checked syntax; the original upstream constructors
supply meaning. This definition is proof-only, never the native compiler runtime. -/
noncomputable def interpret (s : Support n m) : (e : Syntax n m) →
    {Γ : List (Local n)} → {t : Ty n} → e.Typed s Γ t →
    Clafer.Constraints.Expr (support s) (Γ.map (binder s)) (type s t)
  | .boolean b, Γ, t, h => by subst t; exact .boolean b
  | .integer i, Γ, t, h => by subst t; exact .integer i
  | .this, Γ, t, h => by subst t; exact .this
  | .extent x, Γ, t, h => by subst t; exact @Clafer.Constraints.Expr.extent (support s) _ x
  | .var i, Γ, t, h => match hi : Γ[i]? with
    | none => by simp [Syntax.Typed, hi] at h
    | some b => by
      simp only [Syntax.Typed, hi] at h
      subst t
      exact .var (lexical s Γ i b hi)
  | .map e, Γ, t, h => by subst t; exact @Clafer.Constraints.Expr.map (support s) _ e
  | .and a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .and (interpret s a ha) (interpret s b hb)
  | .not a, Γ, t, h => by obtain ⟨rfl, ha⟩ := h; exact .not (interpret s a ha)
  | .equal k a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .equal (interpret s a ha) (interpret s b hb)
  | .less a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .less (interpret s a ha) (interpret s b hb)
  | .arithmetic op a b, Γ, t, h => by
    obtain ⟨rfl, ha, hb⟩ := h
    exact .arithmetic (arithmetic op) (interpret s a ha) (interpret s b hb)
  | .integerOf x a, Γ, t, h => by
    obtain ⟨rfl, hp, ha⟩ := h
    exact .integerOf hp (interpret s a ha)
  | .cardinality k a, Γ, t, h => by obtain ⟨rfl, ha⟩ := h; exact .cardinality (interpret s a ha)
  | .setOp op k a b, Γ, t, h => by
    obtain ⟨rfl, ha, hb⟩ := h
    exact .setOp (setOp op) (interpret s a ha) (interpret s b hb)
  | .subset k a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .subset (interpret s a ha) (interpret s b hb)
  | .image x y a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .image (interpret s a ha) (interpret s b hb)
  | .join x y z a b, Γ, t, h => by obtain ⟨rfl, ha, hb⟩ := h; exact .join (interpret s a ha) (interpret s b hb)
  | .widenObjects x y p a, Γ, t, h => by
    obtain ⟨rfl, hp, ha⟩ := h
    exact .widenObjects (widen s p hp) (interpret s a ha)
  | .widenRelation x y x' y' p q a, Γ, t, h => by
    obtain ⟨rfl, hp, hq, ha⟩ := h
    exact .widenRelation (widen s p hp) (widen s q hq) (interpret s a ha)
  | .all b d a, Γ, t, h => by
    obtain ⟨rfl, hf, hd, ha⟩ := h
    refine .all (binder s b) ?_ (interpret s d hd) (interpret s a ha)
    intro old ho
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ho
    exact fun he => hf c hc (congrArg Clafer.BinderId.value he)
  | .located _ a, Γ, t, h => by exact interpret s a h.2

/-!
[proof->req~compiler-expressions~1]
-/
theorem check_iff (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Term n m) :
    (∃ c, check s Γ t e = .ok c) ↔ e.Typed s Γ t ∧ e.Observed s := by
  unfold check
  split <;> rename_i ht
  · split <;> simp_all
  · simp_all

theorem check_preserves (s : Support n m) (Γ : List (Local n)) (t : Ty n) (e : Term n m)
    (c : Checked s Γ t) (h : check s Γ t e = .ok c) : c.term = e := by
  unfold check at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- Public semantic API accepts zero maps. It does not invoke Compile.Input. -/
noncomputable def denote (c : Checked s Γ t) {U : Type}
    (model : Clafer.Constraints.IntegerBinding (support s) U)
    (ρ : Clafer.Constraints.Environment (support s) U (Γ.map (binder s))) : Option (Clafer.Constraints.Value U (type s t)) :=
  (interpret s c.term.raw c.typed).denote model ρ


/-- Interpretation preserves the complete ordered runtime inventories as semantic
observation sets. No map-support positivity assumption occurs. -/
theorem interpret_footprint (s : Support n m) (e : Syntax n m) {Γ t}
    (h : e.Typed s Γ t) :
    (∀ x, x ∈ (interpret s e h).extents ↔ x ∈ e.extents) ∧
    (∀ f, f ∈ (interpret s e h).maps ↔ f ∈ e.maps) := by
  induction e generalizing Γ t with
  | boolean b =>
    subst t
    simp_all [interpret, Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents,
      Clafer.Constraints.Expr.maps]
  | integer i =>
    subst t
    simp_all [interpret, Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents,
      Clafer.Constraints.Expr.maps]
  | this =>
    subst t
    simp_all [interpret, Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents,
      Clafer.Constraints.Expr.maps]
  | extent x =>
    subst t
    simp_all [interpret, Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents,
      Clafer.Constraints.Expr.maps]
  | map e =>
    subst t
    simp_all [interpret, Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents,
      Clafer.Constraints.Expr.maps]
  | and a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | not a ih =>
    obtain ⟨rfl, ha⟩ := h
    exact ih ha
  | equal k a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | less a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | arithmetic op a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | integerOf x a ih =>
    obtain ⟨rfl, hp, ha⟩ := h
    exact ih ha
  | cardinality k a ih =>
    obtain ⟨rfl, ha⟩ := h
    exact ih ha
  | setOp op k a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | subset k a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | image x y a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | join x y z a b iha ihb =>
    obtain ⟨rfl, ha, hb⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s a ha).extents ∨ v ∈ (interpret s b hb).extents) ↔
        v ∈ a.extents ++ b.extents
      rw [List.mem_append]
      exact or_congr ((iha ha).1 v) ((ihb hb).1 v)
    · intro v
      change (v ∈ (interpret s a ha).maps ∨ v ∈ (interpret s b hb).maps) ↔
        v ∈ a.maps ++ b.maps
      rw [List.mem_append]
      exact or_congr ((iha ha).2 v) ((ihb hb).2 v)
  | widenObjects x y p a ih =>
    obtain ⟨rfl, hp, ha⟩ := h
    exact ih ha
  | widenRelation x y x' y' p q a ih =>
    obtain ⟨rfl, hp, hq, ha⟩ := h
    exact ih ha
  | all b d a ihd iha =>
    obtain ⟨rfl, hf, hd, ha⟩ := h
    constructor
    · intro v
      change (v ∈ (interpret s d hd).extents ∨ v ∈ (interpret s a ha).extents) ↔
        v ∈ d.extents ++ a.extents
      rw [List.mem_append]
      exact or_congr ((ihd hd).1 v) ((iha ha).1 v)
    · intro v
      change (v ∈ (interpret s d hd).maps ∨ v ∈ (interpret s a ha).maps) ↔
        v ∈ d.maps ++ a.maps
      rw [List.mem_append]
      exact or_congr ((ihd hd).2 v) ((iha ha).2 v)
  | located p a ih =>
    exact ih h.2
  | var i =>
    simp only [interpret]
    split
    · rename_i he
      simp [Syntax.Typed, he] at h
    · rename_i b he
      simp only [Syntax.Typed, he] at h
      subst t
      simp [Syntax.extents, Syntax.maps, Clafer.Constraints.Expr.extents, Clafer.Constraints.Expr.maps]

/-- Every observable global extent is nonprimitive after admission. -/
theorem checked_nonprimitive {s : Support n m} (c : Checked s Γ t) (x : (support s).Vertex)
    (hx : x ∈ (interpret s c.term.raw c.typed).extents) : s.integer[x] = false :=
  c.observed x ((interpret_footprint s c.term.raw c.typed).1 x |>.mp hx)

end ClaferCompiler.SemanticsBridge.Expr
