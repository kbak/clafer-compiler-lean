module

public import ClaferCompiler.Correctness.ExpressionConstruction
public import ClaferCompiler.Correctness.ExpressionRelations
public import ClaferCompiler.Correctness.ExprIntermediateRanges

/-! [proof->req~compiler-expression-encoding~1] -/

@[expose] public section
namespace ClaferCompiler.Correctness.ExpressionMeaning
open Backend.Alloy Backend.Alloy.Expressions IR.Expr SemanticsBridge.Expr
open ExpressionRelations ExpressionConstruction
open Clafer.Constraints (Value IntegerBinding relationalImage relationalJoin)

/-- Concrete leaf tables. Primitive observations remain finite; the source
binding still contains every mathematical integer. These equations mention no
expression denotation, definedness, constraint truth, or compilation result. -/
structure LayoutRep (s : Support n m) (l : Layout n m) (o : Observation n m)
    (i : Instance) (f : Atom → Nat) : Prop where
  injective : Function.Injective f
  extents : ∀ (x : Fin n) env, Unary f (atomSet o.objects[x]) (l.extents[x].eval i env)
  maps : ∀ (e : Fin m) env, Binary f (observedRelation o.links[e]) (l.maps[e].eval i env)
  scalarOwners : ∀ (x : Fin n), s.integer[x] = true → ∀ env,
    Unary f (atomSet o.objects[x]) ((Rel.sig l.scalarOwners[x]).eval i env)
  scalarRows : ∀ (x : Fin n), s.integer[x] = true → ∀ row,
    row ∈ i.values[l.scalarOwners[x]]?.getD [] ↔
      ∃ z, Atom.integer z ∈ o.objects[x] ∧ row = (f (.integer z), z)

/-- Target binders prepend locals; the enclosing owner remains after all locals. -/
def EnvironmentRep (s : Support n m) {Γ : List (Local n)} (f : Atom → Nat)
    (ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s)))
    (env : List Nat) : Prop :=
  env[Γ.length]? = some (f ρ.this) ∧
  ∀ x (v : Clafer.Constraints.Var (Γ.map (binder s)) x), env[v.index]? = some (f (ρ.lookup v))

theorem environment_push {s : Support n m} {Γ : List (Local n)} {f : Atom → Nat}
    {ρ : Clafer.Constraints.Environment (support s) Atom (Γ.map (binder s))} {env}
    (h : EnvironmentRep s f ρ env) (v : Local n) (a : Atom) :
    EnvironmentRep s (Γ := v :: Γ) f (ρ.push (binder s v) a) (f a :: env) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro x w
  cases w with
  | here => rfl
  | there w => exact h.2 x w

theorem lexical_index (s : Support n m) (Γ : List (Local n)) (pos : Nat)
    (v : Local n) (hp : Γ[pos]? = some v) : (lexical s Γ pos v hp).index = pos := by
  induction Γ generalizing pos with
  | nil => simp at hp
  | cons c Γ ih =>
    cases pos with
    | zero => have := Option.some.inj hp; subst v; rfl
    | succ pos => exact congrArg Nat.succ (ih pos hp)

def tupleOf (f : Atom → Nat) (s : Support n m) : (k : Collection n) →
    (collection s k).Carrier Atom → Tuple
  | .objects _, a => [f a]
  | .relation _ _, p => [f p.1, f p.2]

theorem tuple_injective (s : Support n m) (k : Collection n) {f : Atom → Nat}
    (hf : Function.Injective f) : Function.Injective (tupleOf f s k) := by
  cases k
  · exact unary_injective hf
  · exact binary_injective hf

noncomputable def propBool (P : Prop) : Bool := @decide P (Classical.propDecidable _)

@[simp] theorem propBool_true (P : Prop) : propBool P = true ↔ P := by
  simp [propBool]

@[simp] theorem propBool_and (P Q : Prop) : propBool (P ∧ Q) = (propBool P && propBool Q) := by
  classical
  simp [propBool]

@[simp] theorem propBool_not (P : Prop) : propBool (¬ P) = !propBool P := by
  classical
  simp [propBool, decide_not]

def ValueAgrees (s : Support n m) (f : Atom → Nat) (w : Nat) (i : Instance) (env : List Nat) :
    (t : Ty n) → Value Atom (type s t) → ValueCode t → Prop
  | .boolean, p, q => q.eval w i env = some (propBool p.down)
  | .integer, z, q => q.eval w i env = some z.down
  | .collection k, S, r => Represents (tupleOf f s k) S (r.eval i env)

/-- Definedness is exact, including false and undefined results. Value agreement
is required whenever the independent upstream denotation has a value. -/
def Agrees (s : Support n m) (f : Atom → Nat) (w : Nat) (i : Instance) (env : List Nat)
    {t : Ty n} (v : Option (Value Atom (type s t))) (c : Code t) : Prop :=
  c.defined.eval w i env = some v.isSome ∧ ∀ a, v = some a → ValueAgrees s f w i env t a c.value

theorem agrees_binary {s : Support n m} {f w i env} {ta tb tc : Ty n}
    {a : Option (Value Atom (type s ta))} {b : Option (Value Atom (type s tb))}
    {ca : Code ta} {cb : Code tb} (ha : Agrees s f w i env a ca) (hb : Agrees s f w i env b cb)
    (hda : ca.defined.Term) (hdb : cb.defined.Term)
    (op : Value Atom (type s ta) → Value Atom (type s tb) → Value Atom (type s tc))
    (out : ValueCode tc)
    (hop : ∀ x y, a = some x → b = some y →
      ValueAgrees s f w i env ta x ca.value → ValueAgrees s f w i env tb y cb.value →
        ValueAgrees s f w i env tc (op x y) out) :
    Agrees s f w i env (Clafer.Constraints.lift₂ op a b)
      ⟨.conj ca.defined cb.defined, out⟩ := by
  constructor
  · rw [Formula.eval_conj hda hdb, ha.1, hb.1]
    cases a <;> cases b <;> rfl
  · intro z hz
    cases a with
    | none => simp [Clafer.Constraints.lift₂] at hz
    | some x =>
      cases b with
      | none => simp [Clafer.Constraints.lift₂] at hz
      | some y =>
        have he : op x y = z := Option.some.inj hz
        subst z
        exact hop x y rfl rfl (ha.2 _ rfl) (hb.2 _ rfl)

theorem agrees_holds {s : Support n m} {f w i env} {a : Option (ULift Prop)}
    {c : Code (.boolean : Ty n)} (h : Agrees s f w i env a c) (hc : Built c) :
    c.holds.eval w i env = some true ↔ a = some ⟨True⟩ := by
  rw [Code.holds, Formula.eval_conj_true hc.1 hc.2, h.1]
  cases a with
  | none => simp
  | some p =>
    have hp := h.2 p rfl
    change c.value.eval w i env = some (propBool p.down) at hp
    rw [hp]
    simp only [Option.isSome_some, Option.some.injEq, true_and, propBool_true]
    constructor
    · intro ht; exact ULift.ext (propext (iff_true_intro ht))
    · intro ht; cases ht; trivial

theorem eval_all_total (p : Formula) (hp : p.Term) (r : Rel) (w : Nat)
    (i : Instance) (env : List Nat)
    (h : ∀ t ∈ r.eval i env, ∃ b, p.eval w i (t.headD 0 :: env) = some b) :
    ∃ b, (Formula.all r p).eval w i env = some b := by
  rw [Formula.eval_all hp]
  have hm : ∃ bs, (r.eval i env).mapM (fun t => p.eval w i (t.headD 0 :: env)) = some bs := by
    generalize r.eval i env = ts at h ⊢
    induction ts with
    | nil => exact ⟨[], rfl⟩
    | cons t ts ih =>
      obtain ⟨b, hb⟩ := h t (by simp)
      obtain ⟨bs, hbs⟩ := ih (fun t ht => h t (by simp [ht]))
      exact ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl⟩
  obtain ⟨bs, hbs⟩ := hm
  exact ⟨bs.all id, by rw [hbs]; rfl⟩

theorem eval_all_prop {f : Atom → Nat} {S : Set Atom} {r : Rel} {p : Formula}
    {w : Nat} {i : Instance} {env : List Nat} (hp : p.Term)
    (hr : Unary f S (r.eval i env)) (P : Atom → Prop)
    (h : ∀ a ∈ S, p.eval w i (f a :: env) = some (propBool (P a))) :
    (Formula.all r p).eval w i env = some (propBool (∀ a ∈ S, P a)) := by
  obtain ⟨v, hv⟩ := eval_all_total p hp r w i env (by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := (hr t).mp ht
    exact ⟨_, h a ha⟩)
  rw [hv]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [propBool_true, ← Option.some.injEq, ← hv, Formula.eval_all_true hp]
  constructor
  · intro ht a ha
    have he := ht [f a] ((hr _).mpr ⟨a, ha, rfl⟩)
    simpa only [List.headD_cons, h a ha, Option.some.injEq, propBool_true] using he
  · intro hall t ht
    obtain ⟨a, ha, rfl⟩ := (hr t).mp ht
    simpa only [List.headD_cons, h a ha, Option.some.injEq, propBool_true] using hall a ha

end ClaferCompiler.Correctness.ExpressionMeaning
