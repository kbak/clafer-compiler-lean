module

public import ClaferCompiler.Frontend.ConstraintsSupport

@[expose] public section
namespace ClaferCompiler.Frontend.Constraints
open IR.Expr

/-- Declarative finite ancestry: the kth super/parent of an occurrence. -/
def ancestor (c : IR.Structural.Core n) (super : Bool) (x : Fin n) (k : Nat) : Option (Fin n) :=
  k.repeat (fun v => v.bind fun i => if super then (c.get i).super else (c.get i).parent) (some x)

def Field (c : IR.Structural.Core n) (x : Fin n) (name : String) (depth : Nat) (p y : Fin n) : Prop :=
  ancestor c true x depth = some p ∧ (c.get y).parent = some p ∧
  (c.get y).name = name ∧ (c.get y).origin = .user ∧
  (∀ k : Fin depth, match ancestor c true x k.val with
    | none => True
    | some q => ∀ j : Fin n, (c.get j).parent = some q → (c.get j).name ≠ name) ∧
  (∀ j : Fin n, (c.get j).parent = some p → (c.get j).name = name → j = y)

instance (c : IR.Structural.Core n) (x : Fin n) (name : String) (d : Nat) (p y : Fin n) :
    Decidable (Field c x name d p y) := by
  letI : DecidablePred (fun k : Fin d => match ancestor c true x k.val with
    | none => True
    | some q => ∀ j : Fin n, (c.get j).parent = some q → (c.get j).name ≠ name) :=
    fun _ => by dsimp only; split <;> infer_instance
  unfold Field
  infer_instance

def HasField (c : IR.Structural.Core n) (x : Fin n) (name : String) : Prop :=
  ∃ k : Fin (n + 1), match ancestor c true x k.val with
    | none => False
    | some p => ∃ y : Fin n, (c.get y).parent = some p ∧ (c.get y).name = name

instance (c : IR.Structural.Core n) (x : Fin n) (name : String) : Decidable (HasField c x name) := by
  letI : DecidablePred (fun k : Fin (n + 1) => match ancestor c true x k.val with
    | none => False
    | some p => ∃ y : Fin n, (c.get y).parent = some p ∧ (c.get y).name = name) :=
    fun _ => by dsimp only; split <;> infer_instance
  unfold HasField
  infer_instance

/-- Navigation preserves head identity. Dereference is explicit and cannot skip
a field on the head. Widening requires an actual checked inclusion path. -/
inductive Navigate (c : IR.Structural.Core n) (s : Support n m) :
    Fin n → Syntax n m → String → Fin n → Syntax n m → Prop where
  | field {x a name depth p y path e} : Field c x name depth p y →
      path.Valid s x p → s.maps[e].kind = .head → s.maps[e].source = p → s.maps[e].target = y →
      Navigate c s x a name y (.image p y (.widenObjects x p path a) (.map e))
  | parent {x a e} : s.maps[e].kind = .parent → s.maps[e].source = x →
      Navigate c s x a "parent" s.maps[e].target (.image x s.maps[e].target a (.map e))
  | dereference {x a e} : s.maps[e].kind = .dereference → s.maps[e].source = x →
      Navigate c s x a "dref" s.maps[e].target (.image x s.maps[e].target a (.map e))
  | throughReference {x a name e y b} : ¬ HasField c x name →
      s.maps[e].kind = .dereference → s.maps[e].source = x →
      Navigate c s s.maps[e].target (.image x s.maps[e].target a (.map e)) name y b →
      Navigate c s x a name y b

def referenceAt (c : IR.Structural.Core n) (x : Fin n) (depth : Nat) : Option (Fin n) :=
  depth.repeat (fun v => v.bind fun i => (c.get i).reference.target) (some x)

def ReachableName (c : IR.Structural.Core n) (x : Fin n) (name : String) : Prop :=
  ∃ depth : Fin (n + 1), match referenceAt c x depth.val with
    | none => False
    | some y => HasField c y name

instance (c : IR.Structural.Core n) (x : Fin n) (name : String) : Decidable (ReachableName c x name) := by
  letI : DecidablePred (fun depth : Fin (n + 1) => match referenceAt c x depth.val with
    | none => False
    | some y => HasField c y name) := fun _ => by dsimp only; split <;> infer_instance
  unfold ReachableName
  infer_instance

inductive ScopePath (s : Support n m) : Fin n → Syntax n m → Nat → Fin n → Syntax n m → Prop where
  | here {x a} : ScopePath s x a 0 x a
  | parent {x a k p b e} : ScopePath s x a k p b →
      s.maps[e].kind = .parent → s.maps[e].source = p →
      ScopePath s x a (k + 1) s.maps[e].target (.image p s.maps[e].target b (.map e))

def NoLocal (Γ : List (Local n)) (name : String) : Prop := ∀ b ∈ Γ, b.name ≠ name
instance (Γ : List (Local n)) (name : String) : Decidable (NoLocal Γ name) := by
  unfold NoLocal; infer_instance

def Global (c : IR.Structural.Core n) (name : String) (y : Fin n) : Prop :=
  (c.get y).name = name ∧ (c.get y).origin = .user ∧
    ∀ j : Fin n, (c.get j).name = name → (c.get j).origin = .user → j = y
instance (c : IR.Structural.Core n) (name : String) (y : Fin n) : Decidable (Global c name y) := by
  unfold Global; infer_instance

def NoContext (c : IR.Structural.Core n) (x : Fin n) (name : String) (depth : Nat) : Prop :=
  ∀ k : Fin depth, match ancestor c false x k.val with
    | none => True
    | some p => p ≠ c.root → ¬ ReachableName c p name
instance (c : IR.Structural.Core n) (x : Fin n) (name : String) (depth : Nat) :
    Decidable (NoContext c x name depth) := by
  letI : DecidablePred (fun k : Fin depth => match ancestor c false x k.val with
    | none => True
    | some p => p ≠ c.root → ¬ ReachableName c p name) := fun _ => by dsimp only; split <;> infer_instance
  unfold NoContext
  infer_instance

abbrev Cursor (n m : Nat) := Option (Fin n × Syntax n m)

inductive NameRule (c : IR.Structural.Core n) (s : Support n m) (Γ : List (Local n)) :
    Cursor n m → String → Ty n → Syntax n m → Prop where
  | this : NameRule c s Γ none "this" (.collection (.objects s.context)) .this
  | local {name i b} : Γ[i]? = some b → b.name = name →
      (∀ k : Fin i, ∀ a, Γ[k.val]? = some a → a.name ≠ name) →
      NameRule c s Γ none name (.collection (.objects b.element)) (.var i)
  | special {name y a} : name = "parent" ∨ name = "dref" →
      Navigate c s s.context .this name y a →
      NameRule c s Γ none name (.collection (.objects y)) a
  | contextual {name k x a y b} : NoLocal Γ name → name ≠ "this" →
      name ≠ "parent" → name ≠ "dref" → x ≠ c.root →
      NoContext c s.context name k → ScopePath s s.context .this k x a →
      Navigate c s x a name y b → NameRule c s Γ none name (.collection (.objects y)) b
  | global {name y} : NoLocal Γ name → name ≠ "this" → name ≠ "parent" → name ≠ "dref" →
      NoContext c s.context name (n + 1) → Global c name y →
      NameRule c s Γ none name (.collection (.objects y)) (.extent y)
  | relative {x a name y b} : Navigate c s x a name y b →
      NameRule c s Γ (some (x, a)) name (.collection (.objects y)) b

/-- Context-directed conversions are explicit syntax, never an assertion that a
collection has one element or that bounded target arithmetic is safe. -/
inductive Coerces (s : Support n m) : Ty n → Syntax n m → Ty n → Syntax n m → Prop where
  | same {t a} : Coerces s t a t a
  | some {k a} : Coerces s (.collection k) a .boolean (.less (.integer 0) (.cardinality k a))
  | integer {x a} : s.integer[x] = true →
      Coerces s (.collection (.objects x)) a .integer (.integerOf x a)
  | dereference {x a e} : s.maps[e].kind = .dereference → s.maps[e].source = x →
      Coerces s (.collection (.objects x)) a (.collection (.objects s.maps[e].target))
        (.image x s.maps[e].target a (.map e))
  | widen {x y p a} : p.Valid s x y → Coerces s (.collection (.objects x)) a
      (.collection (.objects y)) (.widenObjects x y p a)
  | trans {t a u b v d} : Coerces s t a u b → Coerces s u b v d → v ≠ .boolean → Coerces s t a v d

inductive UnaryRule : String → Ty n → Syntax n m → Ty n → Syntax n m → Prop where
  | not {a} : UnaryRule "!" .boolean a .boolean (.not a)
  | negative {a} : UnaryRule "-" .integer a .integer (.arithmetic .subtract (.integer 0) a)
  | count {k a} : UnaryRule "#" (.collection k) a .integer (.cardinality k a)
  | some {k a} : UnaryRule "some" (.collection k) a .boolean (.less (.integer 0) (.cardinality k a))
  | no {op k a} : op = "no" ∨ op = "not" →
      UnaryRule op (.collection k) a .boolean (.equal .integer (.cardinality k a) (.integer 0))
  | one {k a} : UnaryRule "one" (.collection k) a .boolean (.equal .integer (.cardinality k a) (.integer 1))
  | lone {k a} : UnaryRule "lone" (.collection k) a .boolean (.less (.cardinality k a) (.integer 2))

abbrev disjunction (a b : Syntax n m) := Syntax.not (.and (.not a) (.not b))
abbrev implication (a b : Syntax n m) := Syntax.not (.and a (.not b))

def ValueType (s : Support n m) : Ty n → Prop
  | .collection (.objects x) => s.integer[x] = false ∧
      ∀ e : Fin m, s.maps[e].kind = .dereference → s.maps[e].source ≠ x
  | _ => True
instance (s : Support n m) (t : Ty n) : Decidable (ValueType s t) := by
  unfold ValueType; split <;> infer_instance

inductive BinaryRule (s : Support n m) : String → Ty n → Syntax n m → Syntax n m → Ty n → Syntax n m → Prop where
  | and {a b} : BinaryRule s "&&" .boolean a b .boolean (.and a b)
  | or {a b} : BinaryRule s "||" .boolean a b .boolean (disjunction a b)
  | xor {a b} : BinaryRule s "xor" .boolean a b .boolean (.and (disjunction a b) (.not (.and a b)))
  | implies {a b} : BinaryRule s "=>" .boolean a b .boolean (implication a b)
  | iff {a b} : BinaryRule s "<=>" .boolean a b .boolean (.and (implication a b) (implication b a))
  | equal {t a b} : ValueType s t → BinaryRule s "=" t a b .boolean (.equal t a b)
  | unequal {t a b} : ValueType s t → BinaryRule s "!=" t a b .boolean (.not (.equal t a b))
  | less {a b} : BinaryRule s "<" .integer a b .boolean (.less a b)
  | greater {a b} : BinaryRule s ">" .integer a b .boolean (.less b a)
  | le {a b} : BinaryRule s "<=" .integer a b .boolean (.not (.less b a))
  | ge {a b} : BinaryRule s ">=" .integer a b .boolean (.not (.less a b))
  | add {a b} : BinaryRule s "+" .integer a b .integer (.arithmetic .add a b)
  | subtract {a b} : BinaryRule s "-" .integer a b .integer (.arithmetic .subtract a b)
  | union {k a b} : BinaryRule s "++" (.collection k) a b (.collection k) (.setOp .union k a b)
  | difference {k a b} : BinaryRule s "--" (.collection k) a b (.collection k) (.setOp .difference k a b)
  | intersection {k a b} : BinaryRule s "**" (.collection k) a b (.collection k) (.setOp .intersection k a b)
  | subset {k a b} : BinaryRule s "in" (.collection k) a b .boolean (.subset k a b)
  | notSubset {k a b} : BinaryRule s "not in" (.collection k) a b .boolean (.not (.subset k a b))

inductive QuantifierRule (b : Local n) (domain body : Syntax n m) : String → Syntax n m → Prop where
  | all : QuantifierRule b domain body "all" (.all b domain body)
  | some : QuantifierRule b domain body "some" (.not (.all b domain (.not body)))
  | no {op} : op = "no" ∨ op = "not" → QuantifierRule b domain body op (.all b domain (.not body))

/-- Source inference rules, independent of the executable elaborator. Location,
lexical environment, navigation context and every sugar equation are explicit. -/
inductive Elaborates (c : IR.Structural.Core n) (s : Support n m) :
    List (Local n) → Cursor n m → Bool → Frontend.Expr → Ty n → Syntax n m → Prop where
  | name {Γ cursor token t a} : NameRule c s Γ cursor token.text t a →
      Elaborates c s Γ cursor false (.name token) t (.located token.span a)
  | integer {Γ cursor token value} :
      Elaborates c s Γ cursor false (.integer token value) .integer (.located token.span (.integer value))
  | parens {Γ cursor e span t a} : Elaborates c s Γ cursor false e t a →
      Elaborates c s Γ cursor false (.parens e span) t (.located span a)
  | unary {Γ cursor op e span t a u b} :
      Elaborates c s Γ cursor (op.text == "!" || op.text == "-") e t a →
      UnaryRule op.text t a u b →
      Elaborates c s Γ cursor false (.unary op e span) u (.located span b)
  | binary {Γ cursor op left right span t a b u d} :
      Elaborates c s Γ cursor true left t a → Elaborates c s Γ cursor true right t b →
      BinaryRule s op.text t a b u d →
      Elaborates c s Γ cursor false (.binary op left right span) u (.located span d)
  | dot {Γ cursor op left right span x a t b} : op.text = "." →
      Elaborates c s Γ cursor false left (.collection (.objects x)) a →
      Elaborates c s Γ (some (x, a)) false right t b →
      Elaborates c s Γ cursor false (.binary op left right span) t (.located span b)
  | quantified {Γ cursor op binder domain body span b d a out} :
      b.name = binder.text → (∀ old ∈ Γ, old.id ≠ b.id) →
      Elaborates c s Γ cursor false domain (.collection (.objects b.element)) d →
      Elaborates c s (b :: Γ) none true body .boolean a → QuantifierRule b d a op.text out →
      Elaborates c s Γ cursor false (.quantified op binder domain body span) .boolean (.located span out)
  | coerce {Γ cursor e t a u b} : Elaborates c s Γ cursor false e t a → Coerces s t a u b →
      Elaborates c s Γ cursor true e u b

structure Synth (c : IR.Structural.Core n) (s : Support n m)
    (Γ : List (Local n)) (cursor : Cursor n m) (e : Frontend.Expr) where
  type : Ty n
  term : Term n m
  derivation : Elaborates c s Γ cursor false e type term.raw

end ClaferCompiler.Frontend.Constraints
