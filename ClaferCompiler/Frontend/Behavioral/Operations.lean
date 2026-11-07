module

public import ClaferCompiler.Frontend.Behavioral.ExpressionCore
public import ClaferCompiler.Frontend.Behavioral.Traversal

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral.Expressions
open IR.Behavioral Values ValueRules

inductive AggregateTerm (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold) :
    Value k n → Expression.Integer k n → Prop where
  | head {a : Value k n} {domain : Expression.Collection k n} (input : Heads a type domain)
      (view : Target v (.collection type (.set (.var 0)) : Value k (n + 1)) b)
      (targets : Heads b targetType targetValue) (numeric : targetType = .integers ∨ targetType = .empty) :
      AggregateTerm v op a (.fold op (.cons domain .nil) (.extract targetValue))

inductive Aggregate (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold) :
    List (Value k n) → Value k n → Prop where
  | operands (terms : Traversal.Related (AggregateTerm v op) inputs out) : Aggregate v op inputs
      (.integer (out.foldl (fun acc term => .binary (if op == .sum then .add else .multiply) acc term)
        (.literal (if op == .sum then 0 else 1))))

def aggregateTermCertified (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold)
    (a : Value k n) : Except String {term // AggregateTerm v op a term} := do
  let input ← MonadAttach.attach (heads a)
  let view ← MonadAttach.attach (target v (.collection input.val.1 (.set (.var 0)) : Value k (n + 1)))
  let targets ← MonadAttach.attach (heads view.val)
  if hn : targets.val.1 = .integers ∨ targets.val.1 = .empty then
    return ⟨.fold op (.cons input.val.2 .nil) (.extract targets.val.2),
      .head (heads_sound input.property) (target_sound v view.property) (heads_sound targets.property) hn⟩
  throw "behavioral.expected-integer"

-- [impl->req~compiler-behavioral-elaboration~1]
def aggregateCertified (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold)
    (inputs : List (Value k n)) : Except String {value // Aggregate v op inputs value} := do
  let terms ← Traversal.list (aggregateTermCertified v op) inputs
  return ⟨.integer (terms.val.foldl (fun acc term => .binary (if op == .sum then .add else .multiply) acc term)
    (.literal (if op == .sum then 0 else 1))), .operands terms.property⟩

def aggregate (v : IR.BehavioralStructural.Validated k) (op : IR.BehavioralArithmetic.Fold)
    (inputs : List (Value k n)) : Except String (Value k n) := (aggregateCertified v op inputs).map Subtype.val

def booleanCertified (a : Value k n) : Except String {b // Boolean a b} := do
  let b ← MonadAttach.attach (boolean a)
  return ⟨b.val, boolean_sound b.property⟩

inductive ArrowSpelling : String → Surface.Transitions.Arrow → Prop where
  | immediate : ArrowSpelling "-->" .immediate
  | eventual : ArrowSpelling "-->>" .eventual

inductive ChainTail : Value k n → Surface.Transitions.ChainF (Expression.Atom k) (Expression.Collection k) n → Prop where
  | chain : ChainTail (.chain a) a
  | formula : ChainTail (.formula a) ⟨[], a⟩
  | collection : ChainTail (.collection type a) ⟨[], present a⟩

inductive Chain (spelling : String) : Value k n → Option (Value k n) → Value k n → Value k n → Prop where
  | link (arrow : ArrowSpelling spelling kind) (source : Boolean a p) (guard : Option.Rel Boolean b q)
      (tail : ChainTail c rest) : Chain spelling a b c (.chain ⟨⟨p, q, kind⟩ :: rest.links, rest.target⟩)

def arrowCertified (text : String) : Except String {a // ArrowSpelling text a} :=
  if h : text = "-->" then .ok ⟨.immediate, by subst text; exact .immediate⟩
  else if h : text = "-->>" then .ok ⟨.eventual, by subst text; exact .eventual⟩
  else .error "behavioral.arrow"

def chainTailCertified (a : Value k n) : Except String {b // ChainTail a b} :=
  match a with
  | .chain rest => .ok ⟨rest, .chain⟩
  | .formula a => .ok ⟨⟨[], a⟩, .formula⟩
  | .collection _ a => .ok ⟨⟨[], present a⟩, .collection⟩
  | .integer _ => .error "behavioral.expected-formula"

-- [impl->req~compiler-behavioral-elaboration~1]
def chainCertified (arrow : Token) (source : Value k n) (guard : Option (Value k n))
    (target : Value k n) : Except String {value // Chain arrow.text source guard target value} := do
  let arrow ← arrowCertified arrow.text
  let source ← booleanCertified source
  let guard ← Traversal.option booleanCertified guard
  let target ← chainTailCertified target
  return ⟨.chain ⟨⟨source.val, guard.val, arrow.val⟩ :: target.val.links, target.val.target⟩,
    .link arrow.property source.property guard.property target.property⟩

def chain (arrow : Token) (source : Value k n) (guard : Option (Value k n))
    (target : Value k n) : Except String (Value k n) := (chainCertified arrow source guard target).map Subtype.val

inductive PatternKind : String → Expression.Formula k n → Option (Expression.Formula k n) →
    Surface.Patterns.Pattern (Expression.Formula k n) → Prop where
  | never : PatternKind "never" p none (.never p)
  | sometime : PatternKind "sometime" p none (.sometime p)
  | lonce : PatternKind "lonce" p none (.lonce p)
  | always : PatternKind "always" p none (.always p)
  | precede : PatternKind "precede" p (some s) (.precede p s)
  | follow : PatternKind "follow" p (some s) (.follow p s)

inductive PatternScope : Option String → Option (Expression.Formula k n) → Option (Expression.Formula k n) →
    Surface.Patterns.Scope (Expression.Formula k n) → Prop where
  | suffix : PatternScope none none none .suffix
  | before : PatternScope (some "before") none (some r) (.before r)
  | after : PatternScope (some "after") (some q) none (.after q)
  | between : PatternScope (some "between") (some q) (some r) (.between q r)
  | afterUntil : PatternScope (some "after until") (some q) (some r) (.afterUntil q r)

inductive Pattern (kind : String) (scope : Option String) : Value k n → Option (Value k n) →
    Option (Value k n) → Option (Value k n) → Value k n → Prop where
  | expand (first : Boolean a p) (second : Option.Rel Boolean b s)
      (opener : Option.Rel Boolean c q) (closer : Option.Rel Boolean d r)
      (pat : PatternKind kind p s pattern) (sc : PatternScope scope q r region) :
      Pattern kind scope a b c d (.formula (Surface.Patterns.expand pattern region))

def patternKindCertified (kind : String) (p : Expression.Formula k n) (s : Option (Expression.Formula k n)) :
    Except String {pat // PatternKind kind p s pat} :=
  match s with
  | none =>
    if h : kind = "never" then .ok ⟨.never p, by subst kind; exact .never⟩
    else if h : kind = "sometime" then .ok ⟨.sometime p, by subst kind; exact .sometime⟩
    else if h : kind = "lonce" then .ok ⟨.lonce p, by subst kind; exact .lonce⟩
    else if h : kind = "always" then .ok ⟨.always p, by subst kind; exact .always⟩
    else .error "behavioral.pattern-shape"
  | some s =>
    if h : kind = "precede" then .ok ⟨.precede p s, by subst kind; exact .precede⟩
    else if h : kind = "follow" then .ok ⟨.follow p s, by subst kind; exact .follow⟩
    else .error "behavioral.pattern-shape"

def patternScopeCertified (scope : Option String) (q r : Option (Expression.Formula k n)) :
    Except String {sc // PatternScope scope q r sc} :=
  match scope, q, r with
  | none, none, none => .ok ⟨.suffix, .suffix⟩
  | some text, none, some r =>
    if h : text = "before" then .ok ⟨.before r, by subst text; exact .before⟩ else .error "behavioral.scope-shape"
  | some text, some q, none =>
    if h : text = "after" then .ok ⟨.after q, by subst text; exact .after⟩ else .error "behavioral.scope-shape"
  | some text, some q, some r =>
    if h : text = "between" then .ok ⟨.between q r, by subst text; exact .between⟩
    else if h : text = "after until" then .ok ⟨.afterUntil q r, by subst text; exact .afterUntil⟩
    else .error "behavioral.scope-shape"
  | _, _, _ => .error "behavioral.scope-shape"

-- [impl->req~compiler-behavioral-elaboration~1]
def patternCertified (kind : Token) (first : Value k n) (second : Option (Value k n))
    (scope : Option Token) (opener closer : Option (Value k n)) :
    Except String {value // Pattern kind.text (scope.map (·.text)) first second opener closer value} := do
  let p ← booleanCertified first
  let s ← Traversal.option booleanCertified second
  let q ← Traversal.option booleanCertified opener
  let r ← Traversal.option booleanCertified closer
  let pat ← patternKindCertified kind.text p.val s.val
  let sc ← patternScopeCertified (scope.map (·.text)) q.val r.val
  return ⟨.formula (Surface.Patterns.expand pat.val sc.val),
    .expand p.property s.property q.property r.property pat.property sc.property⟩

def pattern (kind : Token) (first : Value k n) (second : Option (Value k n))
    (scope : Option Token) (opener closer : Option (Value k n)) : Except String (Value k n) :=
  (patternCertified kind first second scope opener closer).map Subtype.val

end ClaferCompiler.Frontend.Behavioral.Expressions
