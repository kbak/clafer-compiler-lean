module

public import ClaferCompiler.Correctness.Behavioral.Full.ExpressionsDefined

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
open Backend.Alloy.Temporal
open Backend.Alloy.Behavioral

/-- All four emitted components use arithmetic without relation counts. -/
def PartialPure (a : Partial.Translation) : Prop :=
  FormulaPure a.truth.raw ∧ FormulaPure a.truth.positive ∧
    FormulaPure a.truth.negative ∧ FormulaPure a.defined

@[simp] theorem partial_atom (hd : FormulaPure d) (hp : FormulaPure p) : PartialPure (Partial.atom d p) := by
  simpa [PartialPure, Partial.atom, Translation.atomic] using And.intro hp (And.intro hp (And.intro hp hd))
@[simp] theorem partial_truth : PartialPure Partial.truth := partial_atom pure_truth pure_truth

theorem partial_negation (ha : PartialPure a) : PartialPure (Partial.negation a) := by
  simp_all [PartialPure, Partial.negation, negation]
theorem partial_conjunction (ha : PartialPure a) (hb : PartialPure b) : PartialPure (Partial.conjunction a b) := by
  simp_all [PartialPure, Partial.conjunction, conjunction]
theorem partial_disjunction (ha : PartialPure a) (hb : PartialPure b) : PartialPure (Partial.disjunction a b) := by
  simp_all [PartialPure, Partial.disjunction, disjunction]
theorem partial_implication (ha : PartialPure a) (hb : PartialPure b) : PartialPure (Partial.implication a b) :=
  partial_disjunction (partial_negation ha) hb
theorem partial_equivalence (ha : PartialPure a) (hb : PartialPure b) : PartialPure (Partial.equivalence a b) := by
  simp_all [PartialPure, Partial.equivalence, equivalence, implication, disjunction, conjunction, negation]
theorem partial_exclusiveOr (ha : PartialPure a) (hb : PartialPure b) : PartialPure (Partial.exclusiveOr a b) :=
  partial_negation (partial_equivalence ha hb)
theorem partial_conditional (hc : PartialPure c) (ha : PartialPure a) (hb : PartialPure b) :
    PartialPure (Partial.conditional c a b) := by
  simp_all [PartialPure, Partial.conditional, implication, disjunction, conjunction, negation]

theorem pure_totalAlways (hp : FormulaPure p) (ha : FormulaPure a) : FormulaPure (Partial.totalAlways p a) := by
  unfold Partial.totalAlways
  split <;> simp_all [always, Formula.weakUntil]

theorem partial_next (hp : FormulaPure p) (ha : PartialPure a) : PartialPure (Partial.next p a) := by
  simp_all [PartialPure, Partial.next, Translation.map, next]
theorem partial_eventually (hp : FormulaPure p) (ha : PartialPure a) : PartialPure (Partial.eventually p a) := by
  have domain := pure_totalAlways hp ha.2.2.2
  simp_all [PartialPure, Partial.eventually, eventually, always, Formula.weakUntil]
theorem partial_always (hp : FormulaPure p) (ha : PartialPure a) : PartialPure (Partial.always p a) := by
  have domain := pure_totalAlways hp ha.2.2.2
  simp_all [PartialPure, Partial.always, eventually, always, Formula.weakUntil]
theorem partial_strongUntil (hp : FormulaPure p) (ha : PartialPure a) (hb : PartialPure b) :
    PartialPure (Partial.strongUntil p a b) := by
  have domain := pure_totalAlways hp ((pure_binary .conj _ _).mpr ⟨ha.2.2.2, hb.2.2.2⟩)
  simp_all [PartialPure, Partial.strongUntil, strongUntil, weakUntil, always, Formula.weakUntil]
theorem partial_weakUntil (hp : FormulaPure p) (ha : PartialPure a) (hb : PartialPure b) :
    PartialPure (Partial.weakUntil p a b) := by
  have domain := pure_totalAlways hp ((pure_binary .conj _ _).mpr ⟨ha.2.2.2, hb.2.2.2⟩)
  simp_all [PartialPure, Partial.weakUntil, strongUntil, weakUntil, always, Formula.weakUntil]
theorem partial_initially (hp : FormulaPure p) (ha : PartialPure a) : PartialPure (Partial.initially p a) := by
  simp_all [PartialPure, Partial.initially, Translation.map, initially, Formula.birth]
theorem partial_finally (hp : FormulaPure p) (ha : PartialPure a) : PartialPure (Partial.«finally» p a) := by
  simp_all [PartialPure, Partial.«finally», Translation.map, atEnd]

theorem partial_quantify (q : IR.Behavioral.Quantifier) (domain : Rel)
    (hd : FormulaPure d) (ha : PartialPure a) (hb : PartialPure b) :
    PartialPure (Partial.quantify q domain d a b) := by
  cases q <;> simp_all [PartialPure, Partial.quantify, Translation.atomic]

theorem partial_satisfaction (ha : PartialPure a) (sign : Bool) :
    FormulaPure (Partial.satisfaction a sign) := by
  cases sign <;> simp_all [PartialPure, Partial.satisfaction]

end ClaferCompiler.Correctness.Behavioral.Full.TargetDefined
