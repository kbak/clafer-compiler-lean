module

public import ClaferCompiler.IR.Structural

@[expose] public section
namespace ClaferCompiler.IR.Structural.Normalization

-- [impl->req~compiler-resolved-normalization~1]
/-- A parentless abstract has no local containment fiber. All other slots,
including the concrete root's bounds, remain outside this normal form. -/
def NormalForm (m : Core n) : Prop :=
  ∀ d, (m.get d).parent = none → (m.get d).isAbstract = true →
    (m.get d).localBounds = {}

def declaration (d : Declaration α) : Declaration α :=
  { d with localBounds := if d.parent.isNone && d.isAbstract then {} else d.localBounds }

/-- Pure projection, not admission. Use `checked` for untrusted typed inputs. -/
def normalize (m : Core n) : Core n :=
  { m with declarations := m.declarations.map declaration }

-- [proof->req~compiler-resolved-normalization~1]
@[simp] theorem get_normalize (m : Core n) (d : Fin n) :
    (normalize m).get d = declaration (m.get d) := by
  simp [normalize, Core.get]

/-- Restoring the sole rewritten field recovers the exact original declaration. -/
theorem declaration_preserves (d : Declaration α) :
    { declaration d with localBounds := d.localBounds } = d := rfl

@[simp] theorem root_preserved (m : Core n) : (normalize m).root = m.root := rfl

theorem unchanged (m : Core n) (d : Fin n)
    (h : (m.get d).parent ≠ none ∨ (m.get d).isAbstract = false) :
    (normalize m).get d = m.get d := by
  have hb : ((m.get d).parent.isNone && (m.get d).isAbstract) = false := by
    rcases h with hp | ha
    · simp [hp]
    · simp [ha]
  simp only [get_normalize, declaration, hb, Bool.false_eq_true, ite_false]

theorem normal_form (m : Core n) : NormalForm (normalize m) := by
  intro d hp ha
  simp only [get_normalize, declaration] at hp ha ⊢
  simp [hp, ha]

theorem fixed (m : Core n) (h : NormalForm m) : normalize m = m := by
  have hd : ∀ d : Fin n, declaration (m.get d) = m.get d := by
    intro d
    have hb : (if (m.get d).parent.isNone && (m.get d).isAbstract then
        ({} : Bounds) else (m.get d).localBounds) = (m.get d).localBounds := by
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
        exact (h d hc.1 hc.2).symm
      · rfl
    unfold declaration
    rw [hb]
  cases m with
  | mk ds root =>
    unfold normalize
    congr 1
    apply Vector.ext
    intro i hi
    simpa [Core.get] using hd ⟨i, hi⟩

theorem idempotent (m : Core n) : normalize (normalize m) = normalize m :=
  fixed _ (normal_form m)

theorem core_checked (m : Core n) (k : Certificate n) (h : coreChecks m k) :
    coreChecks (normalize m) k := by
  rcases h with ⟨ids, origins, root, parents, supers, bounds, abstracts⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [declaration] using ids
  · simpa [declaration] using origins
  · simpa [declaration] using root
  · simpa [declaration] using parents
  · simpa [declaration] using supers
  · intro d
    simp only [get_normalize, declaration]
    constructor
    · split
      · trivial
      · exact (bounds d).1
    · exact (bounds d).2
  · simpa [declaration] using abstracts

theorem support_checked (m : Core n) (k : Certificate n) (h : supportChecks m k) :
    supportChecks (normalize m) k := by
  rcases h with ⟨origins, abstracts, supers, targets, groups, unused, propagate⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [declaration] using origins
  · intro d ha
    have ha' : (m.get d).isAbstract = true := by simpa [declaration] using ha
    obtain ⟨hp, hr, hc, hg, _⟩ := abstracts d ha'
    simpa [declaration, hp, ha'] using
      (show (m.get d).parent = none ∧ (m.get d).reference = .basic ∧
        (∀ c, (m.get c).parent ≠ some d) ∧ (m.get d).groupBounds = {} from ⟨hp, hr, hc, hg⟩)
  · simpa [declaration] using supers
  · simpa [declaration] using targets
  · simpa [declaration] using groups
  · simpa [declaration] using unused
  · simpa [declaration] using propagate

-- [impl->req~compiler-resolved-normalization~1]
/-- Total on the existing admitted M1 domain, with the exact original certificate. -/
def admitted (v : Validated n) : Validated n :=
  ⟨normalize v.core, v.certificate, core_checked _ _ v.coreChecked,
    support_checked _ _ v.supportChecked⟩

/-- Validate the original input first: normalization must not repair invalid
intervals or remove an unsupported zero-bound abstract's admission obligation. -/
def checked (m : Core n) (k : Certificate n) : Except Diagnostic (Validated n) :=
  admitted <$> validate m k

-- [proof->req~compiler-resolved-normalization~1]
@[simp] theorem admitted_certificate (v : Validated n) :
    (admitted v).certificate = v.certificate := rfl

theorem admitted_fixed (v : Validated n) (h : NormalForm v.core) : admitted v = v := by
  cases v
  simp only [admitted, fixed _ h]

theorem admitted_idempotent (v : Validated n) : admitted (admitted v) = admitted v :=
  admitted_fixed _ (normal_form v.core)

theorem checked_error (m : Core n) (k : Certificate n) (e : Diagnostic)
    (h : validate m k = .error e) : checked m k = .error e := by
  unfold checked
  rw [h]
  rfl

theorem checked_admitted (v : Validated n) : checked v.core v.certificate = .ok (admitted v) := by
  unfold checked validate
  simp only [dite_eq_left v.coreChecked, dite_eq_left v.supportChecked]
  rfl

theorem checked_fixed (v : Validated n) (h : NormalForm v.core) :
    checked v.core v.certificate = .ok v := by
  rw [checked_admitted, admitted_fixed v h]

theorem checked_again (v : Validated n) :
    checked (admitted v).core (admitted v).certificate = .ok (admitted v) :=
  checked_fixed _ (normal_form v.core)

/-- Every successful checked result is explicit and is accepted unchanged on
the next pass, including its original certificate and metadata. -/
theorem checked_success (m : Core n) (k : Certificate n) (w : Validated n)
    (h : checked m k = .ok w) : NormalForm w.core ∧
      checked w.core w.certificate = .ok w := by
  unfold checked at h
  cases hv : validate m k with
  | error e =>
    rw [hv] at h
    contradiction
  | ok v =>
    rw [hv] at h
    change Except.ok (admitted v) = .ok w at h
    cases h
    exact ⟨normal_form v.core, checked_again v⟩

end ClaferCompiler.IR.Structural.Normalization
