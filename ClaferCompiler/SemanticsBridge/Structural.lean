module

public import ClaferCompiler.IR.Structural
public import Clafer.Verification.Admission

@[expose] public section
namespace ClaferCompiler.SemanticsBridge.Structural
open IR.Structural

/-- Pure field interpretation; no admission or satisfaction is hidden in this map. -/
def bounds (r : Bounds) : DPGraph.Predicates.Range :=
  ⟨r.lower, match r.upper with | .finite n => .finite n | .unbounded => .unbounded⟩

def origin : Origin → Clafer.Origin
  | .syntheticRoot => .syntheticRoot | .user => .user
  | .integer => .primitive .int | .string => .primitive .string | .boolean => .primitive .bool

def reference : Reference α → Clafer.MCS.ReferenceTo α
  | .basic => .basic | .set t => .set t | .bag t => .bag t

def interpret (m : Core n) : Clafer.Semantics.EffectiveCore n where
  family := {
    parent := fun d => (m.get d).parent
    reference := fun d => reference (m.get d).reference
    super := fun d => (m.get d).super
    origin := fun d => origin (m.get d).origin
    isAbstract := fun d => (m.get d).isAbstract
    name := fun d => (m.get d).name
    multiplicity := fun d => bounds (m.get d).localBounds
    group := fun d => ⟨none, .bounds (bounds (m.get d).groupBounds)⟩
    root := m.root }
  id := fun d => ⟨(m.get d).id⟩
  group := fun d => bounds (m.get d).groupBounds

def certificate (k : Certificate n) : Clafer.Verification.CoreCertificate n :=
  ⟨fun d => k.parentRank[d], fun d => k.superRank[d], fun d => k.unused[d]⟩

@[simp] theorem bounds_lower (r : Bounds) : (bounds r).lower = r.lower := rfl

@[simp] theorem bounds_valid (r : Bounds) : Clafer.ValidRange (bounds r) ↔ r.Valid := by
  cases r with | mk l u => cases u <;> rfl

@[simp] theorem bounds_unrestricted (r : Bounds) :
    bounds r = Clafer.unrestricted ↔ r = {} := by
  cases r with | mk l u => cases u <;> simp [bounds, Clafer.unrestricted]

@[simp] theorem bounds_zero (r : Bounds) :
    bounds r = ⟨0, .finite 0⟩ ↔ r = ⟨0, .finite 0⟩ := by
  cases r with | mk l u => cases u <;> simp [bounds]

@[simp] theorem origin_root (o : Origin) : origin o = .syntheticRoot ↔ o = .syntheticRoot := by
  cases o <;> simp [origin]

@[simp] theorem origin_user (o : Origin) : origin o = .user ↔ o = .user := by
  cases o <;> simp [origin]

@[simp] theorem reference_basic (r : Reference α) : reference r = .basic ↔ r = .basic := by
  cases r <;> simp [reference]

@[simp] theorem reference_target (r : Reference α) : (reference r).target = r.target := by
  cases r <;> rfl

/-- Both directions: executable core guards are exactly the upstream certificate guards. -/
theorem coreChecks_iff (m : Core n) (k : Certificate n) :
    coreChecks m k ↔ Clafer.Verification.coreChecks (interpret m) (certificate k) := by
  simp [coreChecks, Clafer.Verification.coreChecks, interpret, certificate,
    Function.Injective]

/-- Both directions, including unused abstract chains and positive group guards. -/
theorem supportChecks_iff (m : Core n) (k : Certificate n) :
    supportChecks m k ↔ Clafer.Verification.supportChecks (interpret m) (certificate k) := by
  simp [supportChecks, Clafer.Verification.supportChecks, interpret, certificate]

/-- A validated value supplies actual upstream well-formedness and support hypotheses. -/
theorem validated_domain (v : Validated n) :
    (interpret v.core).WellFormed ∧ (interpret v.core).Supported := by
  have hc := (coreChecks_iff v.core v.certificate).mp v.coreChecked
  have hs := (supportChecks_iff v.core v.certificate).mp v.supportChecked
  exact ⟨Clafer.Verification.admitted_wellFormed _ _ hc hs,
    Clafer.Verification.admitted_supported _ _ hs⟩

theorem validate_success_iff (m : Core n) (k : Certificate n) :
    (∃ v, validate m k = .ok v) ↔ coreChecks m k ∧ supportChecks m k := by
  unfold validate
  split <;> rename_i hc
  · split <;> simp_all
  · simp_all

/-- Successful admission preserves the whole table, including metadata and head identity. -/
theorem validate_preserves (m : Core n) (k : Certificate n) (v : Validated n)
    (h : validate m k = .ok v) : v.core = m ∧ v.certificate = k := by
  unfold validate at h
  split at h
  · split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- Completeness is existential in the checked auxiliary certificate, not in source models.
Bad supplied ranks/certificates may fail without implying semantic inconsistency. -/
theorem admission_complete (m : Core n)
    (wf : (interpret m).WellFormed) (hs : (interpret m).Supported) :
    ∃ k v, validate m k = .ok v := by
  obtain ⟨k, hc, hk⟩ := Clafer.Verification.certificate_exists (interpret m) wf hs
  let ck : Certificate n := ⟨Vector.ofFn k.parentRank, Vector.ofFn k.superRank,
    Vector.ofFn k.unused⟩
  have he : certificate ck = k := by
    cases k
    simp [certificate, ck]
  have a : coreChecks m ck := (coreChecks_iff m ck).mpr (by simpa [he] using hc)
  have b : supportChecks m ck := (supportChecks_iff m ck).mpr (by simpa [he] using hk)
  exact ⟨ck, (validate_success_iff m ck).mpr ⟨a, b⟩⟩

/-- The admitted domain is exactly the independently defined upstream domain. -/
theorem admission_iff (m : Core n) :
    (∃ k v, validate m k = .ok v) ↔
      (interpret m).WellFormed ∧ (interpret m).Supported := by
  constructor
  · rintro ⟨k, v, hv⟩
    have he := (validate_preserves m k v hv).1
    simpa [he] using validated_domain v
  · rintro ⟨wf, hs⟩
    exact admission_complete m wf hs

/-- Lookup returns an index carrying the requested ID, independent of names. -/
theorem lookup_sound (rows : Vector (Declaration α) n) (id : DeclId) (i : Fin n)
    (h : lookup rows id = some i) : rows[i].id = id := by
  have found := List.find?_some h
  simpa only [beq_iff_eq] using found

/-- Every existing ID is found; uniqueness makes its index unambiguous. -/
theorem lookup_complete (rows : Vector (Declaration α) n) (i : Fin n)
    (unique : ∀ d e : Fin n, rows[d].id = rows[e].id → d = e) :
    lookup rows rows[i].id = some i := by
  cases h : lookup rows rows[i].id with
  | none =>
    have hn := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp at hn
  | some j =>
    have he := unique j i (lookup_sound rows _ j h)
    subst j
    rfl

/-- Every semantic projection is a direct field map, without guards or satisfaction. -/
theorem interpret_fields (m : Core n) (d : Fin n) :
    (interpret m).id d = ⟨(m.get d).id⟩ ∧
    (interpret m).family.root = m.root ∧
    (interpret m).family.parent d = (m.get d).parent ∧
    (interpret m).family.super d = (m.get d).super ∧
    (interpret m).family.reference d = reference (m.get d).reference ∧
    (interpret m).family.name d = (m.get d).name ∧
    (interpret m).family.origin d = origin (m.get d).origin ∧
    (interpret m).family.isAbstract d = (m.get d).isAbstract ∧
    (interpret m).family.multiplicity d = bounds (m.get d).localBounds ∧
    (interpret m).group d = bounds (m.get d).groupBounds := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The raw-ID boundary cannot produce a value outside the upstream domain. -/
theorem validateRaw_domain (r : Raw) (v : Validated r.declarations.size)
    (_success : validateRaw r = .ok v) :
    (interpret v.core).WellFormed ∧ (interpret v.core).Supported := validated_domain v

theorem resolveId_roundtrip (rows : Vector (Declaration DeclId) n) (index : Fin n)
    (id : DeclId) (j : Fin n) (h : resolveId rows index id = .ok j) : rows[j].id = id := by
  unfold resolveId at h
  split at h
  · cases h
    exact lookup_sound rows _ _ (by assumption)
  · cases h

theorem resolveOption_roundtrip (rows : Vector (Declaration DeclId) n) (index : Fin n)
    (input : Option DeclId) (output : Option (Fin n))
    (h : input.mapM (resolveId rows index) = .ok output) :
    output.map (fun j => rows[j].id) = input := by
  cases input with
  | none => cases h; rfl
  | some id =>
    cases hj : resolveId rows index id with
    | error e => simp [Option.mapM, hj] at h
    | ok j =>
      simp [Option.mapM, hj] at h
      subst output
      exact congrArg some (resolveId_roundtrip rows index id j hj)

theorem resolveReference_roundtrip (rows : Vector (Declaration DeclId) n) (index : Fin n)
    (input : Reference DeclId) (output : Reference (Fin n))
    (h : resolveReference rows index input = .ok output) :
    output.mapIds (fun j => rows[j].id) = input := by
  cases input with
  | basic => cases h; rfl
  | set id | bag id =>
    cases hj : resolveId rows index id with
    | error e => simp [resolveReference, hj] at h
    | ok j =>
      simp [resolveReference, hj] at h
      subst output
      exact congrArg _ (resolveId_roundtrip rows index id j hj)

/-- Replacing resolved indices with their original IDs reconstructs every field. -/
theorem resolveDeclaration_roundtrip (rows : Vector (Declaration DeclId) n) (index : Fin n)
    (d : Declaration (Fin n)) (h : resolveDeclaration rows index = .ok d) :
    d.mapIds (fun j => rows[j].id) = rows[index] := by
  cases hp : rows[index.val].parent.mapM (resolveId rows index) with
  | error e => simp [resolveDeclaration, hp, bind, Except.bind] at h
  | ok parent =>
    cases hs : rows[index.val].super.mapM (resolveId rows index) with
    | error e => simp [resolveDeclaration, hp, hs, bind, Except.bind] at h
    | ok super =>
      cases hr : resolveReference rows index rows[index.val].reference with
      | error e => simp [resolveDeclaration, hp, hs, hr, bind, Except.bind] at h
      | ok ref =>
        simp [resolveDeclaration, hp, hs, hr, bind, Except.bind] at h
        have hd : rows[index].withEdges parent super ref = d := Except.ok.inj h
        subst d
        have ep := resolveOption_roundtrip rows index _ _ hp
        have es := resolveOption_roundtrip rows index _ _ hs
        have er := resolveReference_roundtrip rows index _ _ hr
        simp only [Declaration.mapIds, Declaration.withEdges] at ep es er ⊢
        rw [ep, es, er]
        rfl

end ClaferCompiler.SemanticsBridge.Structural
