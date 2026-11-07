module

public import ClaferCompiler.SemanticsBridge.Behavioral.Syntax
public import Clafer.Behavioral.PartialCompatibility

@[expose] public noncomputable section
namespace ClaferCompiler.SemanticsBridge.Behavioral.Generic
open IR.Behavioral
variable {A D A' D' : Nat → Type}

noncomputable def interpret (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n) :
    FormulaF A D n → Source.Formula A' D' n
  | .truth => .truth | .atom a => .atom (am a)
  | .not a => .not (interpret am dm a)
  | .and a b => .and (interpret am dm a) (interpret am dm b)
  | .or a b => .or (interpret am dm a) (interpret am dm b)
  | .implies a b => .implies (interpret am dm a) (interpret am dm b)
  | .iff a b => .iff (interpret am dm a) (interpret am dm b)
  | .xor a b => .xor (interpret am dm a) (interpret am dm b)
  | .ite c a b => .ite (interpret am dm c) (interpret am dm a) (interpret am dm b)
  | .next a => .next (interpret am dm a)
  | .eventually a => .eventually (interpret am dm a)
  | .always a => .always (interpret am dm a)
  | .strongUntil a b => .strongUntil (interpret am dm a) (interpret am dm b)
  | .weakUntil a b => .weakUntil (interpret am dm a) (interpret am dm b)
  | .initially a => .initially (interpret am dm a)
  | .finally a => .finally (interpret am dm a)
  | .quant q d a => .quant (quantifier q) (dm d) (interpret am dm a)
  | .letSet d a => .letSet (dm d) (interpret am dm a)

-- [proof->req~compiler-behavioral-elaboration~1]
/-- Exact constructor translation, for every tree, binder depth and source sign. -/
theorem normalize_interpret (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)] (a : FormulaF A D n) (s : Bool) (fuel : Nat)
    (enough : sizeOf a < fuel) :
    interpret am dm (FormulaF.normalizeAt fuel a enough s) = (interpret am dm a).normalize s := by
  induction a generalizing fuel s with
  | quant q d a ih =>
    cases fuel with
    | zero => omega
    | succ fuel => cases q <;> cases s <;>
      simp [FormulaF.normalizeAt_succ, FormulaF.normalizeStep, interpret, quantifier, Clafer.Behavioral.Formula.normalize, ih]
  | _ => cases fuel with
    | zero => omega
    | succ fuel => cases s <;>
      simp_all [FormulaF.normalizeAt_succ, FormulaF.normalizeStep, interpret, Clafer.Behavioral.Formula.normalize]


-- [proof->req~compiler-behavioral-elaboration~1]
/-- Truth normalization composes with any partial observation only while the
original formula supplies its strict domain. No totality premise is assumed. -/
theorem satisfies_iff_normalized (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)]
    (a : FormulaF A D n) (s : Bool) (fuel : Nat) (enough : sizeOf a < fuel)
    (τ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.PartialObservation A' D' U)
    (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (interpret am dm a).Satisfies τ O s ρ t ↔
      (interpret am dm a).Defined τ O ρ t ∧
      (interpret am dm (a.normalize s fuel enough)).raw τ O.canonical ρ t := by
  rw [FormulaF.normalize, normalize_interpret]
  unfold Clafer.Behavioral.Formula.Satisfies
  exact and_congr_right fun _ =>
    (Clafer.Behavioral.Formula.normalize_agrees τ O.canonical (interpret am dm a) s ρ t).symm

/-- Keep atom syntax fixed while observations vary with the candidate trace.
This lets model-wide properties reuse an interpretation without freezing a
particular trace into the formula's atom values. -/
def pullback (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    (O : Clafer.Behavioral.PartialObservation A' D' U) : Clafer.Behavioral.PartialObservation A D U :=
  ⟨fun a ρ t => O.atom (am a) ρ t, fun d ρ t => O.domain (dm d) ρ t⟩

def pullbackTotal (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    (O : Clafer.Behavioral.Observation A' D' U) : Clafer.Behavioral.Observation A D U :=
  ⟨fun a ρ t => O.atom (am a) ρ t, fun d ρ t => O.domain (dm d) ρ t⟩

-- [proof->req~compiler-behavioral-elaboration~1]
theorem raw_pullback (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    (τ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.Observation A' D' U)
    (a : FormulaF A D n) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (interpret (fun x => x) (fun x => x) a).raw τ (pullbackTotal am dm O) ρ t ↔
      (interpret am dm a).raw τ O ρ t := by
  induction a generalizing t <;>
    simp_all [interpret, Clafer.Behavioral.Formula.raw, pullbackTotal,
      Clafer.Behavioral.Lifetime.next, Clafer.Behavioral.Lifetime.eventually,
      Clafer.Behavioral.Lifetime.always, Clafer.Behavioral.Lifetime.strongUntil,
      Clafer.Behavioral.Lifetime.weakUntil]

theorem defined_pullback (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    (τ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.PartialObservation A' D' U)
    (a : FormulaF A D n) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (interpret (fun x => x) (fun x => x) a).Defined τ (pullback am dm O) ρ t ↔
      (interpret am dm a).Defined τ O ρ t := by
  induction a generalizing t <;>
    simp_all [interpret, Clafer.Behavioral.Formula.Defined, pullback]

theorem signed_pullback (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)]
    (τ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.Observation A' D' U)
    (a : FormulaF A D n) (s : Bool) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (interpret (fun x => x) (fun x => x) a).denote τ (pullbackTotal am dm O) s ρ t ↔
      (interpret am dm a).denote τ O s ρ t := by
  rw [← Clafer.Behavioral.Formula.normalize_agrees, ← Clafer.Behavioral.Formula.normalize_agrees]
  rw [← normalize_interpret (fun x => x) (fun x => x) a s (sizeOf a + 1) (by omega),
    ← normalize_interpret am dm a s (sizeOf a + 1) (by omega)]
  exact raw_pullback am dm τ O _ ρ t

theorem satisfies_pullback (am : ∀ {n}, A n → A' n) (dm : ∀ {n}, D n → D' n)
    [∀ n, SizeOf (A n)] [∀ n, SizeOf (D n)]
    (τ : Clafer.Behavioral.Trace C U) (O : Clafer.Behavioral.PartialObservation A' D' U)
    (a : FormulaF A D n) (s : Bool) (ρ : Clafer.Behavioral.Environment U n) (t : Nat) :
    (interpret (fun x => x) (fun x => x) a).Satisfies τ (pullback am dm O) s ρ t ↔
      (interpret am dm a).Satisfies τ O s ρ t :=
  and_congr (defined_pullback am dm τ O a ρ t) (signed_pullback am dm τ O.canonical a s ρ t)

end ClaferCompiler.SemanticsBridge.Behavioral.Generic
