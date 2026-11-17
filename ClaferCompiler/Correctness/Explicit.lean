module

public import ClaferCompiler.Driver.ExplicitCore
public import ClaferCompiler.Correctness.Behavioral.Full.ModifierCore

@[expose] public noncomputable section
namespace ClaferCompiler.Correctness.Explicit
open Backend.Alloy.Temporal Backend.Alloy.Behavioral.Full Correctness.Behavioral.Full

-- [proof->req~compiler-rich-core-explicit~1]
/-- Independently imported core requests use the same preservation theorem as
source elaboration. The primitive declaration and finite observation assumptions
are explicit; the JSON parser/printer remains an executable testing boundary. -/
theorem sound (c : Driver.ExplicitCore.Product k) (p : Fin k)
    (primitive : (c.request.model.structural.core.structural.get p).origin = .integer)
    (target : Lasso) (sat : Satisfies c.compiled.module.raw target.unfold) :
    ∃ decoded : Σ o steps, ObservedLasso k o steps,
      decode c.request.model.structural target = .ok decoded ∧
      SourceResult c.request completeIntegers (completeTrace c.request.model.structural p decoded.2.2) :=
  compiled_sound c.request c.bounds c.fuel c.compiled c.compiled_checked p primitive target sat

-- [proof->req~compiler-rich-core-explicit~1]
theorem complete (c : Driver.ExplicitCore.Product k) (p : Fin k)
    (primitive : (c.request.model.structural.core.structural.get p).origin = .integer)
    (source : ObservedLasso k o steps) (fit : Fits c.request.model.structural p source c.bounds)
    (sat : SourceResult c.request completeIntegers (completeTrace c.request.model.structural p source)) :
    Lasso.Satisfies c.compiled.module.raw (encode source) :=
  compiled_complete c.request c.bounds c.fuel c.compiled c.compiled_checked p primitive source fit sat

end ClaferCompiler.Correctness.Explicit
