module

public import ClaferCompiler.Backend.Alloy.InheritedViews

public import ClaferCompiler.Backend.Alloy.Semantics
public import ClaferCompiler.Backend.Alloy.Print
public import ClaferCompiler.Backend.Alloy.Structural
public import ClaferCompiler.Backend.Alloy.Decode
public import ClaferCompiler.Backend.Alloy.ExpressionAttachments

public section
/-! Static Alloy ownership: syntax/meaning #8, printer #9, translation #10/#13/#15.
The independent target core, checked serializer, guarded structural translation
and inherited extension are implemented. Selected #15 adds typed constraint
translation and attachment enforcement; source CLI integration belongs to #20. -/
