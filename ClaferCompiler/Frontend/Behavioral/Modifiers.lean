module

public import ClaferCompiler.Frontend.Behavioral.Declarations
public import ClaferCompiler.IR.Behavioral.Modifiers

@[expose] public section
namespace ClaferCompiler.Frontend.Behavioral
open IR.Behavioral.Surface.Modifiers
open IR.Behavioral.Modifiers (spelling)

def modifierTokens {source : Document} (b : BoundDeclarations source) (d : Fin b.resolved.count) :
    List Token :=
  ((b.resolved.candidate.paths[d].bind (headerAt b.expanded)).map (·.modifiers)).getD []

def readModifier (t : Token) : Except Diagnostic {m : Modifier // spelling m = t.text} :=
  if h : "initial" = t.text then .ok ⟨.initial, h⟩
  else if h : "final" = t.text then .ok ⟨.final, h⟩
  else if h : "finalref" = t.text then .ok ⟨.finalref, h⟩
  else if h : "finaltarget" = t.text then .ok ⟨.finaltarget, h⟩
  else .error (Resolution.errorAt t "behavioral.modifier" "unknown behavioral modifier")

structure BoundModifiers {source : Document} (b : BoundDeclarations source) where
  declared : Vector (List Modifier) b.resolved.count
  correspondence : ∀ d, declared[d].map spelling = (modifierTokens b d).map (·.text)

-- [impl->req~compiler-behavioral-elaboration~1]
def bindModifiers {source : Document} (b : BoundDeclarations source) :
    Except Diagnostic (BoundModifiers b) := do
  let entries ← Vector.ofFnM fun d : Fin b.resolved.count =>
    (modifierTokens b d).mapM fun token => (readModifier token).map (·.val)
  if h : ∀ d, entries[d].map spelling = (modifierTokens b d).map (·.text) then
    return ⟨entries, h⟩
  else throw (Resolution.errorAt ⟨"", ⟨source.file, 0, 0⟩, 1, 1, 1⟩
    "behavioral.modifier-correspondence" "modifier binding did not preserve authored tokens")

end ClaferCompiler.Frontend.Behavioral
