module

public import ClaferCompiler.IR.Behavioral.Surface

@[expose] public section
namespace ClaferCompiler.Tests.BehavioralSurface
open IR.Behavioral IR.Behavioral.Surface

def p : Formula 4 n := .atom (.inhabited (.extent 0))
def q : Formula 4 n := .atom (.inhabited (.extent 1))
def r : Formula 4 n := .atom (.inhabited (.extent 2))
def s : Formula 4 n := .atom (.inhabited (.extent 3))

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

-- [utest->req~compiler-behavioral-elaboration~1]
def run : IO Unit := do
  let chain : Transitions.Chain 4 0 := ⟨[⟨p, some q, .immediate⟩, ⟨r, some s, .eventual⟩], p⟩
  check "conditional entry, required later guard, eventual persistence" <|
    match Transitions.expand Transitions.presence chain with
    | .implies (.and (.atom (.inhabited (.extent 0))) (.atom (.inhabited (.extent 1))))
        (.next (.and (.and (.atom (.inhabited (.extent 2))) (.atom (.inhabited (.extent 3))))
          (.strongUntil (.and (.atom (.inhabited .this)) (.atom (.inhabited (.extent 2))))
            (.atom (.inhabited (.extent 0)))))) => true
    | _ => false
  check "declaration keeps this as source and context" <|
    match Transitions.declaration none .eventual (⟨[], p⟩ : Transitions.Chain 4 0) with
    | .implies (.atom (.inhabited .this))
        (.strongUntil (.and (.atom (.inhabited .this)) (.atom (.inhabited .this)))
          (.atom (.inhabited (.extent 0)))) => true
    | _ => false
  check "response between checks every trigger, before the closing boundary" <|
    match Patterns.expand (.follow (s : Formula 4 0) p) (.between q r) with
    | .always (.implies _ (.strongUntil
        (.implies (.atom (.inhabited (.extent 0)))
          (.strongUntil (.not (.atom (.inhabited (.extent 2))))
            (.and (.atom (.inhabited (.extent 3))) (.not (.atom (.inhabited (.extent 2)))))))
        (.atom (.inhabited (.extent 2))))) => true
    | _ => false
  check "precedence after cannot choose a later opener" <|
    match Patterns.expand (.precede (s : Formula 4 0) p) (.after q) with
    | .implies (.eventually (.atom (.inhabited (.extent 1))))
        (.strongUntil (.not (.atom (.inhabited (.extent 1))))
          (.and (.atom (.inhabited (.extent 1)))
            (.weakUntil (.not (.atom (.inhabited (.extent 0)))) (.atom (.inhabited (.extent 3)))))) => true
    | _ => false
  check "finalref captures head reference with explicit self-survival" <|
    match Modifiers.expand (0 : Fin 4) .finalref with
    | [(.heads 0, .letSet (.thisStep (.deref 0))
        (.next (.implies (.atom (.inhabited .this))
          (.atom (.equal (.var 0) (.thisStep (.deref 0)))))))] => true
    | _ => false
  check "finaltarget captures complete target image" <|
    match Modifiers.expand (0 : Fin 4) .finaltarget with
    | [(.all, .letSet (.step (.deref 0) (.thisStep (.child 0)))
        (.next (.implies (.atom (.inhabited .this))
          (.atom (.equal (.var 0) (.step (.deref 0) (.thisStep (.child 0))))))))] => true
    | _ => false
  check "final retains both head and reference obligations" ((Modifiers.expand (0 : Fin 4) .final).length == 2)
  check "initial uses parent births" <|
    match Modifiers.expand (0 : Fin 4) .initial with
    | [(.parents 0, .initially (.atom (.inhabited (.thisStep (.child 0)))))] => true
    | _ => false
  IO.println "behavioral pattern, chain and modifier reductions passed"
end ClaferCompiler.Tests.BehavioralSurface
