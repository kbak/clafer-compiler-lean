module
public import Clafer.Examples.Telematics.Expressions
import all Clafer.Constraints.Typing
import all Init.Data.Int.Repr
import all Init.Data.Repr

@[expose] public section

namespace ClaferCompiler.Tests.ConstraintInventory
open Clafer.Constraints

noncomputable def widening {s : Support} {x y} : Widen s x y → List Nat
  | .same _ => [] | .inclusion e _ => [(s.mapRef e).owner.value]
  | .trans p q => widening p ++ widening q
termination_by structural p => p

/-- Independent projection of the pinned manual expressions. This does not call
the frontend or its normalizer. It retains every constructor and resolved ID. -/
noncomputable def shape {s : Support} {Γ t} : Expr s Γ t → String
  | .boolean b => toString b | .integer i => toString i | .this => "this"
  | .extent x => s!"extent{(s.classId x).value}" | .var i => s!"var{i.index}"
  | .map e => (match (s.mapRef e).kind with
      | .head => "head" | .parent => "parent" | .dereference => "dref"
      | .inclusion => "super" | .target => "target") ++ toString (s.mapRef e).owner.value
  | .and a b => s!"and({shape a},{shape b})" | .not a => s!"not({shape a})"
  | .equal a b => s!"eq({shape a},{shape b})" | .less a b => s!"lt({shape a},{shape b})"
  | .arithmetic op a b => (match op with | .add => "add" | .subtract => "sub") ++ s!"({shape a},{shape b})"
  | .integerOf _ a => s!"int({shape a})" | .cardinality a => s!"count({shape a})"
  | .setOp op a b => (match op with | .union => "union" | .difference => "diff" | .intersection => "inter") ++ s!"({shape a},{shape b})"
  | .subset a b => s!"subset({shape a},{shape b})" | .image a b => s!"image({shape a},{shape b})"
  | .join a b => s!"join({shape a},{shape b})"
  | .widenObjects p a => (widening p).foldl (fun text id => s!"super{id}({text})") (shape a)
  | .widenRelation _ _ _ => "RELATION-WIDEN"
  | .all b _ d a => s!"all[{b.id.value}:{(s.classId b.element).value}]({shape d},{shape a})"

termination_by structural e => e

def image (owner : Nat) (a : String) : String := s!"image({a},head{owner})"
def dereference (owner : Nat) (a : String) : String := s!"image({a},dref{owner})"
def widen (owner : Nat) (a : String) : String := s!"super{owner}({a})"
def some (a : String) : String := s!"lt(0,count({a}))"
def implies (a b : String) : String := s!"not(and({a},not({b})))"
def iff (a b : String) : String := s!"and({implies a b},{implies b a})"

def expected : List String :=
  let small := image 3 (image 2 "this")
  let cache := image 5 "this"
  let version := fun a => s!"int({dereference 9 (image 9 a)})"
  let allSizes := image 2 (widen 13 (image 13 (widen 15 (image 15 "extent14"))))
  [implies s!"and({some small},{some cache})" (some (image 7 (image 6 cache))),
   s!"not(lt({version (widen 11 "this")},{version (widen 10 (dereference 12 (image 12 "this")))}))",
   s!"eq(count({image 5 (widen 13 (image 13 (widen 15 "this")))}),0)",
   s!"eq({dereference 12 (image 12 (widen 15 "this"))},{widen 14 "image(this,parent15)"})",
   iff (some (image 22 (image 20 "this"))) (some "extent17"),
   iff (some (image 23 "this")) s!"eq(count({image 15 (widen 16 "extent16")}),2)",
   iff (some (image 23 "this")) (implies (some "extent17") s!"eq(count({image 15 (widen 17 "extent17")}),2)"),
   iff (some (image 26 (image 24 "this"))) s!"not({some (image 3 allSizes)})",
   iff (some (image 25 (image 24 "this"))) s!"not({some (image 4 allSizes)})",
   some (image 22 (image 20 "extent19")), some (image 23 "extent19"), some (image 26 (image 24 "extent19"))]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- All twelve expected trees are kernel-checked against the existing upstream
manual inventory, independently of the native compiler comparison. -/
theorem expected_is_manual :
    (List.finRange 12).map (fun i => shape (Clafer.Examples.Telematics.Expressions.inventory i).body) = expected := by
  decide +kernel

end ClaferCompiler.Tests.ConstraintInventory
