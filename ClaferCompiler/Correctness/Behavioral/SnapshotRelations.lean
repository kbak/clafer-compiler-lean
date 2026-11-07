module

public import ClaferCompiler.Correctness.Behavioral.ExpressionsRelations
public import ClaferCompiler.Correctness.AlloyEvaluation

@[expose] public section
namespace ClaferCompiler.Correctness.Behavioral
open Backend
open Backend.Alloy
open Backend.Alloy.Behavioral

/-- The relation grammar actually emitted by M1. Diagonal and scalar syntax
belong to later static expression profiles, not these structural clauses. -/
inductive SnapshotRel : Alloy.Rel → Prop where
  | empty (a) : SnapshotRel (.empty a)
  | sig (i) : SnapshotRel (.sig i)
  | field (i) : SnapshotRel (.field i)
  | var (i) : SnapshotRel (.var i)
  | union : SnapshotRel a → SnapshotRel b → SnapshotRel (.union a b)
  | inter : SnapshotRel a → SnapshotRel b → SnapshotRel (.inter a b)
  | diff : SnapshotRel a → SnapshotRel b → SnapshotRel (.diff a b)
  | product : SnapshotRel a → SnapshotRel b → SnapshotRel (.product a b)
  | join : SnapshotRel a → SnapshotRel b → SnapshotRel (.join a b)
  | transpose : SnapshotRel a → SnapshotRel (.transpose a)

theorem SnapshotRel.term (h : SnapshotRel r) : r.Term := by
  induction h <;> constructor <;> assumption

theorem snapshotRel_sig (v : IR.Structural.Layout k) (n : Nat) :
    snapshotRel v (.sig n) = if n == 0 then live v else Temporal.Rel.inter (.sig n) (live v) := rfl

theorem snapshotRel_field (v : IR.Structural.Layout k) (n : Nat) :
    snapshotRel v (.field n) = match (Structural.fieldKeys v.core)[n]? with
      | some (d, .containment) => contains v d
      | some (d, .dereference) => deref d
      | none => Temporal.Rel.empty .binary := rfl

theorem snapshotRel_term (v : IR.Structural.Layout k) (h : SnapshotRel r) :
    (snapshotRel v r).Term := by
  induction h with
  | empty a => exact .empty a
  | sig i =>
    change (if i == 0 then live v else Temporal.Rel.inter (.sig i) (live v)).Term
    split
    · exact .join (.sig _) (.field _)
    · exact .inter (.sig _) (.join (.sig _) (.field _))
  | field i =>
    change (match (Structural.fieldKeys v.core)[i]? with
      | some (d, .containment) => contains v d
      | some (d, .dereference) => deref d
      | none => Temporal.Rel.empty .binary).Term
    split
    · rename_i d
      unfold contains
      split
      · exact .empty _
      · exact .inter (.transpose (.field _))
          (.product (.join (.sig _) (.field _))
            (.inter (.sig _) (.join (.sig _) (.field _))))
    · exact .field _
    · exact .empty _
  | var i => exact .var i
  | union ha hb ia ib =>
    unfold snapshotRel
    rw [Rel.fold_union_term ha.term hb.term]
    exact .union ia ib
  | inter ha hb ia ib =>
    unfold snapshotRel
    rw [Rel.fold_inter_term ha.term hb.term]
    exact .inter ia ib
  | diff ha hb ia ib =>
    unfold snapshotRel
    rw [Rel.fold_diff_term ha.term hb.term]
    exact .diff ia ib
  | product ha hb ia ib =>
    unfold snapshotRel
    rw [Rel.fold_product_term ha.term hb.term]
    exact .product ia ib
  | join ha hb ia ib =>
    unfold snapshotRel
    rw [Rel.fold_join_term ha.term hb.term]
    exact .join ia ib
  | transpose ha ia =>
    unfold snapshotRel
    rw [Rel.fold_transpose_term ha.term]
    exact .transpose ia

theorem snapshotRel_union (v : IR.Structural.Layout k)
    (ha : SnapshotRel a) (hb : SnapshotRel b) :
    snapshotRel v (Rel.union a b) = Temporal.Rel.union (snapshotRel v a) (snapshotRel v b) :=
  Rel.fold_union_term ha.term hb.term _ _

theorem snapshotRel_inter (v : IR.Structural.Layout k)
    (ha : SnapshotRel a) (hb : SnapshotRel b) :
    snapshotRel v (Rel.inter a b) = Temporal.Rel.inter (snapshotRel v a) (snapshotRel v b) :=
  Rel.fold_inter_term ha.term hb.term _ _

theorem snapshotRel_diff (v : IR.Structural.Layout k)
    (ha : SnapshotRel a) (hb : SnapshotRel b) :
    snapshotRel v (Rel.diff a b) = Temporal.Rel.diff (snapshotRel v a) (snapshotRel v b) :=
  Rel.fold_diff_term ha.term hb.term _ _

theorem snapshotRel_product (v : IR.Structural.Layout k)
    (ha : SnapshotRel a) (hb : SnapshotRel b) :
    snapshotRel v (Rel.product a b) = Temporal.Rel.product (snapshotRel v a) (snapshotRel v b) :=
  Rel.fold_product_term ha.term hb.term _ _

theorem snapshotRel_join (v : IR.Structural.Layout k)
    (ha : SnapshotRel a) (hb : SnapshotRel b) :
    snapshotRel v (Rel.join a b) = Temporal.Rel.join (snapshotRel v a) (snapshotRel v b) :=
  Rel.fold_join_term ha.term hb.term _ _

theorem snapshotRel_transpose (v : IR.Structural.Layout k) (ha : SnapshotRel a) :
    snapshotRel v (Rel.transpose a) = Temporal.Rel.transpose (snapshotRel v a) :=
  Rel.fold_transpose_term ha.term _ _

abbrev objectRows (rows : Alloy.Relation) : Temporal.Relation :=
  rows.map (List.map Temporal.Atom.object)

theorem objectRow_injective : Function.Injective (List.map Temporal.Atom.object) :=
  List.map_injective_iff.mpr (by intro a b h; exact Temporal.Atom.object.inj h)

theorem objectRows_dedup (rows : Alloy.Relation) :
    (objectRows rows).eraseDups = objectRows rows.eraseDups :=
  eraseDups_map_injective _ objectRow_injective rows

theorem objectRows_inter (a b : Alloy.Relation) :
    (objectRows a).filter (objectRows b).contains = objectRows (a.filter b.contains) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro row _
  simp [objectRows, objectRow_injective.eq_iff]

theorem objectRows_diff (a b : Alloy.Relation) :
    (objectRows a).filter (fun x => !(objectRows b).contains x) =
      objectRows (a.filter fun x => !b.contains x) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro row _
  simp [objectRows, objectRow_injective.eq_iff]

theorem objectRows_product (a b : Alloy.Relation) :
    ((objectRows a).flatMap fun x => (objectRows b).map (x ++ ·)).eraseDups =
      objectRows ((a.flatMap fun x => b.map (x ++ ·)).eraseDups) := by
  rw [← objectRows_dedup]
  congr 1
  simp [objectRows, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem objectRows_join (a b : Alloy.Relation) :
    ((objectRows a).flatMap fun x =>
      ((objectRows b).filter fun y => x.getLast? == y.head?).map fun y =>
        x.dropLast ++ y.drop 1).eraseDups =
      objectRows ((a.flatMap fun x =>
        (b.filter fun y => x.getLast? == y.head?).map fun y =>
          x.dropLast ++ y.drop 1).eraseDups) := by
  rw [← objectRows_dedup]
  congr 1
  simp only [objectRows, List.flatMap_map, List.map_flatMap, List.filter_map,
    List.map_map, Function.comp_def, List.getLast?_map, List.head?_map,
    List.map_dropLast, List.map_drop, List.map_append]
  congr 1
  funext x
  congr 1
  congr 1
  funext y
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact Option.map_injective (by intro a b h; exact Temporal.Atom.object.inj h) |>.eq_iff

theorem objectRows_transpose (a : Alloy.Relation) :
    ((objectRows a).map List.reverse).eraseDups =
      objectRows ((a.map List.reverse).eraseDups) := by
  rw [← objectRows_dedup]
  congr 1
  simp [objectRows, List.map_map, Function.comp_def]

-- [proof->req~compiler-behavioral-correctness~1]
/-- Substitution commutes with ordinary relational evaluation. The premises
are concrete primitive table equations; no formula truth occurs here. -/
theorem snapshotRel_eval (v : IR.Structural.Layout k) (h : SnapshotRel r)
    (s : Temporal.Schema) (w : Nat) (τ : Temporal.Trace) (t : Nat) (i : Instance)
    (signatures : ∀ n env, (snapshotRel v (.sig n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.sig n).eval i env))
    (fields : ∀ n env, (snapshotRel v (.field n)).eval s w τ (env.map .object) t =
      objectRows ((Rel.field n).eval i env)) (env : List Nat) :
    (snapshotRel v r).eval s w τ (env.map .object) t = objectRows (r.eval i env) := by
  induction h with
  | empty a => rfl
  | sig n => exact signatures n env
  | field n => exact fields n env
  | var n =>
    change (env.map Temporal.Atom.object)[n]?.toList.map (fun x => [x]) =
      objectRows ((env[n]?).toList.map (fun x => [x]))
    simp [objectRows, List.map_map, Option.toList_map, Function.comp_def]
  | union ha hb ia ib =>
    rw [snapshotRel_union v ha hb]
    rw [Temporal.Rel.eval_union (snapshotRel_term v ha) (snapshotRel_term v hb),
      Rel.eval_union ha.term hb.term, ia, ib, ← List.map_append, objectRows_dedup]
  | inter ha hb ia ib =>
    rw [snapshotRel_inter v ha hb]
    rw [Temporal.Rel.eval_inter (snapshotRel_term v ha) (snapshotRel_term v hb), ia, ib]
    simp only [Rel.eval, Rel.fold_inter_term ha.term hb.term]
    exact objectRows_inter _ _
  | diff ha hb ia ib =>
    rw [snapshotRel_diff v ha hb]
    rw [Temporal.Rel.eval_diff (snapshotRel_term v ha) (snapshotRel_term v hb), ia, ib]
    simp only [Rel.eval, Rel.fold_diff_term ha.term hb.term]
    exact objectRows_diff _ _
  | product ha hb ia ib =>
    rw [snapshotRel_product v ha hb]
    rw [Temporal.Rel.eval_product (snapshotRel_term v ha) (snapshotRel_term v hb), ia, ib]
    simp only [Rel.eval, Rel.fold_product_term ha.term hb.term]
    exact objectRows_product _ _
  | join ha hb ia ib =>
    rw [snapshotRel_join v ha hb]
    rw [Temporal.Rel.eval_join (snapshotRel_term v ha) (snapshotRel_term v hb),
      Rel.eval_join ha.term hb.term, ia, ib]
    exact objectRows_join _ _
  | transpose ha ia =>
    rw [snapshotRel_transpose v ha]
    rw [Temporal.Rel.eval_transpose (snapshotRel_term v ha), Rel.eval_transpose ha.term, ia]
    exact objectRows_transpose _

end ClaferCompiler.Correctness.Behavioral
