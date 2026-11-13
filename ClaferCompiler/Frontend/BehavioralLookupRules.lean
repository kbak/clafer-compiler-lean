module

public import ClaferCompiler.Frontend.Defaults

@[expose] public section
namespace ClaferCompiler.Frontend.BehavioralLookupRules
open Resolution

/-- Independent relations inspect the completed table, never the resolver's
worklist, traversal budget, diagnostics or cached choices. -/
def Named (doc : Document) (c : Candidate n) (name : String) (j : Fin n) : Prop :=
  eligible doc c false name j ∧ (c.core.get j).origin = .user

instance : Decidable (Named doc c name j) := by unfold Named; infer_instance

def UniqueBest (eligible : Fin n → Prop) (score : Fin n → Nat) (j : Fin n) : Prop :=
  eligible j ∧ ∀ k, eligible k → score k ≤ score j ∧ (score k = score j → k = j)

instance {eligible : Fin n → Prop} {score : Fin n → Nat} [DecidablePred eligible] : Decidable (UniqueBest eligible score j) := by
  unfold UniqueBest; infer_instance

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem uniqueBest_unique {eligible : Fin n → Prop} {score : Fin n → Nat} (ha : UniqueBest eligible score a) (hb : UniqueBest eligible score b) : a = b := by
  exact (ha.2 b hb.1 |>.2 (Nat.le_antisymm (ha.2 b hb.1).1 (hb.2 a ha.1).1)).symm

def ancestor (c : Candidate n) (owner : Fin n) (depth : Nat) : Option (Fin n) :=
  Nat.repeat (fun p => p.bind (fun p => (c.core.get p).super)) depth (some owner)

def ChildAt (doc : Document) (c : Candidate n) (owner : Fin n) (name : String)
    (exclude : Path) (j : Fin n) (depth : Fin (n + 1)) : Prop :=
  Named doc c name j ∧ c.paths[j] ≠ some exclude ∧
  ∃ p : Fin n, ancestor c owner depth = some p ∧
    ∃ path : Path, c.paths[p] = some path ∧ (c.paths[j].getD []).dropLast = path

instance : Decidable (ChildAt doc c owner name exclude j depth) := by
  unfold ChildAt
  -- Eliminate the unbounded path witness using the retained authored path.
  exact decidable_of_iff
    (Named doc c name j ∧ c.paths[j] ≠ some exclude ∧
      ∃ p : Fin _, ancestor c owner depth = some p ∧
        c.paths[p] = some ((c.paths[j].getD []).dropLast)) (by
      constructor
      · rintro ⟨hn, he, p, hp, hx⟩; exact ⟨hn, he, p, hp, _, hx, rfl⟩
      · rintro ⟨hn, he, p, hp, path, hx, heq⟩; exact ⟨hn, he, p, hp, heq ▸ hx⟩)

-- [impl->req~compiler-behavioral-structural-bridge~1]
/-- Own children have distance zero; inherited children compete at their nearest
declaring super. A tie is rejected rather than falling through to another scope. -/
def Child (doc : Document) (c : Candidate n) (owner : Fin n) (name : String)
    (exclude : Path) (j : Fin n) : Prop :=
  ∃ d : Fin (n + 1), ChildAt doc c owner name exclude j d ∧
    ∀ k e, ChildAt doc c owner name exclude k e → d ≤ e ∧ (d = e → k = j)

instance : Decidable (Child doc c owner name exclude j) := by unfold Child; infer_instance

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem child_unique (ha : Child doc c owner name exclude a)
    (hb : Child doc c owner name exclude b) : a = b := by
  obtain ⟨da, ha, mina⟩ := ha
  obtain ⟨db, hb, minb⟩ := hb
  exact (mina b db hb |>.2 (Fin.le_antisymm (mina b db hb).1 (minb a da ha).1)).symm

def Local (doc : Document) (c : Candidate n) (self : Path) (name : String) (j : Fin n) : Prop :=
  ∃ parent : Fin n, c.paths[parent] = some self.dropLast ∧ Child doc c parent name self j

instance : Decidable (Local doc c self name j) := by unfold Local; infer_instance

def NoLocal (doc : Document) (c : Candidate n) (self : Path) (name : String) : Prop :=
  ∀ parent j d, c.paths[parent] = some self.dropLast → ¬ ChildAt doc c parent name self j d

instance : Decidable (NoLocal doc c self name) := by unfold NoLocal; infer_instance

def Lexical (doc : Document) (c : Candidate n) (self : Path) (name : String) (j : Fin n) : Prop :=
  UniqueBest (fun k => Named doc c name k ∧ c.paths[k] ≠ some self)
    (fun k => proximity self.dropLast (c.paths[k].getD [])) j

instance : Decidable (Lexical doc c self name j) := by unfold Lexical; infer_instance

/-- The local/inherited priority precedes remaining lexical/global candidates.
Concrete declarations remain eligible. -/
def Plain (doc : Document) (c : Candidate n) (self : Path) (name : String) (j : Fin n) : Prop :=
  reserved name = false ∧ (Local doc c self name j ∨
    (NoLocal doc c self name ∧ Lexical doc c self name j))

instance : Decidable (Plain doc c self name j) := by unfold Plain; infer_instance

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem local_unique {n : Nat} {doc : Document} {c : Candidate n} {self : Path} {name : String} {a b : Fin n}
    (paths : ∀ (i j : Fin n) (p : Path), c.paths[i] = some p → c.paths[j] = some p → i = j)
    (ha : Local doc c self name a) (hb : Local doc c self name b) : a = b := by
  obtain ⟨pa, hpa, ha⟩ := ha
  obtain ⟨pb, hpb, hb⟩ := hb
  have he := paths pa pb self.dropLast hpa hpb
  subst pb
  exact child_unique ha hb

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem noLocal_not_local {n : Nat} {doc : Document} {c : Candidate n} {self : Path} {name : String} (h : NoLocal doc c self name) (j : Fin n) :
    ¬ Local doc c self name j := by
  rintro ⟨parent, hp, d, hd, _⟩
  exact h parent j d hp hd

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem plain_unique {n : Nat} {doc : Document} {c : Candidate n} {self : Path} {name : String} {a b : Fin n}
    (paths : ∀ (i j : Fin n) (p : Path), c.paths[i] = some p → c.paths[j] = some p → i = j)
    (ha : Plain doc c self name a) (hb : Plain doc c self name b) : a = b := by
  rcases ha.2 with ha | ⟨na, ha⟩ <;> rcases hb.2 with hb | ⟨nb, hb⟩
  · exact local_unique paths ha hb
  · exact False.elim (noLocal_not_local nb _ ha)
  · exact False.elim (noLocal_not_local na _ hb)
  · exact uniqueBest_unique ha hb

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem plain_excludes_self {n : Nat} {doc : Document} {c : Candidate n} {self : Path} {name : String} {j : Fin n} (h : Plain doc c self name j) : c.paths[j] ≠ some self := by
  rcases h.2 with ⟨_, _, _, hd, _⟩ | ⟨_, h⟩
  · exact hd.2.1
  · exact h.1.2


def firstScore (c : Candidate n) (self : Path) (j : Fin n) : Nat :=
  let path := c.paths[j].getD []
  if path.isPrefixOf self.dropLast then path.length + 2
  else if path.length = 1 then 1 else 0

/-- Enclosing declarations precede a unique top-level or unique global match;
a sibling is not an enclosing declaration. -/
def First (doc : Document) (c : Candidate n) (self : Path) (name : String) (j : Fin n) : Prop :=
  UniqueBest (Named doc c name) (firstScore c self) j

instance : Decidable (First doc c self name j) := by unfold First; infer_instance

def Steps (doc : Document) (c : Candidate n) (names : List Name) : Fin n → Fin n → Prop :=
  names.foldr (fun name rest a b => ∃ next, Child doc c a name.text [] next ∧ rest next b)
    (fun a b => a = b)

/-- Use the project's bounded `Nat.rec` pattern so decision checking has no
compiler-generated unsafe list-recursion helper. Fuel never changes the relation. -/
def stepsDecidableAt (doc : Document) (c : Candidate n) : (fuel : Nat) →
    (names : List Name) → names.length < fuel → (a b : Fin n) → Decidable (Steps doc c names a b) :=
  Nat.rec (fun _ h _ _ => False.elim (Nat.not_lt_zero _ h))
    (fun _ next names h a b => match names with
      | [] => inferInstanceAs (Decidable (a = b))
      | name :: rest =>
        have enough : rest.length < _ := by simp only [List.length_cons] at h; omega
        have : ∀ a, Decidable (Steps doc c rest a b) := fun a => next rest enough a b
        inferInstanceAs (Decidable (∃ target, Child doc c a name.text [] target ∧ Steps doc c rest target b)))

instance stepsDecidable (names : List Name) (a b : Fin n) : Decidable (Steps doc c names a b) :=
  stepsDecidableAt doc c (names.length + 1) names (by omega) a b

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem steps_unique (names : List Name) (ha : Steps doc c names start a)
    (hb : Steps doc c names start b) : a = b := by
  induction names generalizing start with
  | nil => exact ha.symm.trans hb
  | cons name rest ih =>
    obtain ⟨na, ca, ha⟩ := ha
    obtain ⟨nb, cb, hb⟩ := hb
    have he := child_unique ca cb
    subst nb
    exact ih ha hb

def Qualified (doc : Document) (c : Candidate n) (self : Path) (path : SuperPath) (j : Fin n) : Prop :=
  path.rest ≠ [] ∧ c.paths[j] ≠ some self ∧
    ∃ first, First doc c self path.first.text first ∧ Steps doc c path.rest first j

instance : Decidable (Qualified doc c self path j) := by unfold Qualified; infer_instance

-- [proof->req~compiler-behavioral-structural-bridge~1]
theorem qualified_unique (ha : Qualified doc c self path a) (hb : Qualified doc c self path b) : a = b := by
  obtain ⟨_, _, fa, ha, sa⟩ := ha
  obtain ⟨_, _, fb, hb, sb⟩ := hb
  have he := uniqueBest_unique ha hb
  subst fb
  exact steps_unique _ sa sb

end ClaferCompiler.Frontend.BehavioralLookupRules
