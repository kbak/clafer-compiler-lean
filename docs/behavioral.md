# Behavioral compiler profile

`impl~compiler-behavioral-profile-contract~1`

This contract specifies the implemented behavioral profile and its integration
gates under the
[behavioral roadmap][roadmap]. The [behavioral IR](behavioral-ir.md),
[structural handoff](behavioral-structure.md) and
[full encoding](behavioral-encoding.md#full-profile-proof-components) record library
APIs and proof boundaries. The [source workflow](behavioral-source.md) supplies
native model, check and scenario commands and the full feature evidence inventory.
The [structural contract](architecture.md) remains the implemented regression
baseline. Each implementation task still requires selection, accepted hard
dependencies and independent semantic review.

The completion profile is `behavioral-0.5.7-candidate/v1`. Its independent source
meaning is the [accepted upstream profile][profile], including the reviewed
departures D1–D5, at the immutable [source revision](sources.md#behavioral-sources).
The Haskell candidate guides syntax and comparison; its output does not define
source truth. The Lake dependency pins accepted upstream main; its
[source delta](sources.md#accepted-semantics-main-dependency) retains the static
Haskell/Alloy comparison pins and regression corpus. Candidate acceptance still
requires independent review.

The scoped compiler source amendment
[`literal-empty-navigation/1`](sources.md#behavioral-empty-navigation-and-warnings)
adds literal-rooted name-chain erasure and nonfatal self-expression warnings.
Its exact syntax, reporting and strict-domain boundaries are specified by the
[frontend contract](behavioral-frontend.md#literal-empty-navigation-and-successful-warnings).
It preserves the primary profile pin, D1–D5 and all temporal meanings.

Covers:
- `req~compiler-behavioral-profile~1`

## Ownership and interfaces

Keep `ClaferCompiler -> Clafer -> FormalCD -> DPGraph -> Mathlib`. Upstream owns
infinite traces, lifetimes, signed source meaning, surface reductions, structural
and partial-atom bridges, and lasso checking. Downstream owns executable syntax,
frontend judgments, independent Alloy temporal meaning, encoding, decoding and
compiler proofs. No generic temporal graph package is required.

The module families below are responsibility boundaries within the existing
Lake package. The [qualification inventory](qualification.md) links delivered IR,
structural, frontend, encoding and runtime declarations to their component contracts.
Public API names and exact theorem assumptions accompany each accepted implementation.
Runtime modules must
remain independent of noncomputable upstream definitions and proof-only imports.

| Owner | Module family / interface | Required handoff |
| --- | --- | --- |
| [C2: comparison tools][C2] | `scripts/oracles`, separate temporal profile | Pinned Haskell/Alloy tools, explicit temporal options, paired receipts and known comparison gaps |
| [C3: temporal target][C3] | [Temporal target APIs](alloy-temporal.md) in `Backend/Alloy/Temporal` | Independent infinite-trace interpretation, checked serialization, lasso bounds and actual Analyzer correspondence tests |
| [C4: behavioral IR][C4] | `IR/Behavioral`, `SemanticsBridge/Behavioral` | Executable declarations, signed formulas/capture, interpretation and admission agreement |
| [C5: first encoding][C5] | [First-slice encoding APIs](behavioral-encoding.md) in `Backend/Alloy/Behavioral`, `Correctness/Behavioral` | Generated lifetime/identity facts, concrete trace representation and first-slice preservation |
| [C6: structural prerequisites][C6] | [Structural library APIs and proofs](behavioral-structure.md) in `Frontend`, `IR` and `SemanticsBridge` | Richer inheritance/reference admission, defaults, typed atoms and finite integer observations |
| [C7: full frontend][C7] | [Authored frontend and reduction APIs](behavioral-frontend.md) in `Frontend/Behavioral` | Parsing, source spans, resolution, elaboration and preservation of every surface row below |
| [C8: full encoding][C8] | Behavioral backend and correctness families | All source reductions, definedness, arithmetic and full-profile trace preservation |
| [C9: resolved CLI/comparison][C9] | Behavioral parts of `Driver`, decoder and oracle adapter | Closed versioned IR/bounds/trace formats, exact trace replay and typed outcomes |
| [C10: source integration][C10] | Source driver, pipeline and qualification | Composed source pipeline, full corpus, source-matched evidence and reviewed candidate |
| [C11: final integration][C11] | Dependency/source register and integration workflow | Actual upstream-main SHA, full revalidation and concrete main-merge review |

The required API sequence is `admitBehavioral`, `compileBehavioralIR`,
`renderTemporal`, `parseBehavioral`/`elaborateBehavioral`, and `decodeTrace`.
These are interface roles, not reserved exported Lean names. Admission returns
checked data or typed diagnostics; compilation takes explicit bounds and returns
a checked target plus identity/source maps. Decoding retains a single shared
inventory and the complete lasso. C9/C10 define the exact commands and protocol
versions before implementation; no automatic input detection or solver invocation
is implied by compilation.

## Complete feature and evidence matrix

Rows B01–B32 correspond one-for-one to the [upstream disposition matrix][profile].
Its pinned paper/errata locators and source proofs apply at their actual hypotheses.
`P` denotes behavioral paper §§5–6, `T` temporal errata and `S` static errata.
C4 supplies resolved IR for every row; C7 supplies each applicable surface form.
C3 supplies independent target constructs and text. C9 supplies resolved runtime
and exact replay; C10 supplies source runtime and qualification for **every** row.
Thus a row's proof/fixture column is an obligation on its listed encoding owner,
in addition to those common frontend, IR, runtime and qualification assignments.
No row is discharged by a Markdown link or an upstream theorem alone.

| Row / source feature | Source locator / upstream owner | Frontend and encoding/proof owner | Required distinguishing witnesses |
| --- | --- | --- | --- |
| B01 declarations, abstractness, inheritance, containment | P Defs. 1–3; S6/S10; S2/S4 | C6/C7; C8 admission and live-state agreement | Nested abstract/refined parent and concrete super / wrong parent or direct abstract instance |
| B02 shared identities, permanent root, fixed types/parents | P Defs. 2, 5; T1; S2 | C4/C7; C5 trace representation | Same parent over a gap / moved identity after reappearance |
| B03 disappearance, reappearance, replacement | T1/T13; S2/S6 | C4/C7; C5/C9 | Reuse identity after absence / hide replacement with per-state renaming |
| B04 set/bag heads, typed live reference targets | P Def. 3; T11/S4; S4 | C6/C7; C8 occurrence preservation | Two bag heads to one target / duplicate set pair or absent target |
| B05 own/inherited effective groups | P Def. 3.5–6; T10–T11/S1–S5; S4 | C6/C7; C8 group correspondence | Added subtype child satisfies inherited xor / count names or targets instead of heads |
| B06 root/parent, explicit and implicit dereference | P expression equations; S7–S9; S4 | C6/C7; C8 resolved-role agreement | Actual parent, inherited target view / double dereference or fabricated abstract parent |
| B07 `this`, variables, `let`, current navigation | P Def. 4; D1; S3/S4 | C4/C6/C7; C5 capture, C8 full atoms | Captured head sees changed target / rebind to replacement or erase absent capture |
| B08 Boolean/set/relation expressions, emptiness, quantifiers, conditionals | P Def. 4, §6.1; S3/S4 | C6/C7; C8 typing, truth and definedness | Distinct heads/equal targets, empty binders / lost lexical identity or hidden undefined branch |
| B09 `X` / `next` | P Def. 4; T2; S3 | C7; C5 signed next | Parent cancellation / next false with surviving parent |
| B10 `F` / `eventually` | P §6.1; T2; S3/S6 | C7; C5 signed eventuality | Delayed event or parent end / persistent parent with no event |
| B11 `G` / `globally` | P §6.1; T2; S3/S6 | C7; C5 signed always | Body until parent end / false before parent end |
| B12 `U` / `until` | P Def. 4; T2; S3/S6 | C7; C5 strong until | Immediate right operand / left breaks before right and cancellation |
| B13 `W` / `weakuntil` | P §6.1; T2; S3/S6 | C7; C5 weak until | Left forever / neither operand before cancellation |
| B14 source negation, connective/quantifier signs | T2; S3 | C4/C7; C5 core, C8 full normalization | Both signs cancelled / both signs cannot hold with persistent parent and defined atoms |
| B15 implicit always, per-instance attachment | P §6.1; T2/T9; S3/S5 | C7; C8 attachment preservation | Recurrent event / confuse one occurrence with recurrence |
| B16 inherited `initial` | P §6.1; T7–T8; S5 | C7; C8 modifier reduction | Child at each parent birth / missing second birth |
| B17 inherited shallow `final` | P §6.1; T8; S5 | C7; C8 heads plus references | Children can change; parent gap resets / change fixed head or reference within lifetime |
| B18 `finalref`, `finaltarget`, combinations/inherited references | T8; D5; S4/S5 | C6/C7; C8 distinct modifier meanings | Target swap preserves image / swap violates finalref, inherited mutation violates final |
| B19 enum declarations and dynamic final literals | T8/CheatSheet; S5 | C6/C7; C8 enum elaboration | Dynamic literals final / accidentally enable enums in the static profile |
| B20 `initially` | P §6.1; T7; S3/S5/S6 | C7; C8 birth anchors | Time zero and reappearance / skip initial visit or second birth |
| B21 `finally` | P §6.1; T7; S3/S5/S6 | C7; C8 death anchors | Endless lifetime vacuous / require body after death |
| B22 `-->`, `-[g]->` | P §6.1; T2–T3; S5 | C7; C8 immediate transition | Parent death cancels / context death alone cannot cancel |
| B23 `-->>`, `-[g]->>` | P §6.1; T2–T3; S5 | C7; C8 eventual transition | Entry guard may lapse / source disappears before target with parent live |
| B24 declaration transitions and additional outgoing constraints | T3; S5 | C7; C8 owner preservation | Shared source attachment / accidentally attach to parent and use grandparent lifetime |
| B25 mixed guarded chains | T4; S5 | C7; C8 required sequence | All intermediate states / vacuous nested implication, missing middle or later guard |
| B26 six patterns in five scopes | P §6.1; T2/T9; D2; S5 | C7; C8 all thirty reductions | Each cell positive/negative and both signs; corrected response/precedence below |
| B27 top-level/nested universal assertions | P §4.5/§6.1; T5–T6; S5 | C7; C8 property encoding, C10 checks | Possible is not universal; every nested instance / source negation mistaken for counterexample |
| B28 possible/negative scenarios | T4–T6/T12; S5 | C7; C8 scenario composition, C10 runs | Anchored required sequence / false first source makes conditional vacuous |
| B29 syntax, precedence, aliases, disjoint/multiple binders | P §6.1; T12/CheatSheet; S5 | C7 grammar/elaboration; C8 composition | Quantifier `not`, arrow precedence, capture avoidance / change attachment or lose disjointness |
| B30 lassos and bounded reporting | P §6.2; T13; S6 | C3/C4; C5 representation, C9 replay | Nonzero prefix, loop-edge birth / empty trace, bad loop, undersized identity pool |
| B31 integer conversion, operations, extrema, folds | S11; D3; S4 | C6/C7; C8 observation and range proofs | Empty conversion 0, duplicate aggregate heads / zero divisor, infinite/noninteger observation, overflow |
| B32 declaration `=`, rejected `:=`, effective defaults | P §6.1; T10/S1–S2; D4; S4/S5 | C6/C7; C8 equation/default preservation | `=` at each live state / confuse initialization with birth, silently accept `:=` |

The first slice C5 includes resolved guarded structural snapshots, nested presence
and state-machine obligations, replacement/reappearance, X/F/G/U/W and both source
signs, with captured identity/set observations. It uses the accepted S2/S3 common
fragment and must prove reduction to the existing static backend on the actual
common domain. It is not the source frontend or full completion profile. C6/C7/C8 add
the richer rows without relaxing static admission. A partial milestone must
identify unavailable rows explicitly; it cannot close C10.

Structural prerequisites include nested abstract declarations and refined parents,
concrete supers, ordinary inherited fields, inherited/refined references and shared
head assignments, live targets, own/inherited group unions, effective/default
provenance, actual parent/root navigation, head-versus-target coercions, finite
binders and captured sets, conditionals, enums and the complete integer row.
Reuse existing structural APIs only on their proved common domain; the old M1
support guard and static `Realization.Core.Selected` do not admit all these cases.

### Pattern and errata completeness

B26 includes `never`, `sometime`, `lonce`, `always`, precedence and response in
each of whole suffix, before `r`, after `q`, between `q` and `r`, and after `q`
until `r`: all thirty cells in the [accepted surface table][surface]. C7/C8/C10
must retain its cell IDs N0–R4, positive/negative and opposite-sign witnesses.
Cover missing/repeated/simultaneous boundaries, events at boundaries, parent death
and reappearance. `lonce` counts contiguous episodes, not individual live states.

The independent source corrects response-between to check every trigger in the
active interval and precedence-after to start at the first opener. Preserve the
rejecting traces `q@0,p@1,r@3,no-s` and `q@0,p@1,q@2,s@3`, respectively. C2/C9
classify the pinned Haskell acceptances as known comparison gaps, not expected
source truth. Likewise target-image stability may permit head assignments to
swap under `finaltarget`; the pinned per-head equality is stronger.

C9 fixes the entire candidate lasso, including every frame and its loop, in both
compiler outputs and the upstream checker on their common admitted domain. Global
atom renaming is allowed; per-state renaming and stuttering are not comparison
equivalences. `X` observes step timing. Different prefix/period presentations need
proved equality of the infinite observation sequence with the same initial history,
not merely equal SAT results or an informal removal of repeated states. Retain
both discrepancy directions, negative candidates, seeds and minimized exact replays.

| Erratum | Downstream coverage |
| --- | --- |
| T1 | B02–B03/B30: reappearance, trace-wide identity and fixed parent |
| T2 | B07/B09–B15/B20–B28: signed parent cancellation, including scope premises |
| T3 | B22–B24: declaration/source attachment and additional outgoing constraints |
| T4 | B25/B28: required intermediate states and anchored scenarios |
| T5–T6 | B27–B29: universal properties, existential scenarios, correct negative conditions |
| T7 | B16/B20–B21: time-zero birth, later births, last live state |
| T8 | B17–B19: shallow inherited modifiers, reference distinction and dynamic enums |
| T9 | B15/B26: implicit always and recurrence |
| T10 | B05/B32: effective/default provenance, including the adopted numeric policy |
| T11 | B01/B04–B06: structural clauses, set keys, bag identity and effective groups |
| T12 | B28–B29: syntax, quantifier polarity and transition precedence |
| T13 | B03/B30: lasso capacity and bounded results |

### Explicit profile exclusions

This contract retains runtime strings/reals/doubles, optimization
goals, backend escapes, alternative production backends, automatic scope inference
and a source import/module system outside the behavioral compiler profile.
Single-model composition suffices for scenario queries; the paper's external
import directive is not silently erased. These dispositions belong to the
accepted profile; changing them requires explicit review. The upstream-approved
`:=` rejection is retained; `=` is
required. No exclusion removes an integer, reference or structural prerequisite
listed above. Any further omission needs an explicit profile amendment.

## Independent trace assurance

`impl~compiler-trace-assurance-contract~1`

Source meaning is an infinite trace over natural-number time with a shared
identity inventory, fixed direct types and actual parents, live extents and
time-varying references. Root is permanent, children require live parents and
reference occurrences keep their own identities. A live-state projection uses
the live carrier, not the whole allocated pool. Constant structural embedding
and static agreement are used only on the admitted common fragment with their
stated direct-type, environment, definedness and group assumptions.

Each attached constraint starts at every live context/time. Its obligation ends
at the **first absence of that context's fixed parent**, not at context absence,
and does not restart when that parent reappears. Root obligations are unbounded.
Normalize source polarity before lifetime bounding; preserve `one`/`lone`'s
classical counting barrier and strict definedness of the original formula.
Under cancellation, a formula and its source negation can both hold. Therefore
assertion counterexamples use classical `not (interpreted property)` over legal
model traces, never compilation of source-negated syntax. Scenarios require an
existential trace satisfying the model plus scenario, including its initial anchor.

Quantifiers retain chosen identities; `let` retains the captured collection.
Temporal steps preserve captures, while navigation uses current relations.
Standalone `this` is live-filtered; direct navigation starts from its fixed
identity, allowing a parent step to reach a surviving parent after context death.
The [D1 interface][formulas] is deliberately different from the paper's
snapshot-tagged evaluator. C4/C6 must preserve that distinction explicitly.

C3 defines Alloy temporal truth independently over static atom inventories,
immutable fields, mutable memberships/relations and ordinary temporal operators.
It must account for mutable `univ`/`iden`, priming, quantifier environments and
initial versus always facts when emitted. No source lifetime convention is built
into target truth. C5/C8 generate the explicit source guards and invariants.
The [Alloy 6 reference](https://alloytools.org/alloy6.html) and pinned Analyzer
source guide construct correspondence; native parsing/solving remains a tested
boundary. Initial history for emitted past operators must be justified separately
from periodic state valuations.

`TraceRep(I,B,S,A)` must have concrete equations: **one** injective correspondence
between observed source identities and designated target atoms for the entire
trace, covering every observed nonprimitive identity and every used object atom,
including reference heads. It maps root to root, preserves fixed type and parent,
each state's live declaration extents, containment and dereference tuples, and
each observed mathematical integer value. Inheritance uses the same identities;
equal bag targets do not identify their heads. Unused slots and auxiliaries have
explicit roles and capacity accounting and cannot affect source cardinalities.
Repeated frames and the loop edge use this same map. Per-state arbitrary bijections
would hide replacement and are insufficient.

The following are required theorem shapes for the complete profile. The
[first-slice handoff](behavioral-encoding.md#kernel-boundaries) records the
delivered in-memory fragment and its exact assumptions; it does not discharge
the later frontend, primitive observation or serialized runtime obligations.
`L` is an executable finite observation lasso; `unfold L` is its infinite trace.
`ObservesTrace` states data/observation equations with no satisfaction premise.
`FitsTrace` adds only explicit identity, observation, integer and temporal capacity
conditions. `T` is the result of actual successful compilation of admitted `I`.

```text
admitBehavioral(raw) = ok I
  => UpstreamWellFormed(I) and ProfileSupported(I)
elaborateBehavioral(ast) = ok I
  => DeclarativeElaboration(ast,I) and UpstreamWellFormed(I)
TargetSat(T,B,A)
  => exists L S, decodeTrace(I,B,A) = ok L
       and ObservesTrace(I,S,unfold L) and TraceRep(I,B,S,A)
       and SourceSat(I,S)
SourceSat(I,S) and ObservesTrace(I,S,unfold L) and FitsTrace(I,B,S,L)
  => exists A, encodeTrace(I,B,L) = ok A
       and TraceRep(I,B,S,A) and TargetSat(T,B,A)
checkLasso(I,L) = satisfied <=> SourceSat(I,unfold L)
  [within that checker's proved admission and observation domain]
```

Soundness derives decoder success, representation, validity and source truth
from generated target facts. It cannot assume them or an arbitrary observation
adapter's agreement. Each concrete adapter needs a proof; S6's generic agreement
hypothesis is not its discharge. Completeness covers representable ultimately
periodic observations at the selected capacities. It does not assert every
infinite trace is periodic or fits a finite identity pool. Fits cannot contain
target truth, assumed successful encoding or a preservation equivalence.
Formula preservation must retain both definedness and truth at every relevant
time/environment; normalization of truth alone is insufficient.

Kernel proofs stop at admitted in-memory syntax/trace relations unless stronger
boundaries are actually proved. Grammar recognition, serialized target grammar,
JSON/Analyzer decoding, SAT solving and native execution have separate tests.
Required mutations include per-frame renaming, changed parent after absence,
collapsed bag heads, wrong loop edge/history, context instead of parent cancellation,
lost source sign, omitted group/reference fact and overflow hidden under negation.

Covers:
- `req~compiler-trace-assurance~1`

## Bounds, arithmetic and outcomes

Identity bounds count distinct objects used across the **entire trace**, separately
from each state's multiplicities. Require per-declaration exact/upper budgets,
a total nonprimitive identity budget, explicit root/auxiliary accounting, finite
integer-observation capacity and value ranges. Do not sum overlapping inherited
extents to obtain a total budget. Allocation of unused slots and exact scopes must
have an explicit unobservable-slot policy.

A lasso has `n > 0` stored states and `0 <= loop < n`; its final edge returns to
`loop`. Record the loop index, prefix and cycle, including births/deaths on that
edge. Time zero has no previous state, even if the loop later returns to zero.
Search bounds specify minimum/maximum transitions **including** the looping edge
and any exact loop constraint separately. C3/C9 must prove/document their mapping
to Alloy `steps`, rejecting malformed ranges and never using its implicit default.
Unbounded-step solving is not claimed by this bounded profile.

Integer bitwidth is independent of identity and step budgets. Source arithmetic
uses mathematical integers, finite-set sum for implicit conversion (empty gives
zero), strict historical singleton extraction as a distinct operation, and
truncation toward zero with division/remainder undefined at divisor zero.
Empty extrema remain empty until arithmetic conversion. Explicit sum/product
retain occurrence-indexed heads (empty results 0/1); implicit conversion sums
distinct integer targets. Splitting a syntactic aggregate union must retain
occurrences; deduplicated-union agreement requires disjoint operands.

Every encoded literal/count and intermediate must fit the signed width and ranges,
including generated guards, all branches, quantified bodies and temporal frames.
C6/C8 extend range proofs to multiplication/division/remainder, extrema and folds;
they may not treat modular Alloy arithmetic as source semantics. Unsupported
range evidence is not UNSAT. Undefined operands, infinite observations or wrong
domains have no zero/false fallback. The full primitive integer domain remains
infinite; only observations are finite, with uniform trace-wide agreement and
source completion/restriction obligations. Upstream partial-domain rules require
all active observations defined, even when a truth branch could be vacuous.

| Layer / outcome | Required interpretation |
| --- | --- |
| Compile success | Complete deterministic target and maps; no satisfiability claim |
| Malformed | Syntax/schema/typing/identity/loop/bounds error, with stable diagnostic category, phase and source span or JSON pointer |
| Unsupported | Recognized profile/form or unproved representation/range capacity; never silently drop it |
| Operational failure | IO, resource, process or internal/tool error; no successful-looking partial output |
| SAT | Solver witness with complete checked decode and identity-preserving replay |
| Bounded UNSAT | No witness within recorded identity/step/integer bounds, including for an assertion counterexample search; no unrestricted validity claim |
| Unknown / timeout | Separate inconclusive results, retaining tool options and partial evidence |
| Candidate satisfied / violating / undefined | Semantic results after candidate admission, separate from malformed or unsupported candidates |

## Static separation and reuse

`compile-source`, `compile-ir`, `clafer-ir/1`, current bounds versions, static
target admission and the existing oracle profile keep their contracts. Behavioral
syntax/fields/commands require explicit new profile selection and closed schemas;
they cannot be accepted by extending static placeholders or guessing from syntax.
Retain the [parser rejection corpus](../tests/test_parser.py),
[IR protocol tests](../tests/test_cli.py), [source CLI tests](../tests/test_source_cli.py)
and [oracle temporal rejections](../tests/test_oracles.py), alongside all existing
static theorem/axiom/kernel checks. Static enum/arithmetic exclusions remain intact.

Reuse assessment: the local IR, source spans, diagnostics, static target algebra,
checked printer, native driver and exact-candidate oracle harness are useful
components; none supplies mutable target meaning or trace-wide transport. The
accepted upstream `Clafer.Behavioral` and separate `Verification` entry point
supply source meaning/proofs and finite checking. Their noncomputable normalization
and limited concrete adapters do not constitute an executable compiler normalizer
or full primitive temporal oracle. C4/C8/C9 must prove these missing correspondences.
Lean/Std containers and Parsec, Mathlib finite-set/identity results, the existing
Alloy 6.2.0 runtime and pinned Haskell adapter are the first reuse candidates.
No new library or vendored semantic definition is selected by C1.

For workflow changes, reuse upstream's MIT `tickets.py` Ready option and live-ID
regression pattern, Python `argparse`/`unittest`, existing GitHub Actions conditions
and `actionlint`; a new scheduler, dependency bot or YAML interpreter is unnecessary.
The behavioral event predicate selects the existing full check. No runtime/proof
dependency is added; future dependencies need the same semantic, maintenance and
license assessment. External tools and retained evidence remain outside source.

## Intake, review and final integration

Feature PRs target `main` and include `Closes #N`; branches use
`codex/behavioral-...`. Follow the [ticket-readiness workflow](../CONTRIBUTING.md#ticket-readiness).
Hard dependencies, including those in the other repository, require accepted
completion. Parent/sub-issue links group scope and are not extra dependencies.
The [roadmap][roadmap] owns the graph; no downstream lane may bypass its edges.

Handoffs include the accepted commit, actual APIs/theorems/assumptions, positive
and negative fixtures, immutable sources and matching validation evidence. Pin
an accepted upstream SHA in Lake and its manifest; never pin a moving branch or
an unaccepted PR head. Review deltas against both prior source and static pins.
Semantic gaps require a public disposition before dependent interpretation.

Current feature PRs use routine main checks; the full local IntentBond check
remains mandatory before handoff. Scheduled and manually dispatched full
qualification run all three jobs, including the complete reference corpora.
Scheduled full qualification checks `main`. The
[CI profile contract](build.md#ci-profiles) also retains the final-integration event rules,
separate solver jobs and existing deadlines. The required check remains
`Lean proofs and native CLI`; main's protections are preserved. Hosted protection
must separately require that
check with up-to-date branches, PR review, resolved conversations, administrator
enforcement and no force push/deletion. The single-maintainer review minimum can
remain zero; it does not remove the independent semantic-review obligation.
Inspect live protection/rulesets and retain readback externally. Missing protection
is a reported settings gap, not something CI or this document can attest is enabled.

After an accepted feature PR lands, reconcile its issue and mark it Done. Do not close on draft
publication or passing CI. Reconcile affected unstarted tickets in both Projects
after closure, reopening, dependency or scope changes. This is manual reconciliation.

Final gates, in order:

1. S7 ([upstream qualification](https://github.com/kbak/clafer-semantics/issues/129))
   accepts the full semantic candidate and source-profile disposition.
2. C10 accepts the full compiler candidate against S7's immutable behavioral SHA,
   all matrix rows, static regressions, behavioral proofs and exact comparisons.
   Include complete representative models and their deliberate counterexamples,
   and measure compilation/checking costs with explicit scopes, steps and tool versions.
3. S8 ([upstream main integration](https://github.com/kbak/clafer-semantics/issues/130))
   requires S7 and C10, reconciles main, revalidates and obtains concrete merge review.
4. C11 pins the **actual merged upstream main SHA**, updates source/manifest/contracts,
   reruns full static and behavioral qualification and obtains concrete compiler
   main-merge authorization. Changed source requires fresh evidence.

Retain historical SoSyM/static receipts, and review the delta from the pinned 0.5.7
candidate before adopting a later release. The first slice, contract acceptance
and an IntentBond exit 4 do not authorize main merges, tags or binary releases.

[roadmap]: https://github.com/kbak/clafer-compiler-lean/issues/69
[profile]: https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-profile.md
[formulas]: https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-formulas.md
[surface]: https://github.com/kbak/clafer-semantics/blob/6d04d6c856a8b86fafa58ff8f9d8ddc898bbd0f4/docs/behavioral-surface.md
[C2]: https://github.com/kbak/clafer-compiler-lean/issues/71
[C3]: https://github.com/kbak/clafer-compiler-lean/issues/72
[C4]: https://github.com/kbak/clafer-compiler-lean/issues/73
[C5]: https://github.com/kbak/clafer-compiler-lean/issues/74
[C6]: https://github.com/kbak/clafer-compiler-lean/issues/75
[C7]: https://github.com/kbak/clafer-compiler-lean/issues/76
[C8]: https://github.com/kbak/clafer-compiler-lean/issues/77
[C9]: https://github.com/kbak/clafer-compiler-lean/issues/78
[C10]: https://github.com/kbak/clafer-compiler-lean/issues/79
[C11]: https://github.com/kbak/clafer-compiler-lean/issues/80
