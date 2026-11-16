# Parent-lifetime past operators

The `behavioral-rich-core/1` source profile adds `previous`, `once`, `historically`,
`since` and `triggered`. Weak previous is an internal signed/core constructor.
Prefix operators use the existing temporal-prefix precedence; since and triggered
use the strong/weak temporal binary precedence levels. Static source and the
qualified `behavioral-0.5.8/v2` profile reject past-operator syntax while retaining
these spellings as identifiers. Only the new profile reserves them as keywords.

The independent meanings are [upstream Past, Denotation and PartialObservation](https://github.com/kbak/clafer-semantics/tree/3c63d760be99741617c6af539a9e304909d18b26/Clafer/Behavioral).
The behavioral paper §5, Definitions 3–5 and §6.1 remain the source for attachment,
future lifetime restrictions and bindings; past is an explicitly selected
extension. The original attachment's parent's current lifetime bounds history.
A newly born child may observe earlier events under a continuously live parent.
A parent gap resets history. Bound identities do not replace the attachment.

For parent-presence `P` and operands `a,b`, target encodings are:

| Source constructor | Ordinary target formula |
| --- | --- |
| previous | `Y (P && a)` |
| weak previous | `!Y (P && !a)` |
| once | `P S (P && a)` |
| historically | `!(P S (P && !a))` |
| since | `(P && a) S (P && b)` |
| triggered | `!((P && !a) S (P && !b))` |

These guards apply after source sign normalization. In particular, negated
previous uses weak previous over the negatively interpreted operand. Current
parent absence makes once/since false and historically/triggered true. Strong
previous is false at time zero or an absent predecessor; weak previous is true.
Since includes its right endpoint and requires its left operand strictly after
that endpoint. Triggered is its classical dual on the guarded ordinary formulas.

Partial definedness for either previous constructor demands the operand only at
an available predecessor. Other past constructors require every operand throughout
active history, even when a truth witness is nearer. Ordinary implication remains
strict. Initializers retain their separate inactive-RHS guard and closed original
RHS environment, including temporal conditions in values.

`Correctness.Behavioral.Operators`, `Partial` and
`Full.ExpressionsFormulaTemporal` prove the guard encodings and raw/signed/domain
transport. The full recursive expression, completion and source/target
preservation theorems cover all new constructors. The first-slice native checker
uses upstream history machines and absolute-time evaluation; repeating an input
lasso clock does not imply repeating its temporal state.

## Full source observation

The supplementary Python observer is tested, not kernel-proved. It evaluates
past using absolute-time history and scans future obligations through a
compositionally justified periodic suffix. Let the input loop start be `l` and
its period be `p`. Base observations and birth/death tests repeat from `l+1`.
Pointwise constructors combine child prefixes with maximum. Next does not need
a later prefix; previous adds one. Each since/once/historically/triggered node
adds at most one period to its children's maximum prefix. Its Boolean recurrence
over one periodic block has a transfer that is either identity or constant, so
one block reaches a fixed point. The same argument applies to historical strict
definedness. Future temporal operators preserve an already periodic suffix.

This induction is uniform in fixed contexts and captured environments. Quantifier
and let domains select the same values at corresponding periodic times; their
bodies therefore use identical frozen environments. It also traverses formulas
inside integer/collection conditionals, counted bodies and context transport.
The maximum bound over the complete inspected request is used for future scans
and attached properties. This is a periodicity argument, not an arbitrary
unrolling limit or the unsupported assumption that a repeated base frame ends
history. Tests include nested previous deeper than the original loop and a
mutation that drops a violated constraint.

Exact candidate comparisons use the new profile explicitly and the same fixed
identities/loop in the independent source observer and actual Alloy solver.
They distinguish pre-birth child history, parent reset, frozen binders, temporal
initializer RHS values, inactive partial RHS observations and both positive and
negative outcomes. Existing 0.5.8 comparisons retain their own profile and known
source/reference differences.
