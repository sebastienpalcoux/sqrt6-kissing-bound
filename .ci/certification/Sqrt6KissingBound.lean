import Sqrt6KissingBound.Core
import Sqrt6KissingBound.Supremum
import Sqrt6KissingBound.ManuscriptLemmas

/-!
# The universal square-root-of-six bound for kissing numbers

The final public theorems are in `KissingBound`, `KissingNumber`, `Optimality`,
and `Supremum`. Their proof proceeds through measurable disjoint cone bodies,
exact rotational profile volumes, dimension-specific estimates, and a regular
planar hexagon. `ManuscriptLemmas` records the strict sine-integral recurrence.

`Core` retains the earlier conditional numerical lemmas for reference. The final
configuration and kissing-number theorems do not assume a cap-packing inequality,
a cap-area formula, an exceptional-dimensional bound, or a numerical hypothesis.
The exact trusted dependencies are checked by `Axioms.lean` and `scripts/check.sh`.
-/
