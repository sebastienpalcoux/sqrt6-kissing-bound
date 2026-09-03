import Sqrt6KissingBound.Core
import Sqrt6KissingBound.Analysis
import Sqrt6KissingBound.CapFraction
import Sqrt6KissingBound.Geometry

/-!
# Toward a complete Lean certificate for the square-root-of-six kissing-number argument

`Core.lean` contains the numerical and inductive core. `Analysis.lean` proves the
one-dimensional estimates, `CapFraction.lean` constructs the actual analytic cap
data, and `Geometry.lean` develops the cone-packing geometry. Further files on
volume will assemble the end-to-end theorem.
-/
