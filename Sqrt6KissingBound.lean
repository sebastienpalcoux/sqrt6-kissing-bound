import Sqrt6KissingBound.Core
import Sqrt6KissingBound.Analysis
import Sqrt6KissingBound.CapFraction
import Sqrt6KissingBound.Geometry
import Sqrt6KissingBound.Packing

/-!
# Toward a complete Lean certificate for the square-root-of-six kissing-number argument

`Core.lean` contains the numerical and inductive core. `Analysis.lean` proves the
one-dimensional estimates, `CapFraction.lean` constructs the actual analytic cap
data, `Geometry.lean` proves cone separation, and `Packing.lean` proves finite
spherical-cap packing. The remaining bridge identifies the normalized surface
measure of a cap with the sine-integral fraction.
-/
