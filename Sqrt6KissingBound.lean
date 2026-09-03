import Sqrt6KissingBound.Core
import Sqrt6KissingBound.Analysis
import Sqrt6KissingBound.CapFraction
import Sqrt6KissingBound.Geometry
import Sqrt6KissingBound.Packing
import Sqrt6KissingBound.CapMeasure

/-!
# Toward a complete Lean certificate for the square-root-of-six kissing-number argument

`Core.lean` contains the numerical and inductive core. `Analysis.lean` proves the
one-dimensional estimates, `CapFraction.lean` constructs the actual analytic cap
data, `Geometry.lean` proves cone separation, `Packing.lean` proves finite
spherical-cap packing, and `CapMeasure.lean` relates caps to radial sectors. The
remaining bridge computes the normalized sector volume.
-/
