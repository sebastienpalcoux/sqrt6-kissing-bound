import Sqrt6KissingBound.Core
import Sqrt6KissingBound.Analysis
import Sqrt6KissingBound.CapFraction
import Sqrt6KissingBound.Geometry
import Sqrt6KissingBound.Packing
import Sqrt6KissingBound.CapMeasure
import Sqrt6KissingBound.KissingNumber

/-!
# The square-root-of-six kissing-number bound

`Core.lean` contains the numerical and inductive core. `Analysis.lean` proves the
one-dimensional estimates, `CapFraction.lean` constructs the actual analytic cap
data, `Geometry.lean` proves cone separation, `Packing.lean` proves finite
spherical-cap packing, and `CapMeasure.lean` relates caps to radial sectors. The
unconditional theorem uses Euclidean-volume packing of explicit bodies. Its
dimension-specific estimates and the regular-hexagon optimality argument are
imported through `KissingNumber.lean`.
-/
