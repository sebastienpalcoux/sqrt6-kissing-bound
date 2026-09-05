import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Development probe for the bicone packing proof
-/

open Set Metric MeasureTheory
open scoped ENNReal

#check EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
#check AffineSubspace.euclideanHausdorffMeasure_eq_lintegral
#check Submodule.measurableEquivProd
#check Submodule.measurePreserving_measurableEquivProd
#check InnerProductSpace.volume_ball
#check InnerProductSpace.volume_ball_of_dim_even
#check InnerProductSpace.volume_ball_of_dim_odd
#check MeasureTheory.volume_prod
#check MeasureTheory.Measure.prod_apply
#check MeasureTheory.MeasurePreserving.measure_preimage
#check LinearIsometryEquiv.measurePreserving
#check Submodule.orthogonalDecomposition
#check Submodule.orthogonalProjection
#check Submodule.mem_orthogonal_singleton_iff_inner_left
#check Submodule.finrank_orthogonal_add_finrank
#check Module.finrank_orthogonal_span_singleton
#check intervalIntegral.integral_pow
#check MeasureTheory.Measure.addHaar_ball
#check MeasureTheory.Measure.addHaar_ball_of_pos
#check MeasureTheory.Measure.addHaar_smul
