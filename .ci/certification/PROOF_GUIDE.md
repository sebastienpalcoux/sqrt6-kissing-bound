# Guide to the full geometric certificate

This guide describes the proof implemented by the complete-certificate candidates. Verification status must be read from the clean-build and axiom-audit results, not inferred from the presence of this file.

## Statement and normalization

A normalized kissing configuration is a finite set X of vectors in real Euclidean n-space satisfying norm(x) = 1 and dist(x,y) >= 1 for distinct members. The distance condition is proved equivalent to inner(x,y) <= 1/2. Rescaling the centers of equal unit balls tangent to a central unit ball by a factor of 1/2 gives this normalization.

The target theorem bounds |X| by (sqrt(6))^n for every positive integer n. The definition of the kissing number is accompanied by proofs that its value is realized and is at least every realizable configuration cardinality. Thus the final kissing-number bound is about a genuine attained maximum, not an assumed function or an unproved bound on cardinalities.

## Disjoint cones and exact volumes

For a unit vector x, consider the open cone defined by

    (sqrt(3)/2) * norm(y) < inner(x,y).

Two such cones are disjoint whenever their axes have inner product at most 1/2. The proof uses orthogonal components and Cauchy--Schwarz; it does not assume a spherical packing theorem.

Write a = sqrt(3)/2. In coordinates (t,v) about the first axis, an inscribed bicone has radial profile

    t/sqrt(3)              for 0 < t < a,
    (2 + sqrt(3))*(1 - t)  for a < t < 1.

Both pieces lie in the open unit ball and the strict cone. Fubini's theorem and volume-preserving orthonormal coordinates give its exact n-dimensional volume

    V_(n-1) / (n * 2^(n-1)),

where V_d is the volume of the d-dimensional unit ball. Reflections transport this body to every unit axis without changing volume. Additivity and containment in the unit ball imply

    |X| * V_(n-1) / (n * 2^(n-1)) <= V_n.

## Dimensions

For n >= 6, the unit-ball volume recurrence proves V_n <= V_(n-1), and a two-step induction proves n*2^(n-1) <= (sqrt(6))^n. The cases n = 2 and n = 5 follow from the exact low-dimensional unit-ball volumes and the integral nature of |X|.

Dimension one is handled by the two points on the unit sphere. Dimension three uses the upper profile sqrt(1-t^2), combined with the lower half of the bicone. Its volume is ((2-sqrt(3))/3)*V_2, giving |X| <= 14.

Dimension four uses the explicitly verified polynomial profile

    g(t) = (1-t)*(14*t + 2 - 6*sqrt(3)),  a < t < 1.

The proof checks g >= 0 and g^2 <= 1-t^2. Together with the lower half of the bicone, its volume is

    ((265352 - 153195*sqrt(3))/320)*V_3.

Exact rational bounds on sqrt(3) and pi give |X| < 37 and hence |X| <= 36. No exact value of the three- or four-dimensional kissing number is assumed.

## Sharpness and supremum

The six vertices of a regular planar hexagon are given by explicit coordinates. Their norms, pairwise separation, and cardinality are checked. Consequently any nonnegative universal exponential base alpha must satisfy 6 <= alpha^2 and therefore alpha >= sqrt(6).

The set of positive-dimensional roots tau_n^(1/n) is proved bounded above by sqrt(6), with equality at n=2. Its greatest element and its supremum are therefore both sqrt(6).

## Relation to the manuscript

The final configuration bound, the least-universal-base characterization, and the equivalent supremum assertion match the manuscript's principal statements. The sine-integral recurrence is separately formalized for the actual integral-defined cap fractions, including its strict inequality.

The end-to-end geometric proof uses ambient-volume packing and the explicit bodies above. It is an alternative proof of the manuscript's principal results, not a claim to have translated every sentence of its spherical-cap proof. In particular, the final theorem does not assume a cap-area formula, a packing inequality, or exceptional-dimensional estimates.

The original manuscript is preserved unchanged. Its historical disclosure about the earlier conditional certificate should not be mistaken for the status of a later, separately audited certificate.
