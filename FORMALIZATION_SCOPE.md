# Exact formalization scope

This document describes the complete certificate's statements and proof dependencies. Verification status belongs to the build and axiom-audit records for the exact source version; this scope statement does not replace those checks.

## Main statements and hypotheses

`IsKissingConfiguration X` means that `X` is a finite subset of the Euclidean space `EuclideanSpace ℝ (Fin n)`, every member has norm one, and distinct members have inner product at most `1/2`. This is the standard spherical-code definition of a kissing configuration. For unit vectors, the inner-product condition is equivalent to pairwise Euclidean distance at least one.

The principal theorem, `kissingConfiguration_card_le_sqrt6_pow`, states

\[
  n\ge1,\quad \operatorname{IsKissingConfiguration}(X)
  \quad\Longrightarrow\quad |X|\le(\sqrt6)^n.
\]

Its only hypotheses are the dimension restriction and the defining conditions on `X`. No cap-area formula, packing inequality, recurrence, or low-dimensional kissing bound is supplied as an additional assumption.

`kissingNumber n` is a natural number representing the largest realizable configuration size. The finite-configuration theorem first supplies a finite ceiling. The definition then takes the greatest realizable size below that ceiling. `kissingNumber_realized` and `kissingNumber_isGreatest` establish that this number is attained and dominates every realizable size. Thus the ceiling does not impose an unproved restriction on the maximum. `kissingNumber_le_sqrt6_pow` gives the theorem in the usual kissing-number notation.

## Geometric proof used by the certificate

The complete proof uses ordinary Euclidean volume and bodies contained in disjoint cones. It does not require the general spherical-cap area formula.

For a unit vector `x`, `strictCone x` consists of vectors `y` satisfying

\[
  \frac{\sqrt3}{2}\|y\|<\langle x,y\rangle.
\]

Cone separation follows from the inner-product hypotheses. Orthogonal images of a measurable body inside the standard cone and unit ball are disjoint, so their volumes satisfy a finite packing inequality. Coordinate measure preservation, Fubini's theorem, ball scaling, and one-dimensional integration provide the required body volumes.

Write \(V_n\) for the volume of the unit ball in dimension \(n\), and put \(a=\sqrt3/2\). The standard bicone has transverse radius \(t/\sqrt3\) for \(0<t<a\), and \((2+\sqrt3)(1-t)\) for \(a<t<1\). Its volume is

\[
  \frac{V_{n-1}}{n2^{n-1}},
  \qquad
  |X|\frac{V_{n-1}}{n2^{n-1}}\le V_n.
\]

The dimension cases are as follows.

- **Dimension one:** the unit sphere has at most two points, and \(2<\sqrt6\).
- **Dimension two:** bicone packing gives \(|X|\le2\pi<7\), hence \(|X|\le6\).
- **Dimension three:** the upper bicone profile is replaced by \(\sqrt{1-t^2}\). Its squared profile integrates exactly. Together with the lower cone this gives volume \(\pi(2-\sqrt3)/3\), yielding \(|X|<15\), hence \(|X|\le14<(\sqrt6)^3\).
- **Dimension four:** the upper profile is replaced by \(p(t)=(1-t)(14t+2-6\sqrt3)\). Polynomial inequalities establish \(0\le p(t)\le\sqrt{1-t^2}\) on \([a,1]\). Exact integration gives total volume \(T V_3\), where \(T=(265352-153195\sqrt3)/320\). Rational bounds on \(\sqrt3\) and \(\pi\) give \(37T V_3>V_4\), hence \(|X|\le36=(\sqrt6)^4\).
- **Dimension five:** the bicone bound gives \(|X|\le256/3\), hence \(|X|\le85<(\sqrt6)^5\).
- **Dimensions at least six:** the unit-ball recurrence proves \(V_n\le V_{n-1}\). Bicone packing therefore gives \(|X|\le n2^{n-1}\), and numerical induction proves \(n2^{n-1}\le(\sqrt6)^n\).

These cases are assembled in `KissingBound.lean`.

## Optimality

`Optimality.lean` constructs the six vertices of a regular hexagon explicitly, verifies their norms and pairwise inner products, and proves that they form a configuration of cardinality six. It follows that `kissingNumber_two_eq_six` has the expected value.

`sqrt6_isLeast_universalKissingBase` states that \(\sqrt6\) is the least nonnegative real number \(\alpha\) bounding every finite kissing configuration by \(\alpha^n\) in every positive dimension. The upper bound proves admissibility; the explicit hexagon forces \(6\le\alpha^2\). No assumed value of the planar kissing number is needed for this argument.

## Relation to the manuscript's cap proof

The manuscript's original proof uses the sine-integral cap fraction and a two-step recurrence. The complete geometric certificate uses the bicone argument above. Consequently, an unconditional certificate of the main theorem does not by itself certify every intermediate identity in the original proof.

The general identity equating normalized spherical-cap area with

\[
  \frac{\int_0^{\pi/6}\sin^{n-2}t\,dt}
       {\int_0^\pi\sin^{n-2}t\,dt}
\]

remains outside this proof route. No assertion that this identity has been formalized follows from the complete theorem.

The analytic modules provide a companion route through sine-integral recurrences, positivity, base values, and a chord-based lower estimate. The final root imports these modules, and the axiom audit includes their declarations. They are not geometric assumptions of the bicone theorem. The earlier abstract `CapData` results likewise retain their displayed hypotheses and should be distinguished from the unconditional configuration and kissing-number theorems.
