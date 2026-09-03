# Exact formalization scope

## What is Lean-certified

The Lean project verifies, from its explicitly stated inputs:

1. all numerical inequalities involving `sqrt 3` and `sqrt 6` used in the proof;
2. the estimate
   \[
   \left(\frac12-\frac{9\sqrt3}{32}\right)(\sqrt6)^5>1;
   \]
3. the abstract two-step propagation
   \[
   c_n(\sqrt6)^n\ge1,\quad c_{n+2}\ge c_n/6
   \Longrightarrow c_{n+2}(\sqrt6)^{n+2}\ge1;
   \]
4. the even- and odd-dimensional inductions from the supplied base values;
5. cancellation of a positive cap fraction in
   \[
   N c_n\le1,
   \]
   yielding \(N\le(\sqrt6)^n\);
6. the exceptional dimension-three numerical deduction: from the supplied cap-packing inequality with cap fraction \((2-\sqrt3)/4\), one obtains \(N\le14<(\sqrt6)^3\);
7. the optimality implication
   \[
   6\le\alpha^2,\quad \alpha\ge0
   \Longrightarrow \sqrt6\le\alpha.
   \]

The source has no `sorry`, `admit`, project-defined `axiom`, or `native_decide`. The successful axiom audit found only Mathlib's standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

## What is not yet Lean-certified

The current project does **not** define kissing configurations or the kissing number \(\tau_n\). In particular, it does not yet formalize the bridge from geometry and analysis to the abstract inputs used by `Core.lean`.

### Spherical geometry and measure

1. A kissing configuration determines points on \(S^{n-1}\) whose pairwise angular distances are at least \(\pi/3\).
2. The spherical caps of angular radius \(\pi/6\) centered at those points have disjoint interiors.
3. Boundaries of such caps have surface measure zero, so disjoint interiors imply the packing inequality
   \[
   \tau_n c_n\le1.
   \]
4. The normalized surface area of such a cap is
   \[
   c_n=
   \frac{\int_0^{\pi/6}\sin^{n-2}t\,dt}
        {\int_0^\pi\sin^{n-2}t\,dt}.
   \]

### Integral recurrence and lower estimate

With
\[
I_m=\int_0^{\pi/6}\sin^m t\,dt,
\qquad
J_m=\int_0^\pi\sin^m t\,dt,
\]
the following steps in the manuscript remain outside the certificate:

1. the integration-by-parts identities
   \[
   I_{m+2}=\frac{m+1}{m+2}I_m-
   \frac{\sqrt3}{(m+2)2^{m+2}},
   \qquad
   J_{m+2}=\frac{m+1}{m+2}J_m;
   \]
2. the resulting exact recurrence for the actual cap fractions;
3. the substitution \(u=\sin t\) and the identity
   \[
   I_m=\int_0^{1/2}\frac{u^m}{\sqrt{1-u^2}}\,du;
   \]
4. the elementary estimate
   \[
   \frac1{\sqrt{1-u^2}}\ge 1+\frac{u^2}{2}
   \qquad(0\le u\le1/2),
   \]
   its integration, positivity of \(J_m\), and the deduction
   \[
   c_{n+2}>c_n/6;
   \]
5. derivation from the integrals of the concrete values
   \[
   c_2=\frac16,
   \qquad
   c_3=\frac{2-\sqrt3}{4},
   \qquad
   c_5=\frac12-\frac{9\sqrt3}{32}.
   \]

In Lean, the recurrence inequality and the base values `c_2` and `c_5` are fields of the explicit structure `CapData`; the packing bounds are explicit hypotheses named `hpack`. Thus these are visible assumptions, not hidden or project-defined axioms.

### Low-dimensional kissing numbers and final assembly

The facts \(\tau_1=2\) and \(\tau_2=6\) are not formalized. Consequently, the present project does not contain a single end-to-end theorem whose conclusion is
\[
\forall n\ge1,\quad \tau_n\le(\sqrt6)^n,
\]
nor a formal definition and proof of the least universal base. It certifies the numerical, inductive, and cancellation core conditional on the explicitly displayed geometric and analytic inputs above.
